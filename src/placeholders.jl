# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Placeholder sentinel emission, resolution, and AST post-processing.
#
# During pattern walking, length checks and type casts are emitted as
# placeholder sentinel calls (e.g. `__length_check`, `__cast_to_packed`)
# since the final byte counts and type sizes aren't known yet. After
# the full pattern has been walked, `resolve_sentinel_in_expr!`,
# `fold_static_branches!`, and `implement_casting!` replace these
# sentinels with concrete expressions or compile-time constants.

## Sentinel shape validation

sentinel_err(expr::Expr, nargs::Int) =
    ArgumentError("Malformed $(first(expr.args)) sentinel: expected $(nargs - 1) args, got $(length(expr.args) - 1) in $(repr(expr))")

## Sentinel emission

"""
    emit_lengthcheck(state, nctx, n_expr[, n_min, n_max]) -> Expr

Emit a `__length_check` sentinel that will be resolved after pattern walking.

Resolves to `true` when the branch's static byte guarantee covers `n_max`,
or to a runtime `nbytes - pos + 1 >= n_expr` check otherwise. `n_min` and
`n_max` default to `n_expr` for fixed-width segments.
"""
function emit_lengthcheck(::ParserState, nctx::NodeCtx, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    b = nctx[:current_branch]
    Expr(:call, :__length_check, b.id, b.parsed_max, n_min, n_max, n_expr)
end

function emit_static_lengthcheck(::ParserState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__static_length_check, b.id, b.parsed_max, n)
end

function emit_lengthbound(::ParserState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__length_bound, b.id, b.parsed_max, n)
end

## Sentinel resolution helpers

function resolve_branch_check(b::ParseBranch)
    local_min = b.parsed_min - b.start_min
    local_min <= 0 && return true
    # Root branch is resolved by assemble_parsebytes, not here
    parent_remaining = (b.parent::ParseBranch).parsed_min - b.start_max
    if parent_remaining >= local_min
        true
    else
        :(nbytes - pos + 1 >= $local_min)
    end
end

## Length-check resolution

"""
    resolve_sentinel_in_expr!(expr, branches)

Resolve the length sentinels within `expr` in place: each folds to a constant
when its branch's minimum length, less the bytes that may already be consumed
when it was emitted, covers what it needs, and otherwise becomes a runtime check
against `pos`.
"""
function resolve_sentinel_in_expr!(expr::Expr, branches::Vector{ParseBranch})
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args)
            s = first(arg.args)
            if s === :__length_check
                length(arg.args) == 6 || throw(sentinel_err(arg, 6))
                _, branch_id, emission_max, _, n_max, n_expr = arg.args
                if branches[branch_id].parsed_min - emission_max >= n_max
                    expr.args[i] = true
                else
                    r = :(nbytes - pos + 1 >= $n_expr)
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__static_length_check
                length(arg.args) == 4 || throw(sentinel_err(arg, 4))
                _, branch_id, emission_max, n = arg.args
                expr.args[i] = branches[branch_id].parsed_min - emission_max >= n
            elseif s === :__length_bound
                length(arg.args) == 4 || throw(sentinel_err(arg, 4))
                _, branch_id, emission_max, n = arg.args
                if branches[branch_id].parsed_min - emission_max >= n
                    expr.args[i] = n
                else
                    r = :(min($n, nbytes - pos + 1))
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__branch_check
                length(arg.args) == 3 || throw(sentinel_err(arg, 3))
                if arg.args[2] === Bool
                    resolved = resolve_branch_check(branches[arg.args[3]])
                    if resolved isa Expr
                        arg.head, arg.args = resolved.head, resolved.args
                    else
                        expr.args[i] = resolved
                    end
                end
                # __branch_check(Int, id) is left for the assembly pass
            else
                resolve_sentinel_in_expr!(arg, branches)
            end
        else
            resolve_sentinel_in_expr!(arg, branches)
        end
    end
end

## Static branch folding

function fold_branches!(items::AbstractVector)
    splices = Tuple{Int, Vector{Any}}[]
    changed = false
    for (i, item) in enumerate(items)
        item isa Expr || continue
        # Normalize `!Bool` → `Bool` so the next check handles both
        if item.head in (:if, :elseif) &&
               Meta.isexpr(item.args[1], :call, 2) &&
               item.args[1].args[1] === :! && item.args[1].args[2] isa Bool
            item.args[1] = !item.args[1].args[2]
        end
        # A static operand settles a condition: `true || x` is true, `false && x` false
        cond = if item.head in (:if, :elseif) item.args[1] end
        if Meta.isexpr(cond, (:||, :&&)) && cond.args[1] isa Bool
            item.args[1] = if (cond.head === :||) == cond.args[1]; cond.args[1] else cond.args[2] end
        end
        if item.head in (:if, :elseif) && item.args[1] isa Bool
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head === :|| && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[] else Any[item.args[2]] end))
            changed = true
        elseif item.head === :&& && item.args[1] isa Bool
            push!(splices, (i, if item.args[1] Any[item.args[2]] else Any[] end))
            changed = true
        else
            changed |= fold_branches!(item.args)
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(items, i, replacement)
    end
    changed
end

function take_branch(expr::Expr)
    if expr.args[1]::Bool
        body = expr.args[2]
    elseif length(expr.args) >= 3
        body = expr.args[3]
        if body isa Expr && body.head === :elseif
            body.head = :if
        end
    else
        return Any[]
    end
    if body isa Expr && body.head === :block
        filter(e -> !(e isa LineNumberNode), body.args)
    else
        Any[body]
    end
end

## Casting resolution

"""
    implement_casting!(state, exprlikes) -> exprlikes

Replace `__cast_to_packed` / `__cast_from_packed` sentinels with the appropriate
`Core.bitcast`, `zext_int`, or `trunc_int` call, now that the final type
size is known, and each `__packed_shift(position)` with the literal shift that
aligns a bit `position` (counted from the MSB) with the LSB.

Compares physical type sizes (`sizeof`) for intrinsic selection, since
`zext_int`/`trunc_int` operate on physical widths not logical bit counts.
This matters for embedded packed types whose `nbits` may be less than
`8*sizeof`.
"""
function implement_casting!(state::ParserState, exprlikes::Vector{<:ExprVarLine})
    targetsize = cld(state.bits, 8)
    for expr in exprlikes
        if expr isa Expr
            implement_casting!(expr, state.name, targetsize)
        end
    end
    exprlikes
end

function implement_casting!(expr::Expr, name::Symbol, targetsize::Int)
    if Meta.isexpr(expr, :call, 3) && first(expr.args) in (:__cast_to_packed, :__cast_from_packed)
        casttype, valtype, value = expr.args
        targettype, targetbits, valbits = if casttype == :__cast_to_packed
            esc(name), targetsize, sizeof(valtype)
        else
            valtype, sizeof(valtype), targetsize
        end
        expr.args[1:3] = if valbits == targetbits
            :(Core.bitcast($targettype, $value)).args
        elseif valbits < targetbits
            :(Core.Intrinsics.zext_int($targettype, $value)).args
        else
            :(Core.Intrinsics.trunc_int($targettype, $value)).args
        end
    end
    for (i, arg) in enumerate(expr.args)
        if Meta.isexpr(arg, :call, 2) && first(arg.args) === :__packed_shift
            expr.args[i] = 8 * targetsize - arg.args[2]::Int
        elseif arg isa Expr
            implement_casting!(arg, name, targetsize)
        end
    end
    expr
end
