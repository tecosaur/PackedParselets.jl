# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Placeholder sentinel emission, resolution, and AST post-processing.
#
# During pattern walking, length checks and type casts are emitted as
# placeholder sentinel calls (e.g. `__length_check`, `__cast_to_packed`)
# since the final byte counts and type sizes aren't known yet. After
# the full pattern has been walked, `insert_length_checks!`,
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

## Optimal length-check insertion
#
# Framework-driven pass that analyses segment markers and inner sentinels
# to insert the minimum number of runtime length checks. Replaces the
# handler-embedded outer checks with globally optimal placement.

"""
    SegmentInfo

Segment metadata extracted from `__segment_begin`/`__segment_end` markers
for the length-check insertion pass.
"""
const SegmentInfo = @NamedTuple{
    begin_idx::Int,      # index into pexprs of __segment_begin marker
    end_idx::Int,        # index into pexprs of __segment_end marker
    seg_id::Int,         # 1-based segment ID
    branch_id::Int,      # branch owning this segment
    parsed_min::Int,     # minimum bytes consumed by this segment
    parsed_max::Int,     # maximum bytes consumed by this segment
    option::Union{Nothing, Symbol},    # optional scope symbol, or nothing if required
    opt_label::Union{Nothing, Symbol}, # goto label for optional failure, or nothing
    desc::String,        # human-readable description for error messages
}

"""
    SentinelInfo

A length sentinel found within a segment's parse expressions.
"""
const SentinelInfo = @NamedTuple{
    seg_idx::Int,        # index into segments array
    emission_max::Int,   # branch parsed_max at emission time
    threshold::Int,      # bytes needed (for __length_check: n_max; for others: n)
    kind::Symbol,        # :length_check, :static_length_check, :length_bound
}

"""
    insert_length_checks!(state, pexprs, branches) -> pexprs

Resolve length-check sentinels in `pexprs` using byte guarantees
propagated through the segment sequence, then strip segment markers.

Each handler emits its own entry length check; this pass propagates the
remaining byte guarantee across segments so that inner sentinels can be
folded to `true` when prior segments already ensure enough bytes.
"""
function insert_length_checks!(::ParserState, pexprs::Vector{ExprVarLine}, branches::Vector{ParseBranch})
    # Collect segment markers
    segments = SegmentInfo[]
    open_seg = nothing
    for (idx, expr) in enumerate(pexprs)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && !isempty(expr.args)
            sentinel = first(expr.args)
            if sentinel === :__segment_begin
                length(expr.args) == 8 || throw(sentinel_err(expr, 8))
                _, seg_id, branch_id, p_min, p_max, option, opt_label, desc = expr.args
                open_seg = (; begin_idx=idx, seg_id, branch_id,
                              parsed_min=p_min, parsed_max=p_max,
                              option, opt_label, desc)
            elseif sentinel === :__segment_end && !isnothing(open_seg)
                push!(segments, SegmentInfo((; open_seg..., end_idx=idx)))
                open_seg = nothing
            end
        end
    end
    if isempty(segments)
        strip_segment_markers!(pexprs)
        for expr in pexprs
            expr isa Expr || continue
            resolve_sentinel_in_expr!(expr, branches, 0)
        end
        return pexprs
    end
    # Collect inner sentinels within each segment
    sentinels = SentinelInfo[]
    for (si, seg) in enumerate(segments)
        for idx in seg.begin_idx+1:seg.end_idx-1
            collect_sentinels!(sentinels, si, pexprs[idx])
        end
    end
    # Group segments by branch and propagate byte guarantees
    branch_segs = Dict{Int, Vector{Int}}()
    for (si, seg) in enumerate(segments)
        push!(get!(Vector{Int}, branch_segs, seg.branch_id), si)
    end
    for (bid, seg_indices) in branch_segs
        remaining = if bid == 1 branches[1].parsed_min else 0 end
        for si in seg_indices
            seg = segments[si]
            for idx in seg.begin_idx+1:seg.end_idx-1
                expr = pexprs[idx]
                expr isa Expr && resolve_sentinel_in_expr!(expr, branches, remaining)
            end
            remaining -= seg.parsed_max
        end
    end
    strip_segment_markers!(pexprs)
    for expr in pexprs
        expr isa Expr || continue
        resolve_sentinel_in_expr!(expr, branches, 0)
    end
    pexprs
end

# Collect sentinel calls from an expression tree
function collect_sentinels!(sentinels::Vector{SentinelInfo}, seg_idx::Int, expr)
    expr isa Expr || return
    if Meta.isexpr(expr, :call) && !isempty(expr.args)
        s = first(expr.args)
        if s === :__length_check
            length(expr.args) == 6 || throw(sentinel_err(expr, 6))
            _, _, emission_max, _n_min, n_max, _n_expr = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n_max, :length_check)))
        elseif s === :__static_length_check
            length(expr.args) == 4 || throw(sentinel_err(expr, 4))
            _, branch_id, emission_max, n = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n, :static_length_check)))
        elseif s === :__length_bound
            length(expr.args) == 4 || throw(sentinel_err(expr, 4))
            _, branch_id, emission_max, n = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n, :length_bound)))
        else
            for arg in expr.args
                collect_sentinels!(sentinels, seg_idx, arg)
            end
        end
    else
        for arg in expr.args
            collect_sentinels!(sentinels, seg_idx, arg)
        end
    end
end


function resolve_sentinel_in_expr!(expr::Expr, branches::Vector{ParseBranch}, remaining::Int)
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args)
            s = first(arg.args)
            if s === :__length_check
                length(arg.args) == 6 || throw(sentinel_err(arg, 6))
                _, branch_id, emission_max, _, n_max, n_expr = arg.args
                if branches[branch_id].parsed_min - emission_max >= n_max || remaining >= n_max
                    expr.args[i] = true
                else
                    r = :(nbytes - pos + 1 >= $n_expr)
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__static_length_check
                length(arg.args) == 4 || throw(sentinel_err(arg, 4))
                _, branch_id, emission_max, n = arg.args
                expr.args[i] = branches[branch_id].parsed_min - emission_max >= n || remaining >= n
            elseif s === :__length_bound
                length(arg.args) == 4 || throw(sentinel_err(arg, 4))
                _, branch_id, emission_max, n = arg.args
                if branches[branch_id].parsed_min - emission_max >= n || remaining >= n
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
                resolve_sentinel_in_expr!(arg, branches, remaining)
            end
        else
            resolve_sentinel_in_expr!(arg, branches, remaining)
        end
    end
end

function strip_segment_markers!(pexprs::Vector{<:ExprVarLine})
    filter!(pexprs) do expr
        !(expr isa Expr && Meta.isexpr(expr, :call) && !isempty(expr.args) &&
          first(expr.args) in (:__segment_begin, :__segment_end))
    end
    for expr in pexprs
        expr isa Expr && strip_segment_markers_nested!(expr)
    end
    pexprs
end

function strip_segment_markers_nested!(expr::Expr)
    remove = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args) &&
           first(arg.args) in (:__segment_begin, :__segment_end)
            push!(remove, i)
        else
            strip_segment_markers_nested!(arg)
        end
    end
    isempty(remove) || deleteat!(expr.args, sort!(remove))
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
size is known.

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
    else
        for arg in expr.args
            if arg isa Expr
                implement_casting!(arg, name, targetsize)
            end
        end
    end
    expr
end
