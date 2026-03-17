# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Placeholder sentinel emission, resolution, and AST post-processing.
#
# During pattern walking, length checks and type casts are emitted as
# placeholder sentinel calls (e.g. `__length_check`, `__cast_to_id`)
# since the final byte counts and type sizes aren't known yet. After
# the full pattern has been walked, `insert_length_checks!`,
# `fold_static_branches!`, and `implement_casting!` replace these
# sentinels with concrete expressions or compile-time constants.

## Sentinel emission

function emit_lengthcheck(state::ParserState, nctx::NodeCtx, n_expr, n_min::Int=n_expr, n_max::Int=n_min)
    b = nctx[:current_branch]
    Expr(:call, :__length_check, b.id, b.parsed_max, n_min, n_max, n_expr)
end

function emit_static_lengthcheck(state::ParserState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__static_length_check, b.id, b.parsed_max, n)
end

function emit_lengthbound(state::ParserState, nctx::NodeCtx, n::Int)
    b = nctx[:current_branch]
    Expr(:call, :__length_bound, b.id, b.parsed_max, n)
end

## Sentinel resolution helpers

function resolve_branch_check(b::ParseBranch)
    local_min = b.parsed_min - b.start_min
    local_min <= 0 && return true
    parent_remaining = if isnothing(b.parent)
        0
    else
        b.parent.parsed_min - b.start_max
    end
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
    option::Any,         # optional scope symbol, or nothing if required
    opt_label::Any,      # goto label for optional failure, or nothing
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
    insert_length_checks!(pexprs, branches[, state]) -> pexprs

Analyse segment markers and inner sentinels in `pexprs` to insert the
minimum number of runtime length checks. After insertion, resolves all
sentinels (outer and inner) and strips markers.

This is an optimisation pass: at each segment boundary where the remaining
byte guarantee is insufficient, it inserts a check for the maximum useful
amount, pushing the next mandatory check as far forward as possible.

When `state` is provided, error messages are registered via `register_errmsg!`
for proper error reporting. Without `state`, descriptions are used directly
(for validation/comparison purposes only).
"""
function insert_length_checks!(pexprs::Vector{ExprVarLine}, branches::Vector{ParseBranch},
                               state::Union{Nothing, ParserState} = nothing)
    # Pass 1: collect segment markers
    segments = SegmentInfo[]
    open_seg = nothing
    for (idx, expr) in enumerate(pexprs)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && !isempty(expr.args)
            sentinel = first(expr.args)
            if sentinel === :__segment_begin
                _, seg_id, branch_id, p_min, p_max, option, opt_label, desc = expr.args
                open_seg = (idx, seg_id, branch_id, p_min, p_max, option, opt_label, desc)
            elseif sentinel === :__segment_end && !isnothing(open_seg)
                push!(segments, SegmentInfo((open_seg[1], idx, open_seg[2],
                    open_seg[3], open_seg[4], open_seg[5], open_seg[6],
                    open_seg[7], open_seg[8])))
                open_seg = nothing
            end
        end
    end
    isempty(segments) && return pexprs
    # Pass 1b: collect inner sentinels within each segment
    sentinels = SentinelInfo[]
    for (si, seg) in enumerate(segments)
        for idx in seg.begin_idx+1:seg.end_idx-1
            expr = pexprs[idx]
            collect_sentinels!(sentinels, si, expr)
        end
    end
    # Pass 2: greedy forward check placement per branch
    # Group segments by branch
    branch_segs = Dict{Int, Vector{Int}}()  # branch_id -> segment indices
    for (si, seg) in enumerate(segments)
        push!(get!(Vector{Int}, branch_segs, seg.branch_id), si)
    end
    # Classify which segments need framework-inserted entry checks.
    # A segment needs a framework check only if its handler emitted a
    # __length_check sentinel — meaning the handler relies on an outer guard
    # it expects the framework (or itself) to provide.
    # Segments with no __length_check are self-validating: embeds delegate
    # to inner parsebytes, charseqs post-validate after scanning, etc.
    has_length_check = Set{Int}()
    for sent in sentinels
        sent.kind === :length_check && push!(has_length_check, sent.seg_idx)
    end
    # Among segments with __length_check, identify those whose handler check
    # already covers the entry requirement (threshold >= parsed_min). These
    # don't need an additional framework check — their sentinel resolves via
    # the standard resolution pass.
    has_own_outer_check = Set{Int}()
    for sent in sentinels
        if sent.kind === :length_check && sent.threshold >= segments[sent.seg_idx].parsed_min
            push!(has_own_outer_check, sent.seg_idx)
        end
    end
    # For each branch, compute check insertions.
    # The check value is the cumulative minimum entry requirement of the current
    # and all subsequent segments on this branch that need framework checks.
    # Self-validating segments (no __length_check) and segments with their own
    # outer checks are skipped. The remaining guarantee still erodes by parsed_max.
    insertions = Tuple{Int, Expr}[]  # (pexprs index, check expression)
    seg_guarantees = Dict{Int, Int}()  # seg_idx => remaining guarantee at entry
    for (bid, seg_indices) in branch_segs
        # The root branch starts with parsed_min guaranteed by the upfront
        # __branch_check. Optional branches start conservatively at 0 — their
        # entry check (if any) is handled separately by __branch_check.
        remaining = if bid == 1; branches[1].parsed_min else 0 end
        for si in seg_indices
            seg = segments[si]
            seg_entry_need = seg.parsed_min
            needs_framework_check = si in has_length_check && !(si in has_own_outer_check)
            if remaining < seg_entry_need && needs_framework_check
                G = cumulative_entry_min(si, segments)
                G = Base.max(G, seg_entry_need)
                fail = if isnothing(seg.option)
                    erridx = if !isnothing(state)
                        register_errmsg!(state, seg.desc)
                    else
                        seg.desc
                    end
                    :(return ($erridx, pos))
                else
                    opt_fail_expr(seg.option, seg.opt_label)
                end
                push!(insertions, (seg.begin_idx, :(nbytes - pos + 1 >= $G || $fail)))
                remaining = G
            end
            seg_guarantees[si] = remaining
            remaining -= seg.parsed_max
        end
    end
    # Pass 3: resolve inner sentinels using framework-propagated guarantees.
    # Each segment's inner sentinels see the guarantee established by the
    # framework check (or upfront check) that covers this segment.
    for (_, seg_indices) in branch_segs
        for si in seg_indices
            seg = segments[si]
            guarantee = get(seg_guarantees, si, 0)
            for idx in seg.begin_idx+1:seg.end_idx-1
                resolve_sentinels_with_guarantee!(pexprs, idx, branches, guarantee)
            end
        end
    end
    # Pass 4: insert checks and strip markers
    sort!(insertions, by=first, rev=true)
    for (idx, check_expr) in insertions
        insert!(pexprs, idx + 1, check_expr)
    end
    # Strip markers (top-level and nested)
    strip_segment_markers!(pexprs)
    # Pass 5: resolve any remaining sentinels not inside segment ranges
    # (e.g. __branch_check in optional guards, top-level sentinels)
    resolve_remaining_sentinels!(pexprs, branches)
    pexprs
end

# Resolve sentinels that fall outside segment marker ranges (branch checks
# in optional guards, etc.) using only the static parsed_min guarantee.
function resolve_remaining_sentinels!(pexprs::Vector{ExprVarLine}, branches::Vector{ParseBranch})
    for (idx, expr) in enumerate(pexprs)
        expr isa Expr || continue
        if Meta.isexpr(expr, :call) && !isempty(expr.args) && first(expr.args) === :__branch_check
            if expr.args[2] === Bool
                pexprs[idx] = resolve_branch_check(branches[expr.args[3]])
            end
            continue
        end
        # Resolve any nested sentinels that weren't inside segments
        resolve_sentinel_in_expr!(expr, branches, 0)
    end
end

# Collect sentinel calls from an expression tree
function collect_sentinels!(sentinels::Vector{SentinelInfo}, seg_idx::Int, expr)
    expr isa Expr || return
    if Meta.isexpr(expr, :call) && !isempty(expr.args)
        s = first(expr.args)
        if s === :__length_check
            _, branch_id, emission_max, n_min, n_max, n_expr = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n_max, :length_check)))
        elseif s === :__static_length_check
            _, branch_id, emission_max, n = expr.args
            push!(sentinels, SentinelInfo((seg_idx, emission_max, n, :static_length_check)))
        elseif s === :__length_bound
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

# Compute how many bytes a single check at segment si can safely require.
# We can batch fixed-width segments (parsed_min == parsed_max) into one
# check, but must stop at the first variable-width segment boundary because
# the guarantee erodes by parsed_max while we only know parsed_min was needed.
function cumulative_entry_min(si::Int, segments::Vector{SegmentInfo})
    bid = segments[si].branch_id
    cumulative_max = 0
    G = 0
    for sj in si:length(segments)
        segments[sj].branch_id == bid || continue
        G = Base.max(G, segments[sj].parsed_min + cumulative_max)
        cumulative_max += segments[sj].parsed_max
        # Stop batching past a variable-width segment: the guarantee
        # erosion (parsed_max) exceeds the minimum used (parsed_min),
        # so subsequent segments may not be reachable
        segments[sj].parsed_min != segments[sj].parsed_max && break
    end
    G
end

# Resolve sentinels in a single expression using the guarantee at that point
function resolve_sentinels_with_guarantee!(pexprs::Vector{ExprVarLine}, idx::Int,
                                           branches::Vector{ParseBranch}, remaining::Int)
    expr = pexprs[idx]
    expr isa Expr || return
    resolve_sentinel_in_expr!(expr, branches, remaining)
end

function resolve_sentinel_in_expr!(expr::Expr, branches::Vector{ParseBranch}, remaining::Int)
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :call) && !isempty(arg.args)
            s = first(arg.args)
            if s === :__length_check
                _, branch_id, emission_max, n_min, n_max, n_expr = arg.args
                if branches[branch_id].parsed_min - emission_max >= n_max || remaining >= n_max
                    expr.args[i] = true
                else
                    r = :(nbytes - pos + 1 >= $n_expr)
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__static_length_check
                _, branch_id, emission_max, n = arg.args
                expr.args[i] = branches[branch_id].parsed_min - emission_max >= n || remaining >= n
            elseif s === :__length_bound
                _, branch_id, emission_max, n = arg.args
                if branches[branch_id].parsed_min - emission_max >= n || remaining >= n
                    expr.args[i] = n
                else
                    r = :(min($n, nbytes - pos + 1))
                    arg.head, arg.args = r.head, r.args
                end
            elseif s === :__branch_check
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

"""
    strip_segment_markers!(pexprs) -> pexprs

Remove `__segment_begin` and `__segment_end` marker calls from the expression
list and any nested expression blocks.
"""
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

"""
    fold_static_branches!(items::Vector{<:ExprVarLine}) -> items

Resolve `if true`/`if false` and their negations statically, splicing the
taken branch in place. Recurses into nested expressions and repeats until
fixpoint.
"""
function fold_static_branches!(items::Vector{<:ExprVarLine})
    while fold_branches!(items) end
    items
end

function fold_branches!(items::AbstractVector)
    splices = Tuple{Int, Vector{Any}}[]
    changed = false
    for (i, item) in enumerate(items)
        item isa Expr || continue
        if item.head in (:if, :elseif) && item.args[1] isa Bool
            push!(splices, (i, take_branch(item)))
            changed = true
        elseif item.head in (:if, :elseif) &&
               Meta.isexpr(item.args[1], :call, 2) &&
               item.args[1].args[1] === :! && item.args[1].args[2] isa Bool
            item.args[1] = !item.args[1].args[2]
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

Replace `__cast_to_id` / `__cast_from_id` sentinels with the appropriate
`Core.bitcast`, `zext_int`, or `trunc_int` call, now that the final type
size is known.

Compares physical type sizes (`sizeof`) for intrinsic selection, since
`zext_int`/`trunc_int` operate on physical widths — not logical bit counts.
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
    if Meta.isexpr(expr, :call, 3) && first(expr.args) in (:__cast_to_id, :__cast_from_id)
        casttype, valtype, value = expr.args
        targettype, targetbits, valbits = if casttype == :__cast_to_id
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
