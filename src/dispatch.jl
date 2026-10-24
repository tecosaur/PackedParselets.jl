# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern dispatch and structural handlers (field capture, choice/optional branching).

## Segment registries

const CORE_SEGMENTS = (
    literal = SegmentDef(:literal,    compile_literal,  (:casefold,)),
    skip    = SegmentDef(:skip,       compile_skip,     (:casefold, :print)),
    digits  = SegmentDef(:digits,     compile_digits,   (:base, :min, :max, :pad, :skip, :groups, :exclude)),
    letters = SegmentDef(:letters,    compile_charseq,  (:upper, :lower, :casefold, :skip, :groups)),
    alphnum = SegmentDef(:alphnum,    compile_charseq,  (:upper, :lower, :casefold, :skip, :groups)),
    hex     = SegmentDef(:hex,        compile_charseq,  (:upper, :lower, :casefold, :skip, :groups)),
    charset = SegmentDef(:charset,    compile_charseq,  (:upper, :lower, :casefold, :skip, :groups, :numeric)),
    embed   = SegmentDef(:embed,      compile_embed,    ()),
    choice  = SegmentDef(:choice,     compile_choice,   (:casefold, :is, :type)),
)

## Pattern dispatch

function pattern_dispatch!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                           @nospecialize(node), args::Vector{Any})
    if node isa QuoteNode
        pattern_field!(exprs, state, nctx, segments, global_kwargs, node, args)
    elseif node === :seq
        for arg in args
            pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, arg)
        end
    elseif node === :optional
        pattern_optional!(exprs, state, nctx, segments, global_kwargs, args)
    elseif node === :choice && any(a -> !(a isa String), args)
        pattern_choice!(exprs, state, nctx, segments, global_kwargs, args)
    elseif haskey(segments, node)
        def = getfield(segments, node)
        output = def.compile(state, nctx, exprs, def, args)
        process_segment_output!(exprs, state, nctx, node, output)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function pattern_dispatch!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                           @nospecialize(thing))
    all_kws = Symbol[]
    for i in 1:length(segments), kw in getfield(segments, i).kwargs
        push!(all_kws, kw)
    end
    append!(all_kws, global_kwargs)
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ all_kws ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(all_kws, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, :seq, args)
    elseif Meta.isexpr(thing, :call)
        name = first(thing.args)
        args = Any[]
        nkeys = if name isa Symbol && haskey(segments, name)
            getfield(segments, name).kwargs
        else
            all_kws
        end
        for arg in thing.args[2:end]
            if Meta.isexpr(arg, :kw, 2)
                kwname, kwval = arg.args
                kwname ∈ nkeys ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments for $name are: $(join(nkeys, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, name, args)
    elseif thing isa String
        def = getfield(segments, :literal)
        output = def.compile(state, nctx, exprs, def, Any[thing])
        process_segment_output!(exprs, state, nctx, :literal, output)
    end
end

## Field capture

copyexprs(exprs::AbstractVector) = ExprVarLine[if e isa Expr copy(e) else e end for e in exprs]

"""
    pattern_field!(exprs, state, nctx, segments, global_kwargs, node, args)

Handle a `QuoteNode` field-capture node (`:major(digits(4))`). Opens a
`:fieldvar` scope, walks children, then assembles a property expression —
a direct segment label for single-value captures, or an IOBuffer
reconstruction for multi-segment fields.
"""
function pattern_field!(exprs::PatternExprs,
                        state::ParserState, nctx::NodeCtx,
                        @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                        node::QuoteNode,
                        args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print.direct)
    for arg in args
        pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, arg)
    end
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    all_segs = @view exprs.segments[initial_segs+1:end]
    all_exclusive = length(new_value_segs) > 1 &&
        length(new_value_segs) == length(all_segs) &&
        all(s -> !isnothing(s.condition), new_value_segs) &&
        allunique(Any[s.condition for s in new_value_segs])
    if all_exclusive
        for seg in new_value_segs
            push!(exprs.properties, node.value => copyexprs(seg.extract))
        end
    elseif length(new_value_segs) == 1
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        propprints = map(strip_segsets! ∘ copy, exprs.print.direct[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        resolve_print_markers!(propprints)
        push!(exprs.properties, node.value => ExprVarLine[(
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args...])
    end
end

## Choice/optional branching

function resolve_extract(val::Union{Symbol, Vector{ExprVarLine}},
                         segs::Vector{ValueSegment},
                         range::AbstractVector{Int}=eachindex(segs))
    if val isa Symbol
        idx = findfirst(i -> segs[i].label == val, range)
        if isnothing(idx) ExprVarLine[] else copyexprs(segs[range[idx]].extract) end
    else
        copyexprs(val)
    end
end

# Build an optimal nested if-elseif chain from guarded extract entries.
# Entries sharing the same outermost guard are grouped into a single
# branch, with inner content recursively chained.
function chain_guarded(entries)
    groups = Tuple{Any, Vector}[]
    for v in entries
        gexpr = last(v)
        if !Meta.isexpr(gexpr, :if)
            push!(groups, (nothing, [v]))
        else
            body = Meta.isexpr(gexpr.args[2], :block) ?
                filter(a -> !(a isa LineNumberNode), gexpr.args[2].args) : Any[gexpr.args[2]]
            inner = ExprVarLine[v[1:end-1]..., body...]
            guard = gexpr.args[1]
            if !isempty(groups) && string(first(last(groups))) == string(guard)
                push!(last(groups)[2], inner)
            else
                push!(groups, (guard, [inner]))
            end
        end
    end
    ngroups = length(groups)
    chain = nothing
    for (j, (guard, inners)) in enumerate(Iterators.reverse(groups))
        body = if length(inners) == 1 Expr(:block, only(inners)...) else chain_guarded(inners) end
        # Last group in a multi-group chain: the discriminant is valid
        # within this scope, so use `else` instead of a redundant guard check
        chain = if isnothing(guard) body
        elseif isnothing(chain) && j == 1 && ngroups > 1 body
        elseif isnothing(chain) Expr(:if, guard, body)
        else Expr(:if, guard, body, chain) end
    end
    chain
end

function guard_property_extract(@nospecialize(val::Union{Symbol, Vector{ExprVarLine}}),
                                guard::Expr, segs::Vector{ValueSegment},
                                seg_range::UnitRange{Int})
    extract = resolve_extract(val, segs, seg_range)
    isempty(extract) && return ExprVarLine[:(if $guard end)]
    ExprVarLine[extract[1:end-1]..., :(if $guard; $(last(extract)) end)]
end

function patch_optional_extracts!(segments::Vector{ValueSegment},
                                  seg_range::UnitRange{Int}, check::Expr)
    for i in seg_range
        extract = segments[i].extract
        isempty(extract) && continue
        last_expr = extract[end]
        if Meta.isexpr(last_expr, :if) && last_expr.args[1] === true
            last_expr.args[1] = check
        end
    end
end

function arm_clear_bits(state::ParserState, bits_before::Int)
    arm_bits = state.bits - bits_before
    arm_bits > 1 || return ExprVarLine[]
    mT = cardtype(arm_bits)
    mask = typemax(mT) >> (8 * sizeof(mT) - arm_bits)
    ExprVarLine[:(parsed = Core.Intrinsics.and_int(parsed,
        Core.Intrinsics.not_int(
            Core.Intrinsics.shl_int(
                __cast_to_packed($mT, $mask),
                __packed_shift($(state.bits))))))]
end

function walk_choice_arm!(oexprs, state::ParserState, nctx::NodeCtx,
                          @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}), @nospecialize(arm))
    if Meta.isexpr(arm, :tuple)
        for a in arm.args
            pattern_dispatch!(oexprs, state, nctx, segments, global_kwargs, a)
        end
    else
        pattern_dispatch!(oexprs, state, nctx, segments, global_kwargs, arm)
    end
end

## Byte profiling for structured choice dispatch

"""
    find_choice_dispatch(arm_spans, reg) -> Union{Nothing, @NamedTuple{offset::Int, iT::DataType, idx}}

Find a register window, loaded as `iT` from byte `offset` into `reg`, whose hash
alone selects the choice arm: `idx` is the expression computing the 1-based arm
index from `reg` (0 when no arm can match).
"""
function find_choice_dispatch(arm_spans::Vector{Vector{Vector{ByteSet}}}, reg::Symbol)
    narms = length(arm_spans)
    narms >= 2 || return nothing
    any(isempty, arm_spans) && return nothing
    min_len = typemax(Int)
    for spans in arm_spans, span in spans
        min_len = min(min_len, length(span))
    end
    ph_result = try_perfect_hash_dispatch(arm_spans, narms, min_len, reg)
    !isnothing(ph_result) && return ph_result
    function window_index(pos::Int, iT::DataType, hash::WindowHash, maxval::UInt64)
        maxval + 1 > 512 && return nothing
        bwidth = sizeof(iT)
        groups = Dict{UInt64, Int}()
        for (k, spans) in enumerate(arm_spans), alt in spans
            window = Vector{UInt8}[collect(set) for set in @view alt[pos:pos+bwidth-1]]
            any(isempty, window) && continue
            # Every register value the window admits, by an odometer over each byte's candidates
            idx = ones(Int, bwidth)
            while true
                regval = zero(UInt64)
                for j in 1:bwidth
                    regval |= UInt64(window[j][idx[j]]) << (8 * (j - 1))
                end
                mv = hashvalue(hash, regval, iT)
                prev = get(groups, mv, 0)
                (!iszero(prev) && prev != k) && return nothing
                groups[mv] = k
                j = 1
                while j <= bwidth && idx[j] == length(window[j])
                    idx[j] = 1
                    j += 1
                end
                j > bwidth && break
                idx[j] += 1
            end
        end
        length(groups) < 2 && return nothing
        arm_vals = zeros(UInt64, narms)
        direct = true
        for (mv, k) in groups
            if iszero(arm_vals[k])
                arm_vals[k] = mv
            elseif arm_vals[k] != mv
                direct = false
                break
            end
        end
        hx = hashexpr(hash, reg, iT)
        if direct
            sorted = sortperm_by(identity, arm_vals)
            vals = arm_vals[sorted]
            if vals[end] - vals[1] + 1 == narms
                # A hash value's rank among them is an index into the arms by value
                idx = :($hx - $(iT(vals[1]) - one(iT)))
                return if sorted == 1:narms idx else :(@inbounds $(Tuple(map(UInt8, sorted)))[$idx]) end
            end
        end
        table = zeros(UInt8, maxval + 1)
        for (mv, k) in groups
            table[mv + 1] = k % UInt8
        end
        :(@inbounds $(Tuple(table))[$hx + 1])
    end
    # Alternatives of different arms that overlap at every byte of the window share
    # a register value, which no hash can tell apart.
    function separable(pos::Int, bwidth::Int)
        for (k, spans) in enumerate(arm_spans), (l, others) in enumerate(arm_spans)
            l > k || continue
            for a in spans, b in others
                all(p -> !isdisjoint(a[p], b[p]), pos:pos+bwidth-1) && return false
            end
        end
        true
    end
    for iT in REGISTER_TYPES
        sizeof(iT) > min_len && break
        for pos in 1:min_len - sizeof(iT) + 1
            separable(pos, sizeof(iT)) || continue
            for (; hash, maxval) in hash_candidates(narms, iT)
                idx = window_index(pos, iT, hash, maxval)
                isnothing(idx) || return (; offset = pos, iT, idx)
            end
        end
    end
    nothing
end

# Extract canonical byte prefixes from arm bytespans and delegate to
# find_window_hash for direct arithmetic dispatch over table lookups.
function try_perfect_hash_dispatch(arm_spans, narms::Int, min_len::Int, reg::Symbol)
    casefold = false
    prefixes = String[]
    for spans in arm_spans
        bytes = UInt8[]
        for bpos in 1:min_len
            bs = ByteSet()
            for alt in spans
                bpos <= length(alt) && (bs = bs ∪ alt[bpos])
            end
            lo = first(iterate(bs))
            if length(bs) == 1
                push!(bytes, lo)
            elseif length(bs) == 2
                hi = first(iterate(bs, UInt16(lo) + UInt16(1)))
                (hi ⊻ lo == 0x20 && (lo | 0x20) in UInt8('a'):UInt8('z')) || break
                push!(bytes, lo | 0x20)
                casefold = true
            else break end
        end
        isempty(bytes) && return nothing
        push!(prefixes, String(bytes))
    end
    allunique(prefixes) || return nothing
    ph = find_window_hash(classify_hash, prefixes, casefold)
    isnothing(ph) && return nothing
    fm = ph.foldmask % ph.iT
    hx = hashexpr(ph, if iszero(fm) reg else :($reg | $fm) end)
    # Arms are found as a string choice's options are: by table, or in the hash's output order
    idx = if ph.kind === :table
        :(if $hx <= $(length(ph.table)); @inbounds($(Tuple(map(UInt8, ph.table)))[$hx]) else 0x00 end)
    elseif ph.perm == 1:narms; hx
    else :(@inbounds $(Tuple(map(UInt8, ph.perm)))[$hx]) end
    (; offset = ph.pos, iT = ph.iT, idx)
end

"""
    pattern_choice!(exprs, state, nctx, segments, global_kwargs, arms)

Unified handler for choice and optional branching. `arms` is a list of pattern
nodes to try in order; `""` as an arm matches zero bytes (the optional absent
case).

Two paths:
- Single pattern + `""` → sentinel-claiming optional (bit-efficient)
- Multiple arms → explicit discriminant with dispatch or cascading try-rewind
"""
function pattern_choice!(exprs::PatternExprs,
                         state::ParserState, nctx::NodeCtx,
                         @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                         args::Vector{Any})
    # Detect tagged choice: choice(:fieldname, tag1 => arm1, tag2 => arm2, ...)
    tagged = length(args) >= 2 && args[1] isa QuoteNode &&
        all(a -> Meta.isexpr(a, :call, 3) && a.args[1] === :(=>), @view args[2:end])
    if tagged
        fieldname = args[1].value::Symbol
        tags = Any[a.args[2] for a in @view args[2:end]]
        arms = Any[a.args[3] for a in @view args[2:end]]
        pattern_choice_multi!(exprs, state, nctx, segments, global_kwargs, arms;
                              tag_field=fieldname, tag_values=tags)
    else
        nonempty_arms = filter(a -> a !== "", args)
        if length(nonempty_arms) == 1 && length(args) == 2
            pattern_choice_optional!(exprs, state, nctx, segments, global_kwargs,
                                     only(nonempty_arms))
        else
            pattern_choice_multi!(exprs, state, nctx, segments, global_kwargs, args)
        end
    end
end

"""
    pattern_choice_optional!(exprs, state, nctx, segments, global_kwargs, arm)

Handle single-arm-plus-empty optional via sentinel claiming. Walks the arm in
a child branch, steals a zero-encoding sentinel from a value segment (or
allocates a presence bit), then emits guarded parse/print with pos rewind.
"""
function pattern_choice_optional!(exprs::PatternExprs,
                                  state::ParserState, nctx::NodeCtx,
                                  @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                                  @nospecialize(arm))
    popt = get(nctx, :optional, nothing)
    optvar = gensym("optional")
    end_label = gensym("opt_end")
    nctx = NodeCtx(nctx, :optional, optvar)
    nctx = NodeCtx(nctx, :opt_label, end_label)
    nctx = NodeCtx(nctx, :oprint_detect, ExprVarLine[])
    parent = nctx[:current_branch]
    child = ParseBranch(length(state.branches) + 1, parent, optvar,
                        parent.parsed_min, parent.parsed_max,
                        parent.parsed_min, parent.parsed_min,
                        parent.print_min, parent.print_max, parent.parsed_min)
    push!(state.branches, child)
    nctx = NodeCtx(nctx, :current_branch, child)
    sentinel_ref = Ref{Union{Nothing, OptSentinel}}(nothing)
    nctx = NodeCtx(nctx, :optional_sentinel, sentinel_ref)
    seg_start = length(exprs.segments)
    bits_before = state.bits
    oexprs = PatternExprs(ExprVarLine[], PrintExprs(),
                          exprs.segments, exprs.properties, Vector{ByteSet}[])
    walk_choice_arm!(oexprs, state, nctx, segments, global_kwargs, arm)
    if sentinel_ref[] === nothing
        flag_nbits = (state.bits += 1)
        push!(oexprs.parse, emit_pack(state, Bool, optvar, flag_nbits))
        sentinel_ref[] = OptSentinel((flag_nbits, 1))
    end
    sentinel = sentinel_ref[]
    check = :(!iszero($(emit_extract(state, sentinel.position, sentinel.nbits))))
    patch_optional_extracts!(exprs.segments, seg_start+1:length(exprs.segments), check)
    parent.parsed_max += child.parsed_max - child.start_min
    parent.print_max = Base.max(parent.print_max, child.print_max)
    savedpos = gensym("savedpos")
    branch_check = Expr(:call, :__branch_check, Bool, child.id)
    guard = if isnothing(popt) branch_check else :($popt && $branch_check) end
    push!(exprs.parse, :($savedpos = pos))
    push!(exprs.parse, :($optvar = $guard))
    push!(exprs.parse, :(if $optvar; $(oexprs.parse...) end))
    push!(exprs.parse, :(@label $end_label))
    push!(exprs.parse, :(if !$optvar; pos = $savedpos; $(arm_clear_bits(state, bits_before)...) end))
    # Print: hoist extraction + condition, wrap bodies in if
    odetect = nctx[:oprint_detect]
    cond_assign = :($optvar = $check)
    for field in (:direct, :getval)
        append!(getfield(exprs.print, field), odetect)
        push!(getfield(exprs.print, field), cond_assign)
    end
    append!(exprs.print.vars, oexprs.print.vars)
    push!(exprs.print.vars, optvar => false)
    for field in (:direct, :getval, :getlen, :putval)
        body = getfield(oexprs.print, field)
        isempty(body) && continue
        push!(getfield(exprs.print, field), :(if $optvar; $(body...) end))
    end
    if !isempty(oexprs.bytespans)
        extend_bytespans!(exprs.bytespans, push!(copy(oexprs.bytespans), ByteSet[]))
    end
end

struct ChoiceArm
    armvar::Symbol
    end_label::Symbol
    child::ParseBranch
    oexprs::PatternExprs
    arm_nctx::NodeCtx
    arm_props::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}}
    seg_range::UnitRange{Int}
    bits_before::Int
    bits_after::Int
end

"""
    pattern_choice_multi!(exprs, state, nctx, segments, global_kwargs, arms)

Handle multi-arm structured choice with an explicit packed discriminant.
Walks each arm into its own accumulator, selects between table-driven
dispatch (when `find_choice_dispatch` finds a distinguishing byte window)
or cascading try-rewind, and emits separate print blocks per arm.
"""
function pattern_choice_multi!(exprs::PatternExprs,
                               state::ParserState, nctx::NodeCtx,
                               @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                               arms::Vector{Any};
                               tag_field::Union{Nothing, Symbol}=nothing,
                               tag_values::Union{Nothing, Vector{Any}}=nothing)
    narms = length(arms)
    narms >= 2 || throw(ArgumentError("Structured choice requires at least 2 arms"))
    popt = get(nctx, :optional, nothing)
    parent = nctx[:current_branch]
    savedpos = gensym("savedpos")
    push!(exprs.parse, :($savedpos = pos))
    discrim_bits = cardbits(narms + 1)
    discrim_type = cardtype(discrim_bits)
    discrim_pos = state.bits + discrim_bits
    state.bits += discrim_bits
    arm_base = state.bits
    arm_data = ChoiceArm[]
    for (k, arm) in enumerate(arms)
        armvar = gensym("arm$k")
        end_label = gensym("arm$(k)_end")
        arm_nctx = NodeCtx(nctx, :optional, armvar)
        arm_nctx = NodeCtx(arm_nctx, :opt_label, end_label)
        arm_nctx = NodeCtx(arm_nctx, :oprint_detect, ExprVarLine[])
        arm_nctx = NodeCtx(arm_nctx, :optional_sentinel, nothing)
        child = ParseBranch(length(state.branches) + 1, parent, armvar,
                            parent.parsed_min, parent.parsed_max,
                            parent.parsed_min, parent.parsed_min,
                            parent.print_min, parent.print_max, parent.parsed_min)
        push!(state.branches, child)
        arm_nctx = NodeCtx(arm_nctx, :current_branch, child)
        seg_start = length(exprs.segments)
        state.bits = arm_base
        bits_before = state.bits
        arm_props = Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}[]
        oexprs = PatternExprs(ExprVarLine[], PrintExprs(),
                              exprs.segments, arm_props, Vector{ByteSet}[])
        arm !== "" && walk_choice_arm!(oexprs, state, arm_nctx, segments, global_kwargs, arm)
        bits_after = state.bits
        dval = gensym("discrim")
        push!(oexprs.parse, :($dval = $(discrim_type(k))))
        push!(oexprs.parse, emit_pack(state, discrim_type, dval, discrim_pos))
        parent.parsed_max += child.parsed_max - child.start_min
        parent.print_max = Base.max(parent.print_max, child.print_max)
        push!(arm_data, ChoiceArm(armvar, end_label, child, oexprs, arm_nctx, arm_props,
                                  seg_start+1:length(exprs.segments), bits_before, bits_after))
    end
    state.bits = maximum(Int[ad.bits_after for ad in arm_data])
    parent.parsed_min += minimum(Int[ad.child.parsed_min - ad.child.start_min for ad in arm_data])
    for (k, ad) in enumerate(arm_data)
        ad.child.close_min = parent.parsed_min
        check = :($(emit_extract(state, discrim_pos, discrim_bits)) == $(discrim_type(k)))
        patch_optional_extracts!(exprs.segments, ad.seg_range, check)
        for (name, val) in ad.arm_props
            guarded = guard_property_extract(val, check, exprs.segments, ad.seg_range)
            push!(exprs.properties, name => guarded)
        end
    end
    final_bits = state.bits
    arm_spans = Vector{Vector{ByteSet}}[ad.oexprs.bytespans for ad in arm_data]
    dispatch_reg = gensym("dispatch_reg")
    dispatch = find_choice_dispatch(arm_spans, dispatch_reg)
    if !isnothing(dispatch)
        emit_dispatch_parse!(exprs, state, nctx, popt, savedpos, arm_data,
                             dispatch_reg, dispatch, "" in arms)
    else
        emit_cascade_parse!(exprs, state, nctx, popt, savedpos, arm_data,
                            "" in arms, discrim_bits)
    end
    state.bits = final_bits
    # Emit per-arm print blocks. Separate `if` blocks (not if/elseif) so
    # rewrite_bufprint! can reach print calls inside each arm.
    discrim_extract = emit_extract(state, discrim_pos, discrim_bits)
    # An arm prints only on its own discriminant, so any other would print nothing
    tagvar = if isnothing(tag_field); :discriminant else Symbol(:attr_, tag_field) end
    discrim_valid = emit_validity_check(state, tagvar, discrim_extract, 1:length(arm_data))
    push!(exprs.print.direct, discrim_valid)
    push!(exprs.print.getval, copy(discrim_valid))
    for (k, ad) in enumerate(arm_data)
        odetect = ad.arm_nctx[:oprint_detect]
        cond = :($discrim_extract == $(discrim_type(k)))
        # direct: self-contained (odetect + direct inside if)
        append!(exprs.print.direct, odetect)
        push!(exprs.print.direct, :(if $cond; $(ad.oexprs.print.direct...) end))
        # split path: everything inside the if (no hoisting for choice arms)
        append!(exprs.print.vars, ad.oexprs.print.vars)
        push!(exprs.print.getval, :(if $cond; $(odetect...); $(ad.oexprs.print.getval...) end))
        push!(exprs.print.getlen, :(if $cond; $(ad.oexprs.print.getlen...) end))
        push!(exprs.print.putval, :(if $cond; $(ad.oexprs.print.putval...) end))
    end
    # Propagate bytespans upward so parent sequences can dispatch on our content.
    # A choice contributes the union of all arm alternatives.
    all_alts = reduce(vcat, arm_spans)
    extend_bytespans!(exprs.bytespans, all_alts)
    # Tagged choice: the tag is just a property contributed by every arm
    if !isnothing(tag_field)
        tag_tuple = Expr(:tuple, tag_values...)
        for k in eachindex(arm_data)
            check = :($(emit_extract(state, discrim_pos, discrim_bits)) == $(discrim_type(k)))
            push!(exprs.properties, tag_field =>
                ExprVarLine[:(if $check; $tag_tuple[$(discrim_type(k))] end)])
        end
    end
end

function emit_dispatch_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                              @nospecialize(popt::Union{Nothing, Symbol}), savedpos::Symbol,
                              arm_data::Vector{ChoiceArm}, reg_var::Symbol, @nospecialize(dispatch), has_empty::Bool)
    arm_idx_var = gensym("arm_idx")
    (; offset, iT, idx) = dispatch
    bwidth = sizeof(iT)
    load_pos = if offset == 1; :pos else :(pos + $(offset - 1)) end
    load = gen_load(iT, load_pos)
    min_bytes_needed = offset - 1 + bwidth
    push!(exprs.parse, :(if nbytes < pos + $(min_bytes_needed - 1)
                             $arm_idx_var = UInt8(0)
                         else
                             $reg_var = $load
                             $arm_idx_var = $idx
                         end))
    for (k, ad) in enumerate(arm_data)
        branch_check = Expr(:call, :__branch_check, Bool, ad.child.id)
        guard = if isnothing(popt) branch_check else :($popt && $branch_check) end
        state.bits = ad.bits_after
        rewind = :(if !$(ad.armvar); pos = $savedpos; $(arm_clear_bits(state, ad.bits_before)...) end)
        push!(exprs.parse, :($(ad.armvar) = false))
        push!(exprs.parse, :(if $arm_idx_var == $(UInt8(k))
                                 $(ExprVarLine[
                                     :($(ad.armvar) = $guard),
                                     :(if $(ad.armvar); $(ad.oexprs.parse...) end),
                                     :(@label $(ad.end_label)),
                                     rewind]...)
                             end))
    end
    if !has_empty || !isnothing(popt)
        any_ok = false
        for ad in arm_data
            any_ok = :($any_ok || $(ad.armvar))
        end
        fail = build_fail_expr!(state, nctx, "No choice arm matched")
        push!(exprs.parse, :(if !($any_ok); $fail end))
    end
end

"""
    emit_cascade_parse!(exprs, state, nctx, popt, savedpos, arm_data, has_empty, discrim_bits)

Emit try-and-rewind parsing for choice arms without a dispatch window, selecting
the arm that consumes the most input (ties to the earliest in source order).

Arms are tried widest-first. A success commits in place once no remaining arm
could beat it, decided statically where arm bounds allow, so a choice whose
widest arms are also unambiguous costs nothing extra. Otherwise the best success
so far is snapshotted and rewound, and restored once every arm has been tried.
"""
function emit_cascade_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                             @nospecialize(popt::Union{Nothing, Symbol}), savedpos::Symbol,
                             arm_data::Vector{ChoiceArm}, has_empty::Bool, discrim_bits::Int)
    innermost = if has_empty && isnothing(popt)
        ExprVarLine[]
    else
        ExprVarLine[build_fail_expr!(state, nctx, "No choice arm matched")]
    end
    plan = cascade_commit_plan(UnitRange{Int}[
        ad.child.parsed_min - ad.child.start_min:ad.child.parsed_max - ad.child.start_min for ad in arm_data])
    deferring = !all(p -> p.static_commit, plan)
    bestparsed, bestlen, bestsrc, len, isbest =
        map(gensym, ("bestparsed", "bestlen", "bestsrc", "len", "isbest"))
    if deferring
        innermost = ExprVarLine[:(if $bestlen >= 0
                                      parsed = $bestparsed
                                      pos = $savedpos + $bestlen
                                  else
                                      $(innermost...)
                                  end)]
    end
    # Built from the last arm tried (innermost) out
    cascade = innermost
    for p in Iterators.reverse(plan)
        ad = arm_data[p.src]
        branch_check = Expr(:call, :__branch_check, Bool, ad.child.id)
        guard = if isnothing(popt) branch_check else :($popt && $branch_check) end
        state.bits = ad.bits_after
        attempt = ExprVarLine[
            :($(ad.armvar) = $guard),
            :(if $(ad.armvar); $(ad.oexprs.parse...) end),
            :(@label $(ad.end_label))]
        clear = if p.static_commit
            arm_clear_bits(state, ad.bits_before)
        else
            final = if p.clears_threshold isbest else :($isbest && $len >= $(p.threshold)) end
            push!(attempt, :(if $(ad.armvar)
                                 $len = pos - $savedpos
                                 $isbest = $len > $bestlen || ($len == $bestlen && $(p.src) < $bestsrc)
                                 if !($final)
                                     if $isbest
                                         $bestparsed, $bestlen, $bestsrc = parsed, $len, $(p.src)
                                     end
                                     $(ad.armvar) = false
                                 end
                             end))
            # A rewound success has packed its discriminant, just below the arm's bits.
            arm_clear_bits(state, ad.bits_before - discrim_bits)
        end
        cascade = ExprVarLine[attempt...,
            :(if !$(ad.armvar); pos = $savedpos; $(clear...); $(cascade...) end)]
    end
    if deferring
        append!(exprs.parse, ExprVarLine[
            :($bestparsed = parsed), :($bestlen = -1), :($bestsrc = 0)])
    end
    append!(exprs.parse, cascade)
end

# One arm's place in a cascade (see `cascade_commit_plan`)
struct CascadeStep
    src::Int
    threshold::Int
    clears_threshold::Bool
    static_commit::Bool
end

"""
    cascade_commit_plan(consumed) -> Vector{CascadeStep}

Order cascade arms widest-first given each arm's `consumed` byte range. For each
arm (by rank) gives its source index `src`; the `threshold` length at which its
success beats every later arm (strictly, for those earlier in source order);
whether every success `clears_threshold`; and whether it may `static_commit`:
clearing the threshold with no earlier arm able to have deferred a better match.
"""
function cascade_commit_plan(consumed::Vector{UnitRange{Int}})
    order = sortperm_by(last, consumed, true)
    plan = CascadeStep[]
    committing = true
    for (rank, src) in enumerate(order)
        threshold = 0
        for j in @view order[rank+1:end]
            threshold = max(threshold, last(consumed[j]) + (j < src))
        end
        clears = first(consumed[src]) >= threshold
        committing &= clears
        push!(plan, CascadeStep(src, threshold, clears, committing))
    end
    plan
end

function pattern_optional!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), @nospecialize(global_kwargs::Tuple{Vararg{Symbol}}),
                           args::Vector{Any})
    arm = if all(a -> a isa String, args)
        Expr(:call, :choice, join(Vector{String}(args)), "")
    else
        Expr(:tuple, args...)
    end
    pattern_choice!(exprs, state, nctx, segments, global_kwargs, Any[arm, ""])
end
