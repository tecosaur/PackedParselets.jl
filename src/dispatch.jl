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
                           @nospecialize(node), args::Vector{Any})
    if node isa QuoteNode
        pattern_field!(exprs, state, nctx, node, args)
    elseif node === :seq
        for arg in args
            pattern_dispatch!(exprs, state, nctx, arg)
        end
    elseif node === :optional
        pattern_optional!(exprs, state, nctx, args)
    elseif node === :choice && any(a -> !(a isa String), args)
        pattern_choice!(exprs, state, nctx, args)
    elseif haskey(state.segments, node)
        def = getfield(state.segments, node)
        output = def.compile(state, nctx, exprs, def, args)
        process_segment_output!(exprs, state, nctx, node, output)
    else
        throw(ArgumentError("Unknown pattern node $node"))
    end
end

function pattern_dispatch!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           @nospecialize(thing))
    if Meta.isexpr(thing, :tuple)
        args = Any[]
        for arg in thing.args
            if Meta.isexpr(arg, :(=), 2)
                kwname, kwval = arg.args
                kwname ∈ state.kwnames ||
                    throw(ArgumentError("Unknown keyword argument $kwname. Known keyword arguments are: $(join(state.kwnames, ", "))"))
                nctx = NodeCtx(nctx, kwname, kwval)
            else
                push!(args, arg)
            end
        end
        pattern_dispatch!(exprs, state, nctx, :seq, args)
    elseif Meta.isexpr(thing, :call)
        name = first(thing.args)
        args = Any[]
        nkeys = if name isa Symbol && haskey(state.segments, name)
            getfield(state.segments, name).kwargs
        else
            state.kwnames
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
        pattern_dispatch!(exprs, state, nctx, name, args)
    elseif thing isa String
        def = getfield(state.segments, :literal)
        output = def.compile(state, nctx, exprs, def, Any[thing])
        process_segment_output!(exprs, state, nctx, :literal, output)
    else
        throw(ArgumentError("Expected a string, a segment, or a tuple of them in a pattern, got $(repr(thing))"))
    end
end

## Field capture

copyexprs(exprs::AbstractVector) = ExprVarLine[if e isa Expr copy(e) else e end for e in exprs]

function pattern_field!(exprs::PatternExprs,
                        state::ParserState, nctx::NodeCtx,
                        node::QuoteNode,
                        args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print.direct)
    for arg in args
        pattern_dispatch!(exprs, state, nctx, arg)
    end
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    all_segs = @view exprs.segments[initial_segs+1:end]
    all_exclusive = length(new_value_segs) > 1 &&
        all(s -> s.nbits > 0, all_segs) &&
        all(s -> !isnothing(s.condition), new_value_segs) &&
        allunique(Any[s.condition for s in new_value_segs])
    if all_exclusive
        for seg in new_value_segs
            push!(exprs.properties, node.value => copyexprs(seg.extract))
        end
    elseif length(new_value_segs) == 1
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        propprints = strip_print_markers(exprs.print.direct[initialprints+1:end])
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

# Entries sharing an outermost guard with the one before share its branch
function chain_guarded(entries)
    groups = Tuple{Any, Vector}[]
    for v in entries
        gexpr = last(v)
        if !Meta.isexpr(gexpr, :if)
            push!(groups, (nothing, [v]))
        else
            body = if Meta.isexpr(gexpr.args[2], :block)
                filter(a -> !(a isa LineNumberNode), gexpr.args[2].args)
            else
                Any[gexpr.args[2]]
            end
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

# Clear the packed bits `from+1:to`, which an arm that failed may have set
function arm_clear_bits(from::Int, to::Int)
    to - from > 1 || return ExprVarLine[]
    # Built in the packed type, which may be wider than any integer
    mask = :(Core.Intrinsics.lshr_int(Core.Intrinsics.not_int(__cast_to_packed($UInt8, 0x00)), __packed_shift($(to - from))))
    ExprVarLine[:(parsed = Core.Intrinsics.and_int(parsed,
        Core.Intrinsics.not_int(Core.Intrinsics.shl_int($mask, __packed_shift($to)))))]
end

function walk_arm!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx, @nospecialize(arm),
                   armvar::Symbol, end_label::Symbol, @nospecialize(sentinel), props::Vector)
    parent = nctx[:current_branch]
    child = ParseBranch(length(state.branches) + 1, parent, armvar,
                        parent.parsed_min, parent.parsed_max,
                        parent.parsed_min, parent.parsed_min,
                        parent.print_min, parent.print_max, parent.parsed_min)
    push!(state.branches, child)
    odetect = ExprVarLine[]
    nctx = NodeCtx(nctx, :optional, armvar)
    nctx = NodeCtx(nctx, :opt_label, end_label)
    nctx = NodeCtx(nctx, :oprint_detect, odetect)
    nctx = NodeCtx(nctx, :optional_sentinel, sentinel)
    nctx = NodeCtx(nctx, :current_branch, child)
    oexprs = PatternExprs(ExprVarLine[], PrintExprs(), exprs.segments, props, Vector{ByteSet}[], Layout())
    arm === "" || pattern_dispatch!(oexprs, state, nctx, arm)
    child, oexprs, odetect
end

# The segment of `nbits` that select a choice's arm or mark an optional present, which prints nothing
selector(nbits::Int, label::Symbol, desc::String) =
    SegmentOutput(SegmentBounds(0:0, 0:0, nbits, nothing),
                  SegmentCodegen(ExprVarLine[], ExprVarLine[], PrintExprs(), Expr[]),
                  SegmentMeta(label, desc, "", nothing, nothing), Vector{ByteSet}[])

# Parse an arm where its branch's length check allows; failing within, it jumps to `end_label`
function arm_attempt(@nospecialize(popt), armvar::Symbol, end_label::Symbol, child::ParseBranch,
                     parse::Vector{ExprVarLine})
    check = Expr(:call, :__branch_check, child.id)
    ExprVarLine[:($armvar = $(if isnothing(popt) check else :($popt && $check) end)),
                :(if $armvar; $(parse...) end),
                :(@label $end_label)]
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
            # Thousands of values in a window are more than a table could tell apart
            prod(Float64 ∘ length, window) > 4096 && return nothing
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

# Hash each arm's leading bytes that are fixed (or differ only by case) like a string choice's options
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
    ph = find_window_hash(prefixes, casefold, 1)
    isnothing(ph) && return nothing
    fm = ph.foldmask % ph.iT
    hx = hashexpr(ph, if iszero(fm) reg else :($reg | $fm) end)
    # Arms are found as a string choice's options are: by table, or in the hash's output order
    idx = if !isempty(ph.table)
        :(if $hx <= $(length(ph.table)); @inbounds($(Tuple(map(UInt8, ph.table)))[$hx]) else 0x00 end)
    elseif ph.perm == 1:narms; hx
    else :(@inbounds $(Tuple(map(UInt8, ph.perm)))[$hx]) end
    (; offset = ph.pos, iT = ph.iT, idx)
end

# A `""` arm matches zero bytes: the absent case of an optional
function pattern_choice!(exprs::PatternExprs,
                         state::ParserState, nctx::NodeCtx,
                         args::Vector{Any})
    # Detect tagged choice: choice(:fieldname, tag1 => arm1, tag2 => arm2, ...)
    tagged = length(args) >= 2 && args[1] isa QuoteNode &&
        all(a -> Meta.isexpr(a, :call, 3) && a.args[1] === :(=>), @view args[2:end])
    if tagged
        fieldname = args[1].value::Symbol
        tags = Any[a.args[2] for a in @view args[2:end]]
        arms = Any[a.args[3] for a in @view args[2:end]]
        pattern_choice_multi!(exprs, state, nctx, arms;
                              tag_field=fieldname, tag_values=tags)
    else
        # Arms differing only in a leading literal are a string choice before what they share
        heads, rest = Any[], nothing
        for a in args
            parts = if Meta.isexpr(a, :call) && first(a.args) === :seq; a.args[2:end] elseif Meta.isexpr(a, :tuple) a.args end
            (parts isa Vector{Any} && length(parts) >= 2 && first(parts) isa String &&
             first(parts) ∉ heads && something(rest, parts[2:end]) == parts[2:end]) || break
            push!(heads, first(parts)); rest = parts[2:end]
        end
        length(heads) == length(args) &&
            return pattern_dispatch!(exprs, state, nctx, :seq, pushfirst!(rest, Expr(:call, :choice, heads...)))
        nonempty_arms = filter(a -> a !== "", args)
        if length(nonempty_arms) == 1 && length(args) == 2
            pattern_choice_optional!(exprs, state, nctx, only(nonempty_arms))
        else
            pattern_choice_multi!(exprs, state, nctx, args)
        end
    end
end

# Absence is marked by claiming a value segment's zero encoding, or else a presence bit
function pattern_choice_optional!(exprs::PatternExprs,
                                  state::ParserState, nctx::NodeCtx,
                                  @nospecialize(arm))
    popt = get(nctx, :optional, nothing)
    parent = nctx[:current_branch]
    optvar = gensym("optional")
    end_label = gensym("opt_end")
    sentinel_ref = Ref{Union{Nothing, OptSentinel}}(nothing)
    seg_start = length(exprs.segments)
    bits_before = state.bits
    child, oexprs, odetect = walk_arm!(exprs, state, nctx, arm, optvar, end_label, sentinel_ref, exprs.properties)
    if isnothing(sentinel_ref[])
        process_segment_output!(oexprs, state, nctx, :presence, selector(1, gensym(:optional), "present"))
        push!(oexprs.parse, emit_pack(state, Bool, optvar, state.bits))
        sentinel_ref[] = OptSentinel((state.bits, 1))
    end
    push!(exprs.layout, SegmentOptions([oexprs.layout, nothing], [nothing, nothing]))
    sentinel = sentinel_ref[]
    check = :(!iszero($(emit_extract(state, sentinel.position, sentinel.nbits))))
    patch_optional_extracts!(exprs.segments, seg_start+1:length(exprs.segments), check)
    parent.parsed_max += child.parsed_max - child.start_min
    parent.print_max = Base.max(parent.print_max, child.print_max)
    savedpos = gensym("savedpos")
    push!(exprs.parse, :($savedpos = pos))
    append!(exprs.parse, arm_attempt(popt, optvar, end_label, child, oexprs.parse))
    push!(exprs.parse, :(if !$optvar; pos = $savedpos; $(arm_clear_bits(bits_before, state.bits)...) end))
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
    odetect::Vector{ExprVarLine}
    seg_range::UnitRange{Int}
    bits_after::Int
end

function pattern_choice_multi!(exprs::PatternExprs,
                               state::ParserState, nctx::NodeCtx,
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
    process_segment_output!(exprs, state, nctx, :arm,
                            selector(discrim_bits, something(tag_field, gensym(:choice)), "one of $narms options"))
    arm_base = state.bits
    arm_data = ChoiceArm[]
    for (k, arm) in enumerate(arms)
        armvar = gensym("arm$k")
        end_label = gensym("arm$(k)_end")
        seg_start = length(exprs.segments)
        state.bits = arm_base
        child, oexprs, odetect = walk_arm!(exprs, state, nctx, arm, armvar, end_label, nothing,
                                           Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}[])
        bits_after = state.bits
        dval = gensym("discrim")
        push!(oexprs.parse, :($dval = $(discrim_type(k))))
        push!(oexprs.parse, emit_pack(state, discrim_type, dval, discrim_pos))
        push!(arm_data, ChoiceArm(armvar, end_label, child, oexprs, odetect,
                                  seg_start+1:length(exprs.segments), bits_after))
    end
    state.bits = maximum(Int[ad.bits_after for ad in arm_data])
    push!(exprs.layout, SegmentOptions([if arm === ""; nothing else ad.oexprs.layout end for (arm, ad) in zip(arms, arm_data)],
                                       if isnothing(tag_values) fill(nothing, narms)
                                       else Symbol[Symbol(if t isa QuoteNode t.value else t end) for t in tag_values] end))
    # Each arm starts where the choice does, so the choice spans their extremes
    parent.parsed_min += minimum(Int[ad.child.parsed_min - ad.child.start_min for ad in arm_data])
    parent.parsed_max += maximum(Int[ad.child.parsed_max - ad.child.start_min for ad in arm_data])
    parent.print_min = minimum(Int[ad.child.print_min for ad in arm_data])
    parent.print_max = maximum(Int[ad.child.print_max for ad in arm_data])
    armcheck(k) = :($(emit_extract(state, discrim_pos, discrim_bits)) == $(discrim_type(k)))
    for (k, ad) in enumerate(arm_data)
        ad.child.close_min = parent.parsed_min
        check = armcheck(k)
        patch_optional_extracts!(exprs.segments, ad.seg_range, check)
        for (name, val) in ad.oexprs.properties
            guarded = guard_property_extract(val, check, exprs.segments, ad.seg_range)
            push!(exprs.properties, name => guarded)
        end
    end
    arm_spans = Vector{Vector{ByteSet}}[ad.oexprs.bytespans for ad in arm_data]
    dispatch_reg = gensym("dispatch_reg")
    dispatch = find_choice_dispatch(arm_spans, dispatch_reg)
    if !isnothing(dispatch)
        emit_dispatch_parse!(exprs, state, nctx, popt, savedpos, arm_data, arm_base,
                             dispatch_reg, dispatch, "" in arms)
    else
        emit_cascade_parse!(exprs, state, nctx, popt, savedpos, arm_data, arm_base,
                            "" in arms, discrim_bits)
    end
    # Separate `if` blocks (not if/elseif) so rewrite_bufprint! can reach each arm's prints
    discrim_extract = emit_extract(state, discrim_pos, discrim_bits)
    # An arm prints only on its own discriminant, so any other would print nothing
    tagvar = if isnothing(tag_field); :discriminant else Symbol(:attr_, tag_field) end
    discrim_valid = emit_validity_check(state, tagvar, discrim_extract, 1:length(arm_data))
    push!(exprs.print.direct, discrim_valid)
    push!(exprs.print.getval, copy(discrim_valid))
    for (k, ad) in enumerate(arm_data)
        odetect = ad.odetect
        cond = :($discrim_extract == $(discrim_type(k)))
        append!(exprs.print.direct, odetect)
        push!(exprs.print.direct, :(if $cond; $(ad.oexprs.print.direct...) end))
        append!(exprs.print.vars, ad.oexprs.print.vars)
        push!(exprs.print.getval, :(if $cond; $(odetect...); $(ad.oexprs.print.getval...) end))
        push!(exprs.print.getlen, :(if $cond; $(ad.oexprs.print.getlen...) end))
        push!(exprs.print.putval, :(if $cond; $(ad.oexprs.print.putval...) end))
    end
    # Propagated so an enclosing choice can dispatch on this one's content
    all_alts = reduce(vcat, arm_spans)
    extend_bytespans!(exprs.bytespans, all_alts)
    # Tagged choice: the tag is just a property contributed by every arm
    if !isnothing(tag_field)
        tag_tuple = Expr(:tuple, tag_values...)
        for k in eachindex(arm_data)
            push!(exprs.properties, tag_field =>
                ExprVarLine[:(if $(armcheck(k)); $tag_tuple[$(discrim_type(k))] end)])
        end
    end
end

function emit_dispatch_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                              @nospecialize(popt::Union{Nothing, Symbol}), savedpos::Symbol,
                              arm_data::Vector{ChoiceArm}, arm_base::Int, reg_var::Symbol, @nospecialize(dispatch),
                              has_empty::Bool)
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
        rewind = :(if !$(ad.armvar); pos = $savedpos; $(arm_clear_bits(arm_base, ad.bits_after)...) end)
        push!(exprs.parse, :($(ad.armvar) = false))
        push!(exprs.parse, :(if $arm_idx_var == $(UInt8(k))
                                 $(arm_attempt(popt, ad.armvar, ad.end_label, ad.child, ad.oexprs.parse)...)
                                 $rewind
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
    emit_cascade_parse!(exprs, state, nctx, popt, savedpos, arm_data, arm_base, has_empty, discrim_bits)

Emit try-and-rewind parsing for choice arms without a dispatch window, selecting
the arm that consumes the most input (ties to the earliest in source order).

Arms are tried widest-first. A success commits in place once no remaining arm
could beat it, decided statically where arm bounds allow, so a choice whose
widest arms are also unambiguous costs nothing extra. Otherwise the best success
so far is snapshotted and rewound, and restored once every arm has been tried.
"""
function emit_cascade_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                             @nospecialize(popt::Union{Nothing, Symbol}), savedpos::Symbol,
                             arm_data::Vector{ChoiceArm}, arm_base::Int, has_empty::Bool, discrim_bits::Int)
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
        attempt = arm_attempt(popt, ad.armvar, ad.end_label, ad.child, ad.oexprs.parse)
        clear = if p.static_commit
            arm_clear_bits(arm_base, ad.bits_after)
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
            arm_clear_bits(arm_base - discrim_bits, ad.bits_after)
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
                           args::Vector{Any})
    arm = if all(a -> a isa String, args)
        Expr(:call, :choice, join(Vector{String}(args)), "")
    else
        Expr(:tuple, args...)
    end
    pattern_choice!(exprs, state, nctx, Any[arm, ""])
end
