# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern dispatch and structural handlers (field capture, choice/optional branching).

## Segment registries

const CORE_SEGMENTS = (
    literal = SegmentDef(:literal,    compile_literal,  (:casefold,)),
    skip    = SegmentDef(:skip,       compile_skip,     (:casefold, :print)),
    digits  = SegmentDef(:digits,     compile_digits,   (:base, :min, :max, :pad, :skip)),
    letters = SegmentDef(:letters,    compile_charseq,  (:upper, :lower, :casefold, :skip)),
    alphnum = SegmentDef(:alphnum,    compile_charseq,  (:upper, :lower, :casefold, :skip)),
    hex     = SegmentDef(:hex,        compile_charseq,  (:upper, :lower, :casefold, :skip)),
    charset = SegmentDef(:charset,    compile_charseq,  (:upper, :lower, :casefold, :skip)),
    embed   = SegmentDef(:embed,      compile_embed,    ()),
    choice  = SegmentDef(:choice,     compile_choice,   (:casefold, :is, :type)),
)

## Pattern dispatch

function pattern_dispatch!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           segments::NamedTuple, global_kwargs::Tuple,
                           node::Any, args::Vector{Any})
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
                           segments::NamedTuple, global_kwargs::Tuple,
                           thing::Any)
    all_kws = (Iterators.flatten(s.kwargs for s in segments)..., global_kwargs...)
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
"""
    pattern_field!(exprs, state, nctx, segments, global_kwargs, node, args)

Handle a `QuoteNode` field-capture node (`:major(digits(4))`). Opens a
`:fieldvar` scope, walks children, then assembles a property expression —
a direct segment label for single-value captures, or an IOBuffer
reconstruction for multi-segment fields.
"""
function pattern_field!(exprs::PatternExprs,
                        state::ParserState, nctx::NodeCtx,
                        segments::NamedTuple, global_kwargs::Tuple,
                        node::QuoteNode,
                        args::Vector{Any})
    isnothing(get(nctx, :fieldvar, nothing)) || throw(ArgumentError("Fields may not be nested"))
    nctx = NodeCtx(nctx, :fieldvar, Symbol("attr_$(node.value)"))
    initial_segs = length(exprs.segments)
    initialprints = length(exprs.print)
    for arg in args
        pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, arg)
    end
    new_value_segs = filter(s -> !isnothing(s.argtype), @view exprs.segments[initial_segs+1:end])
    isempty(new_value_segs) && throw(ArgumentError("Field $(node.value) does not capture any value"))
    if length(new_value_segs) == 1
        push!(exprs.properties, node.value => new_value_segs[1].label)
    else
        # Multi-node field: property assembles via IOBuffer from print expressions
        propprints = map(strip_segsets! ∘ copy, exprs.print[initialprints+1:end])
        filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, propprints)
        push!(exprs.properties, node.value => ExprVarLine[(
            quote
                io = IOBuffer()
                $(propprints...)
                takestring!(io)
            end).args...])
    end
end

## Choice/optional branching

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
                __cast_to_id($mT, $mask),
                8 * sizeof($(esc(state.name))) - $(state.bits)))))]
end

function walk_choice_arm!(oexprs, state::ParserState, nctx::NodeCtx,
                          segments::NamedTuple, global_kwargs::Tuple, arm)
    if Meta.isexpr(arm, :tuple)
        for a in arm.args
            pattern_dispatch!(oexprs, state, nctx, segments, global_kwargs, a)
        end
    else
        pattern_dispatch!(oexprs, state, nctx, segments, global_kwargs, arm)
    end
end

## Byte profiling for structured choice dispatch

function find_choice_dispatch(arm_spans::Vector{Vector{Vector{ByteSet}}})
    narms = length(arm_spans)
    narms >= 2 || return nothing
    any(isempty, arm_spans) && return nothing
    min_len = minimum(minimum(length, spans) for spans in arm_spans)
    for iT in REGISTER_TYPES
        bwidth = sizeof(iT)
        bwidth > min_len && break
        for pos in 1:min_len - bwidth + 1
            expr, _ = search_hash_families(narms, iT) do fn, expr_fn, _injective, maxval
                maxval + 1 > 512 && return nothing
                groups = Dict{UInt64, Int}()
                for (k, spans) in enumerate(arm_spans)
                    for alt in spans
                        window = @view alt[pos:pos+bwidth-1]
                        for combo in Iterators.product(window...)
                            regval = reduce(|, UInt64(b) << (8*(j-1))
                                            for (j, b) in enumerate(combo); init=zero(UInt64))
                            mv = fn(regval)
                            prev = get(groups, mv, 0)
                            (!iszero(prev) && prev != k) && return nothing
                            groups[mv] = k
                        end
                    end
                end
                length(groups) < 2 && return nothing
                table = zeros(UInt8, maxval + 1)
                for (mv, k) in groups
                    table[mv + 1] = k % UInt8
                end
                tup = Tuple(table)
                (b -> :(@inbounds $tup[$(expr_fn(b)) + 1]), 0)
            end
            !isnothing(expr) && return (; offset = pos, iT, expr)
        end
    end
    nothing
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
                         segments::NamedTuple, global_kwargs::Tuple,
                         arms::Vector{Any})
    nonempty_arms = filter(a -> a !== "", arms)
    if length(nonempty_arms) == 1 && length(arms) == 2
        pattern_choice_optional!(exprs, state, nctx, segments, global_kwargs,
                                 only(nonempty_arms))
    else
        pattern_choice_multi!(exprs, state, nctx, segments, global_kwargs, arms)
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
                                  segments::NamedTuple, global_kwargs::Tuple,
                                  arm)
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
                        parent.print_min, parent.print_max)
    push!(state.branches, child)
    nctx = NodeCtx(nctx, :current_branch, child)
    sentinel_ref = Ref{Union{Nothing, OptSentinel}}(nothing)
    nctx = NodeCtx(nctx, :optional_sentinel, sentinel_ref)
    seg_start = length(exprs.segments)
    bits_before = state.bits
    oexprs = PatternExprs(ExprVarLine[], ExprVarLine[],
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
    append!(exprs.print, nctx[:oprint_detect])
    push!(exprs.print, :($optvar = $check))
    push!(exprs.print, :(if $optvar; $(oexprs.print...) end))
    if !isempty(oexprs.bytespans)
        extend_bytespans!(exprs.bytespans, push!(copy(oexprs.bytespans), ByteSet[]))
    end
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
                               segments::NamedTuple, global_kwargs::Tuple,
                               arms::Vector{Any})
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
    arm_data = map(enumerate(arms)) do (k, arm)
        armvar = gensym("arm$k")
        end_label = gensym("arm$(k)_end")
        arm_nctx = NodeCtx(nctx, :optional, armvar)
        arm_nctx = NodeCtx(arm_nctx, :opt_label, end_label)
        arm_nctx = NodeCtx(arm_nctx, :oprint_detect, ExprVarLine[])
        arm_nctx = NodeCtx(arm_nctx, :optional_sentinel, nothing)
        child = ParseBranch(length(state.branches) + 1, parent, armvar,
                            parent.parsed_min, parent.parsed_max,
                            parent.parsed_min, parent.parsed_min,
                            parent.print_min, parent.print_max)
        push!(state.branches, child)
        arm_nctx = NodeCtx(arm_nctx, :current_branch, child)
        seg_start = length(exprs.segments)
        bits_before = state.bits
        oexprs = PatternExprs(ExprVarLine[], ExprVarLine[],
                              exprs.segments, exprs.properties, Vector{ByteSet}[])
        arm !== "" && walk_choice_arm!(oexprs, state, arm_nctx, segments, global_kwargs, arm)
        bits_after = state.bits
        dval = gensym("discrim")
        push!(oexprs.parse, :($dval = $(discrim_type(k))))
        push!(oexprs.parse, emit_pack(state, discrim_type, dval, discrim_pos))
        parent.parsed_max += child.parsed_max - child.start_min
        parent.print_max = Base.max(parent.print_max, child.print_max)
        (; armvar, end_label, child, oexprs, arm_nctx,
           seg_range = seg_start+1:length(exprs.segments),
           bits_before, bits_after)
    end
    for (k, ad) in enumerate(arm_data)
        check = :($(emit_extract(state, discrim_pos, discrim_bits)) == $(discrim_type(k)))
        patch_optional_extracts!(exprs.segments, ad.seg_range, check)
    end
    final_bits = state.bits
    arm_spans = [ad.oexprs.bytespans for ad in arm_data]
    dispatch = find_choice_dispatch(arm_spans)
    if !isnothing(dispatch)
        emit_dispatch_parse!(exprs, state, nctx, popt, savedpos, arm_data,
                             dispatch, "" in arms)
    else
        emit_cascade_parse!(exprs, state, nctx, popt, savedpos, arm_data,
                            "" in arms)
    end
    state.bits = final_bits
    # Separate `if` blocks (not if/elseif) so rewrite_bufprint! can reach print calls.
    discrim_extract = emit_extract(state, discrim_pos, discrim_bits)
    for (k, ad) in enumerate(arm_data)
        append!(exprs.print, ad.arm_nctx[:oprint_detect])
        push!(exprs.print, :(if $discrim_extract == $(discrim_type(k))
                                 $(ad.oexprs.print...)
                             end))
    end
end

function emit_dispatch_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                              popt::Union{Nothing, Symbol}, savedpos::Symbol,
                              arm_data, dispatch::NamedTuple, has_empty::Bool)
    reg_var = gensym("dispatch_reg")
    arm_idx_var = gensym("arm_idx")
    (; offset, iT, expr) = dispatch
    bwidth = sizeof(iT)
    load_pos = if offset == 1; :pos else :(pos + $(offset - 1)) end
    load = gen_load(iT, load_pos)
    min_bytes_needed = offset - 1 + bwidth
    push!(exprs.parse, :(if nbytes < pos + $(min_bytes_needed - 1)
                             $arm_idx_var = UInt8(0)
                         else
                             $reg_var = $load
                             $arm_idx_var = $(expr(reg_var))
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
        any_ok = reduce((a, ad) -> :($a || $(ad.armvar)), arm_data; init=false)
        fail = build_fail_expr!(state, nctx, "No choice arm matched")
        push!(exprs.parse, :(if !($any_ok); $fail end))
    end
end

function emit_cascade_parse!(exprs::PatternExprs, state::ParserState, nctx::NodeCtx,
                             popt::Union{Nothing, Symbol}, savedpos::Symbol,
                             arm_data, has_empty::Bool)
    innermost = if has_empty && isnothing(popt)
        ExprVarLine[]
    else
        ExprVarLine[build_fail_expr!(state, nctx, "No choice arm matched")]
    end
    cascade = foldr(enumerate(collect(arm_data)), init=innermost) do (_, ad), fallback
        branch_check = Expr(:call, :__branch_check, Bool, ad.child.id)
        guard = if isnothing(popt) branch_check else :($popt && $branch_check) end
        state.bits = ad.bits_after
        clear = arm_clear_bits(state, ad.bits_before)
        ExprVarLine[
            :($(ad.armvar) = $guard),
            :(if $(ad.armvar); $(ad.oexprs.parse...) end),
            :(@label $(ad.end_label)),
            :(if !$(ad.armvar); pos = $savedpos; $(clear...); $(fallback...) end)]
    end
    append!(exprs.parse, cascade)
end

function pattern_optional!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           segments::NamedTuple, global_kwargs::Tuple,
                           args::Vector{Any})
    arm = if all(a -> a isa String, args)
        Expr(:call, :choice, join(Vector{String}(args)), "")
    else
        Expr(:tuple, args...)
    end
    pattern_choice!(exprs, state, nctx, segments, global_kwargs, Any[arm, ""])
end
