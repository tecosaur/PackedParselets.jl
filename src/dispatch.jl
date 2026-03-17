# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern dispatch and structural handlers (field capture, optional branching).

## Segment registries

const CORE_SEGMENTS = (
    literal = SegmentDef(:literal,    compile_literal,  (:casefold,)),
    skip    = SegmentDef(:skip,       compile_skip,     (:casefold, :print)),
    digits  = SegmentDef(:digits,     compile_digits,   (:base, :min, :max, :pad)),
    letters = SegmentDef(:letters,    compile_charseq,  (:upper, :lower, :casefold)),
    alphnum = SegmentDef(:alphnum,    compile_charseq,  (:upper, :lower, :casefold)),
    hex     = SegmentDef(:hex,        compile_charseq,  (:upper, :lower, :casefold)),
    charset = SegmentDef(:charset,    compile_charseq,  (:upper, :lower, :casefold)),
    embed   = SegmentDef(:embed,      compile_embed,    ()),
    choice  = SegmentDef(:choice,     compile_choice,   (:casefold, :is)),
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
    elseif haskey(segments, node)
        def = getfield(segments, node)
        # Some segments (e.g. checkdigit) need exprs for field resolution
        output = if def.compile isa Function && applicable(def.compile, exprs, state, nctx, def, args)
            def.compile(exprs, state, nctx, def, args)
        else
            def.compile(state, nctx, def, args)
        end
        if node === :skip && isempty(output.meta.desc)
            # Skip without print: apply parse codegen and byte bounds only
            append!(exprs.parse, output.codegen.parse)
            inc_parsed!(nctx, first(output.bounds.parsed), last(output.bounds.parsed))
        else
            process_segment_output!(exprs, state, nctx, node, output)
        end
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
        output = def.compile(state, nctx, def, Any[thing])
        process_segment_output!(exprs, state, nctx, :literal, output)
    end
end

## Field capture

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

## Optional branching

# Replace placeholder `true` conditions in optional segment extracts with the
# resolved sentinel presence check.
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

# Build a parse-time cleanup expression that rewinds pos and (when multiple
# bits were packed) clears the optional's stale bits via a bitmask.
function optional_rewind_expr(state::ParserState, optvar::Symbol,
                              savedpos::Symbol, bits_before::Int)
    opt_bits = state.bits - bits_before
    if opt_bits > 1
        mT = cardtype(opt_bits)
        mask = typemax(mT) >> (8 * sizeof(mT) - opt_bits)
        clear = :(parsed = Core.Intrinsics.and_int(parsed,
            Core.Intrinsics.not_int(
                Core.Intrinsics.shl_int(
                    __cast_to_id($mT, $mask),
                    8 * sizeof($(esc(state.name))) - $(state.bits)))))
        :(if !$optvar; pos = $savedpos; $clear end)
    else
        :(if !$optvar; pos = $savedpos end)
    end
end

function pattern_optional!(exprs::PatternExprs,
                           state::ParserState, nctx::NodeCtx,
                           segments::NamedTuple, global_kwargs::Tuple,
                           args::Vector{Any})
    popt = get(nctx, :optional, nothing)
    optvar = gensym("optional")
    end_label = gensym("opt_end")
    nctx = NodeCtx(nctx, :optional, optvar)
    nctx = NodeCtx(nctx, :opt_label, end_label)
    nctx = NodeCtx(nctx, :oprint_detect, ExprVarLine[])
    # Fork a child branch for this optional scope
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
    # Walk children into a separate parse/print accumulator
    oexprs = (; parse = ExprVarLine[], print = ExprVarLine[], segments = exprs.segments, properties = exprs.properties)
    if all(a -> a isa String, args)
        def = getfield(segments, :choice)
        output = def.compile(state, nctx, def, push!(Any[join(Vector{String}(args))], ""))
        process_segment_output!(oexprs, state, nctx, :choice, output)
    else
        for arg in args
            pattern_dispatch!(oexprs, state, nctx, segments, global_kwargs, arg)
        end
    end
    # Ensure a sentinel exists (allocate an explicit presence bit if none was claimed)
    if sentinel_ref[] === nothing
        flag_nbits = (state.bits += 1)
        push!(oexprs.parse, emit_pack(state, Bool, optvar, flag_nbits))
        sentinel_ref[] = OptSentinel((flag_nbits, 1))
    end
    sentinel = sentinel_ref[]
    check = :(!iszero($(emit_extract(state, sentinel.position, sentinel.nbits))))
    patch_optional_extracts!(exprs.segments, seg_start+1:length(exprs.segments), check)
    # Merge max back to parent; min stays unchanged (optional content doesn't raise the guarantee)
    parent.parsed_max += child.parsed_max - child.start_min
    parent.print_max = Base.max(parent.print_max, child.print_max)
    # Emit parse-time guard, body, label, and cleanup
    savedpos = gensym("savedpos")
    branch_check = Expr(:call, :__branch_check, Bool, child.id)
    guard = if isnothing(popt); branch_check else :($popt && $branch_check) end
    push!(exprs.parse, :($savedpos = pos))
    push!(exprs.parse, :($optvar = $guard))
    push!(exprs.parse, :(if $optvar; $(oexprs.parse...) end))
    push!(exprs.parse, :(@label $end_label))
    push!(exprs.parse, optional_rewind_expr(state, optvar, savedpos, bits_before))
    # Print-time presence detection
    append!(exprs.print, nctx[:oprint_detect])
    push!(exprs.print, :($optvar = $check))
    push!(exprs.print, :(if $optvar; $(oexprs.print...) end))
end
