# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Final-stage codegen: assemble complete method definitions from the
# accumulated PatternExprs (parse, print, segments, properties) produced
# by pattern walking.
#
# Each `assemble_*` function emits one or more method definitions for the
# generated type. `assemble_type` is the orchestrator that wires them all
# into a single `:toplevel` block.

## Top-level entry point

"""
    maketype(segments, mod, name, pattern; kwargs...) -> (NamedTuple, ParserState)

Full compilation pipeline: create state, walk the pattern, and assemble all
method definitions for a bit-packed primitive type.

Returns `(typeparts, state)`. `typeparts` is a `NamedTuple` of generated `Expr`s.
Use `Expr(:toplevel, values(typeparts)...)` to produce a block ready for `eval`,
or manipulate individual components before assembling.

# Components

- `typedef`: primitive type declaration
- `nbits`, `parsebounds`, `printbounds`: type-level query methods
- `parsebytes`: `parsebytes` method
- `tobytes`: `tobytes` methods (buf+val and allocating)
- `print`: `Base.write`, `Base.print`, and `Base.string` methods
- `propertynames`: `Base.propertynames` method
- `properties`: `Base.getproperty` method
- `segments_type`, `segments_value`: `segments(::Type)` and `segments(::instance)` methods
- `constructor`: positional constructor
- `show`: `Base.show` method
- `isless`: `Base.isless` method
- `hookdata`: `Expr(:block, ...)` of additional expressions from finalize hooks
"""
function maketype(@nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}), mod::Module, name::Symbol, @nospecialize(pattern);
                  supertype::Type = Any,
                  casefold::Bool = true,
                  globals::NamedTuple = (;),
                  global_kwargs::Tuple = ())
    root = ParseBranch(1, nothing, :root, 0, 0, 0, 0, 0, 0)
    state = ParserState(name, mod, 0, supertype,
                        globals, ParseBranch[root], String[], Pair{Symbol, SegmentOutput}[])
    nctx = NodeCtx(:current_branch, root)
    nctx = NodeCtx(nctx, :casefold, casefold)
    exprs = PatternExprs()
    push!(exprs.parse, Expr(:call, :__branch_check, root.id, nothing))
    pattern_dispatch!(exprs, state, nctx, segments, global_kwargs, pattern)
    assemble_type(exprs, state, name, segments)
end

## Assembly

"""
    assemble_type(exprs, state, name, segments) -> (NamedTuple, ParserState)

Assemble all method definitions for the generated type as a `NamedTuple`
of expression components.

Runs finalize hooks from the segment registry, collecting their outputs
in the `hookdata` field.
"""
function assemble_type(exprs::PatternExprs, state::ParserState, name::Symbol,
                       @nospecialize(segments::NamedTuple{<:Any, <:Tuple{Vararg{SegmentDef}}}) = (;))
    numbits = 8 * cld(state.bits, 8)
    for field in (:direct, :getval, :getlen, :putval)
        implement_casting!(state, getfield(exprs.print, field))
    end
    root = state.branches[1]
    M = PackedParselets
    # Run finalize hooks, collecting extra expressions
    hookdata = Expr[]
    seen_kinds = Set{Symbol}()
    for (kind, _) in state.segment_outputs
        kind ∈ seen_kinds && continue
        push!(seen_kinds, kind)
        if haskey(segments, kind)
            def = getfield(segments, kind)
            if !isnothing(def.finalize)
                def.finalize(hookdata, exprs, state, name)
            end
        end
    end
    pnames = Tuple(unique(map(first, exprs.properties)))
    typeparts = (;
        typedef = :(Base.@__doc__(primitive type $(esc(name)) <: $(state.supertype) $numbits end)),
        nbits = :($(GlobalRef(M, :nbits))(::Type{$(esc(name))}) = $(state.bits)),
        parsebounds = :($(GlobalRef(M, :parsebounds))(::Type{$(esc(name))}) = $((root.parsed_min, root.parsed_max))),
        printbounds = :($(GlobalRef(M, :printbounds))(::Type{$(esc(name))}) = $((root.print_min, root.print_max))),
        parsebytes = assemble_parsebytes(exprs.parse, exprs.segments, state, name),
        tobytes = assemble_tobytes(exprs.print, state, name),
        print = assemble_print(exprs.print, state, name),
        propertynames = :($(GlobalRef(Base, :propertynames))(::$(esc(name))) = $pnames),
        properties = assemble_properties(exprs.properties, exprs.segments, state, name),
        segments_type = assemble_segments_type(exprs.segments, state, name),
        segments_value = assemble_segments_value(exprs.segments, exprs.print, state, name),
        constructor = assemble_constructor(exprs.segments, exprs.properties, state, name),
        show = assemble_show(exprs.segments, exprs.properties, state, name),
        isless = :($(GlobalRef(Base, :isless))(a::$(esc(name)), b::$(esc(name))) =
                       Core.Intrinsics.ult_int(a, b)),
        hookdata = Expr(:block, hookdata...),
    )
    # Qualify bare references to PackedParselets runtime functions so that
    # generated code works when eval'd in any module.
    for v in values(typeparts)
        v isa Expr && qualify_runtime_refs!(v, PackedParselets)
    end
    (typeparts, state)
end

## parsebytes

function assemble_parsebytes(pexprs::Vector{ExprVarLine}, segments::Vector{ValueSegment},
                              state::ParserState, name::Symbol)
    parsed_min = state.branches[1].parsed_min
    M = PackedParselets
    # Primary pass: optimal length-check insertion with sentinel resolution
    resolved = implement_casting!(state, pexprs)
    insert_length_checks!(state, resolved, state.branches)
    while fold_branches!(resolved) end
    # Resolve __checksum_gate sentinel
    gate_idx = findfirst(resolved) do e
        Meta.isexpr(e, :call) && first(e.args) === :__checksum_gate
    end
    if !isnothing(gate_idx)
        ok_sym, checkpos_sym = resolved[gate_idx].args[2:3]
        resolved[gate_idx] = :($ok_sym || return (parsed, -$checkpos_sym))
    end
    # Replace the root __branch_check sentinel with an upfront minimum-length check
    formstr = segments_formstring(segments, state.branches)
    errmsg = register_errmsg!(state, string(
        "Expected at least ", parsed_min, " bytes",
        if isempty(formstr) "" else string(", must match the form '", formstr, "'") end))
    split_idx = findfirst(resolved) do e
        Meta.isexpr(e, :call) && first(e.args) === :__branch_check && e.args[2] == 1
    end
    if !isnothing(split_idx) && parsed_min > 0
        resolved[split_idx] = if split_idx > 1
            :(nbytes - pos >= $(parsed_min - 1) || return ($errmsg, 1))
        else
            :(nbytes >= $parsed_min || return ($errmsg, 1))
        end
    elseif !isnothing(split_idx)
        deleteat!(resolved, split_idx)
    end
    :(Base.@assume_effects :foldable :nothrow function $(GlobalRef(M, :parsebytes))(::Type{$(esc(name))}, data::AbstractVector{UInt8})
          parsed = $(zero_parsed_expr(state))
          pos = 1
          nbytes = length(data)
          $(resolved...)
          (parsed, pos)
      end)
end

## tobytes

function strip_print_markers!(pexprs::Vector)
    map!(strip_segsets! ∘ copy, pexprs, pexprs)
    filter!(e -> !Meta.isexpr(e, :(=), 2) || first(e.args) !== :__segment_printed, pexprs)
end

function assemble_tobytes(print::PrintExprs, state::ParserState, name::Symbol)
    root = state.branches[1]
    fixedlen = root.print_min == root.print_max
    M = PackedParselets
    directexprs = strip_print_markers!(copy(print.direct))
    rewrite_bufprint!(directexprs)
    allocating = if fixedlen
        :(function $(GlobalRef(M, :tobytes))(val::$(esc(name)))
              buf = Base.StringMemory($(root.print_max))
              $(GlobalRef(M, :tobytes))(buf, val)
              buf
          end)
    else
        # Fused: getval+getlen → alloc exact buffer → putval
        putvalexprs = strip_print_markers!(copy(print.putval))
        rewrite_bufprint!(putvalexprs)
        localdecls = [Expr(:(=), v, d) for (v, d) in print.vars]
        :(function $(GlobalRef(M, :tobytes))(val::$(esc(name)))
              $(Expr(:local, localdecls...))
              pos = 0
              $(print.getval...)
              $(print.getlen...)
              buf = Base.StringMemory(pos)
              pos = 0
              $(putvalexprs...)
              buf
          end)
    end
    Expr(:block,
        :(function $(GlobalRef(M, :tobytes))(buf::Memory{UInt8}, val::$(esc(name)), pos::Int=0)
              $(directexprs...)
              pos
          end),
        allocating)
end

## print / string

function assemble_print(::PrintExprs, state::ParserState, name::Symbol)
    maxbytes = state.branches[1].print_max
    M = PackedParselets
    Expr(:block,
        :(function $(GlobalRef(Base, :write))(io::IO, val::$(esc(name)))
              buf = Memory{UInt8}(undef, $maxbytes)
              len = $(GlobalRef(M, :tobytes))(buf, val)
              Base.unsafe_write(io, pointer(buf), len)
          end),
        :($(GlobalRef(Base, :print))(io::IO, val::$(esc(name))) =
              ($(GlobalRef(Base, :write))(io, val); nothing)),
        :($(GlobalRef(Base, :string))(val::$(esc(name))) =
              Base.unsafe_takestring($(GlobalRef(M, :tobytes))(val))))
end

function resolve_print_markers!(exprs)
    for item in exprs
        item isa Expr || continue
        if Meta.isexpr(item, :call) && !isempty(item.args) && item.args[1] == :__tobytes_print
            item.args[1] = :print
        end
        resolve_print_markers!(item.args)
    end
end

## getproperty

function assemble_properties(properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                              segs::Vector{ValueSegment},
                              state::ParserState, name::Symbol)
    isempty(properties) && return :()
    grouped = Pair{Symbol, Vector{Union{Symbol, Vector{ExprVarLine}}}}[]
    seen = Dict{Symbol, Int}()
    for (pname, val) in properties
        if haskey(seen, pname)
            push!(grouped[seen[pname]].second, val)
        else
            seen[pname] = length(grouped) + 1
            push!(grouped, pname => [val])
        end
    end
    fallback = :(throw(FieldError($(esc(name)), prop)))
    clauses = foldr(enumerate(grouped), init = fallback) do (i, (prop, vals)), rest
        prop_exprs = if length(vals) == 1
            resolve_extract(only(vals), segs)
        else
            # Build nested if-elseif chain from guarded extract entries.
            entries = [resolve_extract(val, segs) for val in vals]
            filter!(!isempty, entries)
            ExprVarLine[chain_guarded(entries)]
        end
        qprop = QuoteNode(prop)
        body = Expr(:block, implement_casting!(state, prop_exprs)...)
        Expr(if i == 1; :if else :elseif end, :(prop === $qprop), body, rest)
    end
    :(function $(GlobalRef(Base, :getproperty))(val::$(esc(name)), prop::Symbol)
          $clauses
      end)
end

## Constructor

function assemble_constructor(segs::Vector{ValueSegment},
                              properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                              state::ParserState, name::Symbol)
    resolved = resolve_property_segments(properties, segs)
    isempty(resolved) && return :()
    args = Tuple{Symbol, Int}[]
    for (pname, idxs) in resolved
        if length(idxs) == 1
            push!(args, (pname, only(idxs)))
        else
            for (j, si) in enumerate(idxs)
                push!(args, (Symbol(pname, "_", j), si))
            end
        end
    end
    isempty(args) && return :()
    params = [let seg = segs[si]
                  if isnothing(seg.argtype)
                      :($aname)
                  elseif !isnothing(seg.condition)
                      :($aname::Union{$(seg.argtype), Nothing})
                  else
                      :($aname::$(seg.argtype))
                  end
              end for (aname, si) in args]
    argbindings = [:($(segs[si].argvar) = $aname) for (aname, si) in args]
    scope_checks = constructor_scope_checks(args, segs, state)
    encode_exprs = reduce(vcat, (segs[si].impart for (_, si) in args); init=Expr[])
    targetsize = cld(state.bits, 8)
    for expr in encode_exprs
        implement_casting!(expr, name, targetsize)
    end
    :(function $(esc(name))($(params...))
          parsed = $(zero_parsed_expr(state))
          $(argbindings...)
          $(scope_checks...)
          $(encode_exprs...)
          parsed
      end)
end

# Validate optional scope nesting: a child scope's args must not be
# specified when the parent scope's args are nothing.
function constructor_scope_checks(args::Vector{Tuple{Symbol, Int}},
                                  segs::Vector{ValueSegment},
                                  state::ParserState)
    scope_parents = Dict{Symbol, Symbol}()
    for b in state.branches
        b.scope === :root && continue
        scope_parents[b.scope] = b.parent.scope
    end
    scope_args = Dict{Symbol, Vector{Int}}()
    for (idx, (_, si)) in enumerate(args)
        scope = segs[si].condition
        isnothing(scope) && continue
        push!(get!(Vector{Int}, scope_args, scope), idx)
    end
    checks = Expr[]
    for (scope, cidxs) in scope_args
        parent_scope = get(scope_parents, scope, nothing)
        isnothing(parent_scope) && continue
        pidxs = get(scope_args, parent_scope, nothing)
        isnothing(pidxs) && continue
        parg = args[first(pidxs)][1]
        carg = args[first(cidxs)][1]
        push!(checks, :(if isnothing($parg) && !isnothing($carg)
            throw(ArgumentError(
                string("Cannot specify ", $(QuoteNode(carg)),
                       " when ", $(QuoteNode(parg)), " is nothing")))
        end))
    end
    checks
end

## show

function assemble_show(segs::Vector{ValueSegment},
                       properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
                       state::ParserState, name::Symbol)
    pnames = unique(map(first, properties))
    isempty(pnames) && return :()
    show_parts = ExprVarLine[]
    for pname in pnames
        isempty(show_parts) || push!(show_parts, :(print(io, ", ")))
        push!(show_parts, :(show(io, getproperty(val, $(QuoteNode(pname))))))
    end
    :(function $(GlobalRef(Base, :show))(io::IO, val::$(esc(name)))
          if get(io, :limit, false) === true
              if get(io, :typeinfo, Nothing) != $(esc(name))
                  print(io, $(QuoteNode(name)), ':')
              end
              print(io, val)
          else
              show(io, $(esc(name)))
              print(io, '(')
              $(show_parts...)
              print(io, ')')
          end
      end)
end

## segments

function assemble_segments_type(segs::Vector{ValueSegment}, ::ParserState, name::Symbol)
    isempty(segs) && return :()
    M = PackedParselets
    :(function $(GlobalRef(M, :segments))(::Type{$(esc(name))})
          $(Expr(:tuple, [(; nbits=s.nbits, kind=s.kind, label=s.label, desc=s.desc, shortform=s.shortform)
                          for s in segs if s.nbits > 0]...))
      end)
end

function assemble_segments_value(segs::Vector{ValueSegment}, print::PrintExprs,
                                  ::ParserState, name::Symbol)
    isempty(segs) && return :()
    M = PackedParselets
    svars = Tuple{Int, Symbol}[]
    pexprs2 = map(copy, print.direct)
    resolve_print_markers!(pexprs2)
    for expr in pexprs2
        rewrite_segment_captures!(svars, segs, expr)
    end
    :(function $(GlobalRef(M, :segments))(val::$(esc(name)))
          io = IOBuffer()
          $(Expr(:(=), Expr(:tuple, (s for (_, s) in svars)...), Expr(:tuple, ("" for _ in svars)...)))
          $(pexprs2...)
          $(Expr(:tuple, (Expr(:tuple, i, s) for (i, s) in svars)...))
      end)
end

# Replace `__segment_printed = i` markers with `segN = takestring!(io)`,
# building up the (segment_index, varname) list as we go.
function rewrite_segment_captures!(segvars::Vector{Tuple{Int, Symbol}},
                                   segs::Vector{ValueSegment},
                                   expr::ExprVarLine)
    expr isa Expr || return expr
    if Meta.isexpr(expr, :(=)) && first(expr.args) === :__segment_printed
        _, i = expr.args
        if i > length(segvars)
            anon = iszero(segs[i].nbits)
            precount = sum((s.nbits > 0 for s in segs[1:i-1]), init = 0)
            push!(segvars, (if anon; 0 else precount + 1 end, Symbol("seg$i")))
        end
        var = last(segvars[i])
        expr.args[1:2] = :($var = takestring!(io)).args
    else
        for arg in expr.args
            if arg isa Expr
                rewrite_segment_captures!(segvars, segs, arg)
            end
        end
    end
    expr
end

## Property-segment resolution

# Map Symbol-ref properties to `(name, segment_indices)` pairs.
# Only processes the first Symbol ref per name; Vector{ExprVarLine}
# entries (choice-guarded or multi-segment) are handled separately.
function resolve_property_segments(properties, segs::Vector{ValueSegment})
    result = Pair{Symbol, Vector{Int}}[]
    seen = Set{Symbol}()
    for (pname, val) in properties
        pname ∈ seen && continue
        if val isa Symbol
            push!(seen, pname)
            idx = findfirst(s -> s.label == val, segs)
            isnothing(idx) && continue
            push!(result, pname => [idx])
        elseif val isa Vector
            push!(seen, pname)
            idxs = [i for (i, s) in enumerate(segs)
                     if !isnothing(s.argtype) && s.label == pname]
            isempty(idxs) || push!(result, pname => idxs)
        end
    end
    result
end

## Segment-set stripping

# Remove `__segment_printed = N` markers from expression trees.
# Used when print expressions are reused for buffer output or properties.
function strip_segsets!(expr::ExprVarLine)
    expr isa Expr || return expr
    remove = Int[]
    for (i, arg) in enumerate(expr.args)
        arg isa Expr || continue
        if Meta.isexpr(arg, :(=), 2) && first(arg.args) === :__segment_printed
            push!(remove, i)
        else
            strip_segsets!(arg)
        end
    end
    isempty(remove) || deleteat!(expr.args, remove)
    expr
end

## Buffer printing

"""
    rewrite_bufprint!(pexprs)

Rewrite `print(io, ...)` and `printchars(io, ...)` calls in `pexprs`
into direct `Memory{UInt8}` buffer operations (`bufprint`, `unpackchars!`,
`bufprint_static`), avoiding IO overhead in the generated `tobytes` method.

Recurses into nested expressions. Modifies `pexprs` in place.
"""
function rewrite_bufprint!(pexprs::Union{Vector{<:ExprVarLine}, Vector{Any}})
    # Top-level: collect IO calls for splice replacement (applied in reverse to preserve indices).
    # Nested calls recurse into sub-expression args, which are never top-level
    # vector elements and so are safe from the outer splice.
    splices = Tuple{Int, Vector{Any}}[]
    for (i, expr) in enumerate(pexprs)
        if Meta.isexpr(expr, :call) && length(expr.args) >= 3 && expr.args[2] == :io
            fname, _, args... = expr.args
            replacement = if fname == :print
                rewrite_print_call(args)
            elseif fname == :write && length(args) == 1
                Any[:(@inbounds buf[pos += 1] = $(args[1]))]
            elseif fname == :printchars
                rewrite_printchars(args)
            elseif fname == :__tobytes_print
                tobytes_ref = GlobalRef(PackedParselets, :tobytes)
                ebuf = gensym("ebuf")
                Any[:($ebuf = $tobytes_ref($(args...))),
                    :(Base.unsafe_copyto!(pointer(buf, pos + 1), pointer($ebuf), length($ebuf))),
                    :(pos += length($ebuf))]
            end
            push!(splices, (i, replacement))
        elseif expr isa Expr
            for arg in expr.args
                if arg isa Expr
                    rewrite_bufprint!(arg.args)
                end
            end
        end
    end
    for (i, replacement) in reverse(splices)
        splice!(pexprs, i, replacement)
    end
end


function rewrite_printchars(args)
    if length(args) == 4 && args[2] isa Int && args[3] isa Tuple &&
            args[4] isa Bool && !args[4] && length(args[3]) in (1, 2)
        var, nchars, ranges, _ = args
        return gen_swar_bufprintchars(var, nchars, cardbits(sum(length, ranges)), ranges)
    end
    Any[:(pos = unpackchars!(buf, pos, $(args...)))]
end

function gen_swar_bufprintchars(var, nchars::Int, bpc::Int, ranges)
    exprs = Any[]
    remaining = nchars
    consumed = 0
    for nf in (8, 4, 2)
        remaining >= nf || continue
        sT = register_type(nf)
        svar = gensym("spread")
        rshift = (remaining - nf) * bpc
        lshift = 8 * nf - nf * bpc
        extract = if iszero(rshift) var else :($var >> $rshift) end
        init = :($extract % $sT)
        if !iszero(lshift)
            init = :($init << $lshift & $(typemax(sT) << lshift))
        end
        push!(exprs, Expr(:(=), svar, init))
        append!(exprs, gen_reverse_swar(sT, svar, bpc, nf, ranges))
        push!(exprs, :(Base.unsafe_store!(Ptr{$sT}(pointer(buf, pos + 1)), $svar)))
        push!(exprs, :(pos += $nf))
        consumed += nf
        remaining -= nf
    end
    fmask = (1 << bpc) - 1
    base1 = UInt8(first(first(ranges)))
    len1 = UInt8(length(first(ranges)))
    delta = if length(ranges) >= 2 UInt8(first(ranges[2])) - base1 - len1 else 0x00 end
    for i in consumed:nchars-1
        shift = (nchars - 1 - i) * bpc
        shifted = if iszero(shift) var else :($var >> $shift) end
        idx = :(UInt8($shifted & $fmask))
        byte = if length(ranges) == 1
            :($base1 + $idx)
        else
            :($base1 + $idx + ($idx >= $len1) * $delta)
        end
        push!(exprs, :(@inbounds buf[pos += 1] = $byte))
    end
    exprs
end

function rewrite_print_call(args::Vector)
    if length(args) == 1
        arg = first(args)
        if Meta.isexpr(arg, :call) && first(arg.args) == :string
            sargs = arg.args[2:end]
            positional = Any[]
            base, pad = 10, 0
            for sa in sargs
                if Meta.isexpr(sa, :kw, 2) && sa.args[1] == :base
                    base = sa.args[2]
                elseif Meta.isexpr(sa, :kw, 2) && sa.args[1] == :pad
                    pad = sa.args[2]
                else
                    push!(positional, sa)
                end
            end
            Any[:(pos = bufprint(buf, pos, $(positional...), $base, $pad))]
        elseif arg isa String
            Any[bufprint_static(arg)...]
        else
            Any[:(pos = bufprint(buf, pos, $arg))]
        end
    else
        Any[:(pos = bufprint(buf, pos, $arg)) for arg in args]
    end
end

function bufprint_static(str::String)
    reduce(register_chunks(ncodeunits(str)), init = Expr[]) do exprs, (; offset, width, iT)
        value = pack_bytes(str, offset, width, iT)
        if iT === UInt8
            push!(exprs, :(@inbounds buf[pos += 1] = $value))
        else
            push!(exprs,
                  :(Base.unsafe_store!(Ptr{$iT}(pointer(buf, pos + 1)), htol($value))),
                  :(pos += $width))
        end
    end
end

## Runtime reference qualification

# PackedParselets runtime symbols that appear bare in generated code.
# These must be qualified with GlobalRef when the generated code is
# eval'd outside the defining module (which normally imports them).
# Note: parsebytes/tobytes are excluded — they are API functions whose
# method definitions already use GlobalRef(PackedParselets, ...).
# Bare references in finalize hooks are the hook author's responsibility.
const RUNTIME_SYMS = Set{Symbol}([
    :parsechars, :parseint, :printchars, :chars2string,
    :bufprint, :radix100_store, :unpackchars!, :takestring!,
])

"""
    qualify_runtime_refs!(expr, mod)

Walk `expr` and replace bare calls to known PackedParselets runtime
functions with `GlobalRef(mod, name)`. This ensures generated code
works when eval'd in any module, not just one that imports these symbols.
"""
function qualify_runtime_refs!(expr::Expr, mod::Module)
    for (i, arg) in enumerate(expr.args)
        if arg isa Symbol && arg ∈ RUNTIME_SYMS
            # Only qualify call-position symbols (first arg of :call)
            # and assignment targets that are function calls
            if (Meta.isexpr(expr, :call) && i == 1) ||
               (Meta.isexpr(expr, :., 2) && i == 2)
                expr.args[i] = GlobalRef(mod, arg)
            end
        elseif arg isa Expr
            qualify_runtime_refs!(arg, mod)
        end
    end
    expr
end
