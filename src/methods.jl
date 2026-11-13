# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Final-stage codegen: assemble method definitions from the walked PatternExprs.

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
- `tobytes`: `tobytes` method
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
                  @nospecialize(supertype::Type = Any),
                  casefold::Bool = true,
                  @nospecialize(globals::NamedTuple = (;)),
                  @nospecialize(global_kwargs::Tuple = ()))
    root = ParseBranch(1, nothing, :root, 0, 0, 0, 0, 0, 0, 0)
    kwnames = Symbol[]
    for def in segments; append!(kwnames, def.kwargs) end
    append!(kwnames, global_kwargs)
    state = ParserState(name, mod, 0, supertype, globals, segments, kwnames,
                        ParseBranch[root], String[], Pair{Symbol, SegmentOutput}[])
    nctx = NodeCtx(:current_branch, root)
    nctx = NodeCtx(nctx, :casefold, casefold)
    exprs = PatternExprs()
    push!(exprs.parse, Expr(:call, :__root_check))
    pattern_dispatch!(exprs, state, nctx, pattern)
    assemble_type(exprs, state)
end

## Assembly

function assemble_type(exprs::PatternExprs, state::ParserState)
    (; name, segments) = state
    numbits = 8 * cld(state.bits, 8)
    implement_casting!(state, exprs.print)
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
    # Each property's values, in order of first appearance
    props = Pair{Symbol, Vector{Union{Symbol, Vector{ExprVarLine}}}}[]
    seen = Dict{Symbol, Int}()
    for (pname, val) in exprs.properties
        if haskey(seen, pname)
            push!(last(props[seen[pname]]), val)
        else
            seen[pname] = length(props) + 1
            push!(props, pname => [val])
        end
    end
    typeparts = (;
        typedef = :(Base.@__doc__(primitive type $(esc(name)) <: $(state.supertype) $numbits end)),
        nbits = :($(GlobalRef(M, :nbits))(::Type{$(esc(name))}) = $(state.bits)),
        parsebounds = :($(GlobalRef(M, :parsebounds))(::Type{$(esc(name))}) = $((root.parsed_min, root.parsed_max))),
        printbounds = :($(GlobalRef(M, :printbounds))(::Type{$(esc(name))}) = $((root.print_min, root.print_max))),
        parsebytes = assemble_parsebytes(exprs.parse, exprs.segments, state, name),
        tobytes = assemble_tobytes(exprs.print, name),
        print = assemble_print(state, name),
        propertynames = :($(GlobalRef(Base, :propertynames))(::$(esc(name))) = $(Tuple(Symbol[first(p) for p in props]))),
        properties = assemble_properties(props, exprs.segments, state, name),
        segments_type = assemble_segments_type(exprs.layout, name),
        segments_value = assemble_segments_value(length(exprs.segments), state, name),
        constructor = assemble_constructor(exprs.segments, props, state, name),
        show = assemble_show(props, name),
        isless = :($(GlobalRef(Base, :isless))(a::$(esc(name)), b::$(esc(name))) =
                       Core.Intrinsics.ult_int(a, b)),
        hookdata = Expr(:block, hookdata...),
    )
    # Inlining our globals' values lets the code run in whichever module evals it
    for v in values(typeparts)
        v isa Expr || continue
        Base.remove_linenums!(v)
        inline_globals!(v, PackedParselets)
        VERSION < v"1.12-" && expand_macrocall_inbounds!(v)
    end
    (typeparts, state)
end

## parsebytes

function assemble_parsebytes(pexprs::Vector{ExprVarLine}, segments::Vector{ValueSegment},
                              state::ParserState, name::Symbol)
    parsed_min = state.branches[1].parsed_min
    M = PackedParselets
    resolved = implement_casting!(state, pexprs)
    for expr in resolved
        expr isa Expr && resolve_sentinel_in_expr!(expr, state.branches)
    end
    while fold_branches!(resolved) end
    # The root's minimum length is checked upfront, and a checksum's verdict returns
    formstr = segments_formstring(segments)
    errmsg = register_errmsg!(state, string(
        "Expected at least ", parsed_min, " bytes",
        if isempty(formstr) "" else string(", must match the form '", formstr, "'") end))
    root = 0
    for (i, e) in enumerate(resolved)
        Meta.isexpr(e, :call) || continue
        if first(e.args) === :__checksum_gate
            resolved[i] = :($(e.args[2]) || return (parsed, -$(e.args[3])))
        elseif first(e.args) === :__root_check
            root = i
        end
    end
    if parsed_min > 0
        resolved[root] = :(nbytes - pos >= $(parsed_min - 1) || return ($errmsg, start))
    else
        deleteat!(resolved, root)
    end
    :(Base.@assume_effects :foldable :nothrow @inline function $(GlobalRef(M, :parsebytes))(::Type{$(esc(name))}, data::AbstractVector{UInt8}, start::Int = 1)
          parsed = $(zero_parsed_expr(state))
          pos = start
          nbytes = length(data)
          $(resolved...)
          (parsed, pos)
      end)
end

## tobytes / print / string

# `segments(val)` collects where each segment ends in `marks`
assemble_tobytes(print::Vector{ExprVarLine}, name::Symbol) =
    :(Base.@constprop :none function $(GlobalRef(PackedParselets, :tobytes))(buf::Memory{UInt8}, val::$(esc(name)), pos::Int, marks = nothing)
          $(print...)
          pos
      end)

function assemble_print(state::ParserState, name::Symbol)
    maxbytes = state.branches[1].print_max
    M = PackedParselets
    Expr(:block,
        :(function $(GlobalRef(Base, :write))(io::IO, val::$(esc(name)))
              buf = Memory{UInt8}(undef, $maxbytes)
              len = $(GlobalRef(M, :tobytes))(buf, val)
              GC.@preserve buf Base.unsafe_write(io, pointer(buf), len)
          end),
        :($(GlobalRef(Base, :print))(io::IO, val::$(esc(name))) =
              ($(GlobalRef(Base, :write))(io, val); nothing)),
        :(function $(GlobalRef(Base, :string))(val::$(esc(name)))
              buf = Base.StringMemory($maxbytes)
              $(GlobalRef(M, :takestring))(buf, $(GlobalRef(M, :tobytes))(buf, val))
          end))
end

## getproperty

function assemble_properties(grouped::Vector{Pair{Symbol, Vector{Union{Symbol, Vector{ExprVarLine}}}}},
                              segs::Vector{ValueSegment},
                              state::ParserState, name::Symbol)
    isempty(grouped) && return :()
    fallback = :(throw(FieldError($(esc(name)), prop)))
    clauses = fallback
    for i in length(grouped):-1:1
        prop, vals = grouped[i]
        prop_exprs = if length(vals) == 1
            resolve_extract(only(vals), segs)
        else
            entries = Vector{ExprVarLine}[resolve_extract(val, segs) for val in vals]
            filter!(!isempty, entries)
            ExprVarLine[chain_guarded(entries)]
        end
        qprop = QuoteNode(prop)
        body = Expr(:block, implement_casting!(state, prop_exprs)...)
        clauses = Expr(if i == 1; :if else :elseif end, :(prop === $qprop), body, clauses)
    end
    :(function $(GlobalRef(Base, :getproperty))(val::$(esc(name)), prop::Symbol)
          $clauses
      end)
end

## Constructor

function assemble_constructor(segs::Vector{ValueSegment},
                              props::Vector{Pair{Symbol, Vector{Union{Symbol, Vector{ExprVarLine}}}}},
                              state::ParserState, name::Symbol)
    resolved = resolve_property_segments(props, segs)
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
    params, argbindings, encode_exprs = Union{Symbol, Expr}[], Expr[], Expr[]
    for (aname, si) in args
        seg = segs[si]
        push!(params, if isnothing(seg.argtype)
                  aname
              elseif !isnothing(seg.condition)
                  :($aname::Union{$(seg.argtype), Nothing})
              else
                  :($aname::$(seg.argtype))
              end)
        push!(argbindings, :($(seg.argvar) = $aname))
        append!(encode_exprs, seg.impart)
    end
    scope_checks = constructor_scope_checks(args, segs)
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
function constructor_scope_checks(args::Vector{Tuple{Symbol, Int}}, segs::Vector{ValueSegment})
    # Scopes in order of first appearance, so the checks don't follow hashing
    scopes = ParseBranch[]
    scope_args = Dict{ParseBranch, Vector{Int}}()
    for (idx, (_, si)) in enumerate(args)
        scope = segs[si].condition
        isnothing(scope) && continue
        haskey(scope_args, scope) || push!(scopes, scope)
        push!(get!(Vector{Int}, scope_args, scope), idx)
    end
    checks = Expr[]
    for scope in scopes
        cidxs = scope_args[scope]
        pidxs = get(scope_args, scope.parent, nothing)
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

function assemble_show(props::Vector{Pair{Symbol, Vector{Union{Symbol, Vector{ExprVarLine}}}}}, name::Symbol)
    isempty(props) && return :()
    show_parts = ExprVarLine[]
    for (pname, _) in props
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

assemble_segments_type(layout::Layout, name::Symbol) =
    :($(GlobalRef(PackedParselets, :segments))(::Type{$(esc(name))}) = $layout)

assemble_segments_value(nsegs::Int, state::ParserState, name::Symbol) =
    :($(GlobalRef(PackedParselets, :segments))(val::$(esc(name))) =
          $(GlobalRef(PackedParselets, :printsegments))(val, Val($nsegs), $(state.branches[1].print_max)))

## Property-segment resolution

# Map properties to `(name, segment_indices)` pairs, by their first value: a segment's
# label, or for choice-guarded or multi-segment ones, the segments taking their name
function resolve_property_segments(props, segs::Vector{ValueSegment})
    result = Pair{Symbol, Vector{Int}}[]
    for (pname, vals) in props
        val = first(vals)
        if val isa Symbol
            idx = findfirst(s -> s.label == val, segs)
            isnothing(idx) && continue
            push!(result, pname => [idx])
        else
            idxs = Int[]
            for (i, s) in enumerate(segs)
                !isnothing(s.argtype) && s.label == pname && push!(idxs, i)
            end
            isempty(idxs) || push!(result, pname => idxs)
        end
    end
    result
end

## Compat

# Before Julia 1.12, `@inbounds`'s hygienic `local val` clashes with parameters named `val`
function expand_macrocall_inbounds!(ex)
    ex isa Expr || return ex
    for (i, a) in enumerate(ex.args)
        if Meta.isexpr(a, :macrocall) && !isempty(a.args) &&
                a.args[1] === Symbol("@inbounds")
            inner = a.args[end]
            expand_macrocall_inbounds!(inner)
            v = gensym("inbounds")
            ex.args[i] = Expr(:block,
                              Expr(:inbounds, true),
                              Expr(:local, :($v = $inner)),
                              Expr(:inbounds, :pop),
                              v)
        else
            expand_macrocall_inbounds!(a)
        end
    end
    ex
end

## Global inlining

# Syntax whose symbols aren't references to globals
const INERT_HEADS = (:escape, :quote, :inert, :meta, :inbounds, :loopinfo,
                     :symboliclabel, :symbolicgoto, :line, :primitive, :struct, :abstract)

"""
    inline_globals!(expr, mod::Module) -> expr

Replace references to constant globals of `mod` (bare symbols and `GlobalRef`s) in the
bodies of the functions `expr` defines by their values, so loading the generated
methods needn't rescan them for binding invalidation (Julia 1.12+). Names `expr` binds,
escaped (user) expressions and signatures are left alone.
"""
function inline_globals!(expr::Expr, mod::Module)
    bound = Set{Symbol}()
    collect_bound!(bound, expr)
    inline_globals!(expr, mod, bound)
end

function inline_globals!(expr::Expr, mod::Module, bound::Set{Symbol})
    head, args = expr.head, expr.args
    head in INERT_HEADS && return expr
    head === :macrocall && args[1] in (Symbol("@label"), Symbol("@goto")) && return expr
    # Past a macro's name and line, or a method's signature
    from = if head === :macrocall 3
    elseif head === :function || (head === :(=) && is_signature(args[1])) 2
    else 1 end
    for i in from:length(args)
        args[i] = inline_global(args[i], mod, bound)
    end
    expr
end

function inline_global(@nospecialize(x), mod::Module, bound::Set{Symbol})
    if x isa Expr
        ref = module_path_ref(x)
        if isnothing(ref) inline_globals!(x, mod, bound) else inline_global(ref, mod, bound) end
    elseif x isa GlobalRef
        if isconst(x.mod, x.name) getglobal(x.mod, x.name) else x end
    elseif x isa Symbol && x ∉ bound && !startswith(String(x), '#') &&
            isdefined(mod, x) && isconst(mod, x)
        getglobal(mod, x)
    else
        x
    end
end

is_assignment(head::Symbol) = endswith(String(head), '=')

is_signature(@nospecialize(x)) = Meta.isexpr(x, :call) ||
    (Meta.isexpr(x, (:where, :(::))) && is_signature(x.args[1]))

# Every name `expr` binds: assignment targets, `local`s, and function arguments
function collect_bound!(bound::Set{Symbol}, @nospecialize(x))
    (x isa Expr && x.head !== :escape) || return bound
    if x.head === :local
        collect_names!(bound, x)
    elseif x.head in (:kw, :function, :->) || is_assignment(x.head)
        collect_names!(bound, x.args[1])
    end
    for a in x.args
        collect_bound!(bound, a)
    end
    bound
end

# Names a binding position introduces, from `a`, `a::T`, `(a, b)`, `f(a, b; c=1) where T`
function collect_names!(bound::Set{Symbol}, @nospecialize(x))
    if x isa Symbol
        push!(bound, x)
    elseif Meta.isexpr(x, (:(::), :kw, :(=)))
        collect_names!(bound, x.args[1])
    elseif Meta.isexpr(x, (:tuple, :call, :parameters, :where, :local))
        for a in @view x.args[1 + (x.head === :call):end]
            collect_names!(bound, a)
        end
    end
    bound
end

## Runtime reference qualification

# The `GlobalRef` a dotted path rooted at `Base` or `Core` names, if it resolves.
function module_path_ref(ex::Expr)
    Meta.isexpr(ex, :., 2) && ex.args[2] isa QuoteNode || return nothing
    root = ex.args[1]
    parent = if root === :Base
        Base
    elseif root === :Core
        Core
    elseif root isa Expr
        ref = module_path_ref(root)
        if !isnothing(ref) && isconst(ref.mod, ref.name) getglobal(ref.mod, ref.name) end
    end
    name = ex.args[2].value
    parent isa Module && name isa Symbol && isdefined(parent, name) || return nothing
    GlobalRef(parent, name)
end
