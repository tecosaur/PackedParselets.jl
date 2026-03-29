# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# String-oriented pattern handlers and their codegen helpers.
#
# Compile handlers: compile_literal (required literal), compile_skip (prefix stripping)
# Codegen helpers: gen_literal_mismatch, gen_static_lchop, gen_string_match

## SegmentOutput-returning handlers

function compile_literal(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    length(args) == 1 || throw(ArgumentError("Expected exactly one argument for literal, got $(length(args))"))
    lit = args[1]
    lit isa String || throw(ArgumentError("Expected a string literal for literal, got $lit"))
    notfound = build_fail_expr!(state, nctx, "Expected literal '$(lit)'")
    casefold = get(nctx, :casefold, false) === true
    casefold && !all(isascii, lit) &&
        throw(ArgumentError("Expected ASCII string for literal with casefolding"))
    litref = if casefold; lowercase(lit) else lit end
    litlen = ncodeunits(litref)
    mismatch = gen_literal_mismatch(state, nctx, litref, casefold)
    lencheck = emit_lengthcheck(state, nctx, litlen)
    parse = ExprVarLine[
        :(if !$lencheck
              $notfound
          elseif $mismatch
              $notfound
          end),
        :(pos += $litlen)]
    spans = [[byte_set(codeunit(lit, i), casefold) for i in 1:litlen]]
    SegmentOutput(
        SegmentBounds(litlen:litlen, litlen:litlen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[], ExprVarLine[], Expr[], ExprVarLine[:(print(io, $lit))]),
        SegmentMeta(:literal, sprint(show, lit), lit, nothing, nothing),
        spans)
end

function skip_step_strings(arg)
    arg isa String && return String[arg]
    if Meta.isexpr(arg, :call) && !isempty(arg.args) && first(arg.args) === :choice
        alts = arg.args[2:end]
        all(a -> a isa String, alts) ||
            throw(ArgumentError("choice() inside skip must contain only strings"))
        return Vector{String}(alts)
    end
    throw(ArgumentError(
        "skip arguments must be strings or choice(strings...), got $(repr(arg))"))
end

function gen_skip_step(state::ParserState, nctx::NodeCtx,
                      alts::Vector{String}, casefold::Bool)
    refs = if casefold map(lowercase, alts) else alts end
    if length(refs) == 1
        return gen_static_lchop(refs, casefold=casefold)
    end
    # Multiple alternatives: use the choice matcher for optimal dispatch
    fieldvar = gensym("skip_match")
    cint = cardtype(cardbits(length(refs) + 1))
    cctx = (; mopts=refs, sopts=alts, casefold, fieldvar,
              onmatch = _ -> :(), cint)
    matcher, _, _ = build_choice_matcher(state, nctx, cctx)
    lencheck = emit_lengthcheck(state, nctx, minimum(ncodeunits, refs))
    :(if $lencheck; $fieldvar = zero($cint); $(matcher...) end)
end

function compile_skip(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    pval = get(nctx, :print, nothing)
    casefold = get(nctx, :casefold, false) === true
    steps = [skip_step_strings(a) for a in args]
    !isnothing(pval) && !any(s -> pval ∈ s, steps) && push!(steps, String[pval])
    all_strings = reduce(vcat, steps)
    casefold && !all(isascii, all_strings) &&
        throw(ArgumentError("Expected all skip strings to be ASCII with casefolding"))
    parse = ExprVarLine[]
    for alts in steps
        push!(parse, gen_skip_step(state, nctx, alts, casefold))
    end
    parsed_max = sum(maximum(ncodeunits, step) for step in steps)
    # Cartesian product of per-step alternatives (+ empty for each step)
    arrangements = Vector{ByteSet}[]
    for alts in steps
        step_spans = [[byte_set(codeunit(s, i), casefold) for i in 1:ncodeunits(s)]
                       for s in alts]
        push!(step_spans, ByteSet[])
        extend_bytespans!(arrangements, step_spans)
    end
    plen = if isnothing(pval) 0 else ncodeunits(pval) end
    pexprs = if isnothing(pval) ExprVarLine[] else ExprVarLine[:(print(io, $pval))] end
    desc = if isnothing(pval) "" else string("Skipped literal string \"", join(all_strings, ", "), '"') end
    shortform = something(pval, "")
    SegmentOutput(
        SegmentBounds(0:parsed_max, plen:plen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[], ExprVarLine[], Expr[], pexprs),
        SegmentMeta(:skip, desc, shortform, nothing, nothing),
        arrangements)
end

## Codegen: literal mismatch

"""
    gen_literal_mismatch(state, nctx, str, casefold) -> Expr

Emit an expression that is `true` when `idbytes` at `pos` does not match `str`.

When widening to a single register load reduces the chunk count, emits both
wide and narrow paths gated by `emit_static_lengthcheck`, so that
`fold_static_branches!` can pick the winner.
"""
function gen_literal_mismatch(state::ParserState, nctx::NodeCtx,
                              str::String, casefold::Bool)
    litlen = ncodeunits(str)
    wide_n = min(nextpow(2, litlen), sizeof(UInt) * cld(litlen, sizeof(UInt)))
    use_wide = wide_n > litlen && length(register_chunks(wide_n)) < length(register_chunks(litlen))
    if use_wide
        wide_mm = negate_match(gen_string_match(str, casefold, wide_n))
        narrow_mm = negate_match(gen_string_match(str, casefold))
        Expr(:if, emit_static_lengthcheck(state, nctx, wide_n), wide_mm, narrow_mm)
    else
        negate_match(gen_string_match(str, casefold))
    end
end

## Prefix stripping

"""
    gen_static_lchop(prefixes; casefold) -> Expr

Generate an if/elseif chain that strips the first matching prefix by advancing
`pos`. Prefixes are grouped by length (longest first), with same-length
alternatives as nested if/elseif.

Assumes casefolded prefixes are already lowercased.
Expects `idbytes`, `pos`, `nbytes` in scope.
"""
function gen_static_lchop(prefixes::Vector{String}; casefold::Bool)
    groups = Dict{Int, Vector{String}}()
    for p in prefixes
        push!(get!(Vector{String}, groups, ncodeunits(p)), p)
    end
    lengths = sort!(collect(keys(groups)), rev=true)
    branches = map(lengths) do nb
        grp = groups[nb]
        lencheck = :(nbytes - pos + 1 >= $nb)
        if length(grp) == 1
            :(if $lencheck && $(conjoin_match(only(grp), casefold)); pos += $nb end)
        else
            inner = :(if $(conjoin_match(last(grp), casefold)); pos += $nb end)
            for i in length(grp)-1:-1:1
                inner = Expr(:elseif, conjoin_match(grp[i], casefold), :(pos += $nb), inner)
            end
            :(if $lencheck; $inner end)
        end
    end
    result = branches[end]
    for i in length(branches)-1:-1:1
        br = branches[i]
        result = Expr(:if, br.args[1], br.args[2], result)
    end
    result
end

## String matching primitives

"""
    gen_string_match(str, casefold[, nbytes]) -> Vector{Expr}

Emit register-sized match checks for `str` against `idbytes` at `pos`.
Each returned expression evaluates to `true` when its chunk matches.

When `nbytes > ncodeunits(str)`, chunks are widened and overflow bytes
are masked to `0x00`, enabling fewer loads when subsequent pattern nodes
guarantee the extra bytes are readable.
"""
function gen_string_match(str::String, casefold::Bool, nbytes::Int = ncodeunits(str))
    strlen = ncodeunits(str)
    map(register_chunks(nbytes)) do chunk
        valid = min(chunk.width, strlen - chunk.offset)
        (; value, mask) = pack_chunk(str, chunk; casefold, valid)
        posexpr = if iszero(chunk.offset)
            :pos
        else
            :(pos + $(chunk.offset))
        end
        gen_masked_compare(chunk.iT, posexpr, value, mask)
    end
end

negate_match(checks::Vector{Expr}) =
    :(!($(foldl((a, b) -> :($a && $b), checks))))
conjoin_match(str::String, casefold::Bool) =
    foldl((a, b) -> :($a && $b), gen_string_match(str, casefold))
