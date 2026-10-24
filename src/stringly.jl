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
    spans = string_bytespans([lit], casefold)
    printout = ExprVarLine[:(print(io, $lit))]
    SegmentOutput(
        SegmentBounds(litlen:litlen, litlen:litlen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[],
            PrintExprs(direct=printout, putval=copy(printout),
                       getlen=ExprVarLine[:(pos += $litlen)]),
            Expr[]),
        SegmentMeta(:literal, sprint(show, lit), lit, nothing, nothing),
        spans)
end

function skip_step_strings(@nospecialize(arg))
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
                      alts::Vector{String}, casefold::Bool, peek::Bool)
    # "" matches zero bytes, which a skip's no-match fall-through already covers.
    alts = filter(!isempty, alts)
    refs = if casefold map(lowercase, alts) else alts end
    if length(refs) <= 1
        return gen_static_lchop(refs, casefold, peek)
    end
    # Multiple alternatives: the choice matcher's hash dispatch narrows the
    # candidates to verify, rather than trying each in turn.
    fieldvar = gensym("skip_match")
    cint = cardtype(cardbits(length(refs) + 1))
    cmatch = ChoiceMatch(refs, alts, casefold, fieldvar, cint, :none)
    matcher, _, _ = build_choice_matcher(state, nctx, cmatch)
    lencheck = emit_lengthcheck(state, nctx, minimum(ncodeunits, refs))
    # Inputs rarely start like an alternative: test how they start before hashing
    guard = gen_peek(refs, casefold)
    cond = if peek && peeks(minimum(ncodeunits, refs)); :($guard && $lencheck) else :($lencheck && $guard) end
    :(if $cond; $fieldvar = zero($cint); $(matcher...) end)
end

function compile_skip(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    pval = get(nctx, :print, nothing)
    casefold = get(nctx, :casefold, false) === true
    steps = Vector{String}[skip_step_strings(a) for a in args]
    !isnothing(pval) && !any(s -> pval ∈ s, steps) && push!(steps, String[pval])
    all_strings = reduce(vcat, steps)
    casefold && !all(isascii, all_strings) &&
        throw(ArgumentError("Expected all skip strings to be ASCII with casefolding"))
    parse, parsed_max = ExprVarLine[], 0
    arrangements = Vector{ByteSet}[]  # Cartesian product of per-step alternatives (+ empty)
    # The printed prefix is usually present, the others absent: a run of those shares one
    # test of how they start, unless the printed one after shares a first byte so it'd pass
    run, runalts, runstart = ExprVarLine[], String[], 0
    function flush!(next)
        if length(run) > 1 && isdisjoint(UInt8[codeunit(a, 1) | 0x20 for a in runalts], next)
            fits = emit_static_lengthcheck(state, nctx, runstart + 4)
            push!(parse, Expr(:if, gen_peek(runalts, casefold, fits), Expr(:block, run...)))
        else
            append!(parse, run)
        end
        empty!(run); empty!(runalts)
    end
    for alts in steps
        absent = pval ∉ alts
        absent && isempty(run) && (runstart = parsed_max)
        step = gen_skip_step(state, nctx, alts, casefold, absent)
        firsts = UInt8[codeunit(a, 1) | 0x20 for a in filter(!isempty, alts)]
        absent || flush!(firsts)
        isnothing(step) || push!(if absent run else parse end, step)
        absent && append!(runalts, map(lowercase, filter(!isempty, alts)))
        parsed_max += maximum(ncodeunits, alts)
        extend_bytespans!(arrangements, push!(string_bytespans(alts, casefold), ByteSet[]))
    end
    flush!(UInt8[])
    plen = if isnothing(pval) 0 else ncodeunits(pval) end
    pexprs = if isnothing(pval) ExprVarLine[] else ExprVarLine[:(print(io, $pval))] end
    desc = if isnothing(pval) "" else string("Skipped literal string \"", join(all_strings, ", "), '"') end
    shortform = something(pval, "")
    lenexprs = if iszero(plen) ExprVarLine[] else ExprVarLine[:(pos += $plen)] end
    SegmentOutput(
        SegmentBounds(0:parsed_max, plen:plen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[],
            PrintExprs(direct=pexprs, putval=copy(pexprs), getlen=lenexprs),
            Expr[]),
        SegmentMeta(:skip, desc, shortform, nothing, nothing),
        arrangements)
end

## Codegen: literal mismatch

"""
    gen_literal_mismatch(state, nctx, str, casefold) -> Expr

Emit an expression that is `true` when `data` at `pos` does not match `str`.

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
    gen_static_lchop(prefixes, casefold, peek) -> Expr

Generate an if/elseif chain that strips the first matching prefix by advancing
`pos`. Prefixes are tried longest-first, so a failed match falls through to a
shorter prefix even when one prefix is a prefix of another (e.g. "CL:" / "CL").
With `peek`, for prefixes usually absent, short ones test their first byte before their
length, which varies unpredictably near a short prefix's.

Assumes prefixes are non-empty, and casefolded prefixes already lowercased.
Expects `data`, `pos`, `nbytes` in scope.
"""
function gen_static_lchop(prefixes::Vector{String}, casefold::Bool, peek::Bool)
    ordered = prefixes[sortperm_by(ncodeunits, prefixes, true)]
    # Built from the shortest (innermost) out
    chain = nothing
    for p in Iterators.reverse(ordered)
        nb = ncodeunits(p)
        cond = :(nbytes - pos + 1 >= $nb && $(conjoin(gen_string_match(p, casefold))))
        peek && peeks(nb) && (cond = :($(gen_peek([p], casefold)) && $cond))
        chain = if isnothing(chain) Expr(:if, cond, :(pos += $nb))
        else Expr(:elseif, cond, :(pos += $nb), chain) end
    end
    chain
end

## String matching primitives

# A lone byte keeps its length test first, so its guarded load keeps it a branch
peeks(nbytes::Int) = 1 < nbytes <= sizeof(UInt)
# Whether the input starts like any of `alts`: by their first byte, or the first four of long
# ones, which "https" and "hsa0" don't share, at once where four bytes `fits`, else after the
# first byte, sparing inputs whose length varies about it
function gen_peek(alts::Vector{String}, casefold::Bool, fits = false)
    test = nothing
    for prefix in unique(String[if ncodeunits(a) > 4 a[1:4] else a[1:1] end for a in alts])
        c = pack_chunk(prefix, RegisterChunk((0, 1, UInt8)), casefold, 1)
        first, match = :(peekbyte(data, pos) & $(c.mask) == $(c.value)), conjoin(gen_string_match(prefix, casefold))
        peek = if ncodeunits(prefix) == 1; first else Expr(:if, fits, match, :($first && nbytes - pos + 1 >= 4 && $match)) end
        test = if isnothing(test) peek else :($test || $peek) end
    end
    test
end

"""
    gen_string_match(str, casefold[, nbytes]) -> Vector{Expr}

Emit register-sized match checks for `str` against `data` at `pos`.
Each returned expression evaluates to `true` when its chunk matches.

When `nbytes > ncodeunits(str)`, chunks are widened and overflow bytes
are masked to `0x00`, enabling fewer loads when subsequent pattern nodes
guarantee the extra bytes are readable.
"""
function gen_string_match(str::String, casefold::Bool, nbytes::Int = ncodeunits(str))
    strlen = ncodeunits(str)
    checks = Expr[]
    for chunk in register_chunks(nbytes)
        valid = min(chunk.width, strlen - chunk.offset)
        (; value, mask) = pack_chunk(str, chunk, casefold, valid)
        posexpr = if iszero(chunk.offset)
            :pos
        else
            :(pos + $(chunk.offset))
        end
        push!(checks, gen_masked_compare(chunk.iT, posexpr, value, mask))
    end
    checks
end

function conjoin(checks::Vector{Expr})
    joint = true
    for check in checks
        joint = if joint === true check else :($joint && $check) end
    end
    joint
end
negate_match(checks::Vector{Expr}) = :(!($(conjoin(checks))))
