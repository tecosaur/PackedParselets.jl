# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# String-oriented pattern handlers and their codegen helpers.

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
    match = gen_literal_match(state, nctx, litref, casefold)
    lencheck = emit_lengthcheck(state, nctx, litlen)
    parse = ExprVarLine[
        :(if !$lencheck
              $notfound
          elseif !$match
              $notfound
          end),
        :(pos += $litlen)]
    SegmentOutput(
        SegmentBounds(litlen:litlen, litlen:litlen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[], bufprint_static(lit), Expr[]),
        SegmentMeta(:literal, sprint(show, lit), lit, nothing, nothing),
        string_bytespans([lit], casefold))
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
    refs = unique(if casefold map(lowercase, alts) else alts end)
    if length(refs) <= 1
        return gen_static_lchop(refs, casefold, peek)
    end
    minlen = minimum(ncodeunits, refs)
    lencheck = emit_lengthcheck(state, nctx, minlen)
    # Inputs rarely start like an alternative: test how they start before matching
    guard = gen_peek(refs, casefold)
    cond = if peek && peeks(minlen); :($guard && $lencheck) else :($lencheck && $guard) end
    factored = gen_factored_lchop(refs, casefold)
    isnothing(factored) || return :(if $cond; $factored end)
    # Otherwise the choice matcher's hash dispatch narrows the candidates to verify,
    # rather than trying each in turn
    cint = cardtype(cardbits(length(refs) + 1))
    cmatch = ChoiceMatch(refs, alts, casefold, gensym("skip_match"), cint, :none)
    matcher, _, _ = build_choice_matcher(state, nctx, cmatch)
    :(if $cond; $(matcher...) end)
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
    function flush!(next, runstart)
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
        absent || flush!(firsts, runstart)
        isnothing(step) || push!(if absent run else parse end, step)
        absent && append!(runalts, map(lowercase, filter(!isempty, alts)))
        parsed_max += maximum(ncodeunits, alts)
        extend_bytespans!(arrangements, push!(string_bytespans(alts, casefold), ByteSet[]))
    end
    flush!(UInt8[], runstart)
    printed = something(pval, "")
    plen = ncodeunits(printed)
    desc = if isnothing(pval) "" else string("Skipped literal string \"", join(all_strings, ", "), '"') end
    SegmentOutput(
        SegmentBounds(0:parsed_max, plen:plen, 0, nothing),
        SegmentCodegen(parse, ExprVarLine[], bufprint_static(printed), Expr[]),
        SegmentMeta(:skip, desc, printed, nothing, nothing),
        arrangements)
end

## Codegen: literal match

# Where a wider load needs fewer chunks, both widths are emitted under a static
# length check for `fold_branches!` to choose between
function gen_literal_match(state::ParserState, nctx::NodeCtx,
                           str::String, casefold::Bool)
    wide_n = widened(ncodeunits(str))
    narrow = conjoin(gen_string_match(str, casefold))
    isnothing(wide_n) && return narrow
    Expr(:if, emit_static_lengthcheck(state, nctx, wide_n), conjoin(gen_string_match(str, casefold, wide_n)), narrow)
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
    arms = Tuple{Any, Any}[]
    for p in prefixes[sortperm_by(ncodeunits, prefixes, true)]
        nb = ncodeunits(p)
        cond = :(nbytes - pos + 1 >= $nb && $(conjoin(gen_string_match(p, casefold))))
        peek && peeks(nb) && (cond = :($(gen_peek([p], casefold)) && $cond))
        push!(arms, (cond, :(pos += $nb; keepbranch())))
    end
    ifchain(arms)
end

# `gen_static_lchop`, but matching the head and tail all prefixes share once, around the
# middles that differ: "https://" and "http://" as "http", an optional "s", then "://".
# The longest middle is then the longest prefix, unless a middle may begin where another
# and the tail do, which a maximal head rules out for two prefixes.
function gen_factored_lchop(prefixes::Vector{String}, casefold::Bool)
    shortest = minimum(ncodeunits, prefixes)
    shared(byteof) = allequal(byteof(p) for p in prefixes)
    sharedrun(byteat, n) = something(findfirst(i -> !shared(p -> byteat(p, i)), 1:n), n + 1) - 1
    nhead = sharedrun(codeunit, shortest)
    ntail = sharedrun((p, i) -> codeunit(p, ncodeunits(p) + 1 - i), shortest - nhead)
    nhead + ntail > 0 && (iszero(ntail) || length(prefixes) == 2) || return nothing
    trimmed(p, nfirst, nlast) = String(codeunits(p)[nfirst+1:end-nlast])
    middles = map(p -> trimmed(p, nhead, ntail), prefixes[sortperm_by(ncodeunits, prefixes, true)])
    matches(str, offset) = conjoin(gen_string_match(str, casefold, ncodeunits(str), offset))
    fits(n) = :(nbytes - pos + 1 >= $n)
    skiplen = gensym("skiplen")
    middle = ifchain(Tuple{Any, Any}[
        (:($(fits(nhead + ncodeunits(m))) && $(matches(m, nhead))), :($skiplen += $(ncodeunits(m))))
        for m in middles if !isempty(m)])
    tail = trimmed(first(prefixes), ncodeunits(first(prefixes)) - ntail, 0)
    taken = if iszero(ntail) true else :($(fits(:($skiplen + $ntail))) && $(matches(tail, skiplen))) end
    any(isempty, middles) || (taken = :($skiplen > $nhead && $taken))
    :(if $(matches(trimmed(first(prefixes), 0, ncodeunits(first(prefixes)) - nhead), 0))
          $skiplen = $nhead
          $middle
          if $taken; pos += $skiplen + $ntail; keepbranch() end
      end)
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
    gen_string_match(str, casefold[, nbytes, offset]) -> Vector{Expr}

Emit one check per register-sized chunk of `str` against `data` at `pos + offset`.

With `nbytes > ncodeunits(str)`, chunks widen with the overflow bytes masked
to `0x00`: only valid when those extra bytes are known to be readable.
"""
function gen_string_match(str::String, casefold::Bool, nbytes::Int = ncodeunits(str),
                          offset::Union{Int, Symbol} = 0)
    strlen = ncodeunits(str)
    base = if offset === 0; :pos else :(pos + $offset) end
    checks = Expr[]
    for chunk in register_chunks(nbytes)
        valid = min(chunk.width, strlen - chunk.offset)
        (; value, mask) = pack_chunk(str, chunk, casefold, valid)
        posexpr = if iszero(chunk.offset) base else :($base + $(chunk.offset)) end
        push!(checks, gen_masked_compare(chunk.iT, posexpr, value, mask))
    end
    checks
end

# `if c₁; b₁ elseif c₂; b₂ … end` from `(cond, body)` arms
function ifchain(arms::Vector{Tuple{Any, Any}})
    chain = nothing
    for (cond, body) in Iterators.reverse(arms)
        chain = Expr(:elseif, cond, body, (if isnothing(chain); () else (chain,) end)...)
    end
    isnothing(chain) || (chain.head = :if)
    chain
end

function conjoin(checks::Vector{Expr})
    joint = true
    for check in checks
        joint = if joint === true check else :($joint && $check) end
    end
    joint
end
