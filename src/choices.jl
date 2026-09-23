# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Choice pattern handler and its codegen: perfect hashing, matcher assembly,
# and register-sized verification.

# Below these option counts the unrolled linear matcher, which LLVM often turns into
# a switch, measured as fast or faster than a bucketed hash on varied input. Mixed
# lengths cost the hash path a length lookup and a bytewise tail check.
const BUCKETED_MIN_FIXED_OPTIONS = 8
const BUCKETED_MIN_VARIABLE_OPTIONS = 16

## Choice pattern handler

"""
    compile_choice(state, nctx, def, options) -> SegmentOutput

Handle a `choice(...)` pattern node.

Validates options, builds a matcher (via perfect hashing or linear scan),
then delegates to `compile_choice_value` or `compile_choice_fixed`.
"""
function compile_choice(state::ParserState, nctx::NodeCtx, ::PatternExprs,
                        ::SegmentDef, options::Vector{Any})
    all(o -> o isa String, options) || throw(ArgumentError("Expected all options to be strings for choice"))
    ctx = choice_setup(state, nctx, options)
    if isnothing(ctx.target)
        compile_choice_value(state, nctx, ctx)
    else
        compile_choice_fixed(state, nctx, ctx)
    end
end

function choice_setup(state::ParserState, nctx::NodeCtx, options::Vector{Any})
    sopts = Vector{String}(options)
    allowempty = any(isempty, sopts)
    allowempty && filter!(!isempty, sopts)
    casefold = get(nctx, :casefold, false)
    target = get(nctx, :is, nothing)::Union{Nothing, String}
    fieldvar = get(nctx, :fieldvar, gensym("prefix"))
    option = get(nctx, :optional, nothing)
    claims = is_sentinel_unclaimed(nctx)
    cbits = cardbits(length(sopts) + 1)
    cint = if isnothing(target)
        cardtype(cbits)
    else
        Bool
    end
    !isnothing(target) && push!(sopts, target)
    if casefold
        all(isascii, sopts) || throw(ArgumentError("Expected all options to be ASCII strings for casefolding"))
    end
    mopts = if casefold; map(lowercase, sopts) else sopts end
    onmatch = if isnothing(target)
        valexpr -> :($fieldvar = $valexpr)
    else
        _ -> :($fieldvar = one($fieldvar))
    end
    cctx = (; mopts, sopts, casefold, fieldvar, onmatch, cint)
    matcher, mopts, sopts = build_choice_matcher(state, nctx, cctx)
    # Length-guarded match wrapper
    notfound = build_fail_expr!(state, nctx, "Expected one of $(join(sopts, ", "))")
    lencheck = emit_lengthcheck(state, nctx, minimum(ncodeunits, sopts))
    guarded = if allowempty
        :(if $lencheck
              $(matcher...)
          end)
    else
        :(if !$lencheck
              $notfound
          else
              $(matcher...)
              if $fieldvar == zero($cint)
                  $notfound
              end
          end)
    end
    valtype = get(nctx, :type, :Symbol)
    valtype in (:Symbol, :String) ||
        throw(ArgumentError("choice type must be Symbol or String, got $valtype"))
    (; sopts, fieldvar, option, allowempty, cbits, cint,
       guarded, matcher, target, claims, valtype)
end

"""
    compile_choice_value(state, nctx, ctx) -> SegmentOutput

Produce a `SegmentOutput` for a value-storing choice: the selected index is
packed into the bit stream and extracted as a `Symbol` or `String` property.
Handles the `allowempty` case by guarding print and extract expressions on
a presence check, and claims a zero-encoding sentinel when available.
"""
function compile_choice_value(state::ParserState, nctx::NodeCtx, @nospecialize(ctx))
    (; sopts, fieldvar, option, allowempty, cbits, cint, guarded, claims, valtype) = ctx
    bitpos = state.bits + cbits
    pmin = if allowempty 0 else minimum(ncodeunits, sopts) end
    pexprs = ExprVarLine[
          :($fieldvar = zero($cint)),
          guarded,
          emit_pack(state, cint, fieldvar, bitpos)]
    fextract = :($fieldvar = $(emit_extract(state, bitpos, cbits)))
    present = :(!iszero($fieldvar))
    opttuple = Tuple(sopts)
    printexpr = :(print(io, @inbounds $opttuple[$fieldvar]))
    optlens = ncodeunits.(sopts)
    lenexpr = if allequal(optlens)
        :(pos += $(first(optlens)))
    else
        :(pos += $(GlobalRef(Base, :ncodeunits))(@inbounds $opttuple[$fieldvar]))
    end
    # When allowempty without an enclosing optional, guard on presence
    emptyguard = allowempty && isnothing(option)
    guard(ex) = if emptyguard; :(if $present; $ex end) else ex end
    vars = Pair{Symbol,Any}[fieldvar => :(zero($cint))]
    argvar = gensym("arg_choice")
    extract_value, impart_core, argtype = choice_value_codegen(
        state, valtype, sopts, fieldvar, argvar, cint, bitpos)
    emptyguard && (extract_value = guard(extract_value))
    eopt = if emptyguard gensym("emptyopt") else option end
    sentinel = if claims SentinelSpec((0, cbits)) end
    pmax = maximum(ncodeunits, sopts)
    casefold = get(nctx, :casefold, false) === true
    arrangements = [[byte_set(codeunit(o, i), casefold) for i in 1:ncodeunits(o)]
                     for o in sopts]
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    extract_setup = ExprVarLine[fextract]
    desc = join(sopts, " | ")
    seg_extract, seg_impart = optional_wrap(eopt, argvar, extract_setup, extract_value, impart_core)
    SegmentOutput(
        SegmentBounds(pmin:pmax, pmin:pmax, cbits, sentinel),
        SegmentCodegen(pexprs, seg_extract,
            PrintExprs(direct = ExprVarLine[fextract, guard(copy(printexpr))],
                       vars = vars,
                       getval = ExprVarLine[fextract],
                       getlen = ExprVarLine[guard(lenexpr)],
                       putval = ExprVarLine[guard(copy(printexpr))]),
            seg_impart),
        SegmentMeta(label, desc, desc, argtype, argvar),
        arrangements)
end

function choice_value_codegen(state::ParserState, valtype::Symbol, sopts,
                               fieldvar, argvar, cint, bitpos)
    vals, conv, argtype = if valtype === :Symbol
        Tuple(Symbol.(sopts)), :Symbol, :Symbol
    else
        Tuple(sopts), :String, :AbstractString
    end
    extract_value = :(@inbounds $(vals)[$fieldvar])
    impart_core = Expr[
        :($fieldvar = let idx = findfirst(==($conv($argvar)), $vals)
              isnothing(idx) && throw(ArgumentError(
                  string("Invalid option ", repr($conv($argvar)), "; expected one of: ", $(join(sopts, ", ")))))
              idx % $cint
          end),
        emit_pack(state, cint, fieldvar, bitpos)]
    (extract_value, impart_core, argtype)
end

"""
    compile_choice_fixed(state, nctx, ctx) -> SegmentOutput

Produce a `SegmentOutput` for a fixed-output choice: the parsed option is not
stored; the segment always prints the single `target` string. Allocates no
bits and emits zero-width print/extract codegen.
"""
function compile_choice_fixed(::ParserState, nctx::NodeCtx, @nospecialize(ctx))
    (; sopts, fieldvar, allowempty, cint, guarded, matcher, target) = ctx
    pexprs = if any(isempty, sopts)
        ExprVarLine[matcher]
    else
        ExprVarLine[:($fieldvar = zero($cint)), guarded]
    end
    pmin = if allowempty 0 else minimum(ncodeunits, sopts) end
    tlen = ncodeunits(target)
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    casefold = get(nctx, :casefold, false) === true
    arrangements = [[byte_set(codeunit(o, i), casefold) for i in 1:ncodeunits(o)]
                     for o in sopts]
    printout = ExprVarLine[:(print(io, $target))]
    SegmentOutput(
        SegmentBounds(pmin:maximum(ncodeunits, sopts), tlen:tlen, 0, nothing),
        SegmentCodegen(pexprs, ExprVarLine[],
            PrintExprs(direct=printout, putval=copy(printout),
                       getlen=ExprVarLine[:(pos += $tlen)]),
            Expr[]),
        SegmentMeta(label,
                    string("Choice of literal string \"", target, "\" vs ", join(sopts, ", ")),
                    join(sopts, " | "), nothing, nothing),
        arrangements)
end

## Matcher assembly

"""
    build_choice_matcher(mopts, sopts, casefold, fieldvar, onmatch,
                         cint, state, nctx)
        -> (matcher, mopts, sopts)

Build parse-time matcher expressions for a choice node.

Uses perfect hashing when available (with optional hash-skip optimisation
for injective hashes and widened verify tables when they reduce chunk count),
then a bucketed hash for larger option sets, and falls back to linear scan.
May reorder options to match hash output order.
"""
function build_choice_matcher(state::ParserState, nctx::NodeCtx, @nospecialize(cctx))
    (; mopts, casefold) = cctx
    ph = find_window_hash(classify_hash, mopts, casefold)
    minbucketed = if allequal(map(ncodeunits, mopts))
        BUCKETED_MIN_FIXED_OPTIONS
    else
        BUCKETED_MIN_VARIABLE_OPTIONS
    end
    if isnothing(ph) && length(mopts) >= minbucketed
        ph = find_window_hash(classify_bucketed, mopts, casefold)
    end
    if !isnothing(ph)
        build_hash_matcher(state, nctx, ph, cctx)
    else
        build_linear_matcher(state, nctx, cctx)
    end
end

function build_hash_matcher(state::ParserState, nctx::NodeCtx, ph::HashPlan, @nospecialize(cctx))
    (; casefold, fieldvar, onmatch, cint) = cctx
    # Reorder options to match hash output order
    mopts = cctx.mopts[ph.perm]
    sopts = cctx.sopts[ph.perm]
    optlens = Tuple(ncodeunits.(mopts))
    phoff = ph.pos - 1
    phposexpr = if iszero(phoff); :pos else :(pos + $phoff) end
    load = gen_load(ph.iT, phposexpr)
    foldedload = if iszero(ph.foldmask) load else :($load | $(ph.foldmask % ph.iT)) end
    hashval = hashexpr(ph, foldedload)
    minoptlen = minimum(ncodeunits, mopts)
    maxoptlen = maximum(ncodeunits, mopts)
    variable_len = minoptlen != maxoptlen
    # Common suffix: when variable-length options share trailing bytes (aligned
    # from the end), those bytes can be checked as a constant using pos+optlen
    # addressing. When the suffix covers the entire length difference, no
    # per-option tail verification is needed.
    suffix_len = if variable_len
        min(common_suffix_length(mopts, casefold), maxoptlen - minoptlen)
    else
        0
    end
    suffix_check = if suffix_len > 0
        gen_suffix_check(mopts[1][end-suffix_len+1:end], casefold, suffix_len)
    else
        nothing
    end
    # For injective hashes, skip bytes already validated by the hash window
    hash_skip = if ph.injective
        find_best_hash_skip(minoptlen, phoff, sizeof(ph.iT))
    else
        nothing
    end
    vt = gen_verify_table(mopts, casefold; skip = hash_skip)
    # Try backward-aligned single-register verify when prior parsed content provides safety
    b = nctx[:current_branch]
    bvc = backward_verify_chunk(minoptlen)
    use_backward = !isnothing(bvc) && !variable_len && b.parsed_min >= bvc.padding
    bve = if use_backward
        gen_backward_verify(mopts, casefold, minoptlen, bvc, fieldvar, hash_skip)
    else
        nothing
    end
    # Try widening the verify table when it reduces chunk count (skipped when backward is available)
    wide_minlen = min(nextpow(2, minoptlen), sizeof(UInt) * cld(minoptlen, sizeof(UInt)))
    use_wide_vt = !use_backward && isnothing(hash_skip) && wide_minlen > minoptlen &&
        length(register_chunks(wide_minlen)) < length(vt.chunks)
    vt_wide = if use_wide_vt
        gen_verify_table(mopts, casefold; nbytes = wide_minlen)
    else
        nothing
    end
    # Tail verification: skip when common suffix covers the entire length difference
    tailcheck = if variable_len && suffix_len < maxoptlen - minoptlen
        gen_tail_verify(mopts, casefold, minoptlen, fieldvar)
    else
        nothing
    end
    # Index resolution depends on hash kind
    nopts = length(mopts)
    resolve_i = if ph.kind === :direct
        boundscheck = if nopts == 1
            :(i == 1)
        else
            :(1 <= i <= $nopts)
        end
        ExprVarLine[:(i = $hashval), :(found = $boundscheck)]
    else
        ExprVarLine[:(hi = $hashval),
                    :(i = if 1 <= hi <= $(length(ph.table))
                          $(Tuple(ph.table))[hi]
                      else
                          0
                      end),
                    :(found = !iszero(i))]
    end
    # Assemble the guarded block: resolve index, verify bytes, then act.
    # Each stage can set `found = false`; subsequent stages are guarded on it.
    # `guard_append!` nests new statements inside `if found` when prior
    # stages might have cleared the flag.
    parts = ExprVarLine[resolve_i...]
    body = ExprVarLine[]
    guard_append!(stmts) =
        if isempty(body) append!(body, stmts)
        else push!(body, :(if found; $(stmts...) end)) end
    # Stage 1: variable-length option → look up optlen, check available bytes
    if variable_len
        optlencheck = emit_lengthcheck(state, nctx, :optlen, minoptlen, maximum(ncodeunits, mopts))
        append!(body, ExprVarLine[:(optlen = $(optlens)[i]),
                                  :(found = $optlencheck)])
    end
    # Stage 2: byte verification (backward, widened, normal, or suffix-only)
    and_suffix(checks) = if isnothing(suffix_check) checks else :($checks && $suffix_check) end
    if use_backward
        guard_append!(ExprVarLine[bve.destructure..., :(found = $(and_suffix(bve.checks)))])
    elseif use_wide_vt
        ve = gen_verify_exprs(vt, fieldvar)
        ve_wide = gen_verify_exprs(vt_wide, fieldvar)
        wide_block = Expr(:block, ve_wide.destructure..., :(found = $(and_suffix(ve_wide.checks))))
        narrow_block = Expr(:block, ve.destructure..., :(found = $(and_suffix(ve.checks))))
        guard_append!(ExprVarLine[Expr(:if, emit_static_lengthcheck(state, nctx, wide_minlen),
                                       wide_block, narrow_block)])
    elseif !isempty(vt.chunks)
        ve = gen_verify_exprs(vt, fieldvar)
        guard_append!(ExprVarLine[ve.destructure..., :(found = $(and_suffix(ve.checks)))])
    elseif !isnothing(suffix_check)
        guard_append!(ExprVarLine[:(found = $suffix_check)])
    end
    # Stage 3: per-option tail verification for variable-length options
    !isnothing(tailcheck) && push!(body, tailcheck)
    # Stage 4: advance pos and record the matched option
    coerced_i = if ph.kind === :direct && ph.iT === cint; :i else :(i % $cint) end
    action = ExprVarLine[:(pos += $(if variable_len; :optlen else minoptlen end)),
                         onmatch(coerced_i)]
    guard_append!(action)
    push!(parts, :(if found; $(body...) end))
    if ph.kind === :bucketed
        # A slot holds up to two options: when the first fails to verify, try the second.
        retry = map(e -> e isa Expr ? copy(e) : e, body)
        push!(parts, :(if !found && 1 <= hi <= $(length(ph.table2))
                           i = $(Tuple(ph.table2))[hi]
                           found = !iszero(i)
                           if found; $(retry...) end
                       end))
    end
    (parts, mopts, sopts)
end

function build_linear_matcher(state::ParserState, nctx::NodeCtx, @nospecialize(cctx))
    (; mopts, sopts, casefold, onmatch, cint) = cctx
    # Sort longest-first for greedy matching when options share prefixes
    perm = sortperm(mopts, by=ncodeunits, rev=true)
    mopts = mopts[perm]
    sopts = sopts[perm]
    # Unrolled if/elseif rather than iterating a tuple of byte-tuples, which boxes.
    arms = map(enumerate(sopts)) do (i, opt)
        n = ncodeunits(opt)
        fit = :(nbytes - pos + 1 >= $n)
        nomatch = gen_literal_mismatch(state, nctx, opt, casefold)
        cond = :($fit && !$nomatch)
        body = quote
            $(onmatch(:($(i % cint))))
            pos += $n
        end
        cond => body
    end
    chain = foldr(arms; init = nothing) do (cond, body), rest
        if isnothing(rest); Expr(:if, cond, body)
        else Expr(:elseif, cond, body, rest) end
    end
    (ExprVarLine[chain], mopts, sopts)
end

## Perfect hashing

const HASH_MULTIPLIERS = (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)

"""
    hash_candidates(nopts, iT) -> Vector{@NamedTuple{hash::WindowHash, injective::Bool, maxval::UInt64}}

Candidate hashes of a register window of type `iT` over `nopts` options, in search
order: identity (injective: a hit identifies the window value), then for each modulus
in `nopts:2nopts` the mod, shift-mod and multiply-shift-mod families. `maxval` bounds
the hash's output.
"""
function hash_candidates(nopts::Int, iT::DataType)
    w = 8 * sizeof(iT)
    cands = @NamedTuple{hash::WindowHash, injective::Bool, maxval::UInt64}[
        (WindowHash(1, 0, 0), true, typemax(UInt64) >> (64 - w))]
    for m in nopts:2nopts
        push!(cands, (WindowHash(1, 0, m), false, UInt64(m)))
        for k in 1:min(w - 1, 16)
            push!(cands, (WindowHash(1, k, m), false, UInt64(m)))
        end
        for c in HASH_MULTIPLIERS, k in max(1, w - 8):w - 1
            push!(cands, (WindowHash(c, k, m), false, UInt64(m)))
        end
    end
    cands
end

function hashvalue(h::WindowHash, v::UInt64, iT::DataType)
    iszero(h.modulus) && return v
    widthmask = typemax(UInt64) >> (64 - 8 * sizeof(iT))
    ((v * h.mul) & widthmask) >> h.shift % h.modulus + 1
end

# Expression computing `hashvalue(h, x, iT)` on a window register `x::iT`.
function hashexpr(h::WindowHash, x, iT::DataType)
    iszero(h.modulus) && return x
    m, one_t = iT(h.modulus), one(iT)
    if !isone(h.mul)
        :(($x * $(h.mul % iT)) >> $(h.shift) % $m + $one_t)
    elseif iszero(h.shift)
        :($x % $m + $one_t)
    else
        :(($x >> $(h.shift)) % $m + $one_t)
    end
end

function hashexpr(ph::HashPlan, x)
    hx = hashexpr(ph.hash, x, ph.iT)
    if iszero(ph.offset) hx else :($hx - $(ph.iT(ph.offset))) end
end

"""
    find_window_hash(classify, options::Vector{String}, casefold::Bool) -> Union{HashPlan, Nothing}

Search register-sized byte windows over `options`, under the `hash_candidates`
families, for the cheapest hash that `classify` accepts:
- `classify_hash`: a minimal perfect hash, cost-ranked direct+injective (0) >
  direct (1) > small table > large table. Injective (identity-family) results let
  `find_best_hash_skip` elide verification bytes the hash covers.
- `classify_bucketed`: up to two options per slot (`kind = :bucketed`), for sets
  too large for a perfect hash to be found.

Returns `nothing` when no hash is accepted.
"""
function find_window_hash(@nospecialize(classify), options::Vector{String}, casefold::Bool)
    nopts = length(options)
    iszero(nopts) && return nothing
    minlen = minimum(ncodeunits, options)
    best, bestcost = nothing, typemax(Int)
    for iT in REGISTER_TYPES
        bwidth = sizeof(iT)
        bwidth > minlen && break
        for pos in 1:minlen - bwidth + 1
            values = map(options) do opt
                v = zero(UInt64)
                for j in 0:bwidth-1
                    b = codeunit(opt, pos + j)
                    v |= UInt64(if casefold; b | 0x20 else b end) << (8j)
                end
                v
            end
            allunique(values) || continue
            foldmask = zero(UInt64)
            if casefold
                for j in 0:bwidth-1
                    foldmask |= UInt64(0x20) << (8j)
                end
            end
            for (; hash, injective) in hash_candidates(nopts, iT)
                hvals = UInt64[hashvalue(hash, v, iT) for v in values]
                any(iszero, hvals) && continue
                classified = classify(hvals, pos, iT, foldmask, hash, injective)
                isnothing(classified) && continue
                cost, plan = classified
                cost += plan.kind === :direct && !injective
                if cost < bestcost
                    best, bestcost = plan, cost
                end
                iszero(bestcost) && return best
            end
        end
    end
    best
end

function classify_hash(hvals::Vector{UInt64}, pos::Int, iT::DataType, foldmask::UInt64,
                       hash::WindowHash, injective::Bool; max_tablelen::Int = 4 * length(hvals))
    nopts = length(hvals)
    allunique(hvals) || return nothing
    sorted_indices = sortperm(hvals)
    lo, hi = Int(hvals[first(sorted_indices)]), Int(hvals[last(sorted_indices)])
    # Direct: consecutive values, so the hash less an offset is the option index
    if hi - lo + 1 == nopts
        return (0, HashPlan(pos, iT, foldmask, hash, lo - 1, sorted_indices, :direct,
                            Int[], Int[], injective))
    end
    # Table lookup (original order, no permutation needed)
    hi > max_tablelen && return nothing
    table = zeros(Int, hi)
    for (i, h) in enumerate(hvals)
        table[h] = i
    end
    (2 * nopts + hi, HashPlan(pos, iT, foldmask, hash, 0, collect(1:nopts), :table,
                              table, Int[], injective))
end

function classify_bucketed(hvals::Vector{UInt64}, pos::Int, iT::DataType, foldmask::UInt64,
                           hash::WindowHash, injective::Bool; max_tablelen::Int = 4 * length(hvals))
    nopts = length(hvals)
    maxval = Int(maximum(hvals))
    maxval > max_tablelen && return nothing
    table, table2 = zeros(Int, maxval), zeros(Int, maxval)
    for (i, h) in enumerate(hvals)
        slots = if iszero(table[h]) table elseif iszero(table2[h]) table2 else return nothing end
        slots[h] = i
    end
    # Each second candidate is a potential extra verify
    (2 * nopts + maxval + count(!iszero, table2),
     HashPlan(pos, iT, foldmask, hash, 0, collect(1:nopts), :bucketed, table, table2, injective))
end

"""
    find_best_hash_skip(optlen, hash_offset, hash_width) -> Union{Tuple{Int,Int}, Nothing}

Find the byte removal within the hash window that minimises the total
number of register-sized loads needed to verify the remaining bytes.
"""
function find_best_hash_skip(optlen::Int, hash_offset::Int, hash_width::Int)
    nloads(n) = n ÷ sizeof(Int) + count_ones(n % sizeof(Int))
    baseline = nloads(optlen)
    iszero(baseline) && return (hash_offset, hash_width)
    best_cost, best_start, best_width = baseline, 0, 0
    for start in hash_offset:hash_offset + hash_width - 1
        for w in 1:hash_offset + hash_width - start
            cost = nloads(start) + nloads(optlen - start - w)
            if cost < best_cost
                best_cost = cost
                best_start = start
                best_width = w
            end
        end
    end
    if best_cost < baseline
        (best_start, best_width)
    end
end

## Common suffix
# Longest suffix shared by all options, aligned from the end.
function common_suffix_length(options::Vector{String}, casefold::Bool)
    length(options) < 2 && return 0
    minlen = minimum(ncodeunits, options)
    ref = options[1]
    reflen = ncodeunits(ref)
    for k in 1:minlen
        b = codeunit(ref, reflen - k + 1)
        byte = if casefold; b | 0x20 else b end
        all(options) do opt
            ob = codeunit(opt, ncodeunits(opt) - k + 1)
            (if casefold; ob | 0x20 else ob end) == byte
        end || return k - 1
    end
    minlen
end

# Constant comparison for a shared suffix, addressed via pos+optlen.
function gen_suffix_check(suffix::String, casefold::Bool, suffix_len::Int)
    chunks = register_chunks(suffix_len)
    foldr(chunks, init=:(true)) do c, rest
        (; value, mask) = pack_chunk(suffix, c, casefold)
        tailoff = suffix_len - c.offset
        check = gen_masked_compare(c.iT, :(pos + optlen - $tailoff), value, mask)
        if rest == :(true) check else :($check && $rest) end
    end
end

## Verification codegen
#
# Tables are `Any` vectors of per-option tuples and `Unsigned` vectors of masks,
# so their types never depend on the options; the splice converts to a tuple.

"""
    gen_verify_table(options, casefold; skip, nbytes) -> (; verify_table, masks, chunks)

Build per-option register-sized comparison data for verifying hash matches.

Masks use `0xDF` where any option has a casefold alpha byte, `0xFF` for
exact match, `0x00` for overflow. When `skip = (gap_offset, gap_width)`,
the gap region is excluded from verification (used with injective hashes).
"""
function gen_verify_table(options::Vector{String}, casefold::Bool;
                          skip::Union{Nothing, Tuple{Int, Int}} = nothing,
                          nbytes::Int = minimum(ncodeunits, options))
    minlen = minimum(ncodeunits, options)
    chunks = if isnothing(skip)
        register_chunks(nbytes)
    else
        # Split into chunks covering [0, gap) and [gap+width, total),
        # with right-side offsets adjusted to original string positions
        gap_offset, gap_width = skip
        left = register_chunks(gap_offset)
        right = register_chunks(minlen - gap_offset - gap_width)
        right_base = gap_offset + gap_width
        for i in eachindex(right)
            right[i] = (; right[i]..., offset = right[i].offset + right_base)
        end
        vcat(left, right)
    end
    function chunk_mask(c)
        mask = zero(c.iT)
        for j in 0:c.width-1
            valid = c.offset + j < minlen
            byte = if valid && casefold && any(opt -> codeunit(opt, c.offset + j + 1) in UInt8('a'):UInt8('z'), options)
                0xDF
            elseif valid
                0xFF
            else
                0x00
            end
            mask |= c.iT(byte) << (8j)
        end
        mask
    end
    masks = Unsigned[chunk_mask(c) for c in chunks]
    verify_table = Any[Tuple(Unsigned[pack_bytes(opt, c.offset, min(c.width, max(0, minlen - c.offset)), c.iT) & m
                                      for (c, m) in zip(chunks, masks)])
                       for opt in options]
    (; verify_table, masks, chunks)
end

function gen_verify_exprs(vt, prefix::Symbol; pos_offset::Int = 0)
    nchunks = length(vt.chunks)
    cvars = [Symbol(prefix, "_expect", ci) for ci in 1:nchunks]
    destructure = [Expr(:(=), Expr(:tuple, cvars...), :($(Tuple(vt.verify_table))[i]))]
    checks = foldr(1:nchunks, init = :(true)) do ci, rest
        baseoff = vt.chunks[ci].offset + pos_offset
        posexpr = if iszero(baseoff)
            :pos
        else
            :(pos + $baseoff)
        end
        check = gen_masked_compare(vt.chunks[ci].iT, posexpr, cvars[ci], vt.masks[ci])
        if rest == :(true)
            check
        else
            :($check && $rest)
        end
    end
    (; destructure, checks)
end

# Backward-aligned single-register verify: loads from pos-padding, padding
# bytes masked to 0x00. Returns (; destructure, checks) like gen_verify_exprs.
function gen_backward_verify(options::Vector{String}, casefold::Bool,
                             nbytes::Int, bvc, prefix::Symbol,
                             skip::Union{Nothing, Tuple{Int, Int}})
    (; iT, padding) = bvc
    mask = zero(iT)
    for j in 0:sizeof(iT)-1
        optj = j - padding
        byte = if optj < 0 || optj >= nbytes
            0x00
        elseif !isnothing(skip) && skip[1] <= optj < skip[1] + skip[2]
            0x00
        elseif casefold && any(opt -> UInt8('a') <= codeunit(opt, optj + 1) <= UInt8('z'), options)
            0xDF
        else
            0xFF
        end
        mask |= iT(byte) << (8j)
    end
    function expected(opt)
        v = zero(iT)
        for j in 0:nbytes-1
            v |= iT(codeunit(opt, j + 1)) << (8 * (j + padding))
        end
        v & mask
    end
    verify_table = Unsigned[expected(opt) for opt in options]
    evar = Symbol(prefix, "_bexpect")
    destructure = [:($evar = $(Tuple(verify_table))[i])]
    checks = gen_masked_compare(iT, :(pos - $padding), evar, mask)
    (; destructure, checks)
end

"""
    gen_tail_verify(options, casefold, minoptlen, prefix) -> Expr

Generate verification for the tail bytes (beyond `minoptlen`) of
variable-length options. Uses register-sized comparisons when all
non-empty tails have the same length, otherwise a codeunit loop.
"""
function gen_tail_verify(options::Vector{String}, casefold::Bool, minoptlen::Int, prefix::Symbol)
    tails = [opt[minoptlen+1:end] for opt in options]
    taillens = ncodeunits.(tails)
    has_empty = any(iszero, taillens)
    distinct_taillens = unique(filter(!iszero, taillens))
    body = if length(distinct_taillens) == 1
        # Single tail length: register-sized comparison via gen_verify_exprs
        chunks = register_chunks(only(distinct_taillens))
        nonempty_tails = filter(!isempty, tails)
        function chunk_mask(c)
            mask = zero(c.iT)
            for j in 0:c.width-1
                folds = casefold && any(t -> codeunit(t, c.offset + j + 1) in UInt8('a'):UInt8('z'), nonempty_tails)
                mask |= c.iT(if folds 0xDF else 0xFF end) << (8j)
            end
            mask
        end
        masks = Unsigned[chunk_mask(c) for c in chunks]
        verify_table = Any[if isempty(tail)
                               Tuple(Unsigned[zero(c.iT) for c in chunks])
                           else
                               Tuple(Unsigned[pack_bytes(tail, c.offset, c.width, c.iT) & m for (c, m) in zip(chunks, masks)])
                           end
                           for tail in tails]
        tve = gen_verify_exprs((; verify_table, masks, chunks), Symbol(prefix, "_tail"); pos_offset = minoptlen)
        ExprVarLine[tve.destructure..., :(found = $(tve.checks))]
    else
        # Multiple tail lengths: codeunit loop over tail bytes. Tails are padded
        # to one length so the tables are homogeneous (indexing a tuple of
        # differently-sized tuples by `i` is a runtime field lookup), and bytes
        # compare under a per-byte mask so casefolding spares non-letters.
        maxtail = maximum(taillens)
        masktable = Any[Tuple(UInt8[if j > ncodeunits(t) 0x00
                                    elseif casefold && UInt8('a') <= (codeunit(t, j) | 0x20) <= UInt8('z') 0xDF
                                    else 0xFF end
                                    for j in 1:maxtail])
                        for t in tails]
        bytetable = Any[Tuple(UInt8[if j <= ncodeunits(t) codeunit(t, j) & mask[j] else 0x00 end for j in 1:maxtail])
                        for (t, mask) in zip(tails, masktable)]
        ExprVarLine[:(tailbytes = $(Tuple(bytetable))[i]),
                     :(tailmasks = $(Tuple(masktable))[i]),
                     :(@inbounds(for j in 1:$(Tuple(taillens))[i]
                           if data[pos + $minoptlen + j - 1] & tailmasks[j] != tailbytes[j]
                               found = false
                               break
                           end
                       end))]
    end
    cond = if has_empty
        :(found && optlen > $minoptlen)
    else
        :found
    end
    :(if $cond
          $(body...)
      end)
end
