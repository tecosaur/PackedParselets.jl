# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Choice pattern handler and its codegen: perfect hashing, matcher assembly,
# and register-sized verification.

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
function compile_choice_value(state::ParserState, nctx::NodeCtx, ctx)
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
function compile_choice_fixed(::ParserState, nctx::NodeCtx, ctx)
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
falls back to linear scan. May reorder options to match hash output order.
"""
function build_choice_matcher(state::ParserState, nctx::NodeCtx, cctx)
    ph = find_perfect_hash(cctx.mopts, cctx.casefold)
    if !isnothing(ph)
        build_hash_matcher(state, nctx, ph, cctx)
    else
        build_linear_matcher(state, nctx, cctx)
    end
end

function build_hash_matcher(state::ParserState, nctx::NodeCtx, ph, cctx)
    (; casefold, fieldvar, onmatch, cint) = cctx
    # Reorder options to match hash output order
    mopts = cctx.mopts[ph.perm]
    sopts = cctx.sopts[ph.perm]
    optlens = Tuple(ncodeunits.(mopts))
    phoff = ph.pos - 1
    phposexpr = if iszero(phoff); :pos else :(pos + $phoff) end
    load = gen_load(ph.iT, phposexpr)
    foldedload = if iszero(ph.foldmask) load else :($load | $(ph.foldmask)) end
    hashval = ph.hashexpr(foldedload)
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
                    :(i = if 1 <= hi <= $(ph.tablelen)
                          $(ph.table)[hi]
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
    (parts, mopts, sopts)
end

function build_linear_matcher(state::ParserState, nctx::NodeCtx, cctx)
    (; mopts, sopts, casefold, onmatch, cint) = cctx
    # Sort longest-first for greedy matching when options share prefixes
    perm = sortperm(mopts, by=ncodeunits, rev=true)
    mopts = mopts[perm]
    sopts = sopts[perm]
    opts = if casefold; mopts else sopts end
    optlens = Tuple(ncodeunits.(opts))
    optcus = Tuple(Tuple(codeunits(s)) for s in opts)
    loadbyte = if casefold
        :(@inbounds data[pos + j - 1] | 0x20)
    else
        :(@inbounds data[pos + j - 1])
    end
    action = onmatch(:(i % $cint))
    loop_body = quote
        found = true
        for j in 1:prefixlen
            $loadbyte == prefixbytes[j] || (found = false; break)
        end
        if found; $action; pos += prefixlen; break end
    end
    guarded_loop = :(
        for (i, (prefixlen, prefixbytes)) in enumerate(zip($optlens, $optcus))
            nbytes - pos + 1 >= prefixlen || continue
            $(loop_body.args...)
        end)
    unguarded_loop = :(
        for (i, (prefixlen, prefixbytes)) in enumerate(zip($optlens, $optcus))
            $(loop_body.args...)
        end)
    maxlen = maximum(optlens)
    all_fit = emit_static_lengthcheck(state, nctx, maxlen)
    matcher = ExprVarLine[Expr(:if, all_fit, unguarded_loop, guarded_loop)]
    (matcher, mopts, sopts)
end

## Perfect hashing

"""
    search_hash_families(try_fn, nopts, iT) -> (result, cost)

Iterate hash families (identity, mod, shift-mod, multiply-shift-mod) for
register type `iT` over `nopts` options. Calls `try_fn(fn, expr_fn, injective, maxval)`
for each candidate, where `maxval` is the maximum value `fn` can return.
`try_fn` returns `(result, cost::Int)` on success or `nothing` on failure.
Returns the lowest-cost `(result, cost)` found, or `(nothing, typemax(Int))`
if no hash worked.
"""
function search_hash_families(try_fn::F, nopts::Int, iT::DataType) where {F <: Function}
    best = (nothing, typemax(Int))
    # Identity family (injective: hash hit uniquely identifies the option)
    res = try_fn(v -> v, v -> v, true, typemax(iT) % UInt64)
    !isnothing(res) && last(res) < last(best) && (best = res)
    iszero(last(best)) && return best
    # Mod, shift-mod, and multiply-shift-mod families
    one_t = one(iT)
    for m in nopts:2*nopts
        iszero(last(best)) && break
        mt = iT(m)
        res = try_fn(v -> v % m + 1, v -> :($v % $mt + $one_t), false, UInt64(m))
        !isnothing(res) && last(res) < last(best) && (best = res)
        for k in 1:min(8 * sizeof(iT) - 1, 16)
            iszero(last(best)) && break
            res = try_fn(v -> (v >> k) % m + 1, v -> :(($v >> $k) % $mt + $one_t), false, UInt64(m))
            !isnothing(res) && last(res) < last(best) && (best = res)
        end
        for c in (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)
            iszero(last(best)) && break
            ct = c % iT
            for k in max(1, 8 * sizeof(iT) - 8):8 * sizeof(iT) - 1
                iszero(last(best)) && break
                res = try_fn(v -> (iT(v) * ct) >> k % m + 1,
                             v -> :(($v * $ct) >> $k % $mt + $one_t), false, UInt64(m))
                !isnothing(res) && last(res) < last(best) && (best = res)
            end
        end
    end
    best
end

"""
    find_perfect_hash(options::Vector{String}, casefold::Bool)
        -> Union{NamedTuple, Nothing}

Search for a minimal perfect hash over `options` using register-sized byte
windows and multiple hash families.

Tries identity (injective), mod, shift-mod, and multiply-shift-mod families
across all discriminating byte windows. The `injective` flag on identity-family
results enables `find_best_hash_skip` to elide verification bytes that the hash
already covers.

Cost-ranked: direct+injective (0) > direct (1) > small table > large table.
Returns `nothing` when no perfect hash is found.
"""
function find_perfect_hash(options::Vector{String}, casefold::Bool)
    nopts = length(options)
    iszero(nopts) && return nothing
    minlen = minimum(ncodeunits, options)
    # Collect discriminating window candidates
    candidates = @NamedTuple{pos::Int, iT::DataType, values::Vector{UInt64}, foldmask::UInt64}[]
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
            length(unique(values)) == nopts || continue
            foldmask = zero(UInt64)
            if casefold
                for j in 0:bwidth-1
                    foldmask |= UInt64(0x20) << (8j)
                end
            end
            push!(candidates, (; pos, iT, values, foldmask))
        end
    end
    isempty(candidates) && return nothing
    best = (nothing, typemax(Int))
    for (; pos, iT, values, foldmask) in candidates
        iszero(last(best)) && break
        result = search_hash_families(nopts, iT) do fn, expr_fn, injective, _maxval
            hvals = map(fn, values)
            any(h -> h < 1, hvals) && return nothing
            length(unique(hvals)) == nopts || return nothing
            classified = classify_hash(hvals, nopts, pos, iT, foldmask % iT, expr_fn)
            isnothing(classified) && return nothing
            cost = classified.cost + (classified.ph.kind === :direct && !injective)
            (merge(classified.ph, (; injective)), cost)
        end
        if !isnothing(first(result)) && last(result) < last(best)
            best = result
        end
    end
    first(best)
end

function classify_hash(hvals::Vector{UInt64}, nopts::Int,
                       pos::Int, iT::DataType, foldmask, hashexpr_fn;
                       max_tablelen::Int = 4 * nopts)
    sorted_indices = sortperm(hvals)
    sorted_hvals = hvals[sorted_indices]
    lo, hi = Int(sorted_hvals[1]), Int(sorted_hvals[end])
    # Direct: consecutive values: hashexpr(v) ± offset maps to 1:n
    if hi - lo + 1 == nopts
        hashexpr = if lo == 1
            hashexpr_fn
        else
            offset = iT(lo - 1)
            v -> :($(hashexpr_fn(v)) - $offset)
        end
        ph = (; pos, iT, foldmask, hashexpr,
               perm = sorted_indices, kind = :direct,
               table = (), tablelen = 0)
        return (; cost = 0, ph)
    end
    # Table lookup (original order, no permutation needed)
    maxval = Int(maximum(hvals))
    maxval > max_tablelen && return nothing
    table = zeros(Int, maxval)
    for (i, h) in enumerate(hvals)
        table[Int(h)] = i
    end
    ph = (; pos, iT, foldmask, hashexpr = hashexpr_fn,
           perm = collect(1:nopts), kind = :table,
           table = Tuple(table), tablelen = maxval)
    (; cost = 2 * nopts + maxval, ph)
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
    # Shared mask: 0xDF where any option has casefold alpha, 0xFF for valid, 0x00 for overflow
    masks = Tuple(
        reduce(|, (begin
            valid = c.offset + j < minlen
            if valid && casefold && any(opt -> codeunit(opt, c.offset + j + 1) in UInt8('a'):UInt8('z'), options)
                c.iT(0xDF) << (8j)
            elseif valid
                c.iT(0xFF) << (8j)
            else
                zero(c.iT)
            end
        end for j in 0:c.width-1), init=zero(c.iT))
        for c in chunks)
    verify_table = Tuple(
        Tuple(pack_bytes(opt, c.offset, min(c.width, max(0, minlen - c.offset)), c.iT) & m
              for (c, m) in zip(chunks, masks))
        for opt in options)
    (; verify_table, masks, chunks)
end

function gen_verify_exprs(vt, prefix::Symbol; pos_offset::Int = 0)
    nchunks = length(vt.chunks)
    cvars = [Symbol(prefix, "_expect", ci) for ci in 1:nchunks]
    destructure = [Expr(:(=), Expr(:tuple, cvars...), :($(vt.verify_table)[i]))]
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
    w = sizeof(iT)
    mask = reduce(|, (begin
        optj = j - padding
        if optj < 0 || optj >= nbytes
            zero(iT)
        elseif !isnothing(skip) && skip[1] <= optj < skip[1] + skip[2]
            zero(iT)
        elseif casefold && any(opt -> UInt8('a') <= codeunit(opt, optj + 1) <= UInt8('z'), options)
            iT(0xDF) << (8j)
        else
            iT(0xFF) << (8j)
        end
    end for j in 0:w-1), init=zero(iT))
    verify_table = Tuple(begin
        v = zero(iT)
        for j in 0:nbytes-1
            v |= iT(codeunit(opt, j + 1)) << (8 * (j + padding))
        end
        v & mask
    end for opt in options)
    evar = Symbol(prefix, "_bexpect")
    destructure = [:($evar = $(verify_table)[i])]
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
        taillen = only(distinct_taillens)
        chunks = register_chunks(taillen)
        nonempty_tails = filter(!isempty, tails)
        masks = Tuple(
            reduce(|, (begin
                if casefold && any(t -> codeunit(t, c.offset + j + 1) in UInt8('a'):UInt8('z'), nonempty_tails)
                    c.iT(0xDF) << (8j)
                else
                    c.iT(0xFF) << (8j)
                end
            end for j in 0:c.width-1), init=zero(c.iT))
            for c in chunks)
        zerotup = Tuple(zero(c.iT) for c in chunks)
        verify_table = Tuple(
            if isempty(tails[oi])
                zerotup
            else
                Tuple(pack_bytes(tails[oi], c.offset, c.width, c.iT) & m
                      for (c, m) in zip(chunks, masks))
            end
            for oi in eachindex(options))
        vt = (; verify_table, masks, chunks)
        tve = gen_verify_exprs(vt, Symbol(prefix, "_tail"); pos_offset = minoptlen)
        ExprVarLine[tve.destructure..., :(found = $(tve.checks))]
    else
        # Multiple tail lengths: codeunit loop over tail bytes
        tailtable = Tuple(Tuple(codeunits(t)) for t in tails)
        taillenst = Tuple(taillens)
        loadbyte = if casefold
            :(@inbounds data[pos + $minoptlen + j - 1] | 0x20)
        else
            :(@inbounds data[pos + $minoptlen + j - 1])
        end
        ExprVarLine[:(tailbytes = $tailtable[i]),
                     :(for j in 1:$taillenst[i]
                           if $loadbyte != @inbounds tailbytes[j]
                               found = false
                               break
                           end
                       end)]
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
