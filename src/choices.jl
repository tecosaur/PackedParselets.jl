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
function compile_choice(state::ParserState, nctx::NodeCtx,
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
    soptions = Vector{String}(options)
    allowempty = any(isempty, soptions)
    allowempty && filter!(!isempty, soptions)
    casefold = get(nctx, :casefold, false)
    target = get(nctx, :is, nothing)::Union{Nothing, String}
    fieldvar = get(nctx, :fieldvar, gensym("prefix"))
    option = get(nctx, :optional, nothing)
    claims = unclaimed_sentinel(nctx)
    choicebits = cardbits(length(soptions) + 1)
    choiceint = if isnothing(target)
        cardtype(choicebits)
    else
        Bool
    end
    if !isnothing(target)
        push!(soptions, target)
    end
    if casefold
        all(isascii, soptions) || throw(ArgumentError("Expected all options to be ASCII strings for casefolding"))
    end
    matchoptions = if casefold; map(lowercase, soptions) else soptions end
    foundaction = if isnothing(target)
        valexpr -> :($fieldvar = $valexpr)
    else
        _ -> :($fieldvar = one($fieldvar))
    end
    cctx = (; matchoptions, soptions, casefold, fieldvar, foundaction, choiceint)
    matcher, matchoptions, soptions = build_choice_matcher(state, nctx, cctx)
    # Build the length-guarded match wrapper
    notfound = build_fail_expr!(state, nctx, "Expected one of $(join(soptions, ", "))")
    lencheck = emit_lengthcheck(state, nctx, minimum(ncodeunits, soptions))
    checkedmatch = if allowempty
        :(if $lencheck
              $(matcher...)
          end)
    else
        :(if !$lencheck
              $notfound
          else
              $(matcher...)
              if $fieldvar == zero($choiceint)
                  $notfound
              end
          end)
    end
    (; soptions, fieldvar, option, allowempty, choicebits, choiceint,
       checkedmatch, matcher, target, claims)
end

function compile_choice_value(state::ParserState, nctx::NodeCtx, ctx)
    (; soptions, fieldvar, option, allowempty, choicebits, choiceint, checkedmatch, claims) = ctx
    # Compute bit position without mutating state.bits
    nbits_pos = state.bits + choicebits
    pmin = if allowempty; 0 else minimum(ncodeunits, soptions) end
    parse_exprs = ExprVarLine[
          :($fieldvar = zero($choiceint)),
          checkedmatch,
          emit_pack(state, choiceint, fieldvar, nbits_pos)]
    fextract = :($fieldvar = $(emit_extract(state, nbits_pos, choicebits)))
    symoptions = Tuple(Symbol.(soptions))
    present = :(!iszero($fieldvar))
    printexpr = :(print(io, @inbounds $(Tuple(soptions))[$fieldvar]))
    # When allowempty without an enclosing optional, guard print on presence
    print_exprs = ExprVarLine[if allowempty && isnothing(option)
              :(if $present; $printexpr end)
          else
              printexpr
          end]
    argvar = gensym("arg_choice")
    impart_core = Any[
        :($fieldvar = let idx = findfirst(==(Symbol($argvar)), $symoptions)
              isnothing(idx) && throw(ArgumentError(
                  string("Invalid option :", $argvar, "; expected one of: ", $(join(soptions, ", ")))))
              idx % $choiceint
          end),
        emit_pack(state, choiceint, fieldvar, nbits_pos)]
    extract_value = :(@inbounds $(symoptions)[$fieldvar])
    # For allowempty without an enclosing optional, wrap extract in a presence guard
    eopt = if allowempty && isnothing(option)
        extract_value = :(if $present; $extract_value end)
        gensym("emptyopt")
    else
        option
    end
    sentinel = if claims; SentinelSpec((0, choicebits)) else nothing end
    pmax = maximum(ncodeunits, soptions)
    casefold = get(nctx, :casefold, false) === true
    arrangements = [[byte_set(codeunit(o, i), casefold) for i in 1:ncodeunits(o)]
                     for o in soptions]
    value_segment_output(;
        bounds=SegmentBounds(pmin:pmax, pmin:pmax, choicebits, sentinel),
        fieldvar, desc=join(soptions, " | "),
        shortform=join(soptions, " | "),
        argvar, base_argtype=:Symbol, option=eopt,
        parse=parse_exprs,
        extract_setup=ExprVarLine[fextract], extract_value,
        impart_body=impart_core, print=print_exprs,
        bytespans=arrangements)
end

function compile_choice_fixed(state::ParserState, nctx::NodeCtx, ctx)
    (; soptions, fieldvar, option, allowempty, choiceint, checkedmatch, matcher, target) = ctx
    parse_exprs = if any(isempty, soptions)
        ExprVarLine[matcher]
    else
        ExprVarLine[:($fieldvar = zero($choiceint)), checkedmatch]
    end
    pmin = if allowempty; 0 else minimum(ncodeunits, soptions) end
    tlen = ncodeunits(target)
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    casefold = get(nctx, :casefold, false) === true
    arrangements = [[byte_set(codeunit(o, i), casefold) for i in 1:ncodeunits(o)]
                     for o in soptions]
    SegmentOutput(
        SegmentBounds(pmin:maximum(ncodeunits, soptions), tlen:tlen, 0, nothing),
        SegmentCodegen(parse_exprs, ExprVarLine[], ExprVarLine[], Any[],
                       ExprVarLine[:(print(io, $target))]),
        SegmentMeta(label,
                    "Choice of literal string \"$(target)\" vs $(join(soptions, ", "))",
                    join(soptions, " | "), nothing, nothing),
        arrangements)
end

## Matcher assembly

"""
    build_choice_matcher(matchoptions, soptions, casefold, fieldvar, foundaction,
                         choiceint, state, nctx)
        -> (matcher, matchoptions, soptions)

Build parse-time matcher expressions for a choice node.

Uses perfect hashing when available (with optional hash-skip optimisation
for injective hashes and widened verify tables when they reduce chunk count),
falls back to linear scan. May reorder options to match hash output order.
"""
function build_choice_matcher(state::ParserState, nctx::NodeCtx, cctx)
    ph = find_perfect_hash(cctx.matchoptions, cctx.casefold)
    if !isnothing(ph)
        build_hash_matcher(state, nctx, ph, cctx)
    else
        build_linear_matcher(state, nctx, cctx)
    end
end

function build_hash_matcher(state::ParserState, nctx::NodeCtx, ph, cctx)
    (; casefold, fieldvar, foundaction, choiceint) = cctx
    # Reorder options to match hash output order
    matchoptions = cctx.matchoptions[ph.perm]
    soptions = cctx.soptions[ph.perm]
    optlens = Tuple(ncodeunits.(matchoptions))
    phoff = ph.pos - 1
    phposexpr = if iszero(phoff); :pos else :(pos + $phoff) end
    load = gen_load(ph.iT, phposexpr)
    foldedload = if !iszero(ph.foldmask); :($load | $(ph.foldmask)) else load end
    hashval = ph.hashexpr(foldedload)
    minoptlen = minimum(ncodeunits, matchoptions)
    maxoptlen = maximum(ncodeunits, matchoptions)
    variable_len = minoptlen != maxoptlen
    # Common suffix: when variable-length options share trailing bytes (aligned
    # from the end), those bytes can be checked as a constant using pos+optlen
    # addressing. When the suffix covers the entire length difference, no
    # per-option tail verification is needed.
    suffix_len = if variable_len
        min(common_suffix_length(matchoptions, casefold), maxoptlen - minoptlen)
    else
        0
    end
    suffix_check = if suffix_len > 0
        gen_suffix_check(matchoptions[1][end-suffix_len+1:end], casefold, suffix_len)
    else
        nothing
    end
    # For injective hashes, skip bytes already validated by the hash window
    hash_skip = if ph.injective
        find_best_hash_skip(minoptlen, phoff, sizeof(ph.iT))
    else
        nothing
    end
    vt = gen_verify_table(matchoptions, casefold; skip = hash_skip)
    # Try backward-aligned single-register verify when prior parsed content provides safety
    b = nctx[:current_branch]
    bvc = backward_verify_chunk(minoptlen)
    use_backward = !isnothing(bvc) && !variable_len && b.parsed_min >= bvc.padding
    bve = if use_backward
        gen_backward_verify(matchoptions, casefold, minoptlen, bvc, fieldvar; skip = hash_skip)
    else
        nothing
    end
    # Try widening the verify table when it reduces chunk count (skipped when backward is available)
    wide_minlen = min(nextpow(2, minoptlen), sizeof(UInt) * cld(minoptlen, sizeof(UInt)))
    use_wide_vt = !use_backward && isnothing(hash_skip) && wide_minlen > minoptlen &&
        length(register_chunks(wide_minlen)) < length(vt.chunks)
    vt_wide = if use_wide_vt
        gen_verify_table(matchoptions, casefold; nbytes = wide_minlen)
    else
        nothing
    end
    # Tail verification: skip when common suffix covers the entire length difference
    tailcheck = if variable_len && suffix_len < maxoptlen - minoptlen
        gen_tail_verify(matchoptions, minoptlen, casefold, fieldvar)
    else
        nothing
    end
    # Index resolution depends on hash kind
    nopts = length(matchoptions)
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
    # Collect matcher expressions: resolve_i then a single guarded block
    parts = ExprVarLine[resolve_i...]
    verify_body = ExprVarLine[]
    if variable_len
        optlencheck = emit_lengthcheck(state, nctx, :optlen, minoptlen, maximum(ncodeunits, matchoptions))
        append!(verify_body,
                ExprVarLine[:(optlen = $(optlens)[i]),
                            :(found = $optlencheck)])
    end
    # AND suffix check into a verify checks expression when present
    and_suffix(checks) = isnothing(suffix_check) ? checks : :($checks && $suffix_check)
    if use_backward || !isempty(vt.chunks) || !isnothing(suffix_check)
        verify_stmts = if use_backward
            ExprVarLine[bve.destructure..., :(found = $(and_suffix(bve.checks)))]
        elseif use_wide_vt
            ve = gen_verify_exprs(vt, fieldvar)
            ve_wide = gen_verify_exprs(vt_wide, fieldvar)
            wide_block = Expr(:block, ve_wide.destructure..., :(found = $(and_suffix(ve_wide.checks))))
            verify_block = Expr(:block, ve.destructure..., :(found = $(and_suffix(ve.checks))))
            ExprVarLine[Expr(:if, emit_static_lengthcheck(state, nctx, wide_minlen),
                             wide_block, verify_block)]
        elseif !isempty(vt.chunks)
            ve = gen_verify_exprs(vt, fieldvar)
            ExprVarLine[ve.destructure..., :(found = $(and_suffix(ve.checks)))]
        else
            # Suffix check only (no main verify chunks, e.g. hash-skip covered everything)
            ExprVarLine[:(found = $suffix_check)]
        end
        # Wrap in found guard only when there are prior stages that may have cleared it
        if !isempty(verify_body)
            push!(verify_body, :(if found; $(verify_stmts...) end))
        else
            append!(verify_body, verify_stmts)
        end
    end
    if !isnothing(tailcheck)
        push!(verify_body, tailcheck)
    end
    coerced_i = if ph.kind === :direct && ph.iT === choiceint; :i else :(i % $choiceint) end
    action = ExprVarLine[:(pos += $(if variable_len; :optlen else minoptlen end)),
                         foundaction(coerced_i)]
    if isempty(verify_body)
        append!(verify_body, action)
    else
        push!(verify_body, :(if found; $(action...) end))
    end
    push!(parts, :(if found; $(verify_body...) end))
    (parts, matchoptions, soptions)
end

function build_linear_matcher(state::ParserState, nctx::NodeCtx, cctx)
    (; matchoptions, soptions, casefold, fieldvar, foundaction, choiceint) = cctx
    # Sort longest-first for greedy matching when options share prefixes
    perm = sortperm(matchoptions, by=ncodeunits, rev=true)
    matchoptions = matchoptions[perm]
    soptions = soptions[perm]
    opts = if casefold; matchoptions else soptions end
    optlens = Tuple(ncodeunits.(opts))
    optcus = Tuple(Tuple(codeunits(s)) for s in opts)
    loadbyte = if casefold
        :(@inbounds idbytes[pos + j - 1] | 0x20)
    else
        :(@inbounds idbytes[pos + j - 1])
    end
    action = foundaction(:(i % $choiceint))
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
    (matcher, matchoptions, soptions)
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
    accept!(result) =
        if !isnothing(result) && last(result) < last(best)
            best = result
        end
    # Identity family (injective — hash hit uniquely identifies the option)
    accept!(try_fn(v -> v, v -> v, true, typemax(iT) % UInt64))
    last(best) == 0 && return best
    # Mod, shift-mod, and multiply-shift-mod families
    one_t = one(iT)
    for m in nopts:2*nopts
        last(best) == 0 && break
        mt = iT(m)
        accept!(try_fn(v -> v % m + 1, v -> :($v % $mt + $one_t), false, UInt64(m)))
        for k in 1:min(8 * sizeof(iT) - 1, 16)
            last(best) == 0 && break
            accept!(try_fn(v -> (v >> k) % m + 1, v -> :(($v >> $k) % $mt + $one_t), false, UInt64(m)))
        end
        for c in (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)
            last(best) == 0 && break
            ct = c % iT
            for k in max(1, 8 * sizeof(iT) - 8):8 * sizeof(iT) - 1
                last(best) == 0 && break
                accept!(try_fn(v -> (iT(v) * ct) >> k % m + 1,
                               v -> :(($v * $ct) >> $k % $mt + $one_t), false, UInt64(m)))
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
        last(best) == 0 && break
        result = search_hash_families(nopts, iT) do fn, expr_fn, injective, _maxval
            hvals = map(fn, values)
            any(h -> h < 1, hvals) && return nothing
            length(unique(hvals)) == nopts || return nothing
            result = classify_hash(hvals, nopts, options, pos, iT, foldmask % iT, expr_fn)
            isnothing(result) && return nothing
            cost = result.cost + (result.ph.kind === :direct && !injective)
            (merge(result.ph, (; injective)), cost)
        end
        if !isnothing(first(result)) && last(result) < last(best)
            best = result
        end
    end
    first(best)
end

function classify_hash(hvals::Vector{UInt64}, nopts::Int, options::Vector{String},
                       pos::Int, iT::DataType, foldmask, hashexpr_fn;
                       max_tablelen::Int = 4 * nopts)
    sorted_indices = sortperm(hvals)
    sorted_hvals = hvals[sorted_indices]
    lo, hi = Int(sorted_hvals[1]), Int(sorted_hvals[end])
    # Direct: consecutive values — hashexpr(v) ± offset maps to 1:n
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
    baseline == 0 && return (hash_offset, hash_width)
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
    fold(b) = casefold ? (b | 0x20) : b
    ref = options[1]
    reflen = ncodeunits(ref)
    for k in 1:minlen
        byte = fold(codeunit(ref, reflen - k + 1))
        all(opt -> fold(codeunit(opt, ncodeunits(opt) - k + 1)) == byte, options) || return k - 1
    end
    minlen
end

# Constant comparison for a shared suffix, addressed via pos+optlen.
function gen_suffix_check(suffix::String, casefold::Bool, suffix_len::Int)
    chunks = register_chunks(suffix_len)
    foldr(chunks, init=:(true)) do c, rest
        (; value, mask) = pack_chunk(suffix, c; casefold)
        tailoff = suffix_len - c.offset
        check = gen_masked_compare(c.iT, :(pos + optlen - $tailoff), value, mask)
        rest == :(true) ? check : :($check && $rest)
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
                             nbytes::Int, bvc, prefix::Symbol;
                             skip::Union{Nothing, Tuple{Int, Int}} = nothing)
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
    gen_tail_verify(options, minoptlen, casefold, prefix) -> Expr

Generate verification for the tail bytes (beyond `minoptlen`) of
variable-length options. Uses register-sized comparisons when all
non-empty tails have the same length, otherwise a codeunit loop.
"""
function gen_tail_verify(options::Vector{String}, minoptlen::Int, casefold::Bool, prefix::Symbol)
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
            :(@inbounds idbytes[pos + $minoptlen + j - 1] | 0x20)
        else
            :(@inbounds idbytes[pos + $minoptlen + j - 1])
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
