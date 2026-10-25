# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Below these option counts the unrolled linear matcher, which LLVM often turns into
# a switch, measured as fast or faster than a bucketed hash on varied input. Mixed
# lengths cost the hash path a length lookup and a bytewise tail check.
const BUCKETED_MIN_FIXED_OPTIONS = 8
const BUCKETED_MIN_VARIABLE_OPTIONS = 16

## Choice pattern handler

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
    casefold = get(nctx, :casefold, false)::Bool
    target = get(nctx, :is, nothing)::Union{Nothing, String}
    fieldvar = get(nctx, :fieldvar, gensym("prefix"))::Symbol
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
    cmatch = ChoiceMatch(mopts, sopts, casefold, fieldvar, cint, if isnothing(target); :index else :flag end)
    matcher, mopts, sopts = build_choice_matcher(state, nctx, cmatch)
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
       guarded, target, claims, valtype)
end

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
    valid = emit_validity_check(state, fieldvar, fieldvar, 1:length(sopts))
    opttuple = Tuple(sopts)
    printexpr = :(print(io, @inbounds $opttuple[$fieldvar]))
    optlens = map(ncodeunits, sopts)
    lenexpr = if allequal(optlens)
        :(pos += $(first(optlens)))
    else
        :(pos += $(GlobalRef(Base, :ncodeunits))(@inbounds $opttuple[$fieldvar]))
    end
    emptyguard = allowempty && isnothing(option)
    guard(ex) = if emptyguard; :(if $present; $ex end) else ex end
    # Index checked, as statements rewrite_bufprint! can still reach the print in
    checked(ex) = if emptyguard
        ExprVarLine[Expr(:if, present, Expr(:block, copy(valid), ex))]
    else
        ExprVarLine[copy(valid), ex]
    end
    vars = Pair{Symbol,Any}[fieldvar => :(zero($cint))]
    argvar = gensym("arg_choice")
    extract_value, impart_core, argtype = choice_value_codegen(
        state, valtype, sopts, fieldvar, argvar, cint, bitpos)
    extract_value = guard(Expr(:block, copy(valid), extract_value))
    eopt = if emptyguard gensym("emptyopt") else option end
    sentinel = if claims SentinelSpec((0, cbits)) end
    pmax = maximum(ncodeunits, sopts)
    casefold = get(nctx, :casefold, false) === true
    arrangements = string_bytespans(sopts, casefold)
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    extract_setup = ExprVarLine[fextract]
    desc = join(sopts, " | ")
    seg_extract, seg_impart = optional_wrap(eopt, argvar, extract_setup, extract_value, impart_core)
    SegmentOutput(
        SegmentBounds(pmin:pmax, pmin:pmax, cbits, sentinel),
        SegmentCodegen(pexprs, seg_extract,
            PrintExprs(direct = ExprVarLine[fextract, checked(copy(printexpr))...],
                       vars = vars,
                       getval = ExprVarLine[fextract],
                       getlen = checked(lenexpr),
                       putval = checked(copy(printexpr))),
            seg_impart),
        SegmentMeta(label, desc, desc, argtype, argvar),
        arrangements)
end

function choice_value_codegen(state::ParserState, valtype::Symbol, sopts::Vector{String},
                               fieldvar::Symbol, argvar::Symbol, cint::DataType, bitpos::Int)
    vals, conv, argtype = if valtype === :Symbol
        Tuple(map(Symbol, sopts)), :Symbol, :Symbol
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

# A choice with `is = target`: the parsed option isn't stored, and `target` is always printed
function compile_choice_fixed(::ParserState, nctx::NodeCtx, @nospecialize(ctx))
    (; sopts, fieldvar, allowempty, cint, guarded, target) = ctx
    pexprs = ExprVarLine[:($fieldvar = zero($cint)), guarded]
    pmin = if allowempty 0 else minimum(ncodeunits, sopts) end
    tlen = ncodeunits(target)
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    casefold = get(nctx, :casefold, false) === true
    arrangements = string_bytespans(sopts, casefold)
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

# Returns the options too, as matching may reorder them
function build_choice_matcher(state::ParserState, nctx::NodeCtx, cmatch::ChoiceMatch)
    (; mopts, casefold) = cmatch
    ph = find_window_hash(mopts, casefold, 1)
    minbucketed = if allequal(map(ncodeunits, mopts))
        BUCKETED_MIN_FIXED_OPTIONS
    else
        BUCKETED_MIN_VARIABLE_OPTIONS
    end
    if isnothing(ph) && length(mopts) >= minbucketed
        ph = find_window_hash(mopts, casefold, 2)
    end
    if !isnothing(ph)
        build_hash_matcher(state, nctx, ph, cmatch)
    else
        build_linear_matcher(state, nctx, cmatch)
    end
end

function record_match(cmatch::ChoiceMatch, @nospecialize(index))
    (; fieldvar, record) = cmatch
    if record === :index; :($fieldvar = $index)
    elseif record === :flag; :($fieldvar = one($fieldvar))
    else :() end
end

function build_hash_matcher(state::ParserState, nctx::NodeCtx, ph::HashPlan, cmatch::ChoiceMatch)
    (; casefold, fieldvar, cint) = cmatch
    mopts = cmatch.mopts[ph.perm]
    sopts = cmatch.sopts[ph.perm]
    optlens = Tuple(map(ncodeunits, mopts))
    phoff = ph.pos - 1
    phposexpr = if iszero(phoff); :pos else :(pos + $phoff) end
    load = gen_load(ph.iT, phposexpr)
    foldedload = if iszero(ph.foldmask) load else :($load | $(ph.foldmask % ph.iT)) end
    hashval = hashexpr(ph, foldedload)
    minoptlen = minimum(ncodeunits, mopts)
    maxoptlen = maximum(ncodeunits, mopts)
    variable_len = minoptlen != maxoptlen
    # For injective hashes, skip bytes already validated by the hash window
    hash_skip = if ph.injective
        find_best_hash_skip(minoptlen, phoff, sizeof(ph.iT))
    else
        nothing
    end
    vt = gen_verify_table(mopts, casefold, hash_skip)
    parsed_min = nctx[:current_branch].parsed_min
    tailcheck = if variable_len; gen_tail_verify(mopts, casefold, minoptlen, parsed_min) end
    nopts = length(mopts)
    resolve_i = if isempty(ph.table)
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
    # Any stage may clear `found`, so `guard_append!` nests each later one under `if found`
    parts = ExprVarLine[resolve_i...]
    body = ExprVarLine[]
    guard_append!(stmts) =
        if isempty(body) append!(body, stmts)
        else push!(body, :(if found; $(stmts...) end)) end
    # Stage 1: variable-length option → look up optlen, check available bytes
    if variable_len
        optlencheck = emit_lengthcheck(state, nctx, :optlen, maximum(ncodeunits, mopts))
        append!(body, ExprVarLine[:(optlen = $(optlens)[i]),
                                  :(found = $optlencheck)])
    end
    # Stage 2: byte verification: backward-aligned in one register when what's parsed
    # before covers the read, else widened when that takes fewer registers
    verify(ve) = ExprVarLine[ve.destructure..., :(found = $(if isnothing(tailcheck) ve.checks else :($(ve.checks) && $tailcheck) end))]
    bvc = backward_verify_chunk(minoptlen)
    wide_n = widened(minoptlen)
    if !isnothing(bvc) && !variable_len && parsed_min >= bvc.padding
        guard_append!(verify(gen_backward_verify(mopts, casefold, minoptlen, bvc, fieldvar, hash_skip)))
    elseif isnothing(hash_skip) && !isnothing(wide_n)
        wide = gen_verify_exprs(gen_verify_table(mopts, casefold, nothing, wide_n), fieldvar)
        guard_append!(ExprVarLine[Expr(:if, emit_static_lengthcheck(state, nctx, wide_n),
                                       Expr(:block, verify(wide)...), Expr(:block, verify(gen_verify_exprs(vt, fieldvar))...))])
    elseif !isempty(vt.chunks)
        guard_append!(verify(gen_verify_exprs(vt, fieldvar)))
    elseif !isnothing(tailcheck)
        guard_append!(ExprVarLine[:(found = $tailcheck)])
    end
    # Stage 3: advance pos and record the matched option
    coerced_i = if isempty(ph.table) && ph.iT === cint; :i else :(i % $cint) end
    action = ExprVarLine[:(pos += $(if variable_len; :optlen else minoptlen end); keepbranch()),
                         record_match(cmatch, coerced_i)]
    guard_append!(action)
    push!(parts, :(if found; $(body...) end))
    if !isempty(ph.table2)
        # A slot holds up to two options: when the first fails to verify, try the second.
        retry = copyexprs(body)
        push!(parts, :(if !found && 1 <= hi <= $(length(ph.table2))
                           i = $(Tuple(ph.table2))[hi]
                           found = !iszero(i)
                           if found; $(retry...) end
                       end))
    end
    (parts, mopts, sopts)
end

function build_linear_matcher(state::ParserState, nctx::NodeCtx, cmatch::ChoiceMatch)
    (; mopts, sopts, casefold, cint) = cmatch
    # Sort longest-first for greedy matching when options share prefixes
    perm = sortperm_by(ncodeunits, mopts, true)
    mopts = mopts[perm]
    sopts = sopts[perm]
    # Unrolled if/elseif rather than iterating a tuple of byte-tuples, which boxes.
    # Built last option first by a loop, not a closure: `cint` is a type, which a
    # closure would specialise on.
    chain = nothing
    for i in reverse(eachindex(sopts))
        n = ncodeunits(sopts[i])
        fit = :(nbytes - pos + 1 >= $n)
        nomatch = gen_literal_mismatch(state, nctx, sopts[i], casefold)
        body = quote
            $(record_match(cmatch, :($(i % cint))))
            pos += $n
            keepbranch()
        end
        chain = if isnothing(chain)
            Expr(:if, :($fit && !$nomatch), body)
        else
            Expr(:elseif, :($fit && !$nomatch), body, chain)
        end
    end
    (ExprVarLine[chain], mopts, sopts)
end

## Perfect hashing

const HASH_MULTIPLIERS = (0x9e3779b97f4a7c15, 0x517cc1b727220a95, 0x6c62272e07bb0142)

"""
    hash_candidates(nopts, iT) -> Vector{HashCandidate}

Candidate hashes of a register window of type `iT` over `nopts` options, in search
order: identity (injective: a hit identifies the window value), then for each modulus
in `nopts:2nopts` the mod, shift-mod and multiply-shift-mod families. `maxval` bounds
the hash's output.
"""
function hash_candidates(nopts::Int, iT::DataType)
    w = 8 * sizeof(iT)
    cands = HashCandidate[HashCandidate((WindowHash(1, 0, 0), true, typemax(UInt64) >> (64 - w)))]
    for m in nopts:2nopts
        push!(cands, HashCandidate((WindowHash(1, 0, m), false, UInt64(m))))
        for k in 1:min(w - 1, 16)
            push!(cands, HashCandidate((WindowHash(1, k, m), false, UInt64(m))))
        end
        for c in HASH_MULTIPLIERS, k in max(1, w - 8):w - 1
            push!(cands, HashCandidate((WindowHash(c, k, m), false, UInt64(m))))
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
    find_window_hash(options::Vector{String}, casefold::Bool, depth::Int) -> Union{HashPlan, Nothing}

Search register-sized byte windows over `options`, under the `hash_candidates`
families, for the cheapest hash that puts at most `depth` options in each slot,
cost-ranked direct+injective (0) > direct (1) > small table > large table. Injective
(identity-family) results let `find_best_hash_skip` elide verification bytes the
hash covers. A depth of two serves sets too large for a perfect hash to be found.

Returns `nothing` when no hash is accepted.
"""
function find_window_hash(options::Vector{String}, casefold::Bool, depth::Int)
    nopts = length(options)
    iszero(nopts) && return nothing
    minlen = minimum(ncodeunits, options)
    best, bestcost = nothing, typemax(Int)
    for iT in REGISTER_TYPES
        bwidth = sizeof(iT)
        bwidth > minlen && break
        for pos in 1:minlen - bwidth + 1
            values = UInt64[]
            for opt in options
                v = zero(UInt64)
                for j in 0:bwidth-1
                    b = codeunit(opt, pos + j)
                    v |= UInt64(if casefold; b | 0x20 else b end) << (8j)
                end
                push!(values, v)
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
                classified = classify_window(hvals, pos, iT, foldmask, hash, injective, depth)
                isnothing(classified) && continue
                cost, plan = classified
                if cost < bestcost
                    best, bestcost = plan, cost
                end
                iszero(bestcost) && return best
            end
        end
    end
    best
end

# A plan for hash values `hvals` putting at most `depth` options in a slot, and its cost:
# direct when they're consecutive, so the hash less an offset is the option index, else
# by `table`, and `table2` for the second option in a slot
function classify_window(hvals::Vector{UInt64}, pos::Int, iT::DataType, foldmask::UInt64,
                         hash::WindowHash, injective::Bool, depth::Int)
    nopts = length(hvals)
    sorted_indices = sortperm_by(identity, hvals)
    lo, hi = Int(hvals[first(sorted_indices)]), Int(hvals[last(sorted_indices)])
    if hi - lo + 1 == nopts && allunique(hvals)
        return (Int(!injective), HashPlan(pos, iT, foldmask, hash, lo - 1, sorted_indices, Int[], Int[], injective))
    end
    hi > 4nopts && return nothing
    table, table2 = zeros(Int, hi), zeros(Int, if depth > 1 hi else 0 end)
    for (i, h) in enumerate(hvals)
        slots = if iszero(table[h]) table elseif depth > 1 && iszero(table2[h]) table2 else return nothing end
        slots[h] = i
    end
    # Each second option is a potential extra verify
    (2nopts + hi + count(!iszero, table2), HashPlan(pos, iT, foldmask, hash, 0, collect(1:nopts), table, table2, injective))
end

# The `(offset, width)` span of the hash window to leave unverified that most
# reduces register loads, if any does
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

## Verification codegen
#
# `Any`/`Unsigned` vectors keep the type independent of the options
struct VerifyTable
    verify_table::Vector{Any}
    masks::Vector{Unsigned}
    chunks::Vector{RegisterChunk}
end

"""
    gen_verify_table(options, casefold, skip = nothing, nbytes = minlen) -> VerifyTable

Build per-option register-sized comparison data for verifying hash matches.

Masks use `0xDF` where any option has a casefold alpha byte, `0xFF` for
exact match, `0x00` for overflow. When `skip = (gap_offset, gap_width)`,
the gap region is excluded from verification (used with injective hashes).
These are positional so a `Union`-typed `skip` still dispatches statically.
"""
function gen_verify_table(options::Vector{String}, casefold::Bool,
                          skip::Union{Nothing, Tuple{Int, Int}} = nothing,
                          nbytes::Int = minimum(ncodeunits, options))
    minlen = minimum(ncodeunits, options)
    chunks = if isnothing(skip)
        register_chunks(nbytes)
    else
        # Right-side chunks are offset back to their positions in the option
        gap_offset, gap_width = skip
        left = register_chunks(gap_offset)
        right = register_chunks(minlen - gap_offset - gap_width)
        right_base = gap_offset + gap_width
        for i in eachindex(right)
            right[i] = RegisterChunk((right[i].offset + right_base, right[i].width, right[i].iT))
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
    verify_table = Any[Tuple(Unsigned[pack_bytes(opt, c.offset, min(c.width, max(0, minlen - c.offset)), c.iT) & masks[k]
                                      for (k, c) in enumerate(chunks)])
                       for opt in options]
    VerifyTable(verify_table, masks, chunks)
end

function gen_verify_exprs(vt::VerifyTable, prefix::Symbol; pos_offset::Int = 0)
    cvars = Symbol[Symbol(prefix, "_expect", ci) for ci in eachindex(vt.chunks)]
    destructure = [Expr(:(=), Expr(:tuple, cvars...), :($(Tuple(vt.verify_table))[i]))]
    checks = Expr[]
    for (ci, c) in enumerate(vt.chunks)
        baseoff = c.offset + pos_offset
        posexpr = if iszero(baseoff); :pos else :(pos + $baseoff) end
        push!(checks, gen_masked_compare(c.iT, posexpr, cvars[ci], vt.masks[ci]))
    end
    (; destructure, checks = conjoin(checks))
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
    gen_tail_verify(options, casefold, minoptlen, before) -> Expr

Generate a check of the tail bytes (beyond `minoptlen`) of variable-length options:
one masked compare of the register ending at the option's end, when that stays
within the option and the `before` bytes parsed ahead of it, otherwise a codeunit loop.
"""
function gen_tail_verify(options::Vector{String}, casefold::Bool, minoptlen::Int, before::Int)
    tails = String[opt[minoptlen+1:end] for opt in options]
    taillens = map(ncodeunits, tails)
    maxtail = maximum(taillens)
    # Letters compare casefolded, other bytes exactly, and bytes past a tail not at all
    bytemask(t, j) = if j > ncodeunits(t) 0x00
        elseif casefold && UInt8('a') <= (codeunit(t, j) | 0x20) <= UInt8('z') 0xDF
        else 0xFF end
    iT = register_type(maxtail)
    width = sizeof(iT)
    inreach(k) = before + ncodeunits(options[k]) >= width
    if maxtail <= sizeof(UInt) && all(k -> taillens[k] == 0 || inreach(k), eachindex(options))
        # A tail's bytes sit at the top of the register, compared in a UInt64
        endmask(t) = (m = zero(UInt64); for j in 1:ncodeunits(t); m |= UInt64(bytemask(t, j)) << (8 * (width - ncodeunits(t) + j - 1)); end; m)
        expected(t) = (pack_bytes(t, 0, ncodeunits(t), UInt64) << (8 * (width - ncodeunits(t)))) & endmask(t)
        # One tail shared by every option with a tail compares as a constant
        nonempty = filter(!isempty, tails)
        shared = if allequal(nonempty) first(nonempty) end
        masks, values = UInt64[], UInt64[]
        for t in tails; push!(masks, endmask(something(shared, t))); push!(values, expected(something(shared, t))) end
        pertail(v) = if isnothing(shared); :($(Tuple(v))[i]) else first(v) end
        check = :($(gen_load(iT, :(pos + optlen - $width))) & $(pertail(masks)) == $(pertail(values)))
        # An option without a tail needs no guard when its own last bytes pass, and
        # needs a branch only when its register might reach before what's been parsed
        passes(k) = taillens[k] > 0 || ncodeunits(options[k]) >= width &&
            pack_bytes(options[k], ncodeunits(options[k]) - width, width, UInt64) & masks[k] == values[k]
        if all(passes, eachindex(options)); check
        elseif all(inreach, eachindex(options)); :((optlen == $minoptlen) | $check)
        else :(optlen == $minoptlen || $check) end
    else
        # Tails are padded to one length so the tables are homogeneous (indexing a tuple
        # of differently-sized tuples by `i` is a runtime field lookup)
        masks = Tuple(Any[Tuple(UInt8[bytemask(t, j) for j in 1:maxtail]) for t in tails])
        bytes = Tuple(Any[Tuple(UInt8[if j <= ncodeunits(t) codeunit(t, j) & masks[k][j] else 0x00 end for j in 1:maxtail])
                          for (k, t) in enumerate(tails)])
        :(all(j -> @inbounds(data[pos + $minoptlen + j - 1]) & $masks[i][j] == $bytes[i][j], 1:$(Tuple(taillens))[i]))
    end
end
