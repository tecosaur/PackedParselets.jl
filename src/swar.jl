# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# SWAR (SIMD-Within-A-Register) digit parsing codegen.
#
# Four layers:
#   1. Constants: precomputed masks and multiply-shift reduction parameters
#   2. Digit detection: codegen for per-byte digit/non-digit classification
#   3. Loading: strategies for getting digit bytes into a register (backward,
#      forward-overread, exact sub-loads, cascading variable-width)
#   4. Strategy dispatch: assemble complete parse expressions for a digit field,
#      choosing between SWAR fixed/variable and scalar parseint fallback

## Constants

"""
    swarparse_consts(::Type{T}, base::Int, nd::Int)
        -> (; ascii_mask::T, alpha_mask::T, steps::Tuple)

Compute SWAR ASCII-to-integer reduction constants for `nd` digit bytes
high-aligned in register type `T`.

The `ascii_mask` simultaneously strips ASCII encoding and zeros garbage
(low) bytes. Each reduction step has `(; multiplier, shift[, mask])` where
`Cₖ = base^g × 2^(g×8) + 1` combines adjacent `g`-byte digit groups via
multiply-shift in O(log nd) steps. The final step omits the cleanup mask.
For hex (base > 10), `alpha_mask` enables letter correction before the
first reduction step.
"""
function swarparse_consts(::Type{T}, base::Int, nd::Int) where {T <: Unsigned}
    nbytes = sizeof(T)
    1 <= nd <= nbytes || throw(ArgumentError(
        "ndigits=$nd must be between 1 and $nbytes for $T"))
    2 <= base <= 16 || throw(ArgumentError(
        "base=$base must be between 2 and 16"))
    hex = base > 10
    padding = nbytes - nd
    # Digit bytes sit in the high positions (byte indices padding:nbytes-1).
    # ASCII mask: 0x0F (or 0x4F for hex) per digit byte, 0x00 per garbage byte.
    byteval = if hex; T(0x4F) else T(0x0F) end
    ascii_mask = reduce(|, (byteval << (8 * (padding + i)) for i in 0:nd-1); init=zero(T))
    alpha_mask = if hex
        reduce(|, (T(0x40) << (8 * (padding + i)) for i in 0:nd-1); init=zero(T))
    else
        zero(T)
    end
    # Reduction steps: binary-tree combine of adjacent digit groups via
    # multiply-shift. At each level, groups of `g` bytes are paired; Cₖ
    # computes `even × base^g + odd` for each pair. An AND mask between
    # steps cleans up inter-lane overflow; the final step omits it.
    nsteps = if nd <= 1 0 else 8 * sizeof(nd) - leading_zeros(nd - 1) end
    steps = map(1:nsteps) do step
        g = 1 << (step - 1)
        shift = g * 8
        scale = T(base) ^ g
        multiplier = scale * (one(T) << shift) + one(T)
        if step < nsteps
            group_mask = (one(T) << shift) - one(T)
            mask = reduce(|, (group_mask << (2g * 8 * i) for i in 0:(nbytes ÷ (2g))); init=zero(T))
            (; multiplier, shift, mask)
        else
            (; multiplier, shift)
        end
    end
    (; ascii_mask, alpha_mask, steps = Tuple(steps))
end

"""
    swar_digitconsts(::Type{T}, base::Int) -> NamedTuple

Compute SWAR digit detection constants for register type `T`.

For base ≤ 10 (nibble check): `(val & (val + addmask) & 0xF0…) ⊻ 0x30…`
is zero per-byte for valid digits.
For base 11–16 (hex): addition-based range checks on both decimal and
alpha ranges after casefolding, using bit 7 as the per-byte indicator.
"""
function swar_digitconsts(::Type{T}, base::Int, hexcase::Symbol = :mixed) where {T <: Unsigned}
    rep = T(0x01) * typemax(T) ÷ typemax(UInt8)  # 0x0101…
    if base <= 10
        (; kind = :nibble,
           addmask  = T(0x10 - base) * rep,
           nibmask  = T(0xF0) * rep,
           expected = T(0x30) * rep)
    else
        alp_start = if hexcase === :upper 0x41 else 0x61 end
        alp_end = alp_start + base - 10
        (; kind = :hex, hexcase,
           foldmask = T(0x20) * rep,
           hibits   = T(0x80) * rep,
           dec_lo   = T(0x80 - 0x30) * rep,
           dec_hi   = T(0x80 - 0x3A) * rep,
           alp_lo   = T(0x80 - alp_start) * rep,
           alp_hi   = T(0x80 - alp_end) * rep)
    end
end

## Digit detection codegen

"""
    gen_swar_nondigits(::Type{T}, var, result, base) -> Expr

Emit an expression computing a non-digit indicator from `var::T` into
`result::T`.

For base ≤ 10, each byte of `result` is zero for valid digits and nonzero
otherwise. For base > 10, bit 7 of each byte is set for non-digits.
"""
function gen_swar_nondigits(::Type{T}, var::Symbol, result::Symbol,
                            base::Int, hexcase::Symbol = :mixed) where {T <: Unsigned}
    c = swar_digitconsts(T, base, hexcase)
    if c.kind === :nibble
        :($result = ($var & ($var + $(c.addmask)) & $(c.nibmask)) ⊻ $(c.expected))
    else
        dec_ok = gensym("dec")
        alp_ok = gensym("alp")
        av = if c.hexcase === :mixed gensym("folded") else var end
        fold = if c.hexcase === :mixed Expr(:(=), av, :($var | $(c.foldmask))) end
        quote
            $fold
            $dec_ok = ($var + $(c.dec_lo)) & ~($var + $(c.dec_hi)) & $(c.hibits)
            $alp_ok = ($av + $(c.alp_lo)) & ~($av + $(c.alp_hi)) & $(c.hibits)
            $result = ($dec_ok | $alp_ok) ⊻ $(c.hibits)
        end
    end
end

"""
    gen_swar_digitcheck(::Type{T}, var, base, nd, on_fail) -> Vector{ExprVarLine}

Check that `nd` high-aligned digit bytes in `var::T` are valid, evaluating
`on_fail` otherwise. When `nd < sizeof(T)`, a mask restricts the check to
the digit bytes only.
"""
function gen_swar_digitcheck(::Type{T}, var::Symbol, base::Int, nd::Int, on_fail,
                              hexcase::Symbol = :mixed) where {T <: Unsigned}
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base, hexcase)
    padding = sizeof(T) - nd
    checkmask = if !iszero(padding)
        padmask = typemax(T) - ((one(T) << (8 * padding)) - one(T))
        if base <= 10
            # Nibble check: nonzero byte means non-digit; mask the high nd bytes
            padmask
        else
            # Hex check: bit 7 per byte; mask high bits of the nd digit bytes
            rep80 = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
            rep80 & padmask
        end
    end
    failcond = if isnothing(checkmask)
        :(!iszero($nondig))
    else
        :(!iszero($nondig & $checkmask))
    end
    ExprVarLine[check_expr, :(if $failcond; $on_fail end)]
end

"""
    gen_swar_digitcount(::Type{T}, var, countvar, base, maxdigits) -> Vector{ExprVarLine}

Count consecutive base-`base` digit bytes from the LSB of `var::T`
(low-aligned). Stores the count (0 to `maxdigits`) in `countvar`.
A sentinel mask beyond `maxdigits` caps the count.
"""
function gen_swar_digitcount(::Type{T}, var::Symbol, countvar::Symbol, base::Int, maxdigits::Int) where {T <: Unsigned}
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base)
    # Set sentinel bits beyond maxdigits to stop counting
    sentinel_expr = if maxdigits < sizeof(T)
        sentinel = ~((one(T) << (8 * maxdigits)) - one(T))
        if base <= 10
            :($nondig |= $sentinel)
        else
            hibits = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
            :($nondig |= $(sentinel & hibits))
        end
    end
    count_assign = if base <= 10
        # haszero trick: sets bit 7 for each ZERO byte, invert to find first non-digit
        rep01 = T(0x01) * typemax(T) ÷ typemax(UInt8)
        rep80 = T(0x80) * rep01
        :($countvar = trailing_zeros(
            (($nondig - $rep01) & ~$nondig & $rep80) ⊻ $rep80) >> 3)
    else
        :($countvar = trailing_zeros($nondig) >> 3)
    end
    result = ExprVarLine[check_expr]
    if !isnothing(sentinel_expr)
        push!(result, sentinel_expr)
    end
    push!(result, count_assign)
    result
end

"""
    gen_swarparse(::Type{T}, var, base, nd) -> Vector{ExprVarLine}

Emit the multiply-shift reduction that converts `nd` high-aligned ASCII
digit bytes in `var::T` into an integer value (stored back in `var`).

For hex, applies `(alpha >> 6) * 9` letter correction before reduction.
"""
function gen_swarparse(::Type{T}, var::Symbol, base::Int, nd::Int) where {T <: Unsigned}
    c = swarparse_consts(T, base, nd)
    exprs = ExprVarLine[:($var &= $(c.ascii_mask))]
    if !iszero(c.alpha_mask)
        alpha = gensym("alpha")
        push!(exprs,
              :($alpha = $var & $(c.alpha_mask)),
              :($var = ($alpha >> 6) * $(T(9)) + ($var ⊻ $alpha)))
    end
    for s in c.steps
        if hasproperty(s, :mask)
            push!(exprs, :($var = (($var * $(s.multiplier)) >> $(s.shift)) & $(s.mask)))
        else
            push!(exprs, :($var = ($var * $(s.multiplier)) >> $(s.shift)))
        end
    end
    exprs
end

"""
    gen_swar_chunk(cT, var, nd, base, on_fail) -> (check, parse)

Generate check + parse expressions for a single SWAR chunk.

Handles 1-digit decimal (sub+cmp), 1-digit hex (casefold+dual range),
and multi-digit (via `gen_swar_digitcheck`/`gen_swarparse`).
"""
function gen_swar_chunk(cT::DataType, var::Symbol, nd::Int, base::Int, on_fail,
                        hexcase::Symbol = :mixed)
    check = if nd == 1 && base <= 10
        ExprVarLine[:($var = ($var - $(UInt8('0'))) % $cT),
                    :(if $var >= $(cT(base)); $on_fail end)]
    elseif nd == 1
        folded = gensym("folded")
        ExprVarLine[:($folded = ($var | 0x20) % $cT),
                    :($var = $folded - $(cT(0x30))),
                    :(if $var > $(cT(9))
                          $var = $folded - $(cT(0x61 - 10))
                          if $var < $(cT(10)) || $var >= $(cT(base))
                              $on_fail
                          end
                      end)]
    else
        gen_swar_digitcheck(cT, var, base, nd, on_fail, hexcase)
    end
    parse = if nd == 1 ExprVarLine[] else gen_swarparse(cT, var, base, nd) end
    (check, parse)
end

## Loading strategies

"""
    gen_swar_hiload(state, nctx, var, nd) -> (sT, Expr)

Emit a high-aligned register load of `nd` bytes from `data` at `pos`,
choosing the optimal strategy (backward, forward-overread, or exact sub-loads)
based on the current branch's byte guarantee. Returns `(register_type, load_expr)`.
"""
function gen_swar_hiload(state::ParserState, nctx::NodeCtx, var::Symbol, nd::Int)
    sT = register_type(nd)
    b = nctx[:current_branch]
    backward = b.parsed_min >= sizeof(sT) - nd
    load = if !backward && nd < sizeof(sT)
        shift = 8 * (sizeof(sT) - nd)
        Expr(:if, emit_static_lengthcheck(state, nctx, sizeof(sT)),
             :($var = htol(Base.unsafe_load(Ptr{$sT}(pointer(data, pos)))) << $shift),
             gen_swar_load(sT, var, nd, false))
    else
        gen_swar_load(sT, var, nd, backward)
    end
    sT, load
end

"""
    gen_swar_load(::Type{T}, var, nd, backward) -> Expr

Load `nd` digit bytes from `data` at `pos` into `var::T`, high-aligned.

Three strategies:
- Full-width (`nd == sizeof(T)`): single load, no padding needed.
- Backward (`nd < sizeof(T)`, `backward=true`): single wide load ending at
  the last digit byte, relying on preceding parsed bytes as padding.
- Exact (`nd < sizeof(T)`, `backward=false`): power-of-2 sub-loads shifted
  and ORed together; reads exactly `nd` bytes.
"""
function gen_swar_load(::Type{T}, var::Symbol, nd::Int, backward::Bool, offset::Int=0) where {T}
    posoff(n) = if iszero(n); :pos else :(pos + $n) end
    posexpr = posoff(offset)
    padding = sizeof(T) - nd
    # Full-width: single load, no alignment needed
    if nd == sizeof(T)
        if T === UInt8
            return :($var = @inbounds data[$posexpr])
        end
        return :($var = htol(Base.unsafe_load(Ptr{$T}(pointer(data, $posexpr)))))
    end
    # Backward: single wide load using preceding bytes as padding
    if backward
        return :($var = htol(Base.unsafe_load(Ptr{$T}(pointer(data, $(posoff(offset - padding)))))))
    end
    # Exact: decompose nd into power-of-2 chunks, shift each to its
    # high-aligned position and OR together
    chunks = Tuple{Int,Int}[]  # (chunk_bytes, string_offset)
    remaining, coff = nd, 0
    while remaining > 0
        chunk = 1 << (8 * sizeof(remaining) - 1 - leading_zeros(remaining))
        push!(chunks, (chunk, coff))
        coff += chunk
        remaining -= chunk
    end
    parts = map(chunks) do (chunk, off)
        bit_shift = 8 * (padding + off)
        cT = register_type(chunk)
        cposexpr = posoff(offset + off)
        load = if cT === UInt8
            :($T(@inbounds data[$cposexpr]))
        else
            :(htol(Base.unsafe_load(Ptr{$cT}(pointer(data, $cposexpr)))) % $T)
        end
        if iszero(bit_shift) load else :($load << $bit_shift) end
    end
    rhs = parts[1]
    for i in 2:length(parts)
        rhs = :($rhs | $(parts[i]))
    end
    :($var = $rhs)
end

"""
    gen_swar_varload(::Type{sT}, var, countvar, availvar, base, maxdigits)
        -> Vector{ExprVarLine}

Generate a cascading variable-width load for SWAR digit parsing.

Decomposes `maxdigits` into descending power-of-2 chunks, each conditionally
loaded and digit-checked. After execution, `var` holds digit bytes low-aligned
and `countvar` holds the count (0 to `maxdigits`). References `data`, `pos`,
and `availvar` from the enclosing parse context.
"""
function gen_swar_varload(::Type{sT}, var::Symbol, countvar::Symbol,
                          availvar::Symbol, base::Int, maxdigits::Int) where {sT <: Unsigned}
    @assert sizeof(sT) >= maxdigits "gen_swar_varload requires sizeof(sT) >= maxdigits"
    chunks = Int[]
    c = 1 << (8 * sizeof(maxdigits) - 1 - leading_zeros(maxdigits))
    while c >= 1
        push!(chunks, c)
        c >>= 1
    end
    has_full = !isempty(chunks) && first(chunks) == sizeof(sT)
    done_label = if has_full gensym("done_cascade") end
    exprs = gen_varload_chunks(sT, var, countvar, availvar, base, maxdigits, chunks, done_label)
    if !isnothing(done_label)
        push!(exprs, :(@label $done_label))
    end
    exprs
end

# Generate cascading load-check-accumulate blocks for the given chunk sequence.
# When `done_label` is provided, the full-register success path jumps to it
# instead of duplicating the sub-chunk code in both if/else branches.
function gen_varload_chunks(::Type{sT}, var::Symbol, countvar::Symbol,
                             availvar::Symbol, base::Int, maxdigits::Int,
                             chunks::AbstractVector{Int},
                             done_label::Union{Symbol,Nothing}) where {sT <: Unsigned}
    isempty(chunks) && return ExprVarLine[]
    chunk = first(chunks)
    rest = @view chunks[2:end]
    cT = register_type(chunk)
    chunk_var = gensym("chunk$(chunk)")
    nondig_var = gensym("nondig$(chunk)")
    load_expr = if cT === UInt8
        :($chunk_var = @inbounds data[pos + $countvar])
    else
        :($chunk_var = htol(Base.unsafe_load(Ptr{$cT}(pointer(data, pos + $countvar)))))
    end
    nondig_raw = gen_swar_nondigits(cT, chunk_var, nondig_var, base)
    nondig_stmts = if Meta.isexpr(nondig_raw, :block)
        filter(e -> !(e isa LineNumberNode), nondig_raw.args)
    else
        ExprVarLine[nondig_raw]
    end
    accum = :($var |= ($chunk_var % $sT) << ($countvar << 3))
    advance = :($countvar += $chunk)
    rest_exprs = gen_varload_chunks(sT, var, countvar, availvar, base, maxdigits, rest, nothing)
    if chunk == sizeof(sT) && !isnothing(done_label)
        # Full-register chunk: on success, jump past sub-chunks;
        # on failure or insufficient bytes, fall through to sub-chunks (emitted once).
        ExprVarLine[:(if $countvar + $chunk <= $availvar
                          $load_expr
                          $(nondig_stmts...)
                          if iszero($nondig_var)
                              $accum
                              $advance
                              @goto $done_label
                          end
                      end),
                    rest_exprs...]
    else
        # Sub-register chunk: independent check, then continue to next chunk
        ExprVarLine[:(if $countvar + $chunk <= $availvar
                          $load_expr
                          $(nondig_stmts...)
                          if iszero($nondig_var)
                              $accum
                              $advance
                          end
                      end),
                    rest_exprs...]
    end
end

## Strategy dispatch

# Shared vocabulary for all digit-parse strategies: symbols, encoding
# expressions, range checks, and error messages. Used by the three
# strategy functions below.
function gen_rangecheck(state::ParserState, nctx::NodeCtx, var::Symbol, dspec::NamedTuple)
    (; base, maxdigits, vmin, vmax, pad, exclude) = dspec
    checks = Expr[]
    if vmin > 0
        fail = build_fail_expr!(state, nctx, "Expected at least a value of $(string(vmin; base, pad))")
        push!(checks, :($var >= $vmin || $fail))
    end
    if vmax < Int128(base)^maxdigits - 1
        fail = build_fail_expr!(state, nctx, "Expected at most a value of $(string(vmax; base, pad))")
        push!(checks, :($var <= $vmax || $fail))
    end
    if !isnothing(exclude)
        for r in exclude
            lo, hi = first(r), last(r)
            desc = if lo == hi
                "Value $(string(lo; base, pad)) is excluded"
            else
                "Value must not be in $(string(lo; base, pad))-$(string(hi; base, pad))"
            end
            fail = build_fail_expr!(state, nctx, desc)
            check = if lo == hi
                :($var != $lo || $fail)
            else
                :(($var < $lo || $var > $hi) || $fail)
            end
            push!(checks, check)
        end
    end
    isempty(checks) ? :() : Expr(:block, checks...)
end

function compute_digit_vocab(state::ParserState, nctx::NodeCtx,
                             fieldvar::Symbol, option, dspec::NamedTuple)
    (; base, mindigits, maxdigits, vmin, vmax, dI, dT, claims_sentinel) = dspec
    fixedwidth = mindigits == maxdigits
    fnum = Symbol("$(fieldvar)_num")
    # numexpr: transform raw fnum into the stored representation
    directval = cardbits(vmax - vmin + 1 + claims_sentinel) ==
                cardbits(vmax + 1) && (vmin > 0 || !claims_sentinel)
    numexpr = if directval
        if dI != dT; :($fnum % $dT) else fnum end
    elseif iszero(vmin) && claims_sentinel
        :($fnum + $(one(dT)))
    elseif vmin - claims_sentinel > 0
        :(($fnum - $(dT(vmin - claims_sentinel))) % $dT)
    else
        if dI != dT; :($fnum % $dT) else fnum end
    end
    directvar = numexpr === fnum
    parsevar = if directvar; fnum else fieldvar end
    rangecheck = gen_rangecheck(state, nctx, fnum, dspec)
    fail_expr = build_fail_expr!(state, nctx, if fixedwidth && maxdigits > 1
        "exactly $maxdigits digits in base $base"
    elseif mindigits > 1
        "$mindigits to $maxdigits digits in base $base"
    else
        "up to $maxdigits digits in base $base"
    end)
    (; fnum, fieldvar, parsevar, directvar, numexpr, rangecheck,
       fail_expr, option, dT)
end

# Scalar `parseint` fallback for digit fields where SWAR isn't applicable.
function gen_digit_parseint(state::ParserState, nctx::NodeCtx,
                            vocab, dspec::NamedTuple)
    (; fnum, fail_expr, rangecheck, directvar, fieldvar, numexpr) = vocab
    (; base, mindigits, maxdigits, skipbytes) = dspec
    fixedwidth = mindigits == maxdigits
    bitsconsumed = Symbol("$(vocab.fieldvar)_bitsconsumed")
    scanlimit = emit_lengthbound(state, nctx, maxdigits)
    matchcond = if fixedwidth
        :($bitsconsumed == $maxdigits)
    elseif mindigits > 1
        :($bitsconsumed >= $mindigits)
    else
        :(!iszero($bitsconsumed))
    end
    fnum_set = if isnothing(skipbytes)
        :(($bitsconsumed, $fnum) = parseint($(dspec.dI), data, pos, $base, $scanlimit))
    else
        scanned = Symbol("$(vocab.fieldvar)_scanned")
        :(($bitsconsumed, $fnum, $scanned) = parseint($(dspec.dI), data, pos, $base, $scanlimit, $skipbytes))
    end
    result = ExprVarLine[fnum_set, :($matchcond || $fail_expr)]
    rangecheck != :() && push!(result, rangecheck)
    if !directvar; push!(result, :($fieldvar = $numexpr)) end
    result
end


"""
    gen_digit_swar_fixed(vocab, dspec, state, nctx) -> Vector{ExprVarLine}

Fixed-width SWAR for 1–16 digit fields.
"""
function gen_digit_swar_fixed(state::ParserState, nctx::NodeCtx,
                              vocab, dspec::NamedTuple)
    (; fnum, fail_expr, rangecheck, directvar, fieldvar, numexpr) = vocab
    (; base, maxdigits, dI) = dspec
    chunksize = sizeof(UInt)
    chunks = if maxdigits <= chunksize
        ((0, maxdigits),)
    else
        ((0, chunksize), (chunksize, maxdigits - chunksize))
    end
    b = nctx[:current_branch]
    len_check = Expr(:call, :__length_check, b.id, b.parsed_max, maxdigits, maxdigits, maxdigits)
    result = ExprVarLine[:($len_check || $fail_expr)]
    append!(result, gen_swar_chunks(state, nctx, chunks, base, fnum, dI,
                                    fail_expr, :mul_add))
    rangecheck != :() && push!(result, rangecheck)
    if !directvar; push!(result, :($fieldvar = $numexpr)) end
    result
end

"""
    gen_digit_swar_variable(vocab, dspec, state, nctx) -> Vector{ExprVarLine}

Variable-width SWAR for 2–8 digit fields.

Load strategy preference: backward > forward-overread > cascading exact-loads.
Both runtime and compile-time paths are emitted; `fold_static_branches!`
selects the winner based on resolved length guarantees.
"""
function gen_digit_swar_variable(state::ParserState, nctx::NodeCtx,
                                 vocab, dspec::NamedTuple)
    (; fnum, fail_expr, fieldvar) = vocab
    (; base, mindigits, maxdigits, dI) = dspec
    sT = register_type(Base.min(maxdigits, sizeof(UInt)))
    swar_var = Symbol("$(fieldvar)_swar")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    parse_expr = gen_swarparse(sT, swar_var, base, maxdigits)
    countvar = Symbol("$(fieldvar)_count")
    countcheck = if mindigits > 1; :($countvar >= $mindigits) else :(!iszero($countvar)) end
    swar_cast_var = if sT == dI; swar_var else :($swar_var % $dI) end
    varparse = ExprVarLine[
        :($swar_var <<= ($(sizeof(sT)) - $countvar) << 3),
        parse_expr...,
        :($fnum = $swar_cast_var)]
    b = nctx[:current_branch]
    backward = b.parsed_min >= sizeof(sT) - 1
    vdjob = (; sT, swar_var, countvar,
               availvar = Symbol("$(fieldvar)_avail"),
               avail_bound = emit_lengthbound(state, nctx, maxdigits))
    load_and_count = if backward
        gen_vardigit_backward(state, nctx, vocab, dspec, vdjob, b)
    else
        gen_vardigit_forward(state, nctx, vocab, dspec, vdjob, b)
    end
    (; rangecheck, directvar, fieldvar, numexpr, fail_expr) = vocab
    # When the SWAR register is wider than dI, the range check must test
    # swar_var (full width) rather than fnum (after truncation), since
    # values like 256 would wrap to 0 in a UInt8 and pass a <= 255 check.
    pre_rangecheck = if sT != dI
        gen_rangecheck(state, nctx, swar_var, dspec)
    else
        rangecheck
    end
    result = ExprVarLine[load_and_count...,
                :($countcheck || $fail_expr),
                varparse...,
                :($bitsconsumed = $countvar)]
    pre_rangecheck != :() && push!(result, pre_rangecheck)
    if !directvar; push!(result, :($fieldvar = $numexpr)) end
    result
end

# Backward strategy for variable-width: single wide load ending at
# pos + avail - 1, then right-shift to low-align. Branchless digit count.
function gen_vardigit_backward(::ParserState, nctx::NodeCtx,
                                vocab, dspec::NamedTuple, vdjob, b::ParseBranch)
    (; sT, swar_var, countvar, availvar, avail_bound) = vdjob
    (; base, mindigits, maxdigits) = dspec
    backload = ExprVarLine[
        :($swar_var = htol(Base.unsafe_load(
            Ptr{$sT}(pointer(data, pos + $availvar - $(sizeof(sT))))))),
        :($swar_var >>>= ($(sizeof(sT)) - $availvar) << 3),
        gen_swar_digitcount(sT, swar_var, countvar, base, maxdigits)...]
    guard_n = Base.max(mindigits, 1)
    guard_check = Expr(:call, :__length_check, b.id, b.parsed_max, guard_n, guard_n, guard_n)
    ExprVarLine[:($availvar = $avail_bound),
                :($guard_check || $(vocab.fail_expr)),
                backload...]
end

# Forward-overread + cascading fallback for variable-width.
# Emits both paths gated by __static_length_check; fold_static_branches! picks the winner.
function gen_vardigit_forward(state::ParserState, nctx::NodeCtx,
                               vocab, dspec::NamedTuple, vdjob, b::ParseBranch)
    (; sT, swar_var, countvar, availvar, avail_bound) = vdjob
    (; base, mindigits, maxdigits) = dspec
    # Forward overread: single full-width load at pos, digits at LSB
    fwdload = ExprVarLine[
        :($swar_var = htol(Base.unsafe_load(Ptr{$sT}(pointer(data, pos))))),
        gen_swar_digitcount(sT, swar_var, countvar, base, maxdigits)...]
    guard_n = Base.max(mindigits, 1)
    guard_check = Expr(:call, :__length_check, b.id, b.parsed_max, guard_n, guard_n, guard_n)
    fwd_guarded = ExprVarLine[:($guard_check || $(vocab.fail_expr)), fwdload...]
    # Cascading power-of-2 exact-loads fallback
    varload = gen_swar_varload(sT, swar_var, countvar, availvar, base, maxdigits)
    cascade = ExprVarLine[:($countvar = 0), :($swar_var = zero($sT)),
                          :($availvar = $avail_bound), varload...]
    wide = Expr(:block, fwd_guarded...)
    narrow = Expr(:block, cascade...)
    ExprVarLine[Expr(:if, emit_static_lengthcheck(state, nctx, sizeof(sT)), wide, narrow)]
end

## Top-level digit parse dispatch

"""
    gen_digit_parse(state, nctx, fieldvar, option, dspec)
        -> (; exprs::Vector{ExprVarLine}, parsevar::Symbol, directvar::Bool)

Dispatch digit parsing: SWAR fixed/variable when base ≤ 16 and digit count
is within register limits, scalar `parseint` otherwise.
"""
function gen_digit_parse(state::ParserState, nctx::NodeCtx,
                         fieldvar::Symbol, option,
                         dspec::NamedTuple)
    vocab = compute_digit_vocab(state, nctx, fieldvar, option, dspec)
    (; mindigits, maxdigits, base, skipbytes, groups) = dspec
    fixedwidth = mindigits == maxdigits
    swar_limit = if fixedwidth 2 * sizeof(UInt) else sizeof(UInt) end
    use_swar = base <= 16 && maxdigits <= swar_limit && isnothing(skipbytes)
    use_grouped_swar = !isnothing(groups) && base <= 16
    exprs = if use_grouped_swar
        gen_digit_swar_grouped(state, nctx, vocab, dspec)
    elseif !use_swar
        gen_digit_parseint(state, nctx, vocab, dspec)
    elseif fixedwidth
        gen_digit_swar_fixed(state, nctx, vocab, dspec)
    else
        gen_digit_swar_variable(state, nctx, vocab, dspec)
    end
    (; exprs, vocab.parsevar, vocab.directvar)
end

## Multi-chunk SWAR: load → validate → reduce → accumulate

"""
    gen_swar_chunks(state, nctx, chunks, base, resultvar, resultT, on_fail,
                    accum, hexcase) -> Vector{ExprVarLine}

SWAR parse `chunks` (tuple of `(offset, ndigits)` pairs) and accumulate
into `resultvar::resultT`. `accum` is `:shift_or` (charseq bit-packing)
or `:mul_add` (positional integer value).
"""
function gen_swar_chunks(state::ParserState, nctx::NodeCtx,
                         chunks, base::Int, resultvar::Symbol, resultT::DataType,
                         on_fail, accum::Symbol, hexcase::Symbol = :mixed)
    bpc = cardbits(base)
    exprs = ExprVarLine[]
    digits_remaining = sum(last, chunks)
    for (ci, (offset, nd)) in enumerate(chunks)
        svar = gensym("chunk$ci")
        sT = register_type(nd)
        load = if ci == 1 && iszero(offset)
            _, l = gen_swar_hiload(state, nctx, svar, nd)
            l
        else
            gen_swar_load(sT, svar, nd, false, offset)
        end
        check, parse = gen_swar_chunk(sT, svar, nd, base, on_fail, hexcase)
        append!(exprs, ExprVarLine[load, check..., parse...])
        digits_remaining -= nd
        val = if sT == resultT svar else :($svar % $resultT) end
        expr = if accum === :shift_or
            nbits = digits_remaining * bpc
            if ci == 1 && iszero(nbits) val
            elseif ci == 1; :($val << $nbits)
            elseif iszero(nbits); :($resultvar | $val)
            else :($resultvar | $val << $nbits) end
        else
            if ci == 1 val
            else :($resultvar * $(resultT(base) ^ nd) + $val) end
        end
        push!(exprs, Expr(:(=), resultvar, expr))
    end
    exprs
end

## Grouped SWAR parse with separator validation

# Compute sub-chunked offsets and separator check expression for grouped fields.
# Groups larger than a register are split into register-sized pieces.
function grouped_chunks_and_check(groups, skipbytes, chunksize::Int = sizeof(UInt))
    sep = first(skipbytes)
    ngroups = length(groups)
    total_bytes = sum(groups) + ngroups - 1
    offsets = let off = 0
        ntuple(ngroups) do i
            o = off; off += groups[i] + (i < ngroups); o
        end
    end
    chunks = Tuple(
        (offsets[i] + chunksize * j, Base.min(chunksize, groups[i] - chunksize * j))
        for i in 1:ngroups for j in 0:cld(groups[i], chunksize)-1)
    sep_check = foldl(1:ngroups-1; init=:(true)) do acc, i
        :($acc && @inbounds data[pos + $(offsets[i] + groups[i])] == $sep)
    end
    (; chunks, sep_check, total_bytes)
end

function gen_digit_swar_grouped(state::ParserState, nctx::NodeCtx,
                                vocab, dspec::NamedTuple)
    (; fnum, fail_expr, rangecheck, directvar, fieldvar, numexpr) = vocab
    (; base, maxdigits, dI, groups, skipbytes) = dspec
    (; chunks, sep_check, total_bytes) = grouped_chunks_and_check(groups, skipbytes)
    swar_body = gen_swar_chunks(state, nctx, chunks, base, fnum, dI,
                                fail_expr, :mul_add)
    scanned = Symbol("$(fieldvar)_scanned")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    push!(swar_body, Expr(:(=), scanned, total_bytes))
    scanlimit = emit_lengthbound(state, nctx, maxdigits)
    fallback = ExprVarLine[
        :(($bitsconsumed, $fnum, $scanned) =
            parseint($(dI), data, pos, $base, $scanlimit, $skipbytes)),
        :($bitsconsumed == $maxdigits || $fail_expr)]
    lencheck = emit_lengthcheck(state, nctx, total_bytes)
    result = ExprVarLine[
        :(if $lencheck && $sep_check
              $(swar_body...)
          else
              $(fallback...)
          end)]
    rangecheck != :() && push!(result, rangecheck)
    if !directvar; push!(result, :($fieldvar = $numexpr)) end
    result
end

## Reverse-SWAR: spread packed bpc-bit fields to one-per-byte for printing

"""
    gen_reverse_swar(::Type{T}, var, bpc, nfields, ranges) -> Vector{ExprVarLine}

Spread `nfields` packed `bpc`-bit fields (MSB-aligned in `var::T`) into
individual bytes with ASCII offsets from `ranges`, `hton`-ed for storage.
Supports 1 or 2 contiguous ranges; 2-range uses branchless SWAR comparison.
"""
function gen_reverse_swar(::Type{T}, var::Symbol, bpc::Int, nfields::Int,
                          ranges::NTuple{N, UnitRange{UInt8}}) where {T <: Unsigned, N}
    rep = T(0x01) * typemax(T) ÷ typemax(UInt8)
    nbits = 8 * sizeof(T)
    exprs = ExprVarLine[]
    groupsize, groupwidth = nfields, nfields * bpc
    while groupsize > 1
        half = groupsize >> 1
        gap = half * (8 - bpc)
        lomask = (one(T) << (half * bpc)) - one(T)
        mask = reduce(|, lomask << (nbits - i * groupwidth - groupsize * bpc)
                      for i in 0:nfields ÷ groupsize - 1; init=zero(T))
        push!(exprs, Expr(:(=), var, :($var & $(~mask) | ($var & $mask) >> $gap)))
        groupwidth = half * 8
        groupsize = half
    end
    push!(exprs, Expr(:(=), var, :($var >> $(8 - bpc) & $(T((1 << bpc) - 1) * rep))))
    base1 = T(first(ranges[1]))
    if N == 1
        push!(exprs, Expr(:(=), var, :(hton($var + $(base1 * rep)))))
    else
        len1 = T(length(ranges[1]))
        delta = T(first(ranges[2])) - base1 - len1
        hibits = T(0x80) * rep
        mvar = gensym("rmask")
        # (⊻ must be parenthesised: & binds tighter)
        push!(exprs, Expr(:(=), mvar, :(($var | $hibits - $(len1 * rep) ⊻ $var) & $hibits)))
        push!(exprs, Expr(:(=), var, :(hton($var + $(base1 * rep) + $mvar >> 7 * $delta))))
    end
    exprs
end

