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
function swarparse_consts(T::DataType, base::Int, nd::Int)
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
    ascii_mask, alpha_mask = zero(T), zero(T)
    for i in 0:nd-1
        ascii_mask |= byteval << (8 * (padding + i))
        hex && (alpha_mask |= T(0x40) << (8 * (padding + i)))
    end
    # Reduction steps: binary-tree combine of adjacent digit groups via
    # multiply-shift. At each level, groups of `g` bytes are paired; Cₖ
    # computes `even × base^g + odd` for each pair. An AND mask between
    # steps cleans up inter-lane overflow; the final step omits it.
    nsteps = if nd <= 1 0 else 8 * sizeof(nd) - leading_zeros(nd - 1) end
    steps = Any[]
    for step in 1:nsteps
        g = 1 << (step - 1)
        shift = g * 8
        multiplier = T(base) ^ g * (one(T) << shift) + one(T)
        if step < nsteps
            group_mask = (one(T) << shift) - one(T)
            mask = zero(T)
            for i in 0:(nbytes ÷ (2g))
                mask |= group_mask << (2g * 8 * i)
            end
            push!(steps, (; multiplier, shift, mask))
        else
            push!(steps, (; multiplier, shift))
        end
    end
    (; ascii_mask, alpha_mask, steps)
end

"""
    swar_digitconsts(::Type{T}, base::Int) -> NamedTuple

Compute SWAR digit detection constants for register type `T`.

For base ≤ 10 (nibble check): `(val & (val + addmask) & 0xF0…) ⊻ 0x30…`
is zero per-byte for valid digits.
For base 11–16 (hex): addition-based range checks on both decimal and
alpha ranges after casefolding, using bit 7 as the per-byte indicator.
"""
function swar_digitconsts(T::DataType, base::Int)
    rep = T(0x01) * typemax(T) ÷ typemax(UInt8)  # 0x0101…
    if base <= 10
        (; kind = :nibble,
           addmask  = T(0x10 - base) * rep,
           nibmask  = T(0xF0) * rep,
           expected = T(0x30) * rep)
    else
        alp_start = 0x61
        alp_end = alp_start + base - 10
        (; kind = :hex,
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
function gen_swar_nondigits(T::DataType, var::Symbol, result::Symbol,
                            base::Int)
    c = swar_digitconsts(T, base)
    if c.kind === :nibble
        :($result = ($var & ($var + $(c.addmask)) & $(c.nibmask)) ⊻ $(c.expected))
    else
        dec_ok = gensym("dec")
        alp_ok = gensym("alp")
        av = gensym("folded")
        quote
            $av = $var | $(c.foldmask)
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
function gen_swar_digitcheck(T::DataType, var::Symbol, base::Int, nd::Int, on_fail)
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base)
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
function gen_swar_digitcount(T::DataType, var::Symbol, countvar::Symbol, base::Int, maxdigits::Int)
    nondig = gensym("nondig")
    hibits = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
    result = ExprVarLine[gen_swar_nondig_flags(T, var, nondig, base)]
    if maxdigits < sizeof(T)
        push!(result, :($nondig |= $(~((one(T) << (8 * maxdigits)) - one(T)) & hibits)))
    end
    push!(result, :($countvar = trailing_zeros($nondig) >> 3))
    result
end

# Set bit 7 of each byte of `nondig` whose byte in `var` is not a base-`base` digit
function gen_swar_nondig_flags(T::DataType, var::Symbol, nondig::Symbol, base::Int)
    base > 10 && return gen_swar_nondigits(T, var, nondig, base)
    hibits = T(0x80) * (T(0x01) * typemax(T) ÷ typemax(UInt8))
    rep(b) = T(b) * (hibits >> 7)
    # A non-ASCII byte's carries only reach later lanes
    :($nondig = ((($var + $(rep(0x50))) ⊻ ($var + $(rep(0x50 - base)))) & ~$var & $hibits) ⊻ $hibits)
end

"""
    gen_swarparse(::Type{T}, var, base, nd, decoded = false) -> Vector{ExprVarLine}

Emit the multiply-shift reduction that converts `nd` high-aligned ASCII
digit bytes in `var::T` into an integer value (stored back in `var`).

For hex, applies `(alpha >> 6) * 9` letter correction before reduction.
When `decoded`, the bytes already hold digit values (zero in padding bytes).
"""
function gen_swarparse(T::DataType, var::Symbol, base::Int, nd::Int, decoded::Bool = false)
    c = swarparse_consts(T, base, nd)
    exprs = if decoded ExprVarLine[] else ExprVarLine[:($var &= $(c.ascii_mask))] end
    if !decoded && !iszero(c.alpha_mask)
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
function gen_swar_chunk(cT::DataType, var::Symbol, nd::Int, base::Int, on_fail)
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
        gen_swar_digitcheck(cT, var, base, nd, on_fail)
    end
    parse = if nd == 1 ExprVarLine[] else gen_swarparse(cT, var, base, nd) end
    (check, parse)
end

## Loading strategies

"""
    gen_swar_hiload(state, nctx, var, nd) -> Expr

Emit a high-aligned register load of `nd` bytes from `data` at `pos`: backward,
reading the bytes before as padding, when the branch guarantees them, else
forward-overread or exact sub-loads, as the input's length allows.
"""
function gen_swar_hiload(state::ParserState, nctx::NodeCtx, var::Symbol, nd::Int)
    sT = register_type(nd)
    padding = sizeof(sT) - nd
    backload = :($var = $(gen_load(sT, if iszero(padding); :pos else :(pos - $padding) end)))
    nctx[:current_branch].parsed_min >= padding && return backload
    Expr(:if, emit_static_lengthcheck(state, nctx, sizeof(sT)),
         :($var = $(gen_load(sT, :pos)) << $(8padding)),
         Expr(:if, :(canreadback(data, pos, $padding)), backload, gen_swar_load(sT, var, nd)))
end

# Load exactly `nd` bytes at `pos + offset` into `var::T`, high-aligned, in power-of-2 parts
function gen_swar_load(T::DataType, var::Symbol, nd::Int, offset::Int = 0)
    rhs = nothing
    for c in register_chunks(nd)
        load = gen_load(c.iT, if iszero(offset + c.offset); :pos else :(pos + $(offset + c.offset)) end)
        c.iT === T || (load = :($load % $T))
        shift = 8 * (sizeof(T) - nd + c.offset)
        iszero(shift) || (load = :($load << $shift))
        rhs = if isnothing(rhs) load else :($rhs | $load) end
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
function gen_swar_varload(sT::DataType, var::Symbol, countvar::Symbol,
                          availvar::Symbol, base::Int, maxdigits::Int)
    exprs = ExprVarLine[]
    chunk = prevpow(2, maxdigits)
    # A full register of digits needs none of the smaller chunks
    done_label = if chunk == sizeof(sT) gensym("done_cascade") end
    while chunk >= 1
        cT = register_type(chunk)
        chunk_var, nondig_var = gensym("chunk$(chunk)"), gensym("nondig$(chunk)")
        took = ExprVarLine[:($var |= ($chunk_var % $sT) << (($countvar << 3) & $(8 * sizeof(sT) - 1))),
                           :($countvar += $chunk)]
        chunk == sizeof(sT) && push!(took, :(@goto $done_label))
        push!(exprs, :(if $countvar + $chunk <= $availvar
                           $chunk_var = $(gen_load(cT, :(pos + $countvar)))
                           $(gen_swar_nondigits(cT, chunk_var, nondig_var, base))
                           if iszero($nondig_var); $(took...) end
                       end))
        chunk >>= 1
    end
    isnothing(done_label) || push!(exprs, :(@label $done_label))
    exprs
end

## Strategy dispatch

function gen_rangecheck(state::ParserState, nctx::NodeCtx, var::Symbol, d::DigitSpec)
    (; base, maxdigits, vmin, vmax, pad) = d
    checks = Expr[]
    if vmin > 0
        fail = build_fail_expr!(state, nctx, "Expected at least a value of $(string(vmin; base, pad))")
        push!(checks, :($var >= $vmin || $fail))
    end
    if vmax < Int128(base)^maxdigits - 1
        fail = build_fail_expr!(state, nctx, "Expected at most a value of $(string(vmax; base, pad))")
        push!(checks, :($var <= $vmax || $fail))
    end
    for r in something(d.exclude, UnitRange{Int}[])
        lo, hi = first(r), last(r)
        desc, cond = if lo == hi
            "Value $(string(lo; base, pad)) is excluded", :($var != $lo)
        else
            "Value must not be in $(string(lo; base, pad))-$(string(hi; base, pad))", :($var < $lo || $var > $hi)
        end
        push!(checks, :($cond || $(build_fail_expr!(state, nctx, desc))))
    end
    checks
end

function gen_digit_parseint(state::ParserState, nctx::NodeCtx, d::DigitSpec, fail::Expr)
    (; fieldvar, fnum, base, mindigits, maxdigits, skipbytes) = d
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    scanlimit = emit_lengthbound(state, nctx, maxdigits)
    matchcond = if mindigits == maxdigits
        :($bitsconsumed == $maxdigits)
    elseif mindigits > 1
        :($bitsconsumed >= $mindigits)
    else
        :(!iszero($bitsconsumed))
    end
    fnum_set = if isnothing(skipbytes)
        :(($bitsconsumed, $fnum) = parseint($(d.dI), data, pos, $base, $scanlimit))
    else
        :(($bitsconsumed, $fnum, $(Symbol("$(fieldvar)_scanned"))) =
              parseint($(d.dI), data, pos, $base, $scanlimit, $skipbytes))
    end
    ExprVarLine[fnum_set, :($matchcond || $fail)], fnum
end

function gen_digit_swar_fixed(state::ParserState, nctx::NodeCtx, d::DigitSpec, fail::Expr)
    (; maxdigits, fnum) = d
    chunks = if maxdigits <= sizeof(UInt)
        ((0, maxdigits),)
    else
        ((0, sizeof(UInt)), (sizeof(UInt), maxdigits - sizeof(UInt)))
    end
    ExprVarLine[:($(emit_lengthcheck(state, nctx, maxdigits)) || $fail),
                gen_swar_chunks(state, nctx, chunks, d.base, fnum, d.dI, fail)...], fnum
end

"""
    gen_digit_swar_variable(state, nctx, d, fail) -> (Vector{ExprVarLine}, Symbol)

Variable-width SWAR for digit fields of up to 8 digits in one register;
digits beyond the first 8 continue in `parseint`.

Load strategy preference: backward > forward-overread > cascading exact-loads.
Both runtime and compile-time paths are emitted; `fold_static_branches!`
selects the winner based on resolved length guarantees.
"""
function gen_digit_swar_variable(state::ParserState, nctx::NodeCtx, d::DigitSpec, fail::Expr)
    (; fnum, fieldvar, base, mindigits, maxdigits, pad, dI) = d
    head = Base.min(maxdigits, sizeof(UInt))
    sT = register_type(head)
    nT = if maxdigits == head; sT
    elseif Int128(base)^maxdigits - 1 <= typemax(UInt64); UInt64
    else UInt128 end
    swar_var = Symbol("$(fieldvar)_swar")
    numvar = if nT == sT; swar_var else Symbol("$(fieldvar)_wide") end
    parse_expr = gen_swarparse(sT, swar_var, base, head)
    countvar = Symbol("$(fieldvar)_count")
    countcheck = if mindigits > 1; :($countvar >= $mindigits) else :(!iszero($countvar)) end
    varparse = ExprVarLine[
        # Masked shifts skip Julia's out-of-range handling; a zero count fails regardless
        :($swar_var <<= (($(sizeof(sT)) - $countvar) << 3) & $(8 * sizeof(sT) - 1)),
        parse_expr...]
    if maxdigits > head
        tailcount, tailnum = gensym("tailcount"), gensym("tailnum")
        powers = Tuple(UInt64[UInt64(base)^k for k in 0:maxdigits - head])
        tailmax = :($(emit_lengthbound(state, nctx, maxdigits)) - $head)
        tailparse = if maxdigits - head > 8
            :(($tailcount, $tailnum) = parseint(UInt64, data, pos + $head, $base, $tailmax))
        elseif pad > head
            # Padded values usually come at full width, so a loop over a short tail is predicted
            digit = gensym("digit")
            :(($tailcount, $tailnum) = (0, zero(UInt64));
              while $tailcount < $tailmax && ($digit = byte2int(peekbyte(data, pos + $head + $tailcount), $base)) != 0xff
                  ($tailcount, $tailnum) = ($tailcount + 1, $tailnum * $base + $digit)
              end)
        else
            # One register ending where the tail may, reading back into the head; halved
            # shifts take an empty tail to zero
            tT = register_type(maxdigits - head)
            w = sizeof(tT)
            tail, tailshift, tailnondig = gensym("tail"), gensym("tailshift"), gensym("tailnondig")
            quote
                $tailcount = $tailmax
                $tail = $(gen_load(tT, :(pos + $head + $tailcount - $w)))
                $tailshift = (($w - $tailcount) << 2) & $(8w - 1)
                $tail = ($tail >>> $tailshift) >>> $tailshift
                $(gen_swar_nondig_flags(tT, tail, tailnondig, base))
                $tailcount = trailing_zeros($tailnondig) >> 3
                $tailshift = (($w - $tailcount) << 2) & $(8w - 1)
                $tail = ($tail << $tailshift) << $tailshift
                $(gen_swarparse(tT, tail, base, w)...)
                $tailnum = $tail % UInt64
            end
        end
        push!(varparse, :($numvar = $swar_var % $nT),
              :(if $countvar == $head
                    $tailparse
                    $numvar = $numvar * ($powers[$tailcount + 1] % $nT) + $tailnum
                    $countvar += $tailcount
                end))
    end
    push!(varparse, :($fnum = $(if nT == dI numvar else :($numvar % $dI) end)))
    b = nctx[:current_branch]
    vdjob = (; sT, swar_var, countvar, base, fail,
               mindigits = Base.min(mindigits, head), maxdigits = head,
               availvar = Symbol("$(fieldvar)_avail"),
               avail_bound = emit_lengthbound(state, nctx, head),
               end_min = b.parsed_min + mindigits,
               # Padded values usually come at full width, so at one length
               trailing_free = mindigits < sizeof(UInt) <= maxdigits && pad < maxdigits &&
                   Expr(:call, :__trailing_free, b.id, b.parsed_max + maxdigits))
    load_and_count = if b.parsed_min >= sizeof(sT) - 1
        gen_vardigit_backward(state, nctx, vdjob)
    else
        gen_vardigit_forward(state, nctx, vdjob)
    end
    # A register wider than the value's type is range-checked before truncating wraps it
    ExprVarLine[load_and_count..., varparse..., :($countcheck || $fail),
                :($(Symbol("$(fieldvar)_bitsconsumed")) = $countvar)],
        if nT == dI fnum else numvar end
end

# Backward strategy for variable-width: single wide load ending at
# pos + avail - 1, then right-shift to low-align.
function gen_vardigit_backward(state::ParserState, nctx::NodeCtx, @nospecialize(vdjob))
    (; sT, swar_var, countvar, availvar, end_min, base, mindigits, maxdigits) = vdjob
    b = nctx[:current_branch]
    shift, nondig = Symbol(availvar, :_shift), gensym("nondig")
    hibits = sT(0x80) * (typemax(sT) ÷ typemax(UInt8))
    load = gen_load(sT, :(pos + $availvar - $(sizeof(sT))))
    lowshift = :((($(sizeof(sT)) - $availvar) << 3) & $(8 * sizeof(sT) - 1))
    filled = :(iszero($nondig & ($hibits >>> $shift)))
    scan = :(while $countvar < $availvar && byte2int(@inbounds(data[pos + $countvar]), $base) != 0xff
                 $countvar += 1
             end)
    # Digits usually fill what's available short of the bytes that must follow, counted by
    # length; a loop counting the rest keeps this a branch, where counting in-register
    # would become a cmov, unless taking digits that run on into those bytes keeps it one
    backload = ExprVarLine[
        :($swar_var = $load),
        :($shift = $lowshift),
        :($swar_var >>>= $shift),
        gen_swar_nondig_flags(sT, swar_var, nondig, base),
        :(if $(Expr(:call, :__must_follow, b.id, end_min))
              if $filled && ($availvar == $maxdigits || byte2int(peekbyte(data, pos + $availvar), $base) == 0xff)
                  $countvar = $availvar
              else
                  $countvar = trailing_zeros($nondig) >> 3
                  if $countvar == $availvar
                      $availvar = $(emit_lengthbound(state, nctx, maxdigits))
                      $scan
                      $availvar = $countvar
                      $swar_var = $load >>> $lowshift
                  end
              end
          elseif $filled
              $countvar = $availvar
          else
              $countvar = 0
              $scan
          end)]
    ExprVarLine[:($availvar = $(emit_lengthbound(state, nctx, maxdigits, end_min))),
                :($(emit_lengthcheck(state, nctx, Base.max(mindigits, 1))) || $(vdjob.fail)),
                backload...]
end

# Forward-overread + cascading fallback for variable-width.
# Emits both paths gated by __static_length_check; fold_static_branches! picks the winner.
function gen_vardigit_forward(state::ParserState, nctx::NodeCtx, @nospecialize(vdjob))
    (; sT, swar_var, countvar, availvar, avail_bound, base, mindigits, maxdigits) = vdjob
    # Forward overread: single full-width load at pos, digits at LSB
    wide = Expr(:block,
        :($(emit_lengthcheck(state, nctx, Base.max(mindigits, 1))) || $(vdjob.fail)),
        :($swar_var = $(gen_load(sT, :pos))),
        gen_swar_digitcount(sT, swar_var, countvar, base, maxdigits)...)
    # Cascading power-of-2 exact-loads fallback
    cascade = Expr(:block, :($countvar = 0), :($swar_var = zero($sT)), :($availvar = $avail_bound),
                   gen_swar_varload(sT, swar_var, countvar, availvar, base, maxdigits)...)
    narrow = Expr(:if, :(canreadback(data, pos, $(sizeof(sT) - 1))),
                  Expr(:block, gen_vardigit_backward(state, nctx, vdjob)...), cascade)
    fits = emit_lengthcheck(state, nctx, sizeof(sT))
    # Digits ending the input reach its end, which a backward load serves at any length
    vdjob.trailing_free === false ||
        (fits = :($fits && (!$(vdjob.trailing_free) || !canreadback(data, pos, $(sizeof(sT) - 1)))))
    ExprVarLine[Expr(:if, fits, wide, narrow)]
end

## Top-level digit parse dispatch

# SWAR when base ≤ 16 and the digits fit registers, else a scalar `parseint` scan
function gen_digit_parse(state::ParserState, nctx::NodeCtx, d::DigitSpec)
    (; mindigits, maxdigits, base, skipbytes) = d
    fixedwidth = mindigits == maxdigits
    fail = build_fail_expr!(state, nctx, if fixedwidth && maxdigits > 1
        "exactly $maxdigits digits in base $base"
    elseif mindigits > 1
        "$mindigits to $maxdigits digits in base $base"
    else
        "up to $maxdigits digits in base $base"
    end)
    swar_limit = if fixedwidth 2 * sizeof(UInt) else ndigits(typemax(UInt128); base) - 1 end
    exprs, checkvar = if base > 16
        gen_digit_parseint(state, nctx, d, fail)
    elseif !isnothing(skipbytes)
        # Fixed-width digits with separators anywhere parse like one group of them
        if !isnothing(d.groups) || fixedwidth && maxdigits <= 2 * sizeof(UInt)
            gen_digit_swar_grouped(state, nctx, d, fail)
        else
            gen_digit_parseint(state, nctx, d, fail)
        end
    elseif maxdigits > swar_limit
        gen_digit_parseint(state, nctx, d, fail)
    elseif fixedwidth
        gen_digit_swar_fixed(state, nctx, d, fail)
    else
        gen_digit_swar_variable(state, nctx, d, fail)
    end
    append!(exprs, gen_rangecheck(state, nctx, checkvar, d))
    d.direct || push!(exprs, :($(d.fieldvar) = $(encoding(d))))
    exprs
end

## Multi-chunk SWAR: load → validate → reduce → accumulate

"""
    gen_swar_chunks(state, nctx, chunks, base, resultvar, resultT, on_fail) -> Vector{ExprVarLine}

SWAR parse `chunks` (tuple of `(offset, ndigits)` pairs) and accumulate
their positional integer value into `resultvar::resultT`.
"""
function gen_swar_chunks(state::ParserState, nctx::NodeCtx,
                         @nospecialize(chunks), base::Int, resultvar::Symbol, resultT::DataType,
                         @nospecialize(on_fail))
    exprs = ExprVarLine[]
    for (ci, (offset, nd)) in enumerate(chunks)
        svar = gensym("chunk$ci")
        sT = register_type(nd)
        load = if ci == 1 && iszero(offset)
            gen_swar_hiload(state, nctx, svar, nd)
        else
            gen_swar_load(sT, svar, nd, offset)
        end
        check, parse = gen_swar_chunk(sT, svar, nd, base, on_fail)
        append!(exprs, ExprVarLine[load, check..., parse...])
        val = if sT == resultT svar else :($svar % $resultT) end
        push!(exprs, Expr(:(=), resultvar,
                          if ci == 1 val else :($resultvar * $(resultT(base) ^ nd) + $val) end))
    end
    exprs
end

## Character sequences

# Ranges as `(lo, len, base)`, or `nothing` unless lane-wise indexing is exact: ASCII,
# disjoint once folded, and `base <= lo` so no lane borrows from the next
function swar_charset_spans(ranges::Vector{UnitRange{UInt8}}, casefold::Bool, base::Int)
    spans = Tuple{UInt8, Int, Int}[]
    for r in ranges
        lo, len = if casefold first(r) | 0x20 else first(r) end, length(r)
        (lo + len <= 0x80 && base <= lo) || return nothing
        for (l, n, _) in spans
            lo < l + n && l < lo + len && return nothing
        end
        push!(spans, (lo, len, base))
        base += len
    end
    spans
end

"""
    gen_swar_charseq(var, cT, chunks, spans, casefold, bpc, on_fail[, count]) -> Vector{ExprVarLine}

Parse the characters at `chunks` (`(offset, count ≤ 8)` pairs) into `var::cT` as
`parsechars` would, a register per chunk. With `count = (lenvar, avail)`, instead parse
the valid characters at `pos` in one chunk, at most `avail` of them, counting them in `lenvar`.
"""
function gen_swar_charseq(var::Symbol, cT::DataType, chunks::Vector{Tuple{Int, Int}},
                          spans::Vector{Tuple{UInt8, Int, Int}}, casefold::Bool, bpc::Int,
                          @nospecialize(on_fail), @nospecialize(count = nothing))
    exprs = ExprVarLine[:($var = zero($cT))]
    valid = nothing
    for (start, nd) in chunks
        sT = register_type(nd)
        width = sizeof(sT)
        pad = width - nd
        # `b` in each character lane (a short load fills the high lanes)
        lanes(b) = (m = zero(sT); for i in pad:width-1; m |= sT(b) << 8i; end; m)
        reg, folded, idx, cut = gensym("chars"), gensym("folded"), gensym("indices"), gensym("cut")
        isnothing(count) || push!(exprs, :($cut = ((8 - $(last(count))) << 3) % UInt))
        push!(exprs, if isnothing(count) gen_swar_load(sT, reg, nd, start)
              else :($reg = if canreadback(data, pos + $start, 7); $(gen_load(sT, :(pos + $start + $(last(count)) - 8))) >>> $cut
                            else $(gen_load(sT, :(pos + $start))) & (typemax(UInt64) >>> $cut) end) end,
              :($folded = $(if casefold; :($reg | $(lanes(0x20))) else reg end)))
        # A non-ASCII byte's carries may corrupt neighbouring flags, but it fails its own lane
        # Every valid lane lies in one range: offset by the least, plus its range's excess
        least = minimum(Int[lo - base for (lo, _, base) in spans])
        matched, offsets = nothing, lanes(least)
        for (lo, len, base) in spans
            f = gensym("inrange")
            push!(exprs, :($f = (($folded + $(lanes(0x80 - lo))) ⊻
                                 ($folded + $(lanes(0x80 - lo - len)))) & $(lanes(0x80))))
            matched = if isnothing(matched) f else :($matched | $f) end
            lo - base > least && (offsets = :($offsets + ($f >> 7) * $(sT(lo - base - least))))
        end
        chunkvalid = :($matched & ~$reg == $(lanes(0x80)))
        valid = if isnothing(valid) chunkvalid else :($valid & $chunkvalid) end
        push!(exprs, :($idx = $folded - $offsets))
        if !isnothing(count)
            push!(exprs, :($(first(count)) = trailing_zeros(~($matched & ~$reg) & $(lanes(0x80))) >> 3),
                  :($idx <<= ((8 - $(first(count))) << 3) % UInt))
        end
        # Packing reads indices as base-2^bpc digits (the zero padding lanes as leading
        # zeros); above 4 bits they overflow the reduction's lanes, so merge pairwise
        if bpc <= 4
            append!(exprs, gen_swarparse(sT, idx, 1 << bpc, nd, true))
        else
            half = 8
            while half < 8width
                low = zero(sT)
                for i in 0:2half:8width-1
                    low |= ((one(sT) << half) - one(sT)) << i
                end
                push!(exprs, :($idx = (($idx & $low) << $(bpc * (half ÷ 8))) | (($idx >> $half) & $low)))
                half *= 2
            end
        end
        push!(exprs, :($var = ($var << $(bpc * nd)) | ($idx % $cT)))
    end
    isnothing(count) && push!(exprs, :($valid || $on_fail))
    exprs
end

## Grouped SWAR parse with separator validation

# Compute sub-chunked offsets and separator check expression for grouped fields.
# Groups larger than a register are split into register-sized pieces.
function grouped_chunks_and_check(groups::Vector{Int}, @nospecialize(skipbytes), chunksize::Int = sizeof(UInt))
    sep = first(skipbytes)
    chunks = Tuple{Int, Int}[]
    sep_check = :(true)
    offset = 0
    for (i, gsize) in enumerate(groups)
        for j in 0:cld(gsize, chunksize)-1
            push!(chunks, (offset + chunksize * j, Base.min(chunksize, gsize - chunksize * j)))
        end
        offset += gsize
        i < length(groups) || break
        sep_check = :($sep_check && @inbounds data[pos + $offset] == $sep)
        offset += 1
    end
    (; chunks, sep_check, total_bytes = offset)
end

function gen_digit_swar_grouped(state::ParserState, nctx::NodeCtx, d::DigitSpec, fail::Expr)
    (; fnum, fieldvar, base, maxdigits, dI, skipbytes) = d
    (; chunks, sep_check, total_bytes) = grouped_chunks_and_check(something(d.groups, [maxdigits]), skipbytes)
    # Ungrouped, separators may fall anywhere, so a non-digit leaves the registers for a scan
    regs = gensym("regs")
    swar_body = gen_swar_chunks(state, nctx, chunks, base, fnum, dI,
                                if isnothing(d.groups); :($regs = false) else fail end)
    scanned = Symbol("$(fieldvar)_scanned")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    push!(swar_body, Expr(:(=), scanned, total_bytes))
    scanlimit = emit_lengthbound(state, nctx, maxdigits)
    fallback = ExprVarLine[
        :(($bitsconsumed, $fnum, $scanned) =
            parseint($(dI), data, pos, $base, $scanlimit, $skipbytes)),
        :($bitsconsumed == $maxdigits || $fail)]
    lencheck = emit_lengthcheck(state, nctx, total_bytes)
    result = ExprVarLine[
        :($regs = $lencheck && $sep_check),
        :(if $regs; $(swar_body...) end)]
    # Grouped digits often come without their separators
    if !isnothing(d.groups)
        compact = gen_swar_chunks(state, nctx, grouped_chunks_and_check([maxdigits], skipbytes).chunks,
                                  base, fnum, dI, :($regs = false))
        push!(result, :(if !$regs && $(emit_lengthcheck(state, nctx, maxdigits))
                            $regs = true
                            $(compact...)
                            $scanned = $maxdigits
                        end))
    end
    push!(result, :(if !$regs; $(fallback...) end))
    result, fnum
end

## Reverse-SWAR: spread packed bpc-bit fields to one-per-byte for printing

"""
    gen_reverse_swar(::Type{T}, var, bpc, nfields, ranges) -> Vector{ExprVarLine}

Spread `nfields` packed `bpc`-bit fields (MSB-aligned in `var::T`) into
individual bytes with ASCII offsets from `ranges`, `hton`-ed for storage.
Supports 1 or 2 contiguous ranges; 2-range uses branchless SWAR comparison.
"""
function gen_reverse_swar(T::DataType, var::Symbol, bpc::Int, nfields::Int,
                          @nospecialize(ranges::Tuple{Vararg{UnitRange{UInt8}}}))
    rep = T(0x01) * typemax(T) ÷ typemax(UInt8)
    nbits = 8 * sizeof(T)
    exprs = ExprVarLine[]
    groupsize, groupwidth = nfields, nfields * bpc
    while groupsize > 1
        half = groupsize >> 1
        gap = half * (8 - bpc)
        lomask = (one(T) << (half * bpc)) - one(T)
        mask = zero(T)
        for i in 0:nfields ÷ groupsize - 1
            mask |= lomask << (nbits - i * groupwidth - groupsize * bpc)
        end
        push!(exprs, Expr(:(=), var, :($var & $(~mask) | ($var & $mask) >> $gap)))
        groupwidth = half * 8
        groupsize = half
    end
    push!(exprs, Expr(:(=), var, :($var >> $(8 - bpc) & $(T((1 << bpc) - 1) * rep))))
    base1 = T(first(ranges[1]))
    if length(ranges) == 1
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

