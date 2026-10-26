# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# SWAR (SIMD-Within-A-Register) codegen for digits and character sequences.

## Constants

# Byte `b` in every lane of a `T`
bytelanes(T::DataType, b::Integer) = T(b) * (typemax(T) ÷ typemax(UInt8))

## Digit detection codegen

"""
    gen_swar_nondigits(::Type{T}, var, result, base) -> Expr

For base ≤ 10, each byte of `result` is zero for valid digits and nonzero
otherwise. For base > 10, bit 7 of each byte is set for non-digits.
"""
function gen_swar_nondigits(T::DataType, var::Symbol, result::Symbol, base::Int)
    base <= 10 &&
        return :($result = ($var & ($var + $(bytelanes(T, 0x10 - base))) & $(bytelanes(T, 0xf0))) ⊻ $(bytelanes(T, 0x30)))
    :($result = digitflags($var, $base))
end

"""
    gen_swar_digitcheck(::Type{T}, var, base, nd, on_fail) -> Vector{ExprVarLine}

Check that `nd` high-aligned digit bytes in `var::T` are valid, evaluating
`on_fail` otherwise.
"""
function gen_swar_digitcheck(T::DataType, var::Symbol, base::Int, nd::Int, on_fail)
    nondig = gensym("nondig")
    check_expr = gen_swar_nondigits(T, var, nondig, base)
    padding = sizeof(T) - nd
    checkmask = if !iszero(padding)
        padmask = typemax(T) - ((one(T) << (8 * padding)) - one(T))
        if base <= 10
            padmask
        else
            bytelanes(T, 0x80) & padmask
        end
    end
    failcond = if isnothing(checkmask)
        :(!iszero($nondig))
    else
        :(!iszero($nondig & $checkmask))
    end
    ExprVarLine[check_expr, :(if $failcond; $on_fail end)]
end

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
    parse = if nd == 1 ExprVarLine[] else ExprVarLine[:($var = swarparse($var, $base, $nd))] end
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
    chunks = grouped_chunks_and_check([maxdigits], nothing).chunks
    ExprVarLine[:($(emit_lengthcheck(state, nctx, maxdigits)) || $fail),
                gen_swar_chunks(state, nctx, chunks, d.base, fnum, d.dI, fail)...], fnum
end

"""
    gen_digit_swar_variable(state, nctx, d, fail) -> (Vector{ExprVarLine}, Symbol)

Variable-width SWAR for digit fields of up to 8 digits in one register;
digits beyond the first 8 continue in `parseint`.

Load strategy preference: backward > forward-overread > exact loads.
Both runtime and compile-time paths are emitted; `fold_branches!` drops those
the resolved length guarantees rule out.
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
    countvar = Symbol("$(fieldvar)_count")
    countcheck = if mindigits > 1; :($countvar >= $mindigits) else :(!iszero($countvar)) end
    varparse = ExprVarLine[
        # Masked shifts skip Julia's out-of-range handling; a zero count fails regardless
        :($swar_var <<= (($(sizeof(sT)) - $countvar) << 3) & $(8 * sizeof(sT) - 1)),
        :($swar_var = swarparse($swar_var, $base, $head))]
    if maxdigits > head
        tailcount, tailnum = gensym("tailcount"), gensym("tailnum")
        powers = Tuple(UInt64[UInt64(base)^k for k in 0:maxdigits - head])
        tailmax = :($(emit_lengthbound(state, nctx, maxdigits)) - $head)
        tailparse = if maxdigits - head > 8
            :(($tailcount, $tailnum) = parseint(UInt64, data, pos + $head, $base, $tailmax))
        elseif pad > head
            # Padded values usually come at full width, so a loop over a short tail is predicted
            :(($tailcount, $tailnum) = digittail_scan(data, pos + $head, $tailmax, $base))
        else
            :(($tailcount, $tailnum) = digittail_word($(register_type(maxdigits - head)), data, pos + $head, $tailmax, $base))
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
    end_min = b.parsed_min + mindigits
    # Bytes before `pos` already parsed can be read back over by any input
    backward = b.parsed_min >= sizeof(sT) - 1
    wide = !backward && emit_lengthcheck(state, nctx, sizeof(sT))
    # Digits ending the input reach its end, which a backward load serves at any length, and
    # padded values usually come at full width, so at one length
    if !backward && mindigits < sizeof(UInt) <= maxdigits && pad < maxdigits
        wide = :($wide && (!$(Expr(:call, :__trailing_free, b.id, b.parsed_max + maxdigits)) || !canreadback(data, pos, $(sizeof(sT) - 1))))
    end
    run = :(if $wide
        ($swar_var, $countvar) = digitrun_forward($sT, data, pos, $head, $base)
    else
        $(emit_lengthcheck(state, nctx, Base.max(Base.min(mindigits, head), 1))) || $fail
        ($swar_var, $countvar) = digitrun_backward($sT, data, pos, $(emit_lengthbound(state, nctx, head, end_min)), $head, $base,
                                                   $(Expr(:call, :__must_follow, b.id, end_min)), $(!backward))
    end)
    # A register wider than the value's type is range-checked before truncating wraps it
    ExprVarLine[run, varparse..., :($countcheck || $fail),
                :($(Symbol("$(fieldvar)_bitsconsumed")) = $countvar)],
        if nT == dI fnum else numvar end
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

# Parse the digits at `chunks` (`(offset, ndigits)` pairs) into `resultvar::resultT`
function gen_swar_chunks(state::ParserState, nctx::NodeCtx,
                         chunks::Vector{Tuple{Int, Int}}, base::Int, resultvar::Symbol, resultT::DataType,
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
            push!(exprs, :($idx = swarparse($idx, $(1 << bpc), $nd, true)))
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

# Groups larger than a register are split into register-sized chunks
function grouped_chunks_and_check(groups::Vector{Int}, @nospecialize(skipbytes))
    chunksize = sizeof(UInt)
    chunks = Tuple{Int, Int}[]
    sep_check = :(true)
    offset = 0
    for (i, gsize) in enumerate(groups)
        for j in 0:cld(gsize, chunksize)-1
            push!(chunks, (offset + chunksize * j, Base.min(chunksize, gsize - chunksize * j)))
        end
        offset += gsize
        i < length(groups) || break
        sep_check = :($sep_check && @inbounds data[pos + $offset] == $(first(skipbytes)))
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
    rep = bytelanes(T, 0x01)
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

