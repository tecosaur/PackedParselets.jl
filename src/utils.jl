# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Runtime functions called by code generated from pattern compilation.
#
# Three families:
# - Parsing: parseint, parsechars (digit/character scanning from byte vectors)
# - IO printing: printchars, chars2string (character unpacking to IO/String)
# - Buffer printing: bufprint (direct Memory{UInt8} output)

## Invalid values

@noinline throw_invalidpacking(@nospecialize(T::Type), field::Union{Symbol, Nothing}, value::Integer) =
    throw(InvalidPacking(T, field, value))

## Compat

@static if VERSION < v"1.13-"
    takestring!(io::IO) = String(take!(io))
end

const unsafe_takestring = @static VERSION < v"1.12-" ? String : Base.unsafe_takestring

## Load bounds

# Whether a load may read `n` bytes before `data[pos]`; a `String`'s length word precedes its data
canreadback(::AbstractVector{UInt8}, pos::Int, n::Int) = pos > n
canreadback(::Base.CodeUnits{UInt8, <:Union{String, SubString{String}}}, pos::Int, n::Int) =
    n <= sizeof(Int) || pos > n

# The byte at `data[pos]`, or zero just past the end: a `String` ends in a NUL byte
peekbyte(data::AbstractVector{UInt8}, pos::Int) = if pos <= length(data) @inbounds data[pos] else 0x00 end
peekbyte(data::Base.CodeUnits{UInt8, <:Union{String, SubString{String}}}, pos::Int) =
    unsafe_load(pointer(data, pos))

## Character parsing

"""
    parsechars(::Type{P}, bytes, pos, maxlen, ranges, casefold[, oneindexed]) -> (Int, P)

Scan up to `maxlen` bytes from `bytes` at `pos`, mapping each to a 0-based
index via the given byte `ranges` and packing MSB-first into `P`.

Ranges map contiguously: the first covers indices 0:length(r1)-1, the
second continues from there, etc. When `casefold` is true, input bytes
are lowercased before matching. Returns `(chars_consumed, packed_value)`.
"""
function parsechars(::Type{P}, bytes::AbstractVector{UInt8}, pos::Int, maxlen::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    casefold::Bool, oneindexed::Bool = false,
                    skip::NTuple{S, UInt8} = ()) where {P <: Unsigned, N, S}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals + oneindexed)
    packed = zero(P)
    endpos = if iszero(S) min(pos + maxlen, length(bytes) + 1) else length(bytes) + 1 end
    pos > length(bytes) && return if iszero(S); (0, packed) else (0, packed, 0) end
    offset = UInt8(oneindexed)
    nread = 0
    startpos = pos
    @inbounds while pos < endpos && nread < maxlen
        b = bytes[pos]
        if !iszero(S) && b in skip
            pos += 1
            continue
        end
        casefold && (b |= 0x20)
        idx = 0xff % UInt8
        base = offset
        for r in ranges
            lo = if casefold; first(r) | 0x20 else first(r) end
            d = b - lo
            if d < length(r) % UInt8
                idx = base + d
                break
            end
            base += length(r) % UInt8
        end
        idx == 0xff && break
        packed = (packed << bpc) | P(idx)
        nread += 1
        pos += 1
    end
    if iszero(S)
        nread, packed
    else
        nread, packed, pos - startpos
    end
end

## Digit parsing

function byte2int(b::UInt8, base::Integer)
    # base ≤ 10: digits 0-9 (truncated to base)
    if b in UInt8('0'):(UInt8('0') - 0x1 + min(base, 10) % UInt8)
        b - UInt8('0')
    # base 11-36: digits 0-9 then case-insensitive a-z (standard Base36)
    elseif 10 < base <= 36 && (b | 0x20) in UInt8('a'):(UInt8('a') - 0x1 + (base - 10) % UInt8)
        (b | 0x20) - (UInt8('a') - UInt8(10))
    # base 37-62: digits 0-9, uppercase A-Z (10-35), lowercase a-z (36-61)
    elseif base > 36 && b in UInt8('A'):(UInt8('z') - UInt8(62) + base % UInt)
        b - (UInt8('A') - UInt8(10)) - ifelse(b >= UInt8('a'), 0x06, 0x00)
    else
        0xff
    end
end

@inline function parseint(::Type{I}, bytes::AbstractVector{UInt8}, pos::Int, base::Integer,
                  maxlen::Integer, skip::NTuple{S, UInt8} = ()) where {I <: Unsigned, S}
    num = zero(I)
    nread = 0
    nbytes = length(bytes)
    endpos = min(pos + maxlen, nbytes + 1)
    pos >= endpos && return if iszero(S); (0, zero(I)) else (0, zero(I), 0) end
    startpos = pos
    if iszero(S) && base == 10 && sizeof(I) >= 4
        while pos + 7 < endpos && num <= (typemax(I) - 99999999) ÷ 100000000
            x = htol(unsafe_load(Ptr{UInt64}(pointer(bytes, pos))))
            iszero(x & (x + 0x0606060606060606) & 0xf0f0f0f0f0f0f0f0 ⊻ 0x3030303030303030) || break
            x &= 0x0f0f0f0f0f0f0f0f
            x = (x * 10 + x >> 8) & 0x00ff00ff00ff00ff
            x = (x * 100 + x >> 16) & 0x0000ffff0000ffff
            x = (x * 10000 + x >> 32) & 0x00000000ffffffff
            num = num * I(100000000) + x % I
            nread += 8
            pos += 8
        end
        pos < endpos || return nread, num
    end
    # `while true` is measurably faster than `while cond` (~4ns vs ~7ns)
    @inbounds while true
        b = bytes[pos]
        if !iszero(S) && b in skip
            pos += 1
            pos <= nbytes || break
            continue
        end
        digit = byte2int(b, base)
        digit == 0xff && break
        numnext = muladd(widen(num), base % I, digit)
        iszero(numnext & ~widen(typemax(I))) || return if iszero(S); (0, zero(I)) else (0, zero(I), 0) end
        num = numnext % I
        nread += 1
        pos += 1
        if iszero(S)
            pos < endpos || break
        else
            nread < maxlen && pos <= nbytes || break
        end
    end
    if iszero(S)
        nread, num
    else
        nread, num, pos - startpos
    end
end


## Character unpacking

"""
    unpackchars!(buf, pos, packed::Unsigned, nchars, ranges[, oneindexed]) -> pos

Unpack `nchars` characters from `packed` (MSB-first, same encoding as
`parsechars`) into `buf` starting at `pos+1`. Returns the updated position.
An index past the last range (only held by bits no parse produced) continues past
its end, as the SWAR printers do, so exactly `nchars` bytes are always written.
"""
function unpackchars!(buf, pos::Int, packed::P, nchars::Int,
                      ranges::NTuple{N, UnitRange{UInt8}},
                      oneindexed::Bool = false) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals + oneindexed)
    topshift = 8 * sizeof(P) - bpc
    packed <<= 8 * sizeof(P) - nchars * bpc
    offset = UInt8(oneindexed)
    @inbounds for _ in 1:nchars
        buf[pos += 1] = charbyte(ranges, UInt8(packed >> topshift) - offset)
        packed <<= bpc
    end
    pos
end

# The byte for character index `idx` over `ranges`, continuing past the last range
@inline function charbyte(ranges::NTuple{N, UnitRange{UInt8}}, idx::UInt8) where {N}
    for r in ranges
        rlen = length(r) % UInt8
        idx < rlen && return first(r) + idx
        idx -= rlen
    end
    last(last(ranges)) + 0x01 + idx
end

"""
    printchars(io::IO, packed::Unsigned, nchars, ranges[, oneindexed])

Unpack `nchars` characters from `packed` and write them to `io`.
"""
function printchars(io::IO, packed::P, nchars::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    oneindexed::Bool = false) where {P <: Unsigned, N}
    nvals = sum(length, ranges)
    bpc = cardbits(nvals + oneindexed)
    topshift = 8 * sizeof(P) - bpc
    packed <<= 8 * sizeof(P) - nchars * bpc
    offset = UInt8(oneindexed)
    for _ in 1:nchars
        write(io, charbyte(ranges, UInt8(packed >> topshift) - offset))
        packed <<= bpc
    end
end

"""
    printdigits(io::IO, num::Integer, base, pad, maxdigits)

Write `num` in `base`, zero-padded to `pad` digits. `maxdigits` bounds the digit
count of the field's values; only the buffer form (`bufprint`) uses it, to drop
the widths no value can have.
"""
printdigits(io::IO, num::Integer, base::Int, pad::Int, ::Int) = print(io, string(num; base, pad = Base.max(pad, 1)))

"""
    chars2string(packed::Unsigned, nchars, ranges[, oneindexed]) -> String

Unpack `nchars` characters from `packed` into a `String`.
"""
function chars2string(packed::P, nchars::Int,
                      ranges::NTuple{N, UnitRange{UInt8}},
                      oneindexed::Bool = false) where {P <: Unsigned, N}
    buf = Base.StringMemory(nchars)
    unpackchars!(buf, 0, packed, nchars, ranges, oneindexed)
    unsafe_takestring(buf)
end

## Buffer printing

function bufprint(buf::Memory{UInt8}, pos::Int, str::String)
    n = ncodeunits(str)
    Base.unsafe_copyto!(pointer(buf, pos + 1), pointer(str), n)
    pos + n
end

# Radix-100 digit pair table for two-at-a-time decimal output.
const RADIX100 = Tuple(UInt16(UInt8('0') + i % 10) << 8 | UInt16(UInt8('0') + i ÷ 10)
                       for i in 0:99)

@inline function radix100_store(buf::Memory{UInt8}, pos::Int, pair::Integer)
    Base.unsafe_store!(Ptr{UInt16}(pointer(buf, pos)), @inbounds RADIX100[pair + 1])
end

const POW10 = ntuple(i -> UInt64(10)^(i - 1), Val(20))

Base.@constprop :aggressive @inline function bufprint(buf::Memory{UInt8}, pos::Int, num::Integer, base::Int = 10,
                                                      pad::Int = 0, maxdigits::Int = length(POW10))
    base == 10 && return bufprint_decimal(buf, pos, num % UInt64, pad, maxdigits)
    nd = ndigits(num; base)
    endpos = pos + Base.max(nd, pad)
    i = endpos
    @inline int2byte(d) = if d < 10
        UInt8('0') + d % UInt8
    elseif base <= 36
        UInt8('a') - 0x0a + d % UInt8
    else
        db = d % UInt8
        ifelse(db < 36, UInt8('A') - 0x0a + db, UInt8('a') - 0x24 + db)
    end
    @inbounds while num != 0
        num, d = divrem(num, base)
        buf[i] = int2byte(d)
        i -= 1
    end
    @inbounds while i > pos; buf[i] = UInt8('0'); i -= 1 end
    endpos
end

# jeaiii multiply-shift: division-free decimal printing for UInt32.
# Each range selects a magic constant; prod >> 32 gives digit pairs,
# (UInt32(prod) * 100) advances to the next pair. The first pair's
# value (< 10 or ≥ 10) determines odd/even digit count implicitly.
# Ref: Jeon, "Faster integer formatting: jeaiii's algorithm", 2022.
# Each digit field inlines only the UInt32 printer; wider values call out, since
# inlining the UInt64 path copies the UInt32 printer into every field up to four times.
# With a constant `pad` and `maxdigits` only the widths a field's values can have
# remain: values its padding covers print as fixed digit pairs, and wider ones keep
# just the jeaiii ranges from `pad + 1` to `maxdigits` digits. Values beyond
# `maxdigits`, which only reinterpreted bits can hold, take the general path out of line.
Base.@constprop :aggressive @inline function bufprint_decimal(buf::Memory{UInt8}, pos::Int, num::UInt64,
                                                              pad::Int, maxdigits::Int = length(POW10))
    maxdigits < length(POW10) && num >= @inbounds(POW10[maxdigits + 1]) &&
        return @noinline bufprint_decimal(buf, pos, num, pad)
    if pad > 0
        (pad >= maxdigits || num < @inbounds(POW10[pad + 1])) &&
            return bufprint_fixed(buf, pos, num, pad)
    end
    mindigits = Base.max(pad + 1, 1)
    if maxdigits <= 9 || num <= typemax(UInt32)
        bufprint_decimal32(buf, pos, num % UInt32, 0, mindigits, Base.min(maxdigits, 10))
    else
        bufprint_decimal64(buf, pos, num, pad)
    end
end

# Exactly `width` digits of `num < 10^width`. The jeaiii constants below are exact
# over the whole of 0:10^6-1 (the wider ones only near the top of their ranges), so
# 4-digit chunks are peeled off the right until at most six digits remain. With a
# constant `width` the split folds away, leaving about one multiply per digit pair.
Base.@constprop :aggressive @inline function bufprint_fixed(buf::Memory{UInt8}, pos::Int, num::UInt64, width::Int)
    nchunks = cld(Base.max(width - 6, 0), 4)
    i = pos + width
    for _ in 1:nchunks
        num, chunk = divrem(num, UInt64(10_000))
        bufprint_fixed6(buf, i - 4, chunk % UInt32, 4)
        i -= 4
    end
    bufprint_fixed6(buf, pos, num % UInt32, width - 4 * nchunks)
    pos + width
end

# Exactly `width ≤ 6` digits; an odd `width` leaves a single digit in the leading pair.
Base.@constprop :aggressive @inline function bufprint_fixed6(buf::Memory{UInt8}, pos::Int, num::UInt32, width::Int)
    prod, npairs = if width <= 2
        (UInt64(num) << 32, 0)
    elseif width <= 4
        (UInt64(num) * 42949673, 1)
    else
        (UInt64(num) * 429497, 2)
    end
    pair = Int(prod >> 32)
    if isodd(width)
        @inbounds buf[pos += 1] = UInt8('0') + pair % UInt8
    else
        radix100_store(buf, pos + 1, pair)
        pos += 2
    end
    for _ in 1:npairs
        prod = UInt64(prod % UInt32) * UInt64(100)
        radix100_store(buf, pos + 1, Int(prod >> 32))
        pos += 2
    end
    pos
end

@noinline function bufprint_decimal64(buf::Memory{UInt8}, pos::Int, num::UInt64, pad::Int)
    startpos = pos
    # Split into ≤8-digit UInt32 chunks via divrem by 10^8.
    # UInt64 max ≈ 1.8×10^19 → at most three chunks (4+8+8 digits).
    hi, lo = divrem(num, UInt64(100_000_000))
    if hi <= typemax(UInt32)
        pos = bufprint_decimal32(buf, pos, hi % UInt32, 0)
    else
        hi2, mid = divrem(hi, UInt64(100_000_000))
        pos = bufprint_decimal32(buf, pos, hi2 % UInt32, 0)
        pos = bufprint_decimal32(buf, pos, mid % UInt32, 8)
    end
    pos = bufprint_decimal32(buf, pos, lo % UInt32, 8)
    # Pad if needed
    nd = pos - startpos
    if nd < pad
        npad = pad - nd
        @inbounds for j in pos:-1:startpos+1; buf[j + npad] = buf[j] end
        @inbounds for j in startpos+1:startpos+npad; buf[j] = UInt8('0') end
        pos += npad
    end
    pos
end

# A range `num` must lie in, by `mindigits:maxdigits`, is taken without a test, and
# one it can't lie in is skipped: the ranges above 10^6, whose constants are only exact
# near their tops, are still only reached by values the ranges below them exclude.
Base.@constprop :aggressive @inline function bufprint_decimal32(buf::Memory{UInt8}, pos::Int, num::UInt32, pad::Int,
                                                                mindigits::Int = 1, maxdigits::Int = 10)
    startpos = pos
    if maxdigits <= 2 || (mindigits <= 2 && num < 100)
        if num < 10
            @inbounds buf[pos += 1] = UInt8('0') + num % UInt8
        else
            radix100_store(buf, pos + 1, num)
            pos += 2
        end
    else
        # Select the range's constant, then emit once: every field inlines this
        # printer, so one emission loop keeps each inlined copy small.
        prod, npairs = if maxdigits <= 4 || (mindigits <= 4 && num < 10_000)
            (UInt64(num) * 42949673, 1)
        elseif maxdigits <= 6 || (mindigits <= 6 && num < 1_000_000)
            (UInt64(num) * 429497, 2)
        elseif maxdigits <= 8 || (mindigits <= 8 && num < 100_000_000)
            ((UInt64(num) * 281474978) >> 16, 3)
        elseif maxdigits <= 9 || (mindigits <= 9 && num < 1_000_000_000)
            ((UInt64(num) * 1441151882) >> 25, 4)
        else
            ((UInt64(num) * 1441151881) >> 25, 4)
        end
        pair = Int(prod >> 32)
        if pair < 10
            @inbounds buf[pos += 1] = UInt8('0') + pair % UInt8
        else
            radix100_store(buf, pos + 1, pair)
            pos += 2
        end
        for _ in 1:npairs
            prod = UInt64(prod % UInt32) * UInt64(100)
            radix100_store(buf, pos + 1, Int(prod >> 32))
            pos += 2
        end
    end
    nd = pos - startpos
    if nd < pad
        npad = pad - nd
        @inbounds for j in pos:-1:startpos+1; buf[j + npad] = buf[j] end
        @inbounds for j in startpos+1:startpos+npad; buf[j] = UInt8('0') end
        pos += npad
    end
    pos
end

# Keeps the branch it's in from becoming a conditional move
@inline keepbranch() = Base.llvmcall("call void asm sideeffect \"\", \"\"()\nret void", Cvoid, Tuple{})
