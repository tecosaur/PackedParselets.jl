# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Runtime functions called by code generated from pattern compilation.
#
# Three families:
# - Parsing: parseint, parsechars (digit/character scanning from byte vectors)
# - IO printing: printchars, chars2string (character unpacking to IO/String)
# - Buffer printing: bufprint (direct Memory{UInt8} output)

## Compat

@static if VERSION < v"1.13-"
    takestring!(io::IO) = String(take!(io))
end

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

function parsechars(::Type{P}, str::AbstractString, maxlen::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    casefold::Bool, oneindexed::Bool = false) where {P <: Unsigned, N}
    parsechars(P, codeunits(str), 1, maxlen, ranges, casefold, oneindexed)
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

function parseint(::Type{I}, bytes::AbstractVector{UInt8}, pos::Int, base::Integer,
                  maxlen::Integer, skip::NTuple{S, UInt8} = ()) where {I <: Unsigned, S}
    num = zero(I)
    nread = 0
    nbytes = length(bytes)
    endpos = min(pos + maxlen, nbytes + 1)
    pos > nbytes && return if iszero(S); (0, zero(I)) else (0, zero(I), 0) end
    startpos = pos
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

function parseint(::Type{I}, str::AbstractString, base::Integer, maxlen::Integer) where {I <: Unsigned}
    parseint(I, codeunits(str), 1, base, maxlen)
end

## Character unpacking

"""
    unpackchars!(buf, pos, packed::Unsigned, nchars, ranges[, oneindexed]) -> pos

Unpack `nchars` characters from `packed` (MSB-first, same encoding as
`parsechars`) into `buf` starting at `pos+1`. Returns the updated position.
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
        idx = UInt8(packed >> topshift) - offset
        for r in ranges
            rlen = length(r) % UInt8
            if idx < rlen
                buf[pos += 1] = first(r) + idx
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
    pos
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
    @inbounds for _ in 1:nchars
        idx = UInt8(packed >> topshift) - offset
        for r in ranges
            rlen = length(r) % UInt8
            if idx < rlen
                write(io, first(r) + idx)
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
end

"""
    chars2string(packed::Unsigned, nchars, ranges[, oneindexed]) -> String

Unpack `nchars` characters from `packed` into a `String`.
"""
function chars2string(packed::P, nchars::Int,
                      ranges::NTuple{N, UnitRange{UInt8}},
                      oneindexed::Bool = false) where {P <: Unsigned, N}
    buf = Base.StringMemory(nchars)
    unpackchars!(buf, 0, packed, nchars, ranges, oneindexed)
    Base.unsafe_takestring(buf)
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

Base.@constprop :aggressive @inline function bufprint(buf::Memory{UInt8}, pos::Int, num::Integer, base::Int = 10, pad::Int = 0)
    base == 10 && return bufprint_decimal(buf, pos, num % UInt64, pad)
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
# Ref: Jeon, "Faster integer formatting — jeaiii's algorithm", 2022.
Base.@constprop :aggressive @inline function bufprint_decimal(buf::Memory{UInt8}, pos::Int, num::UInt64, pad::Int)
    num <= typemax(UInt32) && return bufprint_decimal32(buf, pos, num % UInt32, pad)
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

Base.@constprop :aggressive @inline function bufprint_decimal32(buf::Memory{UInt8}, pos::Int, num::UInt32, pad::Int)
    @inline function jeaiii_emit(buf, pos, prod, npairs)
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
        pos
    end
    startpos = pos
    pos = if num < 100
        if num < 10; @inbounds buf[pos + 1] = UInt8('0') + num % UInt8; pos + 1
        else radix100_store(buf, pos + 1, num); pos + 2 end
    elseif num < 1_000_000
        if num < 10_000; jeaiii_emit(buf, pos, UInt64(num) * 42949673, 1)
        else jeaiii_emit(buf, pos, UInt64(num) * 429497, 2) end
    elseif num < 100_000_000
        jeaiii_emit(buf, pos, (UInt64(num) * 281474978) >> 16, 3)
    elseif num < 1_000_000_000
        jeaiii_emit(buf, pos, (UInt64(num) * 1441151882) >> 25, 4)
    else
        jeaiii_emit(buf, pos, (UInt64(num) * 1441151881) >> 25, 4)
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
