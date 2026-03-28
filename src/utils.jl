# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Runtime functions called by code generated from pattern compilation.
#
# Three families:
# - Parsing: parseint, parsechars (digit/character scanning from byte vectors)
# - IO printing: printchars, chars2string (character unpacking to IO/String)
# - Buffer printing: bufprint, bufprintchars (direct Memory{UInt8} output)

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
    unpackchars(f!, packed::Unsigned, nchars, ranges[, oneindexed])

Unpack `nchars` characters from `packed` (MSB-first, same encoding as
`parsechars`) and call `f!(byte)` for each decoded byte.

This is the shared core of `printchars`, `chars2string`, and
`bufprintchars` — each passes a different `f!` closure.
"""
function unpackchars(f!::F, packed::P, nchars::Int,
                     ranges::NTuple{N, UnitRange{UInt8}},
                     oneindexed::Bool = false) where {F, P <: Unsigned, N}
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
                f!(first(r) + idx)
                break
            end
            idx -= rlen
        end
        packed <<= bpc
    end
end

"""
    printchars(io::IO, packed::Unsigned, nchars, ranges[, oneindexed])

Unpack `nchars` characters from `packed` and write them to `io`.
"""
function printchars(io::IO, packed::P, nchars::Int,
                    ranges::NTuple{N, UnitRange{UInt8}},
                    oneindexed::Bool = false) where {P <: Unsigned, N}
    unpackchars(packed, nchars, ranges, oneindexed) do b
        write(io, b)
    end
end

"""
    chars2string(packed::Unsigned, nchars, ranges[, oneindexed]) -> String

Unpack `nchars` characters from `packed` into a `String`.
"""
function chars2string(packed::P, nchars::Int,
                      ranges::NTuple{N, UnitRange{UInt8}},
                      oneindexed::Bool = false) where {P <: Unsigned, N}
    buf = Vector{UInt8}(undef, nchars)
    ci = Ref(0)
    unpackchars(packed, nchars, ranges, oneindexed) do b
        buf[ci[] += 1] = b
    end
    String(buf)
end

## Buffer printing

function bufprint(buf::Memory{UInt8}, pos::Int, str::String)
    n = ncodeunits(str)
    Base.unsafe_copyto!(pointer(buf, pos + 1), pointer(str), n)
    pos + n
end

Base.@constprop :aggressive function bufprint(buf::Memory{UInt8}, pos::Int, num::Integer, base::Int = 10, pad::Int = 0)
    @inline int2byte(d) = if d < 10
        UInt8('0') + d % UInt8
    elseif base <= 36
        UInt8('a') - 0x0a + d % UInt8
    else
        db = d % UInt8
        ifelse(db < 36, UInt8('A') - 0x0a + db, UInt8('a') - 0x24 + db)
    end
    nd = ndigits(num; base)
    width = Base.max(nd, pad)
    endpos = pos + width
    i = endpos
    @inbounds while num != 0
        num, d = divrem(num, base)
        buf[i] = int2byte(d)
        i -= 1
    end
    @inbounds while i > pos
        buf[i] = UInt8('0')
        i -= 1
    end
    endpos
end

function bufprintchars(buf::Memory{UInt8}, pos::Int, packed::P, nchars::Int,
                       ranges::NTuple{N, UnitRange{UInt8}},
                       oneindexed::Bool = false) where {P <: Unsigned, N}
    posref = Ref(pos)
    unpackchars(packed, nchars, ranges, oneindexed) do b
        buf[posref[] += 1] = b
    end
    posref[]
end
