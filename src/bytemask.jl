# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

"""
    ByteSet

A 256-bit set representing a subset of all possible byte values (0x00–0xff).

Constructed from integers, ranges, or combinations thereof:

    ByteSet(0x41)                  # single byte
    ByteSet(0x30:0x39)             # range
    ByteSet(0x41:0x5a, 0x61:0x7a)  # union of ranges

Supports `∪` (union), `∩` (intersection), `in`, `isempty`, `isdisjoint`,
`length`, and iteration over member bytes in ascending order.
"""
primitive type ByteSet 256 end

ByteSet() = Core.Intrinsics.zext_int(ByteSet, UInt8(0))
ByteSet(b::Integer) = Core.Intrinsics.shl_int(Core.Intrinsics.zext_int(ByteSet, UInt8(1)), UInt8(b))
ByteSet(r::AbstractUnitRange{<:Integer}) = mapreduce(ByteSet, ∪, r)
ByteSet(parts::Union{Integer, AbstractUnitRange{<:Integer}}...) = mapreduce(ByteSet, ∪, parts)

Base.union(a::ByteSet, b::ByteSet) = Core.Intrinsics.or_int(a, b)
Base.intersect(a::ByteSet, b::ByteSet) = Core.Intrinsics.and_int(a, b)
Base.isempty(m::ByteSet) = m === ByteSet()
Base.isdisjoint(a::ByteSet, b::ByteSet) = isempty(a ∩ b)
Base.in(b::Integer, m::ByteSet) = !isempty(ByteSet(b) ∩ m)
Base.:(==)(a::ByteSet, b::ByteSet) = Core.Intrinsics.eq_int(a, b)
Base.length(m::ByteSet) = Core.Intrinsics.trunc_int(Int, Core.Intrinsics.ctpop_int(m))

function Base.iterate(m::ByteSet, last::UInt16=zero(UInt16))
    shifted = Core.Intrinsics.lshr_int(m, last)
    next = Core.Intrinsics.trunc_int(UInt16, Core.Intrinsics.cttz_int(shifted))
    if next < UInt16(256)
        (last + next) % UInt8, last + next + UInt16(1)
    end
end
Base.eltype(::Type{ByteSet}) = UInt8
Base.IteratorSize(::Type{ByteSet}) = Base.HasLength()

function byte_set(b::UInt8, casefold::Bool)
    if casefold && UInt8('a') <= (b | 0x20) <= UInt8('z')
        ByteSet(b & 0xdf) ∪ ByteSet(b | 0x20)
    else
        ByteSet(b)
    end
end
