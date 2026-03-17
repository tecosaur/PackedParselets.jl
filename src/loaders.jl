# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Register-loading and byte-comparison primitives for pattern codegen.
#
# Three layers:
#   1. Register decomposition — break byte counts into typed register chunks
#   2. Packing — encode compile-time string data into register values with masks
#   3. Codegen — emit Expr nodes that load from idbytes and compare at runtime

## Register decomposition

const REGISTER_TYPES = let types = DataType[UInt8]
    while types[end] != UInt
        push!(types, widen(types[end]))
    end
    Tuple(types)
end

function register_type(nbytes::Int)
    if nbytes <= 1
        UInt8
    elseif nbytes <= 2
        UInt16
    elseif nbytes <= 4
        UInt32
    else
        UInt64
    end
end

"""
    register_chunks(nbytes::Int) -> Vector{@NamedTuple{offset::Int, width::Int, iT::DataType}}

Decompose `nbytes` into a sequence of descending power-of-2 register-sized
chunks covering the byte range. Each chunk carries its byte `offset` from
the start, byte `width`, and unsigned integer type `iT`.
"""
function register_chunks(nbytes::Int)
    chunks = @NamedTuple{offset::Int, width::Int, iT::DataType}[]
    off, remaining = 0, nbytes
    while remaining > 0
        isize = min(length(REGISTER_TYPES), 8 * sizeof(Int) - leading_zeros(remaining))
        bw = 1 << (isize - 1)
        push!(chunks, (; offset = off, width = bw, iT = REGISTER_TYPES[isize]))
        off += bw
        remaining -= bw
    end
    chunks
end

# Returns (; iT, padding) when a backward-aligned register load reduces chunk
# count for nbytes verification, nothing when already power-of-2 aligned.
function backward_verify_chunk(nbytes::Int)
    rT = register_type(min(nbytes, sizeof(UInt)))
    sizeof(rT) <= nbytes && return nothing
    (; iT = rT, padding = sizeof(rT) - nbytes)
end

## Packing

function pack_bytes(str::String, offset::Int, width::Int, iT::DataType)
    v = zero(iT)
    for j in 0:width-1
        v |= iT(codeunit(str, offset + j + 1)) << (8j)
    end
    v
end

"""
    pack_chunk(str::String, chunk; casefold::Bool, valid::Int) -> (; value::iT, mask::iT)

Compute a masked register value for comparing `chunk` against `str`.

For each byte position in the chunk: valid bytes get mask `0xFF` (exact match)
or `0xDF` (case-insensitive alpha when `casefold` is true), and overflow bytes
(beyond `valid`) get mask `0x00`. The returned `value` is already AND-ed with
the mask.

This encapsulates the recurring `build_chunk_mask` + `pack_bytes & mask` pattern
used across string matching, choice verification, and tail checking.
"""
function pack_chunk(str::String, chunk::@NamedTuple{offset::Int, width::Int, iT::DataType};
                    casefold::Bool, valid::Int = min(chunk.width, ncodeunits(str) - chunk.offset))
    (; offset, width, iT) = chunk
    mask = reduce(|, (begin
        if j < valid
            byte = codeunit(str, offset + j + 1)
            if casefold && UInt8('a') <= byte <= UInt8('z')
                iT(0xDF) << (8j)
            else
                iT(0xFF) << (8j)
            end
        else
            zero(iT)
        end
    end for j in 0:width-1), init=zero(iT))
    value = pack_bytes(str, offset, valid, iT) & mask
    (; value, mask)
end

## Codegen primitives

function gen_load(iT::DataType, posexpr::Union{Symbol, Expr})
    if iT === UInt8
        :(@inbounds idbytes[$posexpr])
    else
        :(Base.unsafe_load(Ptr{$iT}(pointer(idbytes, $posexpr))))
    end
end

function gen_masked_compare(iT::DataType, posexpr, value, mask)
    load = gen_load(iT, posexpr)
    if mask == typemax(iT)
        :($load == $value)
    else
        :($load & $mask == $value)
    end
end

