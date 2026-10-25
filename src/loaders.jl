# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

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

const RegisterChunk = @NamedTuple{offset::Int, width::Int, iT::DataType}

# Descending power-of-2 register chunks covering `nbytes`
function register_chunks(nbytes::Int)
    chunks = RegisterChunk[]
    off, remaining = 0, nbytes
    while remaining > 0
        isize = min(length(REGISTER_TYPES), 8 * sizeof(Int) - leading_zeros(remaining))
        bw = 1 << (isize - 1)
        push!(chunks, RegisterChunk((off, bw, REGISTER_TYPES[isize])))
        off += bw
        remaining -= bw
    end
    chunks
end

# A wider read covering `nbytes` in fewer registers, when there is one
function widened(nbytes::Int)
    n = min(nextpow(2, nbytes), sizeof(UInt) * cld(nbytes, sizeof(UInt)))
    if n > nbytes && length(register_chunks(n)) < length(register_chunks(nbytes)) n end
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
    pack_chunk(str::String, chunk, casefold::Bool[, valid::Int]) -> (; value::iT, mask::iT)

Compute a masked register value for comparing `chunk` against `str`.

Bytes within `valid` get mask `0xFF` (exact match) or `0xDF` (letters, when
`casefold`); bytes beyond it get `0x00`. The returned `value` is already masked.
"""
function pack_chunk(str::String, chunk::RegisterChunk,
                    casefold::Bool, valid::Int = min(chunk.width, ncodeunits(str) - chunk.offset))
    (; offset, iT) = chunk
    mask = zero(iT)
    for j in 0:valid-1
        byte = codeunit(str, offset + j + 1)
        folds = casefold && UInt8('a') <= (byte | 0x20) <= UInt8('z')
        mask |= iT(if folds 0xDF else 0xFF end) << (8j)
    end
    value = pack_bytes(str, offset, valid, iT) & mask
    (; value, mask)
end

## Codegen primitives

function gen_load(iT::DataType, posexpr::Union{Symbol, Expr})
    if iT === UInt8
        :(@inbounds data[$posexpr])
    else
        :(htol(Base.unsafe_load(Ptr{$iT}(pointer(data, $posexpr)))))
    end
end

function gen_masked_compare(iT::DataType, @nospecialize(posexpr), @nospecialize(value), @nospecialize(mask))
    load = gen_load(iT, posexpr)
    if mask == typemax(iT)
        :($load == $value)
    else
        :($load & $mask == $value)
    end
end

