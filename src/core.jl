# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

## Generic functions (overridden by generated methods)

"""
    nbits(T::DataType) -> Int

Return the logical bit width of a packed type. Defaults to `8*sizeof(T)`.
Generated methods override this for types with padding bits.
"""
nbits(@nospecialize(T::DataType)) = 8 * sizeof(T)

"""
    parsebounds(::Type{T}) -> Tuple{Int, Int}

Return `(min_bytes, max_bytes)` for parsing type `T`.
"""
function parsebounds end

"""
    printbounds(::Type{T}) -> Tuple{Int, Int}

Return `(min_bytes, max_bytes)` for printing type `T`.
"""
function printbounds end

"""
    parsebytes(::Type{T}, bytes::AbstractVector{UInt8}[, start::Int]) -> (T_or_errcode, pos)

Raw byte parser, from `bytes[start]` (default 1). Returns the parsed value and
the position after it on success, or an error code and position on failure.
"""
function parsebytes end

"""
    tobytes(val) -> Memory{UInt8}
    tobytes(buf::Memory{UInt8}, val[, pos::Int]) -> Int

Buffer-based output. The first form returns a `StringMemory` of exact length; the
second writes into `buf` after byte `pos` (default 0) and returns the new end position.
"""
function tobytes end

tobytes(buf::Memory{UInt8}, val) = tobytes(buf, val, 0)

function segments end

@doc """
    segments(::Type{T}) -> Vector{Union{Segment, SegmentOptions}}

The layout of `T`'s pattern, in order: each element a [`Segment`](@ref), or the
[`SegmentOptions`](@ref) of a choice. Each element takes the next bits of the packed
value, from the most significant: a segment its `nbits`, and options as many as the
widest of them, their bits overlapping.
A choice's options follow the segment selecting one (`kind = :arm`). An optional's
are its contents and `nothing`, its contents ending with a segment marking them
present (`kind = :presence`) unless a segment's zero value marks absence instead.
""" segments(::Type)

@doc """
    segments(val::T) -> Tuple{Vararg{Union{String, Nothing}}}

The printed text of each segment of `segments(T)`, in order, including those within
options, or `nothing` for those `val` doesn't hold: a choice took the option whose
segments aren't `nothing`, or, when only its `:arm` segment isn't, its empty option.
""" segments(::Any)

## Bit-sizing

# Bits needed to represent `n` distinct values: `ceil(log2(n))`
cardbits(n::Integer) = 8 * sizeof(n) - leading_zeros(max(n, 1) - 1)

# Smallest unsigned type holding `minbits` bits (`Nothing` for zero); at most `UInt128`
Base.@assume_effects :foldable function cardtype(minbits::Int)
    iszero(minbits) && return Nothing
    logtypesize = 1 + 8 * sizeof(minbits) - leading_zeros(cld(minbits, 8) - 1)
    if logtypesize > 5
        throw(ArgumentError(
            "Cannot allocate more than 128 bits for a packed field, but $minbits bits were requested"))
    end
    (UInt8, UInt16, UInt32, UInt64, UInt128)[logtypesize]
end

## Ordering

# Insertion sort: the generator sorts a handful of items, and Base's sort bloats the image
function sortperm_by(key, v::AbstractVector, rev::Bool = false)
    perm = collect(eachindex(v))
    for i in 2:length(perm)
        j = i
        while j > 1
            a, b = key(v[perm[j - 1]]), key(v[perm[j]])
            (if rev isless(a, b) else isless(b, a) end) || break
            perm[j - 1], perm[j] = perm[j], perm[j - 1]
            j -= 1
        end
    end
    perm
end

## State mutation helpers

# The returned index is the error code `parsebytes` returns, mapped back to `msg` by `parse`
function register_errmsg!(state::ParserState, msg::String)
    push!(state.errconsts, msg)
    length(state.errconsts)
end

## Optional codegen wrapping

# Within an optional, the extract's `if true` guard is a placeholder that
# `patch_optional_extracts!` replaces with the presence check.
function optional_wrap(@nospecialize(option::Union{Nothing, Symbol}), argvar::Symbol,
                       extract_setup::Vector{ExprVarLine}, @nospecialize(extract_value::ExprVarLine),
                       impart_body::Vector{Expr})
    seg_extract = if isnothing(option)
        ExprVarLine[extract_setup..., extract_value]
    else
        ExprVarLine[extract_setup..., :(if true; $extract_value end)]
    end
    seg_impart = if isnothing(option)
        copy(impart_body)
    else
        Expr[Expr(:if, :(!isnothing($argvar)), Expr(:block, impart_body...))]
    end
    seg_extract, seg_impart
end

## Bit packing

# zext_int requires output > input size, so 1-byte types need bitcast instead.
function zero_int(@nospecialize(T::DataType))
    if sizeof(T) == 1
        Core.bitcast(T, 0x00)
    else
        Core.Intrinsics.zext_int(T, 0x0)
    end
end

function zero_parsed_expr(state::ParserState)
    if state.bits <= 8
        :(Core.bitcast($(esc(state.name)), 0x00))
    else
        :(Core.Intrinsics.zext_int($(esc(state.name)), 0x0))
    end
end

"""
    emit_pack(state, type, value, shift) -> Expr

Emit an expression that OR-packs `value` (cast from `type` to the target
primitive type) into the `parsed` accumulator at bit position `shift`
(counted from MSB).
"""
function emit_pack(state::ParserState, type::Type, value::Union{Symbol, Expr, Bool}, shift::Int)
    valcast = Expr(:call, :__cast_to_packed, type, value)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, __packed_shift($shift))))
end

"""
    emit_extract(state, position, width[, fT]) -> Expr

Emit an expression that extracts `width` bits ending at bit `position`
(from MSB) from `val`, returning a value of type `fT` (defaults to
`cardtype(width)`).
"""
function emit_extract(state::ParserState, position::Int, width::Int,
                            fT::Type=cardtype(width))
    fTbits = 8 * sizeof(fT)
    fval = :(Core.Intrinsics.lshr_int(val, __packed_shift($position)))
    ival = Expr(:call, :__cast_from_packed, fT, fval)
    if width == fTbits
        ival
    elseif fT === cardtype(width)
        fTmask = ~(typemax(fT) << width)
        :($ival & $fTmask)
    else
        fTmask = Core.Intrinsics.not_int(
                     Core.Intrinsics.shl_int(
                         Core.Intrinsics.not_int(zero_int(fT)),
                         width))
        :(Core.Intrinsics.and_int($ival, $fTmask))
    end
end

"""
    emit_validity_check(state, fieldvar, var, valid) -> Expr

Throw `InvalidPacking` unless `var` lies in `valid`, naming the field when `fieldvar`
is a named field's `attr_<name>`. Where a field's value bounds a
print buffer or indexes a table, parsing and constructors only ever store values in
`valid`; this stops a value built from other bits before it is used.
"""
function emit_validity_check(state::ParserState, fieldvar::Symbol, @nospecialize(var),
                             valid::AbstractUnitRange{<:Integer})
    lo, hi = first(valid), last(valid)
    hi = if hi <= typemax(Int) Int(hi) else hi end
    inrange = if iszero(lo); :($var <= $hi) else :($(Int(lo)) <= $var <= $hi) end
    name = String(fieldvar)
    field = if startswith(name, "attr_") QuoteNode(Symbol(chopprefix(name, "attr_"))) end
    :($inrange || $(GlobalRef(PackedParselets, :throw_invalidpacking))($(esc(state.name)), $field, $var))
end

## Form string assembly

# The expected form shown in parse errors, e.g. `"SN<0-9 × 4>[-<0-9 × 2>[-<0-9 × 1>]]"`
function segments_formstring(segments::Vector{ValueSegment})
    io = IOBuffer()
    scopes = ParseBranch[]
    for seg in segments
        transition_scopes!(io, scopes, seg.condition)
        isempty(seg.shortform) && continue
        if seg.kind in (:literal, :skip)
            print(io, seg.shortform)
        else
            print(io, '<', seg.shortform, '>')
        end
    end
    print(io, ']' ^ length(scopes))
    String(take!(io))
end

# Close brackets for scopes left and open them for scopes entered on the way to `target`
function transition_scopes!(io::IO, scopes::Vector{ParseBranch}, target::Union{Nothing, ParseBranch})
    current = if isempty(scopes) nothing else last(scopes) end
    target === current && return
    chain = ParseBranch[]
    s = target
    while !isnothing(s) && !isnothing(s.parent)
        push!(chain, s)
        s = s.parent
    end
    reverse!(chain)
    shared = 0
    for i in 1:min(length(scopes), length(chain))
        scopes[i] === chain[i] || break
        shared = i
    end
    for _ in shared+1:length(scopes)
        print(io, ']')
    end
    resize!(scopes, shared)
    for i in shared+1:length(chain)
        print(io, '[')
        push!(scopes, chain[i])
    end
end

## Optional context helpers

"""
    build_fail_expr!(state, nctx, msg) -> Expr

Build a parse-failure expression appropriate to the current scope.

In required context, registers `msg` as an error and returns
`:(return (erridx, pos))`. Inside an optional scope, returns an expression
that sets the optional flag to `false` and jumps to the cleanup label.
"""
function build_fail_expr!(state::ParserState, nctx::NodeCtx, msg::String)
    option = get(nctx, :optional, nothing)
    isnothing(option) && return :(return ($(register_errmsg!(state, msg)), pos))
    label = nctx[:opt_label]
    Expr(:block, :($option = false), :(@goto $label))
end

## Optional sentinel helpers

is_sentinel_unclaimed(nctx::NodeCtx) =
    (ref = get(nctx, :optional_sentinel, nothing)) !== nothing && ref[] === nothing

## SegmentOutput processing

function process_segment_output!(exprs::PatternExprs, state::ParserState,
                                 nctx::NodeCtx, kind::Symbol, output::SegmentOutput)
    (; bounds, codegen, meta) = output
    option = get(nctx, :optional, nothing)
    append!(exprs.parse, codegen.parse)
    bounds.nbits > 0 && (state.bits += bounds.nbits)
    if !isnothing(bounds.sentinel) && is_sentinel_unclaimed(nctx)
        nctx[:optional_sentinel][] = OptSentinel((state.bits + bounds.sentinel.offset, bounds.sentinel.width))
    end
    b = nctx[:current_branch]
    b.parsed_min += first(bounds.parsed)
    b.parsed_max += last(bounds.parsed)
    b.print_min += first(bounds.printed)
    b.print_max += last(bounds.printed)
    (; direct, vars, getval, getlen, putval) = codegen.print
    append!(exprs.print.direct, direct)
    append!(exprs.print.vars, vars)
    append!(if isnothing(option) exprs.print.getval else nctx[:oprint_detect] end, getval)
    append!(exprs.print.getlen, getlen)
    append!(exprs.print.putval, putval)
    argvar = something(meta.argvar, :_)
    push!(exprs.layout, Segment((bounds.nbits, kind, meta.label, meta.desc, meta.shortform)))
    push!(exprs.segments, ValueSegment(
        bounds.nbits, kind, meta.label, meta.desc, meta.shortform,
        meta.argtype, argvar,
        codegen.extract, codegen.impart, if !isnothing(option) nctx[:current_branch] end))
    push!(exprs.print.direct, :(__segment_printed = $(length(exprs.segments))))
    push!(state.segment_outputs, kind => output)
    extend_bytespans!(exprs.bytespans, output.bytespans)
end

# Each bytespan is one alternative byte sequence the pattern can match; extending takes
# the Cartesian product. Nested choices would multiply these without bound, so past
# 1024 they describe only what came before.
function extend_bytespans!(target::Vector{Vector{ByteSet}}, new::Vector{Vector{ByteSet}})
    isempty(new) && return
    if isempty(target)
        append!(target, new)
    elseif length(target) * length(new) <= 1024
        combined = Vector{ByteSet}[]
        for prev in target, ext in new
            push!(combined, vcat(prev, ext))
        end
        empty!(target)
        append!(target, combined)
    end
end
