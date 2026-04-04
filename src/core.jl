# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# State-mutation helpers and codegen utilities for pattern compilation.
#
# Small helpers that every pattern handler calls to track bits, bytes,
# errors, and segments.

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
    parsebytes(::Type{T}, bytes::AbstractVector{UInt8}) -> (T_or_errcode, pos)

Raw byte parser. Returns the parsed value and position on success,
or an error code and position on failure.
"""
function parsebytes end

"""
    tobytes(val) -> Memory{UInt8}

Buffer-based output. Returns a `StringMemory` of exact length.
"""
function tobytes end

function segments end

@doc """
    segments(::Type{T}) -> Tuple{@NamedTuple{nbits, kind, label, desc, shortform}...}

Return the type-level segment schema (one entry per value-carrying segment,
excluding zero-bit segments like literals).
""" segments(::Type)

@doc """
    segments(val::T) -> Tuple{Tuple{Int, String}...}

Return instance-level segment values as `(index, formatted_string)` pairs,
where `index` corresponds to the position in the schema tuple.
""" segments(::Any)

## Bit-sizing

"""
    cardbits(n::Integer) -> Int

Return the number of bits needed to represent `n` distinct values (i.e. `ceil(log2(n))`
computed via leading zeros).
"""
cardbits(n::Integer) = 8 * sizeof(n) - leading_zeros(max(n, 1) - 1)

"""
    cardtype(minbits::Int) -> DataType

Return the smallest unsigned integer type that can hold `minbits` bits.

Returns `Nothing` for zero bits. Supports up to 128 bits (`UInt128`).
"""
Base.@assume_effects :foldable function cardtype(minbits::Int)
    iszero(minbits) && return Nothing
    logtypesize = 1 + 8 * sizeof(minbits) - leading_zeros(cld(minbits, 8) - 1)
    if logtypesize > 5
        throw(ArgumentError(
            "Cannot allocate more than 128 bits for a packed field, but $minbits bits were requested"))
    end
    (UInt8, UInt16, UInt32, UInt64, UInt128)[logtypesize]
end

## State mutation helpers

function inc_parsed!(nctx::NodeCtx, dmin, dmax)
    b = nctx[:current_branch]
    b.parsed_min += dmin
    b.parsed_max += dmax
end
function inc_print!(nctx::NodeCtx, dmin, dmax)
    b = nctx[:current_branch]
    b.print_min += dmin
    b.print_max += dmax
end

"""
    register_errmsg!(state::ParserState, msg::String) -> Int

Register a compile-time error message and return its 1-based index.

The index is used as an error code in the generated `parsebytes` function,
mapped back to the message string at `parse` time.
"""
function register_errmsg!(state::ParserState, msg::String)
    push!(state.errconsts, msg)
    length(state.errconsts)
end

## Optional codegen wrapping

"""
    optional_wrap(option, argvar, extract_setup, extract_value, impart_body)
        -> (extract::Vector{ExprVarLine}, impart::Vector{Expr})

Apply the standard required/optional split for value-carrying segments.

In required context (`option === nothing`), returns extract and impart as-is.
In optional context, wraps the extract value in a presence guard (`if true`)
resolved later by `patch_optional_extracts!`, and wraps impart in an
`isnothing` guard on the constructor argument.
"""
function optional_wrap(option::Union{Nothing, Symbol}, argvar::Symbol,
                       extract_setup::Vector{ExprVarLine}, extract_value::ExprVarLine,
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
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(state.name))) - $shift))))
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
    fval = :(Core.Intrinsics.lshr_int(val, 8 * sizeof($(esc(state.name))) - $position))
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

## Form string assembly

"""
    segments_formstring(segments, branches) -> String

Join segment shortforms into a compact pattern notation like
`"SN<0-9 × 4>[-<0-9 × 2>[-<0-9 × 1>]]"`, used in parse error messages
to show the expected form. Optional segments are wrapped in square brackets,
with proper nesting for nested optionals.
"""
function segments_formstring(segments::Vector{ValueSegment}, branches::Vector{ParseBranch})
    scope_parent = Dict{Symbol, Symbol}()
    for b in branches
        b.scope === :root && continue
        scope_parent[b.scope] = b.parent.scope
    end
    io = IOBuffer()
    scopes = Symbol[]
    for seg in segments
        transition_scopes!(io, scopes, seg.condition, scope_parent)
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

# Diff the active scope stack against `target`'s ancestor chain,
# closing brackets for scopes we're leaving and opening brackets
# for scopes we're entering.
function transition_scopes!(io::IO, scopes::Vector{Symbol}, target::Union{Nothing, Symbol},
                            scope_parent::Dict{Symbol, Symbol})
    current = if isempty(scopes) nothing else last(scopes) end
    target === current && return
    # Build ancestor chain for target scope (root-first)
    chain = Symbol[]
    s = target
    while !isnothing(s)
        push!(chain, s)
        s = get(scope_parent, s, nothing)
    end
    reverse!(chain)
    # Find how many levels of the current stack match
    shared = 0
    for i in 1:min(length(scopes), length(chain))
        scopes[i] === chain[i] || break
        shared = i
    end
    # Close scopes we're leaving, open scopes we're entering
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
#
# Bridge between the SegmentOutput return type and the existing
# PatternExprs/ParserState mutation model. Handlers return SegmentOutput;
# this function performs all the side effects they used to do inline.

"""
    process_segment_output!(exprs, state, nctx, kind, output)

Process a `SegmentOutput` returned by a segment handler, performing all
framework-level state mutations: expression accumulation, bit allocation,
sentinel claiming, byte bounds tracking, and segment registration.
"""
function process_segment_output!(exprs::PatternExprs, state::ParserState,
                                 nctx::NodeCtx, kind::Symbol, output::SegmentOutput)
    (; bounds, codegen, meta) = output
    option = get(nctx, :optional, nothing)
    # Defer error message registration to avoid shifting indices
    seg_id = length(state.segment_outputs) + 1
    b = nctx[:current_branch]
    opt_label = get(nctx, :opt_label, nothing)
    push!(exprs.parse, Expr(:call, :__segment_begin, seg_id, b.id,
                            first(bounds.parsed), last(bounds.parsed),
                            option, opt_label, meta.desc))
    append!(exprs.parse, codegen.parse)
    push!(exprs.parse, Expr(:call, :__segment_end, seg_id))
    bounds.nbits > 0 && (state.bits += bounds.nbits)
    # Claim sentinel from this segment if the enclosing optional needs one
    if !isnothing(bounds.sentinel) && is_sentinel_unclaimed(nctx)
        nctx[:optional_sentinel][] = OptSentinel((state.bits + bounds.sentinel.offset, bounds.sentinel.width))
    end
    inc_parsed!(nctx, first(bounds.parsed), last(bounds.parsed))
    inc_print!(nctx, first(bounds.printed), last(bounds.printed))
    # Route print expressions: getval hoisted to oprint_detect inside optionals
    (; direct, vars, getval, getlen, putval) = codegen.print
    append!(exprs.print.direct, direct)
    append!(exprs.print.vars, vars)
    append!(if isnothing(option) exprs.print.getval else nctx[:oprint_detect] end, getval)
    append!(exprs.print.getlen, getlen)
    append!(exprs.print.putval, putval)
    argvar = something(meta.argvar, :_)
    push!(exprs.segments, ValueSegment(
        bounds.nbits, kind, meta.label, meta.desc, meta.shortform,
        meta.argtype, argvar,
        codegen.extract, codegen.impart, option))
    push!(exprs.print.direct, :(__segment_printed = $(length(exprs.segments))))
    push!(state.segment_outputs, kind => output)
    extend_bytespans!(exprs.bytespans, output.bytespans)
end

# Bytespans represent alternative byte sequences that a pattern can match.
# Each element of the vector is one alternative (a sequence of ByteSets,
# one per byte position). Extending with new alternatives forms the
# Cartesian product: each existing alternative is concatenated with each
# new alternative, producing all possible combined sequences.
function extend_bytespans!(target::Vector{Vector{ByteSet}}, new::Vector{Vector{ByteSet}})
    isempty(new) && return
    if isempty(target)
        append!(target, new)
    else
        combined = [vcat(prev, ext) for prev in target for ext in new]
        empty!(target)
        append!(target, combined)
    end
end
