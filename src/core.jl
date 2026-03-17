# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Core types, constants, and state-mutation helpers for pattern codegen.
#
# Defines the data structures threaded through pattern walking
# (PatternExprs, ParserState, ParseBranch) and the small helpers
# that every pattern handler calls to track bits, bytes, errors,
# and segments.

## Type aliases

# Hoisted optional sentinel: bit coordinates where absent = all-zero.
const OptSentinel = @NamedTuple{position::Int, nbits::Int}

# Schema for a single value-carrying pattern node in the packed representation.
const ValueSegment = @NamedTuple{
    nbits::Int,                            # bits consumed in packed representation
    kind::Symbol,                          # :digits, :choice, :letters, :alphnum, :hex, :charset, :literal, :skip
    label::Symbol,                         # attr_fieldname (inside field) or gensym (anonymous)
    desc::String,                          # human-readable description
    shortform::String,                     # compact pattern notation for error messages
    argtype::Any,                          # :Integer, :Symbol, :AbstractString, or nothing (non-parameterisable)
    argvar::Symbol,                        # gensym used as parameter placeholder in impart
    extract::Vector{ExprVarLine},          # bits → typed value (last expr is the value)
    impart::Vector{Any},                   # argvar → packed bits (validate + encode + orshift)
    condition::Union{Nothing, Symbol},     # optional scope gensym, nothing if required
}

# Accumulator for the expression vectors built during pattern walking.
const PatternExprs = @NamedTuple{
    parse::Vector{ExprVarLine},
    print::Vector{ExprVarLine},
    segments::Vector{ValueSegment},
    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}},
}

## Structs

"""
    ParseBranch

Per-branch byte counters for tracking parse/print bounds through optional nesting.

The root branch covers the required pattern; each `optional(...)` forks a child.
`parsed_min`/`parsed_max` track cumulative input bytes consumed;
`print_min`/`print_max` track cumulative output bytes produced.
Length-check sentinels reference these counters so that `insert_length_checks!`
can fold static guarantees and emit minimal runtime checks.
"""
mutable struct ParseBranch
    const id::Int
    const parent::Union{Nothing, ParseBranch}
    const scope::Symbol
    const start_min::Int
    const start_max::Int
    parsed_min::Int
    parsed_max::Int
    print_min::Int
    print_max::Int
end

"""
    ParserState

Global mutable state for pattern compilation (bit width, branches, errors).

- `supertype`: abstract supertype for the generated primitive type
- `globals`: domain-specific keyword arguments for finalize hooks to read
"""
mutable struct ParserState
    const name::Symbol
    const mod::Module
    bits::Int
    const supertype::Type
    const globals::NamedTuple
    const branches::Vector{ParseBranch}
    const errconsts::Vector{String}
    const segment_outputs::Vector{Pair{Symbol, SegmentOutput}}
end

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
    tobytes(id) -> (buf, len)

Buffer-based output. Returns `(Memory{UInt8}, length)`.
"""
function tobytes end

"""
    segments(::Type{T}) -> Tuple
    segments(id) -> Tuple

Return type-level segment schema or instance-level segment values.
"""
function segments end

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

## Segment and property assembly

"""
    value_segment_output(; nbits, fieldvar, desc, shortform,
                          argvar, base_argtype, option,
                          sentinel, parsed, printed,
                          parse, extract_setup, extract_value,
                          present_check, impart_body, print)

Build a `SegmentOutput` for a value-carrying segment with the standard
required/optional split: optional fields get a presence-guarded extract
and isnothing-guarded impart.
"""
function value_segment_output(;
        bounds::SegmentBounds,
        fieldvar::Symbol, desc::String, shortform::String,
        argvar::Symbol, base_argtype::Any, option::Union{Nothing, Symbol},
        parse::Vector{ExprVarLine},
        extract_setup::Vector{ExprVarLine}, extract_value::Any,
        present_check::Any = true,
        impart_body::Vector{Any}, print::Vector{ExprVarLine})
    seg_extract = if isnothing(option)
        ExprVarLine[extract_setup..., extract_value]
    else
        ExprVarLine[extract_setup..., :(if $present_check; $extract_value end)]
    end
    seg_impart, seg_argtype = if isnothing(option)
        copy(impart_body), base_argtype
    else
        wrapped = Expr(:if, :(!isnothing($argvar)), Expr(:block, impart_body...))
        Any[wrapped], :(Union{$base_argtype, Nothing})
    end
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    SegmentOutput(
        bounds,
        SegmentCodegen(parse, seg_extract, copy(extract_setup), seg_impart, print),
        SegmentMeta(label, desc, shortform, seg_argtype, argvar))
end

"""
    emit_print_detect!(exprs::PatternExprs, nctx::NodeCtx, option, extracts)

Route extract expressions to the right target.

For optional fields (non-nothing `option`), appends to `nctx[:oprint_detect]`
so the enclosing optional handler can emit them before the conditional print
block. For required fields, appends directly to `exprs.print`.
"""
function emit_print_detect!(exprs::PatternExprs, nctx::NodeCtx,
                            option, extracts::Vector{ExprVarLine})
    if !isnothing(option)
        append!(nctx[:oprint_detect], extracts)
    else
        append!(exprs.print, extracts)
    end
end

## Bit packing

function zero_int(@nospecialize(T::DataType))
    if sizeof(T) == 1
        Core.bitcast(T, 0x00)
    else
        Core.Intrinsics.zext_int(T, 0x0)
    end
end

zero_parsed_expr(state::ParserState) =
    if state.bits <= 8
        :(Core.bitcast($(esc(state.name)), 0x00))
    else
        :(Core.Intrinsics.zext_int($(esc(state.name)), 0x0))
    end

function emit_pack(state::ParserState, type::Type, value::Union{Symbol, Expr, Bool}, shift::Int)
    valcast = Expr(:call, :__cast_to_id, type, value)
    :(parsed = Core.Intrinsics.or_int(parsed, Core.Intrinsics.shl_int($valcast, (8 * sizeof($(esc(state.name))) - $shift))))
end

function emit_extract(state::ParserState, position::Int, width::Int,
                            fT::Type=cardtype(width))
    fTbits = 8 * sizeof(fT)
    fval = :(Core.Intrinsics.lshr_int(id, 8 * sizeof($(esc(state.name))) - $position))
    ival = Expr(:call, :__cast_from_id, fT, fval)
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
    # Build scope→parent_scope mapping from branch tree
    scope_parent = Dict{Symbol, Symbol}()
    for b in branches
        b.scope === :root && continue
        scope_parent[b.scope] = b.parent.scope
    end
    io = IOBuffer()
    scope_stack = Symbol[]  # stack of active optional scopes
    for seg in segments
        target = seg.condition
        # Walk down from current scope to find the common ancestor with target
        current = isempty(scope_stack) ? nothing : last(scope_stack)
        if target !== current
            # Build ancestor chain for target scope
            target_chain = Symbol[]
            s = target
            while !isnothing(s)
                push!(target_chain, s)
                s = get(scope_parent, s, nothing)
            end
            reverse!(target_chain)
            # Find how many levels of the current stack match
            shared = 0
            for i in 1:min(length(scope_stack), length(target_chain))
                scope_stack[i] === target_chain[i] || break
                shared = i
            end
            # Close scopes that are no longer active
            for _ in shared+1:length(scope_stack)
                print(io, ']')
            end
            resize!(scope_stack, shared)
            # Open new scopes
            for i in shared+1:length(target_chain)
                print(io, '[')
                push!(scope_stack, target_chain[i])
            end
        end
        isempty(seg.shortform) && continue
        if seg.kind in (:literal, :skip)
            print(io, seg.shortform)
        else
            print(io, '<', seg.shortform, '>')
        end
    end
    # Close all remaining open brackets
    for _ in scope_stack
        print(io, ']')
    end
    String(take!(io))
end

## Optional context helpers

# Build the failure block for an optional scope: set flag=false, jump to cleanup label.
function opt_fail_expr(flag::Symbol, label::Symbol)
    Expr(:block, :($flag = false), :(@goto $label))
end

# Build a parse-failure expression: `return (erridx, pos)` in required context,
# `opt_fail_expr(...)` inside an optional scope.
function build_fail_expr!(state::ParserState, nctx::NodeCtx, msg::String)
    option = get(nctx, :optional, nothing)
    if isnothing(option)
        erridx = register_errmsg!(state, msg)
        :(return ($erridx, pos))
    else
        opt_fail_expr(option, nctx[:opt_label])
    end
end

## Optional sentinel helpers

unclaimed_sentinel(nctx::NodeCtx) =
    (ref = get(nctx, :optional_sentinel, nothing)) !== nothing && ref[] === nothing

function claim_sentinel!(nctx::NodeCtx, position::Int, nbits::Int)
    nctx[:optional_sentinel][] = OptSentinel((position, nbits))
end

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
    # Segment markers for assembly-phase length-check insertion.
    # Store context needed to build a fail_expr later (without registering
    # error messages now, which would shift indices for the old pass).
    seg_id = length(state.segment_outputs) + 1
    b = nctx[:current_branch]
    opt_label = get(nctx, :opt_label, nothing)
    push!(exprs.parse, Expr(:call, :__segment_begin, seg_id, b.id,
                            first(bounds.parsed), last(bounds.parsed),
                            option, opt_label, meta.desc))
    # Parse codegen
    append!(exprs.parse, codegen.parse)
    push!(exprs.parse, Expr(:call, :__segment_end, seg_id))
    # Bit allocation
    if bounds.nbits > 0
        state.bits += bounds.nbits
    end
    # Sentinel claiming
    if !isnothing(bounds.sentinel) && unclaimed_sentinel(nctx)
        claim_sentinel!(nctx, state.bits + bounds.sentinel.offset, bounds.sentinel.width)
    end
    # Byte bounds
    inc_parsed!(nctx, first(bounds.parsed), last(bounds.parsed))
    inc_print!(nctx, first(bounds.printed), last(bounds.printed))
    # Print codegen routing (optional fields route through oprint_detect)
    emit_print_detect!(exprs, nctx, option, codegen.print_detect)
    append!(exprs.print, codegen.print)
    # Segment registration (ValueSegment for compatibility)
    argvar = if isnothing(meta.argvar); :_ else meta.argvar end
    push!(exprs.segments, ValueSegment((
        bounds.nbits, kind, meta.label, meta.desc, meta.shortform,
        meta.argtype, argvar,
        codegen.extract, codegen.impart, option)))
    push!(exprs.print, :(__segment_printed = $(length(exprs.segments))))
    # Store for assembly-phase use
    push!(state.segment_outputs, kind => output)
end
