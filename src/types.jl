# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Core types for the PackedParselets compilation pipeline.
#
# All data structures used during compilation: type aliases, segment
# handler types (SegmentOutput, SegmentDef), pattern walking state
# (PatternExprs, ParserState, ParseBranch), and value segment schema.

## Type aliases

const ExprVarLine = Union{Expr, Symbol, LineNumberNode}
const NodeCtx = Base.ImmutableDict{Symbol, Any}

## SegmentOutput — handler return type

"""
    SentinelSpec(offset, width)

Describes where within a segment's bit allocation the optional-absence
sentinel lives. `offset` is relative to the end of the segment's allocation
(e.g. 0 = sentinel covers the trailing bits, -4 = sentinel starts 4 bits
before the end). `width` is the sentinel bit count.
"""
const SentinelSpec = @NamedTuple{offset::Int, width::Int}

"""
    SegmentBounds(parsed, printed, nbits, sentinel)

Byte and bit budget declared by a segment handler.

- `parsed`: input bytes consumed (min:max range)
- `printed`: output bytes produced (min:max range)
- `nbits`: bits to allocate in the packed representation (0 for non-value segments)
- `sentinel`: optional sentinel spec for absence encoding (`nothing` = no sentinel)
"""
struct SegmentBounds
    parsed::UnitRange{Int}       # bytes consumed from input (min:max)
    printed::UnitRange{Int}      # bytes produced in output (min:max)
    nbits::Int                   # bits to allocate (0 for non-value segments)
    sentinel::Union{Nothing, SentinelSpec}  # absence sentinel location, or nothing
end

"""
    SegmentCodegen(parse, extract, print_detect, impart, print)

Expression vectors produced by a segment handler.

- `parse`: input bytes -> value variable (appended to the parse expression list)
- `extract`: raw bits -> user-facing value (for getproperty, show, segments)
- `print_detect`: extract setup expressions routed to print or optional detect list
- `impart`: user argument -> raw value for bit-packing (for the constructor)
- `print`: extracted value -> formatted output (appended to the print expression list)
"""
struct SegmentCodegen
    parse::Vector{ExprVarLine}        # input bytes -> value var
    extract::Vector{ExprVarLine}      # raw bits -> user-facing value (full extract for segments)
    print_detect::Vector{ExprVarLine} # extract setup routed to print-time detection
    impart::Vector{Expr}               # user arg -> raw value for packing
    print::Vector{ExprVarLine}        # extracted value -> formatted output
end

"""
    SegmentMeta(label, desc, shortform, argtype, argvar[, context])

Metadata describing a segment for introspection and error messages.

- `label`: field name (from :fieldvar context) or gensym for anonymous segments
- `desc`: human-readable description for error messages
- `shortform`: compact pattern notation (e.g. "0-9 x 4")
- `argtype`: constructor parameter type annotation (Symbol, DataType, or nothing)
- `argvar`: gensym used as parameter placeholder in impart (nothing for non-value segments)
- `context`: handler-specific data for finalize hooks (nothing by default)
"""
struct SegmentMeta
    label::Symbol                # field name or gensym for anonymous
    desc::String                 # human-readable description
    shortform::String            # compact pattern notation for error messages
    argtype::Union{Symbol, DataType, Nothing}  # type annotation for constructor, or nothing
    argvar::Union{Nothing, Symbol} # parameter placeholder in impart
    context::Any                 # handler-specific data for finalize hooks
end
SegmentMeta(label, desc, shortform, argtype, argvar) =
    SegmentMeta(label, desc, shortform, argtype, argvar, nothing)

"""
    SegmentOutput(bounds, codegen, meta)

Structured return value from a segment compile handler.

Handlers read `state` and `nctx` but must not mutate them — the framework
handles all state changes via `process_segment_output!` after the handler
returns.
"""
struct SegmentOutput
    bounds::SegmentBounds
    codegen::SegmentCodegen
    meta::SegmentMeta
    bytespans::Vector{Vector{ByteSet}}
end

## SegmentDef — segment registry entry

"""
    SegmentDef(name, compile, kwargs[, finalize])

Description of a non-structural pattern node in the segment registry.

- `name`: pattern node name (e.g. :digits, :choice), used as the registry key
- `compile`: handler function with signature `(state, nctx, exprs, def, args) -> SegmentOutput`
- `kwargs`: keyword argument names accepted by this segment (for validation)
- `finalize`: optional post-assembly hook `(hookdata, exprs, state, name) -> nothing`,
   appends additional expressions to `hookdata::Vector{Expr}`
"""
struct SegmentDef
    name::Symbol
    compile::Function
    kwargs::Tuple{Vararg{Symbol}}
    finalize::Union{Nothing, Function}
end

SegmentDef(name, compile, kwargs) = SegmentDef(name, compile, kwargs, nothing)

## Pipeline types

# Hoisted optional sentinel: bit coordinates where absent = all-zero.
const OptSentinel = @NamedTuple{position::Int, nbits::Int}

"""
    ValueSegment

Schema for a single value-carrying pattern node in the packed representation.
"""
struct ValueSegment
    nbits::Int                            # bits consumed in packed representation
    kind::Symbol                          # :digits, :choice, :letters, :alphnum, :hex, :charset, :literal, :skip
    label::Symbol                         # attr_fieldname (inside field) or gensym (anonymous)
    desc::String                          # human-readable description
    shortform::String                     # compact pattern notation for error messages
    argtype::Union{Symbol, DataType, Nothing}  # type annotation for constructor, or nothing (non-parameterisable)
    argvar::Symbol                        # gensym used as parameter placeholder in impart
    extract::Vector{ExprVarLine}          # bits → typed value (last expr is the value)
    impart::Vector{Expr}                   # argvar → packed bits (validate + encode + orshift)
    condition::Union{Nothing, Symbol}     # optional scope gensym, nothing if required
end

"""
    PatternExprs

Accumulator for the expression vectors built during pattern walking.

Choice/optional arms construct instances that share `segments` and `properties`
with the parent while owning separate `parse`, `print`, and `bytespans` vectors.
"""
struct PatternExprs
    parse::Vector{ExprVarLine}
    print::Vector{ExprVarLine}
    segments::Vector{ValueSegment}
    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}}
    bytespans::Vector{Vector{ByteSet}}
end
PatternExprs() = PatternExprs([], [], [], [], [])

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
