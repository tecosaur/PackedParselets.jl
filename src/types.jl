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

## SegmentOutput: handler return type

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
    PrintExprs(; direct, vars, getval, getlen, putval)

Print-phase expression bundle produced by segment handlers.

- `direct`: self-contained extract+write (for `tobytes(buf, id)` and `print(io, id)`)
- `vars`: variables shared across phases, with default values (`Symbol => init`)
- `getval`: extract bit-packed values to variables declared in `vars`
- `getlen`: increment `pos` by the output byte count (using variables from `getval`)
- `putval`: write to buffer/IO using variables from `getval`, incrementing `pos`
"""
const PrintExprs = @NamedTuple{
    direct::Vector{ExprVarLine},
    vars::Vector{Pair{Symbol, Any}},
    getval::Vector{ExprVarLine},
    getlen::Vector{ExprVarLine},
    putval::Vector{ExprVarLine},
}

PrintExprs(; direct=ExprVarLine[], vars=Pair{Symbol,Any}[],
             getval=ExprVarLine[], getlen=ExprVarLine[],
             putval=ExprVarLine[]) =
    (direct=direct, vars=vars, getval=getval, getlen=getlen, putval=putval)

"""
    SegmentCodegen(parse, extract, print, impart)

Expression vectors produced by a segment handler.

- `parse`: input bytes -> value variable (appended to the parse expression list)
- `extract`: raw bits -> user-facing value (for getproperty, show, segments)
- `print`: output expressions as a `PrintExprs` named tuple
- `impart`: user argument -> raw value for bit-packing (for the constructor)
"""
struct SegmentCodegen
    parse::Vector{ExprVarLine}        # input bytes -> value var
    extract::Vector{ExprVarLine}      # raw bits -> user-facing value (full extract for segments)
    print::PrintExprs                 # output expression bundle
    impart::Vector{Expr}               # user arg -> raw value for packing
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

Handlers read `state` and `nctx` but must not mutate them: the framework
handles all state changes via `process_segment_output!` after the handler
returns.
"""
struct SegmentOutput
    bounds::SegmentBounds
    codegen::SegmentCodegen
    meta::SegmentMeta
    bytespans::Vector{Vector{ByteSet}}
end

## Errors

"""
    InvalidPacking(type, field, value)

A value of the packed `type` whose `field` (`nothing` when unnamed) holds `value`,
which parsing and constructors never produce: its bits came from elsewhere, such as
`reinterpret` of raw data. Printing or reading such a field throws this rather than
going out of bounds.
"""
struct InvalidPacking <: Exception
    type::Type
    field::Union{Symbol, Nothing}
    value::Integer
end

function Base.showerror(io::IO, e::InvalidPacking)
    print(io, "InvalidPacking: a ", e.type, " value holds ", e.value, " in ",
          if isnothing(e.field) "an unnamed field" else "field `$(e.field)`" end,
          ", which parsing and constructors never produce. Its bits must have come ",
          "from elsewhere (e.g. `reinterpret` of raw data); check that source.")
end

## SegmentDef: segment registry entry

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
    print::PrintExprs
    segments::Vector{ValueSegment}
    properties::Vector{Pair{Symbol, Union{Symbol, Vector{ExprVarLine}}}}
    bytespans::Vector{Vector{ByteSet}}
end
PatternExprs() = PatternExprs([], PrintExprs(), [], [], [])

# A digit field's values and how they're stored: `dI` holds a value, `dT` its encoding,
# which offsets values by `vmin`, and by one more when zero is claimed to mark absence
struct DigitSpec
    fieldvar::Symbol
    base::Int
    mindigits::Int
    maxdigits::Int
    vmin::Int128
    vmax::Int128
    pad::Int
    claims::Bool
    skipbytes::Union{Nothing, Tuple{Vararg{UInt8}}}
    exclude::Union{Nothing, Vector{UnitRange{Int}}}
    groups::Union{Nothing, Vector{Int}}
    dbits::Int
    dI::DataType
    dT::DataType
    direct::Bool
    fnum::Symbol
    parsevar::Symbol
end

function DigitSpec(fieldvar::Symbol, base::Int, mindigits::Int, maxdigits::Int, vmin::Int128, vmax::Int128,
                   pad::Int, claims::Bool, @nospecialize(skipbytes), exclude, groups)
    dbits = cardbits(vmax - vmin + 1 + claims)
    direct = dbits == cardbits(vmax + 1) && (vmin > 0 || !claims)
    fnum = Symbol("$(fieldvar)_num")
    DigitSpec(fieldvar, base, mindigits, maxdigits, vmin, vmax, pad, claims, skipbytes, exclude, groups,
              dbits, cardtype(cardbits(vmax + 1)), cardtype(dbits), direct, fnum, if direct fnum else fieldvar end)
end

"""
    ParseBranch

Per-branch byte counters for tracking parse/print bounds through optional nesting.

The root branch covers the required pattern; each `optional(...)` forks a child.
`parsed_min`/`parsed_max` track cumulative input bytes consumed;
`print_min`/`print_max` track cumulative output bytes produced.
`close_min` is the parent's `parsed_min` where the branch's construct ends.
Length-check sentinels reference these counters so that `resolve_sentinel_in_expr!`
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
    close_min::Int
end

"""
    ParserState

Global mutable state for pattern compilation (bit width, branches, errors).

- `supertype`: abstract supertype for the generated primitive type
- `globals`: domain-specific keyword arguments for finalize hooks to read
- `segments`: the registry of segment definitions patterns may use
- `kwnames`: every keyword a pattern may set, the segments' and the globals'
"""
mutable struct ParserState
    const name::Symbol
    const mod::Module
    bits::Int
    const supertype::Type
    const globals::NamedTuple
    const segments::NamedTuple
    const kwnames::Vector{Symbol}
    const branches::Vector{ParseBranch}
    const errconsts::Vector{String}
    const segment_outputs::Vector{Pair{Symbol, SegmentOutput}}
end

## Choice hashing
#
# Hash searches run once per choice at macro-expansion time. Their data is kept to
# pattern-independent types (no tuples sized by the options, no captured register
# types), so the search compiles once rather than once per pattern shape.

"""
    WindowHash(mul, shift, modulus)

Hash of a little-endian register window `v` of `w` bits:
`((v * mul) mod 2^w >> shift) % modulus + 1`, or `v` itself when `modulus` is zero.
"""
struct WindowHash
    mul::UInt64
    shift::Int
    modulus::Int
end

"""
    HashPlan

A hash of the register window at byte `pos` (loaded as `iT`, OR-ed with `foldmask`
when casefolding) that identifies each of a choice's options, from `find_window_hash`.

- `table`: the option index of each hash value, or empty when the hash less `offset`
  is the option index; `table2` holds a second candidate per slot, when there are any
- `perm`: option order matching the indices
- `injective`: the hash alone distinguishes every window value (identity family),
  so the window's bytes need no further verification
"""
struct HashPlan
    pos::Int
    iT::DataType
    foldmask::UInt64
    hash::WindowHash
    offset::Int
    perm::Vector{Int}
    table::Vector{Int}
    table2::Vector{Int}
    injective::Bool
end

# `record`: a match stores its index (`:index`), `true` (`:flag`), or nothing (`:none`)
struct ChoiceMatch
    mopts::Vector{String}
    sopts::Vector{String}
    casefold::Bool
    fieldvar::Symbol
    cint::DataType
    record::Symbol
end

# `injective`: a hit identifies the window value
const HashCandidate = @NamedTuple{hash::WindowHash, injective::Bool, maxval::UInt64}
