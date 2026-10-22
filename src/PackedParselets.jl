# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# PackedParselets: parser compiler for bit-packed primitive types.
#
# Generates optimised parsers, printers, and accessors from declarative
# pattern specifications.

module PackedParselets

include("bytemask.jl")
include("types.jl")
include("core.jl")
include("loaders.jl")
include("utils.jl")
include("swar.jl")
include("placeholders.jl")
include("stringly.jl")
include("choices.jl")
include("sequences.jl")
include("dispatch.jl")
include("methods.jl")

export parsebytes, tobytes, segments, nbits, parsebounds, printbounds,
    maketype, CORE_SEGMENTS

public InvalidPacking

# Extension API for custom segment handlers
public ExprVarLine, NodeCtx, PatternExprs, ParserState, ByteSet, PrintExprs,
    SegmentDef, SegmentOutput, SegmentBounds, SegmentCodegen, SegmentMeta,
    build_fail_expr!, emit_pack, emit_extract, emit_lengthcheck,
    is_sentinel_unclaimed, implement_casting!

# Handlers sit in `SegmentDef` fields, out of inference's reach from `maketype`
if ccall(:jl_generating_output, Cint, ()) == 1
    @assert precompile(maketype, (typeof(CORE_SEGMENTS), Module, Symbol, Expr))
    for def in CORE_SEGMENTS
        @assert precompile(def.compile, (ParserState, NodeCtx, PatternExprs, SegmentDef, Vector{Any}))
    end
end

end # module PackedParselets
