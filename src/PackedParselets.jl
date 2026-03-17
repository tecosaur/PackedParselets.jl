# SPDX-FileCopyrightText: © 2026 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# PackedParselets — parser compiler for bit-packed primitive types.
#
# Generates optimised parsers, printers, and accessors from declarative
# pattern specifications. This submodule has no knowledge of identifiers,
# PURLs, or checksums — those are added by the FastIdentifiers layer.

module PackedParselets

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

# Extension API for custom segment handlers
public ExprVarLine, NodeCtx, PatternExprs, ParserState,
    SegmentDef, SegmentOutput, SegmentBounds, SegmentCodegen, SegmentMeta,
    register_errmsg!, emit_pack, emit_extract, emit_lengthcheck,
    build_fail_expr!, unclaimed_sentinel,
    value_segment_output, implement_casting!,
    cardbits, cardtype, fastparse

end # module PackedParselets
