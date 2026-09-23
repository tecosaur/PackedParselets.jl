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

# Run maketype on representative patterns so the choice/charseq codegen functions
# (build_hash_matcher, choice_setup, build_linear_matcher, gen_tail_verify, …) are
# inferred and cached here, instead of re-inferred at every downstream @defid.
# Segment handlers are reached through `SegmentDef` function fields, which
# inference can't follow from an entry-point precompile directive, so only actual
# maketype calls warm them. maketype stops before eval, so no type is defined or leaked.
using PrecompileTools: @compile_workload
@compile_workload begin
    m = @__MODULE__
    maketype(CORE_SEGMENTS, m, :_WarmHash,
             :((:p(choice("AA", "BB", "CC")), :id(digits(max=999999999)))))
    maketype(CORE_SEGMENTS, m, :_WarmLinear,
             :((skip(choice("Q:", "Q_", "Q")), :id(digits(6, pad=6)))))
    maketype(CORE_SEGMENTS, m, :_WarmTagged,
             :(choice(:kind, :a => seq("A", :v(digits(2))),
                             :b => seq("B", :v(digits(3))))))
end

end # module PackedParselets
