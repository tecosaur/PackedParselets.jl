# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern handlers for value-carrying sequences: digits, character sequences
# (letters, alphnum, hex, charset), and embedded identifier types. These
# return SegmentOutput and let process_segment_output! handle framework mutations.

## Skip and groups kwargs

function parse_skip_kwarg(nctx::NodeCtx)
    raw = get(nctx, :skip, nothing)
    isnothing(raw) && return nothing
    raw isa String || throw(ArgumentError("skip must be a string of characters to skip, got $raw"))
    all(isascii, raw) || throw(ArgumentError("skip characters must be ASCII"))
    isempty(raw) && return nothing
    Tuple(map(UInt8, codeunits(raw)))
end

function parse_groups_kwarg(nctx::NodeCtx, nchars::Int, skipbytes)
    raw = get(nctx, :groups, nothing)
    isnothing(raw) && return nothing
    isnothing(skipbytes) &&
        throw(ArgumentError("groups requires skip (separator comes from the first skip character)"))
    groups = if raw isa Integer
        raw > 0 || throw(ArgumentError("groups must be positive"))
        ntuple(i -> Base.min(raw, nchars - raw * (i - 1)), cld(nchars, raw))
    elseif raw isa Tuple || (raw isa Expr && Meta.isexpr(raw, :tuple))
        vals = if raw isa Tuple raw else Tuple(raw.args) end
        all(v -> v isa Integer && v > 0, vals) ||
            throw(ArgumentError("groups must contain positive integers"))
        sum(vals) == nchars ||
            throw(ArgumentError("groups must sum to $nchars, got $(sum(vals))"))
        Tuple{Vararg{Int}}(vals)
    else
        throw(ArgumentError("groups must be an integer or tuple, got $(repr(raw))"))
    end
    length(groups) < 2 && return nothing
    groups
end

function emit_grouped(emit_group::Function, groups::Tuple, sep::UInt8)
    exprs = ExprVarLine[]
    for i in 1:length(groups)
        i > 1 && push!(exprs, :(write(io, $sep)))
        append!(exprs, emit_group(i, groups[i]))
    end
    exprs
end

## Digits

function compile_digits(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    length(args) ∈ (0, 1) || throw(ArgumentError("Expected at most one positional argument for digits, got $(length(args))"))
    # digits(UIntN) → digits(max=typemax(UIntN))
    if length(args) == 1 && args[1] isa Symbol
        T = Core.eval(state.mod, args[1])
        if T isa Type && T <: Unsigned
            get(nctx, :max, nothing) === nothing ||
                throw(ArgumentError("Cannot specify both a UInt type and max for digits"))
            nctx = NodeCtx(nctx, :max, Int(typemax(T)))
            args = Any[]
        end
    end
    base = get(nctx, :base, 10)::Int
    min = get(nctx, :min, 0)::Int
    max = get(nctx, :max, nothing)
    if max isa Expr
        max = Core.eval(state.mod, max)::Int
    end
    pad = get(nctx, :pad, 0)::Int
    skipbytes = parse_skip_kwarg(nctx)
    mindigits, maxdigits = parse_digit_range(args, max, base)
    min > 0 && (mindigits = Base.max(mindigits, ndigits(min; base)))
    fixedwidth = mindigits == maxdigits
    isnothing(max) && (max = (base^maxdigits) - 1)
    option = get(nctx, :optional, nothing)
    claims = is_sentinel_unclaimed(nctx)
    range = max - min + 1 + claims
    directval = cardbits(range) == cardbits(max + 1) && (min > 0 || !claims)
    dbits = cardbits(range)
    dI = cardtype(cardbits(max + 1))
    dT = cardtype(dbits)
    fieldvar = get(nctx, :fieldvar, gensym("digits"))
    bitpos = state.bits + dbits
    # gen_digit_parse reads parsed_min for SWAR safety, so call before
    # process_segment_output! updates bounds
    dspec = (; base, mindigits, maxdigits, min, max, pad, dI, dT, claims_sentinel=claims, skipbytes)
    parsed = gen_digit_parse(state, nctx, fieldvar, option, dspec)
    fnum = Symbol("$(fieldvar)_num")
    (; parsevar, directvar) = parsed
    posadv = if !isnothing(skipbytes)
        Symbol("$(fieldvar)_scanned")
    elseif fixedwidth
        maxdigits
    else
        Symbol("$(fieldvar)_bitsconsumed")
    end
    pexprs = ExprVarLine[parsed.exprs...,
        emit_pack(state, dT, parsevar, bitpos), :(pos += $posadv)]
    # Extract: raw bits → user-facing integer value
    fextract = :($fnum = $(emit_extract(state, bitpos, dbits)))
    fcast = if dI == dT fnum else :($fnum % $dI) end
    fvalue = if iszero(min) && claims
        :($fcast - $(one(dI)))
    elseif !directval && min - claims > 0
        :(($fcast + $(dI(min - claims))) % $dI)
    else
        fcast
    end
    propvalue = if max < typemax(dI) ÷ 2
        :($fvalue % $(signed(dI)))
    else
        fvalue
    end
    # Print codegen
    groups = parse_groups_kwarg(nctx, maxdigits, skipbytes)
    !isnothing(groups) && !fixedwidth &&
        throw(ArgumentError("groups requires fixed-width digits"))
    prexprs = if isnothing(groups)
        digits_print_exprs(fieldvar, fvalue, directvar, fnum,
                           fixedwidth, maxdigits, pad, base)
    else
        grouped_digits_print(fieldvar, fvalue, directvar, fnum,
                             groups, first(skipbytes), base)
    end
    # Constructor (impart) codegen
    argvar = gensym("arg_digit")
    body = digits_impart_exprs(state, argvar, fnum, parsevar, dI, dT, dspec,
                               directval, claims, bitpos)
    extract_setup = ExprVarLine[fextract]
    seg_extract, seg_impart = optional_wrap(option, argvar, extract_setup, propvalue, body)
    # Metadata and bytespans
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    seg_shortform, seg_desc = digits_meta(base, min, max, pad, mindigits, maxdigits, fixedwidth)
    sentinel = if claims SentinelSpec((0, dbits)) end
    has_skip = !isnothing(skipbytes)
    parsed_max = if has_skip
        (maxdigits + 1) * (length(skipbytes) + 1)
    else
        maxdigits
    end
    fixedpad = if fixedwidth maxdigits else 0 end
    nseps = if isnothing(groups) 0 else length(groups) - 1 end
    printmin = Base.max(ndigits(Base.max(min, 1); base), pad, fixedpad) + nseps
    printmax = Base.max(ndigits(max; base), pad, fixedpad) + nseps
    digit_set = digits_byteset(base)
    bytespans = if has_skip
        Vector{ByteSet}[]
    else
        [fill(digit_set, n) for n in mindigits:maxdigits]
    end
    SegmentOutput(
        SegmentBounds(mindigits:parsed_max, printmin:printmax, dbits, sentinel),
        SegmentCodegen(pexprs, seg_extract, extract_setup, seg_impart, prexprs),
        SegmentMeta(label, seg_desc, seg_shortform, :Integer, argvar),
        bytespans)
end

function digits_print_exprs(fieldvar::Symbol, fvalue, directvar::Bool, fnum::Symbol,
                            fixedwidth::Bool, maxdigits::Int, pad::Int, base::Int)
    printvar = if directvar fnum else fieldvar end
    printpad = if fixedwidth && maxdigits > 1; maxdigits
    elseif pad > 0; pad
    else 0 end
    printex = if printpad > 0
        :(print(io, string($printvar, base=$base, pad=$printpad)))
    elseif base == 10
        :(print(io, $printvar))
    else
        :(print(io, string($printvar, base=$base)))
    end
    prexprs = ExprVarLine[]
    directvar || push!(prexprs, :($fieldvar = $fvalue))
    push!(prexprs, printex)
    prexprs
end

function grouped_digits_print(fieldvar::Symbol, fvalue, directvar::Bool, fnum::Symbol,
                              groups::Tuple, sep::UInt8, base::Int)
    printvar = if directvar fnum else fieldvar end
    ngroups = length(groups)
    gvars = ntuple(i -> gensym("g$i"), ngroups)
    prexprs = ExprVarLine[]
    directvar || push!(prexprs, :($fieldvar = $fvalue))
    # Decompose via divrem from least-significant group upward
    remainder = printvar
    for i in ngroups:-1:2
        push!(prexprs, :(($remainder, $(gvars[i])) = divrem($remainder, $(base^groups[i]))))
    end
    push!(prexprs, :($(gvars[1]) = $remainder))
    append!(prexprs, emit_grouped(groups, sep) do gi, gsize
        ExprVarLine[:(print(io, string($(gvars[gi]), base=$base, pad=$gsize)))]
    end)
    prexprs
end

function digits_impart_exprs(state::ParserState, argvar::Symbol, fnum::Symbol,
                             parsevar::Symbol, dI::DataType, dT::DataType,
                             dspec::NamedTuple, directval::Bool, claims::Bool,
                             bitpos::Int)
    (; min, max) = dspec
    offset = min - claims
    encode_expr = if directval || iszero(offset)
        if dI != dT; :($parsevar = $fnum % $dT) else :($parsevar = $fnum) end
    elseif offset > 0
        :($parsevar = (($fnum - $(dT(offset))) % $dT))
    else # `offset < 0`  # sentinel claim with min==0: +1 to reserve zero for "absent"
        :($parsevar = ($fnum + $(one(dT))) % $dT)
    end
    body = Expr[]
    push!(body, :($argvar >= $min || throw(ArgumentError(
        string("Value ", $argvar, " is below minimum ", $min)))))
    push!(body, :($argvar <= $max || throw(ArgumentError(
        string("Value ", $argvar, " is above maximum ", $max)))))
    push!(body, :($fnum = $argvar % $dI))
    directval || push!(body, encode_expr)
    push!(body, emit_pack(state, dT, parsevar, bitpos))
    body
end

function digits_meta(base::Int, min::Int, max::Int, pad::Int,
                     mindigits::Int, maxdigits::Int, fixedwidth::Bool)
    charset = if base <= 10; "0-$(Char('0' + base - 1))"
    else "0-9A-$(Char('A' + base - 11))" end
    count = if fixedwidth; "$maxdigits" else "$mindigits:$maxdigits" end
    shortform = "$charset \u00d7 $count"
    desc = string(if fixedwidth; "$maxdigits" else "$mindigits-$maxdigits" end,
                  if isone(maxdigits) " digit" else " digits" end,
                  if base != 10 " in base $base" else "" end,
                  if min > 0 && max < base^maxdigits - 1
                      " between $(string(min; base, pad)) and $(string(max; base, pad))"
                  elseif min > 0
                      ", at least $(string(min; base, pad))"
                  elseif max < base^maxdigits - 1
                      ", at most $(string(max; base, pad))"
                  else "" end)
    shortform, desc
end

function digits_byteset(base::Int)
    if base <= 10
        ByteSet(UInt8('0'):UInt8('0' + base - 1))
    else
        ByteSet(UInt8('0'):UInt8('9')) ∪ ByteSet(UInt8('A'):UInt8('A' + base - 11)) ∪
        ByteSet(UInt8('a'):UInt8('a' + base - 11))
    end
end

function parse_digit_range(args::Vector, max::Union{Nothing, Integer}, base::Integer)
    if !isempty(args) && Meta.isexpr(first(args), :call, 3) && first(first(args).args) == :(:)
        lo, hi = first(args).args[2], first(args).args[3]
        (lo isa Integer && hi isa Integer) ||
            throw(ArgumentError("Range bounds for digits must be integer literals"))
        lo <= hi || throw(ArgumentError("digits range min must be <= max"))
        (lo, hi)
    elseif !isempty(args) && first(args) isa Integer
        n = first(args)
        (n, n)
    elseif !isnothing(max)
        (1, ndigits(max, base=base))
    else
        throw(ArgumentError("Must specify either a digits argument or a max argument for digits"))
    end
end

function charseq_impart_exprs(state::ParserState, cspec::NamedTuple,
                              argvar::Symbol, charvar::Symbol,
                              lenvar::Symbol, lenoffset::Symbol)
    (; cT, lT, cfold, oneindexed, ranges, kind, variable, minlen, maxlen,
       lenbase, bitpos, lenbits) = cspec
    kindstr = String(kind)
    body = Expr[
        :(($lenvar, $charvar) = parsechars($cT, String($argvar), $maxlen, $ranges, $cfold, $oneindexed)),
        :($lenvar == ncodeunits(String($argvar)) || throw(ArgumentError(
            string("Invalid characters in \"", $argvar, "\" for ", $kindstr))))]
    if variable
        push!(body,
            :($lenvar < $minlen && throw(ArgumentError(
                string("String \"", $argvar, "\" is too short (minimum ", $minlen, " characters)")))),
            :($lenvar > $maxlen && throw(ArgumentError(
                string("String \"", $argvar, "\" is too long (maximum ", $maxlen, " characters)")))))
    else
        push!(body,
            :($lenvar != $maxlen && throw(ArgumentError(
                string("String \"", $argvar, "\" must be exactly ", $maxlen, " characters")))))
    end
    push!(body, emit_pack(state, cT, charvar, bitpos - lenbits))
    if variable
        lenpack = if iszero(lenbase)
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(body, lenpack, emit_pack(state, lT, lenoffset, bitpos))
    end
    body
end

## Character sequences (letters, alphnum, hex, charset)

# Named charset canonical ranges.
# letters/alphnum include both cases (case-preserving by default).
# hex is single-case uppercase by default.
const NAMED_CHARSETS = (
    letters = (UInt8('A'):UInt8('Z'), UInt8('a'):UInt8('z')),
    alphnum = (UInt8('0'):UInt8('9'), UInt8('A'):UInt8('Z'), UInt8('a'):UInt8('z')),
    hex     = (UInt8('0'):UInt8('9'), UInt8('A'):UInt8('F')),
)

function compile_charseq(state::ParserState, nctx::NodeCtx, ::PatternExprs,
                         def::SegmentDef, args::Vector)
    kind = def.name
    named = haskey(NAMED_CHARSETS, kind)
    if named
        length(args) == 1 || throw(ArgumentError(
            "Expected exactly one positional argument for $kind"))
    else
        length(args) >= 2 || throw(ArgumentError(
            "charset requires a length and at least one character range"))
    end
    minlen, maxlen = parse_charseq_length(first(args), kind)
    base_ranges = if named NAMED_CHARSETS[kind] else parse_charset_ranges(args) end
    ranges, cfold = resolve_charseq_flags(state, nctx, kind, base_ranges)
    skipbytes = parse_skip_kwarg(nctx)
    compile_charseq_impl(state, nctx, minlen, maxlen, ranges, cfold, kind, skipbytes)
end

function parse_charseq_length(arg, kind::Symbol)
    if arg isa Integer
        (arg, arg)
    elseif Meta.isexpr(arg, :call, 3) && first(arg.args) == :(:)
        lo, hi = arg.args[2], arg.args[3]
        (lo isa Integer && hi isa Integer) ||
            throw(ArgumentError("Range bounds for $kind must be integer literals"))
        lo <= hi || throw(ArgumentError("$kind range min must be <= max"))
        (lo, hi)
    else
        throw(ArgumentError("Expected integer or range for $kind, got $arg"))
    end
end

function parse_charset_ranges(args::Vector)
    ranges = UnitRange{UInt8}[]
    for arg in @view args[2:end]
        if arg isa Char
            b = UInt8(arg)
            push!(ranges, b:b)
        elseif Meta.isexpr(arg, :call, 3) && first(arg.args) == :(:)
            lo, hi = arg.args[2], arg.args[3]
            (lo isa Char && hi isa Char) ||
                throw(ArgumentError("charset range bounds must be character literals, got $lo:$hi"))
            lo <= hi || throw(ArgumentError("charset range '$lo':'$hi' is empty"))
            push!(ranges, UInt8(lo):UInt8(hi))
        else
            throw(ArgumentError("charset arguments must be character ranges ('a':'z') or single characters ('x'), got $arg"))
        end
    end
    ranges
end

"""
    resolve_charseq_flags(state, nctx, kind, ranges) -> (Vector{UnitRange{UInt8}}, cfold::Bool)

Resolve `upper`/`lower`/`casefold` flags and transform character ranges.

- `casefold=true`: collapse letter ranges to uppercase, `cfold=true`
- `upper=true`: collapse letter ranges to uppercase, `cfold` from casefold flag
- `lower=true`: collapse letter ranges to lowercase, `cfold` from casefold flag
- No flags, `casefold=false`: ranges unchanged, `cfold=false`

Letter ranges (subsets of A-Z or a-z) are shifted to the target case and deduplicated.
Non-letter ranges pass through unchanged.
"""
function resolve_charseq_flags(::ParserState, nctx::NodeCtx, kind::Symbol, ranges)
    upper = get(nctx, :upper, false)::Bool
    lower = get(nctx, :lower, false)::Bool
    casefold = get(nctx, :casefold, false)::Bool
    upper && lower && throw(ArgumentError("Cannot specify both upper=true and lower=true for $kind"))
    if lower
        collapse_letter_ranges(ranges, :lower), casefold
    elseif upper || casefold
        collapse_letter_ranges(ranges, :upper), casefold
    else
        collect(UnitRange{UInt8}, ranges), false
    end
end

is_letter(r::UnitRange{UInt8}) =
    (first(r) in UInt8('A'):UInt8('Z') && last(r) in UInt8('A'):UInt8('Z')) ||
    (first(r) in UInt8('a'):UInt8('z') && last(r) in UInt8('a'):UInt8('z'))

function collapse_letter_ranges(ranges, target::Symbol)
    function shift_case(r::UnitRange{UInt8}, direction::Symbol)
        if direction === :upper
            (first(r) & 0xdf):(last(r) & 0xdf)
        else
            (first(r) | 0x20):(last(r) | 0x20)
        end
    end
    seen = Set{UnitRange{UInt8}}()
    out = UnitRange{UInt8}[]
    for r in ranges
        mapped = if is_letter(r) shift_case(r, target) else r end
        if mapped ∉ seen
            push!(seen, mapped)
            push!(out, mapped)
        end
    end
    sort!(out; by=first)
end

function compile_charseq_impl(state::ParserState, nctx::NodeCtx,
                              minlen::Int, maxlen::Int,
                              ranges::Vector{UnitRange{UInt8}},
                              cfold::Bool, kind::Symbol,
                              skipbytes::Union{Nothing, NTuple{<:Any, UInt8}} = nothing)
    ranges = Tuple(ranges)  # runtime functions dispatch on NTuple
    has_skip = !isnothing(skipbytes)
    variable = minlen != maxlen
    option = get(nctx, :optional, nothing)
    nvals = sum(length, ranges)
    claims = is_sentinel_unclaimed(nctx)
    oneindexed = claims && !variable
    bpc = cardbits(nvals + oneindexed)
    charbits = maxlen * bpc
    claim_via_length = claims && !oneindexed && variable
    optoffset = claim_via_length && minlen > 0
    directlen = variable && cardbits(maxlen + 1) == cardbits(maxlen - minlen + 1 + optoffset)
    lenbits = if !variable; 0
    else cardbits(if directlen; maxlen + 1 else maxlen - minlen + 1 + optoffset end)
    end
    totalbits = charbits + lenbits
    fieldvar = get(nctx, :fieldvar, gensym(string(kind)))
    charvar = Symbol("$(fieldvar)_chars")
    lenvar = Symbol("$(fieldvar)_len")
    lenoffset = Symbol("$(fieldvar)_lenoff")
    cT = cardtype(charbits)
    lT = if variable; cardtype(lenbits) else Nothing end
    bitpos = state.bits + totalbits
    lenbase = if directlen; 0 elseif optoffset; minlen - 1 else minlen end
    sentinel = if oneindexed
        SentinelSpec((-lenbits, charbits))
    elseif claim_via_length
        SentinelSpec((0, lenbits))
    end
    scanlimit = emit_lengthbound(state, nctx, maxlen)
    notfound = build_fail_expr!(state, nctx, if variable
        "Expected $minlen to $maxlen $kind characters"
    else
        "Expected $maxlen $kind characters"
    end)
    scannedvar = Symbol("$(fieldvar)_scanned")
    parse_exprs = if has_skip
        ExprVarLine[:(($lenvar, $charvar, $scannedvar) =
            parsechars($cT, idbytes, pos, $scanlimit, $ranges, $cfold, $oneindexed, $skipbytes))]
    else
        ExprVarLine[:(($lenvar, $charvar) =
            parsechars($cT, idbytes, pos, $scanlimit, $ranges, $cfold, $oneindexed))]
    end
    if !isnothing(option) && variable && iszero(minlen)
        push!(parse_exprs, :($lenvar > 0 || $notfound))
    else
        push!(parse_exprs,
              :(if $(if variable; :($lenvar < $minlen) else :($lenvar != $maxlen) end)
                    $notfound
                end))
    end
    posadv = if has_skip; scannedvar else lenvar end
    push!(parse_exprs, emit_pack(state, cT, charvar, bitpos - lenbits), :(pos += $posadv))
    if variable
        lenpack = if iszero(lenbase)
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(parse_exprs, lenpack, emit_pack(state, lT, lenoffset, bitpos))
    end
    # printchars/chars2string share the same arg pattern
    extracts = ExprVarLine[:($charvar = $(emit_extract(state, bitpos - lenbits, charbits)))]
    if variable
        push!(extracts, if iszero(lenbase)
            :($lenvar = $(emit_extract(state, bitpos, lenbits)))
        else
            :($lenvar = $(emit_extract(state, bitpos, lenbits)) + $lenbase)
        end)
    end
    charargs = if variable
        :($charvar, Int($lenvar), $ranges)
    else
        :($charvar, $maxlen, $ranges, $oneindexed)
    end
    groups = parse_groups_kwarg(nctx, maxlen, skipbytes)
    !isnothing(groups) && variable &&
        throw(ArgumentError("groups requires fixed-width character sequence"))
    printexprs = if isnothing(groups)
        ExprVarLine[:(printchars(io, $(charargs.args...)))]
    else
        # Precompute the bit shift for each group (chars remaining after it)
        shifts = let total = sum(groups)
            ntuple(length(groups)) do i
                total -= groups[i]
                total * bpc
            end
        end
        emit_grouped(groups, first(skipbytes)) do gi, gsize
            gexpr = if iszero(shifts[gi]) charvar else :($charvar >> $(shifts[gi])) end
            ExprVarLine[:(printchars(io, $gexpr, $gsize, $ranges, $oneindexed))]
        end
    end
    tostringex = :(chars2string($(charargs.args...)))
    argvar = gensym("arg_charseq")
    cspec = (; cT, lT, cfold, oneindexed, ranges, kind,
               variable, minlen, maxlen, lenbase, bitpos, lenbits)
    impart_body = charseq_impart_exprs(state, cspec, argvar, charvar, lenvar, lenoffset)
    seg_shortform = let charset = join((string(Char(first(r)), '-', Char(last(r))) for r in ranges), "")
        count = if variable; "$minlen:$maxlen" else "$maxlen" end
        "$charset × $count"
    end
    char_set = reduce(∪, ByteSet(r) for r in ranges; init=ByteSet())
    if cfold
        folded = ByteSet()
        for b in char_set
            if UInt8('A') <= b <= UInt8('Z')
                folded = folded ∪ ByteSet(b + 0x20)
            elseif UInt8('a') <= b <= UInt8('z')
                folded = folded ∪ ByteSet(b - 0x20)
            end
        end
        char_set = char_set ∪ folded
    end
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    seg_desc = string(if variable; "$minlen-$maxlen" else "$maxlen" end,
                      " ", kind, if maxlen > 1 " characters" else " character" end)
    seg_extract, seg_impart = optional_wrap(option, argvar, extracts, tostringex, impart_body)
    # Practical upper bound (see compile_digits for rationale)
    parsed_max = if has_skip
        (maxlen + 1) * (length(skipbytes) + 1)
    else
        maxlen
    end
    bytespans = if has_skip
        Vector{ByteSet}[]
    else
        let char_set = char_set
            [fill(char_set, n) for n in minlen:maxlen]
        end
    end
    nseps = if isnothing(groups) 0 else length(groups) - 1 end
    SegmentOutput(
        SegmentBounds(minlen:parsed_max, minlen+nseps:maxlen+nseps, totalbits, sentinel),
        SegmentCodegen(parse_exprs, seg_extract, copy(extracts), seg_impart, printexprs),
        SegmentMeta(label, seg_desc, seg_shortform, :AbstractString, argvar),
        bytespans)
end

## Embedded packed types

function compile_embed(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    length(args) == 1 || throw(ArgumentError("embed takes exactly one argument (the type)"))
    T = Core.eval(state.mod, args[1])
    T isa DataType && T <: state.supertype && isprimitivetype(T) ||
        throw(ArgumentError("embed type must be a primitive $(state.supertype) subtype, got $T"))
    ebits = nbits(T)
    epad = 8 * sizeof(T) - ebits
    option = get(nctx, :optional, nothing)
    claims = is_sentinel_unclaimed(nctx)
    presbits = Int(claims)
    fieldvar = get(nctx, :fieldvar, gensym("embed"))
    bitpos = state.bits + ebits + presbits
    # Packed types store values MSB-aligned, so shift right before packing, left after extracting
    to_lsb(val) = :(Core.Intrinsics.lshr_int($val, $epad))
    to_msb(val) = :(Core.Intrinsics.shl_int($val, $epad))
    eresult = Symbol("$(fieldvar)_result")
    epos = Symbol("$(fieldvar)_epos")
    notfound = build_fail_expr!(state, nctx, "Invalid embedded $(T)")
    eshifted = Symbol("$(fieldvar)_shifted")
    pack = emit_pack(state, T, eshifted, bitpos - presbits)
    parse_exprs = ExprVarLine[
          :(($eresult, $epos) = $(GlobalRef(PackedParselets, :parsebytes))($T, @view idbytes[pos:end])),
          :(if !($eresult isa $T); $notfound end),
          :($eshifted = $(to_lsb(eresult))),
          pack]
    if claims
        push!(parse_exprs, emit_pack(state, Bool, true, bitpos))
    end
    push!(parse_exprs, :(pos += $epos - 1))
    fextract = :($fieldvar = $(to_msb(emit_extract(state, bitpos - presbits, ebits, T))))
    argvar = gensym("arg_embed")
    argshifted = gensym("arg_embed_shifted")
    body = Expr[:($argshifted = $(to_lsb(argvar))),
               emit_pack(state, T, argshifted, bitpos - presbits)]
    if presbits > 0
        push!(body, emit_pack(state, Bool, true, bitpos))
    end
    sentinel = if claims SentinelSpec((0, presbits)) end
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    extract_setup = ExprVarLine[fextract]
    seg_extract, seg_impart = optional_wrap(option, argvar, extract_setup, fieldvar, body)
    SegmentOutput(
        SegmentBounds(parsebounds(T)[1]:parsebounds(T)[2],
                      printbounds(T)[1]:printbounds(T)[2],
                      ebits + presbits, sentinel),
        SegmentCodegen(parse_exprs, seg_extract, extract_setup, seg_impart,
                       ExprVarLine[:(__tobytes_print(io, $fieldvar))]),
        SegmentMeta(label, "embedded $(T)", string(T), T, argvar),
        Vector{ByteSet}[])
end
