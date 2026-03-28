# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

# Pattern handlers for value-carrying sequences: digits, character sequences
# (letters, alphnum, hex, charset), and embedded identifier types. These
# return SegmentOutput and let process_segment_output! handle framework mutations.

## Skip kwarg

# Parse the `skip` keyword into a Tuple{UInt8...} expression for codegen.
# Accepts a string of characters to skip (e.g. "-" or "- .").
function parse_skip_kwarg(nctx::NodeCtx)
    raw = get(nctx, :skip, nothing)
    isnothing(raw) && return nothing
    raw isa String || throw(ArgumentError("skip must be a string of characters to skip, got $raw"))
    all(isascii, raw) || throw(ArgumentError("skip characters must be ASCII"))
    isempty(raw) && return nothing
    Tuple(map(UInt8, codeunits(raw)))
end

## Digits

function compile_digits(state::ParserState, nctx::NodeCtx, ::PatternExprs, ::SegmentDef, args::Vector{Any})
    length(args) ∈ (0, 1) || throw(ArgumentError("Expected at most one positional argument for digits, got $(length(args))"))
    base = get(nctx, :base, 10)::Int
    min = get(nctx, :min, 0)::Int
    max = get(nctx, :max, nothing)
    if max isa Expr
        max = Core.eval(state.mod, max)::Int
    end
    pad = get(nctx, :pad, 0)::Int
    skipbytes = parse_skip_kwarg(nctx)
    mindigits, maxdigits = parse_digit_range(args, max, base)
    if min > 0
        mindigits = Base.max(mindigits, ndigits(min; base))
    end
    fixedwidth = mindigits == maxdigits
    if isnothing(max)
        max = (base^maxdigits) - 1
    end
    option = get(nctx, :optional, nothing)
    claims = unclaimed_sentinel(nctx)
    range = max - min + 1 + claims
    directval = cardbits(range) == cardbits(max + 1) && (min > 0 || !claims)
    dbits = cardbits(range)
    dI = cardtype(cardbits(max + 1))
    dT = cardtype(dbits)
    fieldvar = get(nctx, :fieldvar, gensym("digits"))
    nbits_pos = state.bits + dbits
    fixedpad = ifelse(fixedwidth, maxdigits, 0)
    printmin = Base.max(ndigits(Base.max(min, 1); base), pad, fixedpad)
    printmax = Base.max(ndigits(max; base), pad, fixedpad)
    # gen_digit_parse reads parsed_min for SWAR safety, so call before process_segment_output! updates bounds
    dspec = (; base, mindigits, maxdigits, min, max, pad, dI, dT, claims_sentinel=claims, skipbytes)
    parsed = gen_digit_parse(state, nctx, fieldvar, option, dspec)
    fnum = Symbol("$(fieldvar)_num")
    bitsconsumed = Symbol("$(fieldvar)_bitsconsumed")
    (; parsevar, directvar) = parsed
    posadv = if !isnothing(skipbytes)
        Symbol("$(fieldvar)_scanned")
    elseif fixedwidth
        maxdigits
    else
        bitsconsumed
    end
    parse_exprs = ExprVarLine[parsed.exprs...,
        emit_pack(state, dT, parsevar, nbits_pos), :(pos += $posadv)]
    fextract = :($fnum = $(emit_extract(state, nbits_pos, dbits)))
    fcast = if dI == dT; fnum else :($fnum % $dI) end
    fvalue = if iszero(min) && claims
        :($fcast - $(one(dI)))
    elseif !directval && min - claims > 0
        :(($fcast + $(dI(min - claims))) % $dI)
    else
        fcast
    end
    printvar = ifelse(directvar, fnum, fieldvar)
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
    print_exprs = ExprVarLine[]
    directvar || push!(print_exprs, :($fieldvar = $fvalue))
    push!(print_exprs, printex)
    propvalue = if max < typemax(dI) ÷ 2
        sI = signed(dI)
        :($fvalue % $sI)
    else
        fvalue
    end
    argvar = gensym("arg_digit")
    directval = cardbits(max - min + 1 + claims) ==
                cardbits(max + 1) && (min > 0 || !claims)
    offset = min - claims
    encode_expr = if directval
        if dI != dT; :($parsevar = $fnum % $dT) else :($parsevar = $fnum) end
    elseif offset > 0
        :($parsevar = (($fnum - $(dT(offset))) % $dT))
    elseif offset < 0  # sentinel claim with min==0: +1 to reserve zero for "absent"
        :($parsevar = ($fnum + $(one(dT))) % $dT)
    else
        if dI != dT; :($parsevar = $fnum % $dT) else :($parsevar = $fnum) end
    end
    body = Any[]
    push!(body, :($argvar >= $min || throw(ArgumentError(
        string("Value ", $argvar, " is below minimum ", $min)))))
    push!(body, :($argvar <= $max || throw(ArgumentError(
        string("Value ", $argvar, " is above maximum ", $max)))))
    push!(body, :($fnum = $argvar % $dI))
    directvar || push!(body, encode_expr)
    push!(body, emit_pack(state, dT, parsevar, nbits_pos))
    seg_shortform = let charset = if base <= 10; "0-$(Char('0' + base - 1))"
                                   else "0-9A-$(Char('A' + base - 11))" end
        count = if fixedwidth; "$maxdigits" else "$mindigits:$maxdigits" end
        "$charset \u00d7 $count"
    end
    seg_desc = string(if fixedwidth; "$maxdigits" else "$mindigits-$maxdigits" end,
                      if isone(maxdigits); " digit" else " digits" end,
                      base != 10 ? " in base $base" : "",
                      if min > 0 && max < base^maxdigits - 1
                          " between $(string(min; base, pad)) and $(string(max; base, pad))"
                      elseif min > 0
                          ", at least $(string(min; base, pad))"
                      elseif max < base^maxdigits - 1
                          ", at most $(string(max; base, pad))"
                      else "" end)
    sentinel = if claims; SentinelSpec((0, dbits)) else nothing end
    digit_set = if base <= 10
        ByteSet(UInt8('0'):UInt8('0' + base - 1))
    else
        ByteSet(UInt8('0'):UInt8('9')) ∪ ByteSet(UInt8('A'):UInt8('A' + base - 11)) ∪
        ByteSet(UInt8('a'):UInt8('a' + base - 11))
    end
    label = Symbol(chopprefix(String(fieldvar), "attr_"))
    extract_setup = ExprVarLine[fextract]
    seg_extract, seg_impart = optional_wrap(option, argvar, extract_setup, propvalue, body)
    has_skip = !isnothing(skipbytes)
    # Practical upper bound: at most one of each skip char kind between
    # value chars (and at boundaries). Pathological inputs with runs of
    # skip chars may exceed this, but such inputs are degenerate.
    parsed_max = if has_skip
        (maxdigits + 1) * (length(skipbytes) + 1)
    else
        maxdigits
    end
    bytespans = if has_skip
        Vector{ByteSet}[]
    else
        [fill(digit_set, n) for n in mindigits:maxdigits]
    end
    SegmentOutput(
        SegmentBounds(mindigits:parsed_max, printmin:printmax, dbits, sentinel),
        SegmentCodegen(parse_exprs, seg_extract, extract_setup, seg_impart, print_exprs),
        SegmentMeta(label, seg_desc, seg_shortform, :Integer, argvar),
        bytespans)
end

function parse_digit_range(args, max, base)
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
                         def::SegmentDef, args::Vector{Any})
    kind = def.name
    named = haskey(NAMED_CHARSETS, kind)
    minargs = named ? 1 : 2
    length(args) >= minargs || throw(ArgumentError(
        named ? "Expected exactly one positional argument for $kind" :
                "charset requires a length and at least one character range"))
    named && length(args) > 1 && throw(ArgumentError(
        "Expected exactly one positional argument for $kind"))
    minlen, maxlen = parse_charseq_length(first(args), kind)
    base_ranges = named ? NAMED_CHARSETS[kind] : parse_charset_ranges(args)
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

function parse_charset_ranges(args)
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
function resolve_charseq_flags(state::ParserState, nctx, kind::Symbol, ranges)
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
        mapped = if is_letter(r); shift_case(r, target) else r end
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
    bpc = cardbits(nvals)
    claims = unclaimed_sentinel(nctx)
    oneindexed = claims && !variable
    if oneindexed; bpc = cardbits(nvals + 1) end
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
    nbits_pos = state.bits + totalbits
    lenbase = if directlen; 0 elseif optoffset; minlen - 1 else minlen end
    sentinel = if oneindexed; SentinelSpec((-lenbits, charbits))
    elseif claim_via_length; SentinelSpec((0, lenbits))
    else nothing end
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
    if !isnothing(option) && variable && minlen == 0
        push!(parse_exprs, :($lenvar > 0 || $notfound))
    else
        push!(parse_exprs,
              :(if $(if variable; :($lenvar < $minlen) else :($lenvar != $maxlen) end)
                    $notfound
                end))
    end
    posadv = if has_skip; scannedvar else lenvar end
    push!(parse_exprs, emit_pack(state, cT, charvar, nbits_pos - lenbits), :(pos += $posadv))
    if variable
        lenpack = if lenbase == 0
            :($lenoffset = $lenvar % $lT)
        else
            :($lenoffset = ($lenvar - $lenbase) % $lT)
        end
        push!(parse_exprs, lenpack, emit_pack(state, lT, lenoffset, nbits_pos))
    end
    # printchars/chars2string share the same arg pattern
    extracts = ExprVarLine[:($charvar = $(emit_extract(state, nbits_pos - lenbits, charbits)))]
    if variable
        push!(extracts, if lenbase == 0
            :($lenvar = $(emit_extract(state, nbits_pos, lenbits)))
        else
            :($lenvar = $(emit_extract(state, nbits_pos, lenbits)) + $lenbase)
        end)
    end
    charargs = if variable
        :($charvar, Int($lenvar), $ranges)
    else
        :($charvar, $maxlen, $ranges, $oneindexed)
    end
    printex = :(printchars(io, $(charargs.args...)))
    tostringex = :(chars2string($(charargs.args...)))
    argvar = gensym("arg_charseq")
    kindstr = String(kind)
    encode_chars = quote
        ($lenvar, $charvar) = parsechars($cT, String($argvar), $maxlen, $ranges, $cfold, $oneindexed)
        $lenvar == ncodeunits(String($argvar)) || throw(ArgumentError(
            string("Invalid characters in \"", $argvar, "\" for ", $kindstr)))
        $(if variable
              quote
                  $lenvar < $minlen && throw(ArgumentError(
                      string("String \"", $argvar, "\" is too short (minimum ", $minlen, " characters)")))
                  $lenvar > $maxlen && throw(ArgumentError(
                      string("String \"", $argvar, "\" is too long (maximum ", $maxlen, " characters)")))
              end
          else
              :($lenvar != $maxlen && throw(ArgumentError(
                  string("String \"", $argvar, "\" must be exactly ", $maxlen, " characters"))))
          end)
        $(emit_pack(state, cT, charvar, nbits_pos - lenbits))
        $(if variable
              lenpack = if lenbase == 0
                  :($lenoffset = $lenvar % $lT)
              else
                  :($lenoffset = ($lenvar - $lenbase) % $lT)
              end
              quote $lenpack; $(emit_pack(state, lT, lenoffset, nbits_pos)) end
          else
              nothing
          end)
    end
    impart_body = filter(e -> !isnothing(e) && !(e isa LineNumberNode), encode_chars.args)
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
                      " ", kind, if maxlen > 1; " characters" else " character" end)
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
        [fill(char_set, n) for n in minlen:maxlen]
    end
    SegmentOutput(
        SegmentBounds(minlen:parsed_max, minlen:maxlen, totalbits, sentinel),
        SegmentCodegen(parse_exprs, seg_extract, copy(extracts), seg_impart,
                       ExprVarLine[printex]),
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
    claims = unclaimed_sentinel(nctx)
    presbits = claims ? 1 : 0
    fieldvar = get(nctx, :fieldvar, gensym("embed"))
    nbits_pos = state.bits + ebits + presbits
    # Packed types store values MSB-aligned, so shift right before packing, left after extracting
    to_lsb(val) = :(Core.Intrinsics.lshr_int($val, $epad))
    to_msb(val) = :(Core.Intrinsics.shl_int($val, $epad))
    eresult = Symbol("$(fieldvar)_result")
    epos = Symbol("$(fieldvar)_epos")
    notfound = build_fail_expr!(state, nctx, "Invalid embedded $(T)")
    eshifted = Symbol("$(fieldvar)_shifted")
    pack = emit_pack(state, T, eshifted, nbits_pos - presbits)
    parse_exprs = ExprVarLine[
          :(($eresult, $epos) = $(GlobalRef(PackedParselets, :parsebytes))($T, @view idbytes[pos:end])),
          :(if !($eresult isa $T); $notfound end),
          :($eshifted = $(to_lsb(eresult))),
          pack]
    if claims
        push!(parse_exprs, emit_pack(state, Bool, true, nbits_pos))
    end
    push!(parse_exprs, :(pos += $epos - 1))
    fextract = :($fieldvar = $(to_msb(emit_extract(state, nbits_pos - presbits, ebits, T))))
    argvar = gensym("arg_embed")
    argshifted = gensym("arg_embed_shifted")
    body = Any[:($argshifted = $(to_lsb(argvar))),
               emit_pack(state, T, argshifted, nbits_pos - presbits)]
    if presbits > 0
        push!(body, emit_pack(state, Bool, true, nbits_pos))
    end
    sentinel = if claims; SentinelSpec((0, presbits)) else nothing end
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
