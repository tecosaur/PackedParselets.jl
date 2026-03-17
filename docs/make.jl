# SPDX-FileCopyrightText: © 2025 TEC <contact@tecosaur.net>
# SPDX-License-Identifier: MPL-2.0

using PackedParselets
using Documenter
using Org

# Convert .org files to .md for Documenter
for (root, _, files) in walkdir(joinpath(@__DIR__, "src"))
    for f in filter(endswith(".org"), files)
        orgfile = joinpath(root, f)
        mdfile = replace(orgfile, r"\.org$" => ".md")
        read(orgfile, String) |>
            c -> Org.parse(OrgDoc, c) |>
            o -> sprint(markdown, o) |>
            s -> replace(s, r"\.org\]" => ".md]") |>
            m -> write(mdfile, m)
    end
end

makedocs(;
    modules=[PackedParselets],
    authors="TEC <git@tecosaur.net>",
    sitename="PackedParselets.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://tecosaur.github.io/PackedParselets.jl",
        edit_link="main",
        assets=["assets/favicon.ico"],
    ),
    pages=[
        "Introduction" => "index.md",
        "Usage" => "usage.md",
        "Segments" => "segments.md",
        "Optimisations" => [
            "Code Generation" => "opt/overview.md",
            "Data Loading" => "opt/dataloading.md",
            "Bit-packing" => "opt/bitpacking.md",
            "SWAR Digit Parsing" => "opt/swar.md",
            "Perfect Hashing" => "opt/perfecthash.md",
            "String Matching" => "opt/stringmatch.md",
            "Buffer Printing" => "opt/bufprint.md",
        ],
    ],
    warnonly=[:missing_docs, :cross_references],
)

deploydocs(;
    repo="github.com/tecosaur/PackedParselets.jl",
    devbranch="main",
)
