# Dependencies

This directory contains intentional, immutable dependency material for the
Tao 2026 formalization.

`GafniTaoFrozen/` is the exact recursive Lean import closure of
`GafniTao.Theorem11` together with the native Wooley VMVT bridge: 965
Gafni--Tao modules, 291 frozen Guth--Maynard foundation modules, and 83 PNT+
modules, for 1,339 source files total. Every
copied Lean source is recorded in `GafniTaoFrozen/SOURCE_SHA256SUMS.txt`.
Upstream provenance files, package pins, and licenses are retained in the
snapshot.

`Tools/refresh_gafnitao_snapshot.ps1` deterministically reconstructs these
closures from node 74 and handles both ordinary and `public import`
declarations. Regeneration is a deliberate review operation; production code
imports the frozen package, never the mutable sibling node. The canonical
verifier checks the manifest count, paths, hashes, exact file set, pins, and
forbidden proof shortcuts.

Any future dependency must meet the same standard: repository and immutable
revision, retained closure, license and provenance, source hashes, and exact
declarations consumed by node 73.
