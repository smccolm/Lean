# Tao 2026 build tools

`run_tao_build.ps1` verifies the pinned Tao source artifacts, all 1,226 frozen
dependency hashes and their exact file set, the raw Mermaid contract, Lean and
dependency pins, direct production-root coverage, forbidden proof shortcuts,
the current axiom audit, and a warning-free build. It currently certifies only
the Proposition 2.3(i),(iii), exact `B¹`/`VB¹` sums, and powerful-decomposition
milestone; it is not yet the final
proof-release verifier described by `Tao Goal Prompt.md`.

`refresh_gafnitao_snapshot.ps1` reconstructs the exact recursive import
closure of `GafniTao.Theorem11` from node 74, including `public import`
declarations, and regenerates the per-source SHA-256 manifest. Run it only as
an intentional dependency-update operation and review all resulting changes.
