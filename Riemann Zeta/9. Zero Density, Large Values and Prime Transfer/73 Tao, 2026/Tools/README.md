# Tao 2026 build tools

`run_tao_build.ps1` verifies the pinned Tao source artifacts, all 1,226 frozen
dependency hashes and their exact file set, the raw Mermaid contract, Lean and
dependency pins, direct production-root coverage, forbidden proof shortcuts,
the current axiom audit, and a warning-free build. It currently certifies only
Proposition 2.3(i),(iii), the exact `B¹`/`VB¹` sums, the factorial
endpoint/counting bridge, and the `F₃¹` square-family lower bound, including
its reverse-big-O transfer to the `F₃` and factorial-triple counts. It also
certifies the dominated-convergence limit, square-times-squarefree series
identity, zeta identification, and exact `ζ(3/2)/ζ(3) √x` asymptotic for
`VB¹`. It is not
yet the final
proof-release verifier described by `Tao Goal Prompt.md`.
The audit also covers the positive-start first clause of Lemma 3.1 and the
complete Lemma 3.2 proof: canonical extraction, coefficient-product
divisibility, finite Abel/Chebyshev bounds, polynomial selection, and the
nonzero-shift powerful relation.

`refresh_gafnitao_snapshot.ps1` reconstructs the exact recursive import
closure of `GafniTao.Theorem11` from node 74, including `public import`
declarations, and regenerates the per-source SHA-256 manifest. Run it only as
an intentional dependency-update operation and review all resulting changes.
