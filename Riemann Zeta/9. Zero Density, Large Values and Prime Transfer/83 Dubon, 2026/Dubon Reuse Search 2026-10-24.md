# Dubon proof reuse review — 24 October 2026

The renewed search checked current public repository heads, the complete TauCeti file tree, and eight exact candidate source files. Source bytes were checked against Git blob identifiers and SHA-256 hashes. These are source-inspection findings; neither external repository was built against this project's pinned toolchain.

The immediate required chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → all-weight symmetric-power continuation → automorphy and residual association → original weight-two Frobenius/inertia → modular good reduction and prime-to-characteristic Picard torsion injectivity → original-field Kummer power lifting → residue-genus inequality and common chart constants. The search also checked available genus, good-reduction and arithmetic comparison results relevant to later links.

## Verified source revisions

- [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem/commit/6e837e75355538c7f80bab5b956861e86c4eacc2): `6e837e75355538c7f80bab5b956861e86c4eacc2`, committed 2026-09-24T14:06:36Z.
- [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti/commit/e177885ee120f8074a7610c3e60571ab00b20004): `e177885ee120f8074a7610c3e60571ab00b20004`, committed 2026-10-24T06:33:22Z.

FLT's head is unchanged from the previously frozen revision. TauCeti has a newer head. No claim is made that this search exhausts all public or private Lean work.

## Findings and route decisions

| Candidate | Exact applicability | Decision |
|---|---|---|
| [Stable-reduction Picard torsion](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/Curves/StableReduction/Picard/Torsion/Basic.lean) | Picard groups of numerical intersection types, with multidegree presentations and large-prime torsion bounds. | These are different objects from the required degree-zero Picard group and specialization map; no substitution. |
| [Genus under base change](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/Curves/Genus/BaseChange.lean) | Smooth proper connected schemes, using cohomology base change. | Reuse the already proved local function-field genus/conorm chain; a new scheme dictionary would add work. |
| [Elliptic torsion reduction](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/TorsionReduction.lean) | Actual prime-to-characteristic elliptic point torsion injectivity and henselian lifting. | Useful elliptic arithmetic reference; it does not prove arbitrary-genus Picard specialization. Local elliptic reduction is already available. |
| [Elliptic Tate-module good reduction](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/EllipticCurve/TateModule/GoodReduction.lean) | Elliptic Neron–Ogg–Shafarevich over nonarchimedean local fields. | Retain for later arithmetic comparison; it does not establish modular-curve good reduction in general. |
| [Geometric connectedness](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/Geometrically/Connected.lean) | Connectedness of affine tensor products from connectedness of both factors. | Does not provide the needed generic-to-special-fiber implication. |
| [Potential good reduction](https://github.com/TauCetiProject/TauCeti/blob/e177885ee120f8074a7610c3e60571ab00b20004/TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/PotentialGoodReduction.lean) | Integral j and potential good reduction, including Legendre/Deuring forms in all residue characteristics. | Bytes match the October 23 snapshot. Keep Deuring normalization as a candidate for characteristic two; avoid repeating unchanged work. |

The unchanged FLT source supplies the common-residue-chart argument. Its necessary steps were adapted to the actual local objects. Before expanding each step, the pinned Mathlib and existing project proofs were checked for a shorter route:

- Native PID bases and finite integral closures provide full polynomial chart bases.
- Existing valuation normalization and polynomial root cancellation give controlled coordinate denominators directly.
- The proved local resultant compatibility plus native integral Bezout and monic division replace a longer recursive partial-fraction framework.
- The resulting finite overlap quotient gives common residue constants without a finiteness certificate.
- Existing degree–dimension maxima, positive-pole stabilization and exact pole degrees give the actual residue-genus inequality without rebuilding general Riemann–Roch.

These adaptations have passing scratch axiom, linter and declaration-value dependency audits in scopes 380–386. Their production promotion and assembled verification are still pending. The four incidental residual-correction/fraction modules from scope 383 are deferred because the direct denominator route removes their need. No external theorem is represented as a kernel-verified import merely because its source was inspected.

## Evidence and completion boundary

The [archived assessment](Tools/curve-reuse-20261024-380/assessment.json), [repository search](Tools/curve-reuse-20261024-380/search-results.json), [verified candidates](Tools/curve-reuse-20261024-380/verified-candidates.json), and [copy manifest](Tools/curve-reuse-20261024-380/archive-manifest.json) preserve the exact source revisions, decisions and hashes. Original absolute scratch paths inside the frozen evidence are provenance; matching files are archived beside it under the same relative paths.

The latest assembled production verification is the 7,314-module receipt: sequential foundation and paper runners pass with zero diagnostics and all thirteen retained regressions. The new scratch results do not extend that receipt. Acceptance remains 16/20; DUB-17–20 remain open. Wild genus/good reduction in characteristics two and three, full Picard torsion injectivity, original arithmetic-action comparison, Frobenius/inertia, residual association, automorphy and all-weight continuation remain required. Root pins, proof limits, source fidelity and completion criteria are unchanged.
