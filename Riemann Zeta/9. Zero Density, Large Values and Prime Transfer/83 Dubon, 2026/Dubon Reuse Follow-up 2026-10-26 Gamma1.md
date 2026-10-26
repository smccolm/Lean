# Dubon reuse follow-up: actual Gamma1 geometry

Reviewed 26 October 2026 (America/Vancouver). This follows the [25 October broad search](Dubon%20Reuse%20Search%202026-10-25%20All-Weight.md). The frozen Dubon paper, root pins and all twenty acceptance conditions remain unchanged.

The inspected primary proofs shorten the actual Gamma1 function-field and Hecke-map construction. They do **not** supply the original all-weight characteristic-zero Galois association. No inspected ready proof closes higher symmetric-power automorphy or literal continuation; this is a finding about the inspected sources, not a claim that no such proof exists.

## Exact source boundary

DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of the actual original finite Gamma1 Hecke characters -> geometric/H1 and diamond comparison.

The [frozen Anthropic revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2) provides genuine Gamma1 modular-curve constructions. Its inspected adic association theorem takes a **characteristic-zero rational Hecke-and-diamond character**. The finite characters constructed for the original all-weight form are not that input. Neither a characteristic-zero Witt coefficient ring nor a universal deformation ring supplies a characteristic-zero specialization.

The separately inspected GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom takes a field of characteristic p and a Gamma0 constant-coefficient H1 eigensystem. Its determinant is the cyclotomic value at a good prime. It does not accept a Gamma1 character over an Artinian ring at arbitrary prime-power precision. The already proved local all-weight residual association remains the appropriate reuse.

## Shorter proved route

| Inspected argument | Existing local proof reused | Obligation discharged |
| --- | --- | --- |
| Integral modular ratios and finite coordinates | Original j, modular norms, level-one j polynomials, Laurent coefficient independence, native primitive elements | Actual rational Gamma1 and Hecke fields finite over the original transcendental coordinate. |
| Laurent scalar extension | Existing DegreeTransport.finite_and_finrank_le | Finite coordinates after actual scalar extension. |
| Integral modular dilation | Native ModularForm.translate, original diagonal matrix, existing sparse sums and native power-series expansion | Actual f(dz), including holomorphy, cusp bounds and integral sparse coefficients. |
| Second Hecke field map | Existing qExpandAlgHom, coeffMap_qExpand and native adjoin maps | Literal q-substitution preserves the actual Hecke field, including after scalar extension. |
| Finite maps | Existing coordinate exchange and finite_hom_of_finite_image_coordinate | Both actual maps finite without a finite-map or modular-polynomial-symmetry premise. |
| Picard and arithmetic Hecke action | Existing closed residues, divisor norm/degree identities, inverse coefficient place transport, normalized orders and quotient action laws | The actual Picard Hecke operator commutes with the genuine arithmetic action; every torsion subgroup is preserved. |

The external alternate coordinate, duplicate scalar-extension/cusp developments and conditional fallback beta-map definition were not adopted. Selected arguments retain Apache-2.0 provenance. No external project was compiled or imported, and no toolchain was upgraded.

## Verification and next dependency

The twenty-six modules passed scratch compilation, explicit and exhaustive axiom checks, sixteen linters per module and four value-only dependency audits. The audits check 144 required declaration dependencies; 185 exhaustive theorem checks and 102 public queries support this verification. All scratch logs have exit zero and zero diagnostics. Counts are verification evidence, not completed Dubon source theorems.

The [assembled proof record](Tools/source-gamma-one-arithmetic-geometry.json) and [reproduction manifest](Dubon%20Reproduction%20Manifest.md) record the current production and sequential verification status. This follow-up closes no acceptance gate: **16/20; DUB-17--20 OPEN**.

The actual Picard Hecke operator and genuine arithmetic action have also been constructed and proved compatible, including preservation of every torsion subgroup. The next comparison is with the finite H1 operators, retaining their original homogeneous coefficient action. Upper/lower correspondence and transpose/diamond conventions must be proved. Diamond comparison, finite-character Galois realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Finite characters alone do not justify a characteristic-zero lift.

## Preserved evidence

The [scope 619 assessment](Tools/gamma-one-arithmetic-geometry-20261026-626/gamma1-geometric-reuse-assessment-619.json) and [snapshot manifest](Tools/gamma-one-arithmetic-geometry-20261026-626/gamma1-geometric-reuse-619/snapshots.json) record the two finite-coordinate files and exact residual Galois boundary.

The [scope 621 assessment](Tools/gamma-one-arithmetic-geometry-20261026-626/gamma1-hecke-correspondence-reuse-assessment-621.json) and [snapshot manifest](Tools/gamma-one-arithmetic-geometry-20261026-626/gamma1-hecke-correspondence-reuse-621/snapshots.json) record the actual Hecke-map definition and q-dilation proof. Source URLs, frozen commit, Git-blob and SHA-256 hashes and full relative paths are preserved. Downloaded source snapshots use .txt extensions outside all Lean import closures.

Failed evidence remains preserved. Seven missing definition docstrings were corrected before fresh audits; one kernel reflexivity timeout was avoided with the native inclusion projection theorem. A fresh Picard dependency audit checks the construction values explicitly: their wrapper names occurring only in consumer types were correctly rejected as proof-value edges. No declaration was excluded. These repairs change no mathematical statement, proof standard or resource limit.
