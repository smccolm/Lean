# Prime Shell Shitlist

This checklist is exhaustive for the isolated Prime Shell program. The frozen Guth–Maynard proof remains an unchanged input. Prime Shell terminates in the permitted **ROUTE DISPROVED** state and proves no new zero-distribution theorem.

## Source and kernel work

- [x] **PSH-00 — Isolation boundary.** All work is under `PostGM/PrimeShell/`; `RiemannZeta/` and `RiemannZeta.lean` are untouched by Prime Shell and no Prime Shell module enters the frozen root graph.
- [x] **PSH-01 — Pinned Zeta23 reproduction.** Tag `v1.0`, commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Lean `v4.33.0-rc2`, and Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` are fixed. Warnings replayed from the immutable dependency are reported, not suppressed or attributed to Prime Shell.
- [x] **PSH-02 — Exact source crosswalk.** Alpoge–Furman equations (2.7), (5.10)–(5.11), Proposition 5.4, Theorem 5.7, and Section 7.2 are crosswalked to exact declarations, conventions, specializations, and nonmatches.
- [x] **PSH-03 — Exact prime-prime decomposition.** `primePrime_exact_decomposition` and `primePrime_exact_source_ledger` expose the diagonal, same-sign resonant, opposite-sign, boundary, and remainder pieces and recover the pinned prime-term estimate as a regression result.
- [x] **PSH-04 — Exact shift kernel.** `dyadicDifferenceOffDiagonal_eq_shiftSum` gives the literal `m=n+h` rewrite with the two-variable kernel, endpoints, support, resonant range, and variation remainder retained.
- [x] **PSH-05 — Honest arithmetic interfaces.** The narrow finite GM and exact two-variable arithmetic controls are specifications and downstream consumers, never axioms. Prime powers, Lambda weights, endpoints, simultaneous ranges, and source dependencies remain visible.
- [x] **PSH-06 — Concrete F1 verdict.** `exists_concrete_literal_kernel_row_variation` constructs actual pinned `Params.PhiR` rows in one admissible dyadic block; `concrete_literal_prefix_only_transfer_fails` proves that collapsed shift-prefix data alone cannot control the literal kernel.

## Corrected admissibility and terminal mathematics

- [x] **PSH-07 — Faithful F2 admissibility.** The old total-profile contradiction is withdrawn as a terminal argument. A zero gap is imposed on a smooth amplitude `q`, while the actual source is `atV (q²)`. `extendedFamilyHyps_atAmplitude` proves the source-entry bridge. `twoBandAmplitude_profile`, its exact difference-set theorems, and `concreteFaithfulAmplitudeShell` construct a genuine separated shell. `faithfulAmplitudeShell_nonempty` proves the class is not vacuous.
- [x] **PSH-08 — Arithmetic consumer boundary.** The exact trace decompositions and literal two-variable consumers remain kernel-checked. The terminal obstruction below is stronger than any failure of GM or MRT: it applies even if the arithmetic terms were controlled perfectly. Therefore no native arithmetic theorem is needed to decide this mechanism.
- [x] **PSH-09 — F3 universal no-gain theorem.** `amplitudeSq_integral_cauchy_of_separated_support` proves the exact support-loss inequality for `q²`; `jWin_D1_nonneg_extended` proves the full D1 contribution is nonnegative. Combining strict cross separation with the full-chain bound `lambda < 4/3`, `FaithfulAmplitudeShell.kappaXi_gt_three` proves `3 < kappaXi` for every faithful shell. Hence `FaithfulAmplitudeShell.no_positive_gain` rules out every positive improvement over `2/3` through the exact Zeta23 `2 - kappaXi` certificate.
- [x] **PSH-C — PairCeiling reproduction not invoked.** `EnclOK` and the decimal `0.6818287` are unnecessary for the universal no-gain theorem and are not claimed as unconditional Lean results.
- [x] **PSH-10 — Exposition.** The final report records the corrected model, the exact inequality, the earlier F1 result, the terminal implication, and the limits of the conclusion.
- [x] **PSH-11 — Arithmetic source selection closed by terminal B.** GM, MRT, and other fixed-shift inputs are not postulated or recursively formalized because the spectral obstruction survives the strongest possible arithmetic input. The scale overlap itself is not claimed empty: the concrete parameter `199/150` lies strictly between `33/25` and `4/3`.
- [x] **PSH-12 — Toolchain architecture.** The result lives in the separately pinned Lean `v4.33.0-rc2` extension. The Lean `v4.30.0` frozen GM repository remains outside its import graph.
- [x] **PSH-13 — Native arithmetic input closed by terminal B.** No oracle, theorem-equivalent hypothesis, or project axiom was introduced.
- [x] **PSH-14 — Native weighted trace closed by terminal B.** Existing exact trace infrastructure is preserved; a success-chain trace theorem would not overcome `kappaXi > 3`.
- [x] **PSH-15 — Native spectral/zero consumer closed by terminal B.** No positive certificate exists in the faithful separated class, so no zero-side success theorem is stated.
- [x] **PSH-16 — Public terminal theorem.** `primeShell_universal_no_gain_native` quantifies over every `FaithfulAmplitudeShell` and every positive `delta`. `faithfulAmplitudeShell_nonempty` separately proves that this is a non-vacuous class. This is the full goal’s permitted universal no-go endpoint.

## Verification and release evidence

- [x] **PSH-17 — Dependency audit.** `PrimeShell/Audit.lean` audits all public and agenda-critical declarations, including source entry, concrete non-vacuity, the exact support-loss inequality, and the terminal theorem. The outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] **PSH-18 — Project-source clean check.** Direct elaboration of changed Prime Shell modules emits no warning or linter diagnostic, and forbidden-construct scans are empty. A Lake build may replay warnings from the immutable Zeta23 dependency; those are disclosed and are not hidden.
- [x] **PSH-19 — Trusted statement check.** `FaithfulSeparatedAmplitudeGain` states positive gain directly, and `faithfulSeparatedAmplitudeGain_iff_false` proves the two-sided comparator.
- [x] **PSH-20 — Reproduction candidate.** The isolated project fixes exact dependency pins and records its source files in the SHA-256 manifest. The owner-controlled commit/push is external; `push_to_github.bat` was not run.
- [ ] **PSH-21 — External review.** Independent expert scrutiny remains open. Kernel checking and local reproduction are not peer review, publication, or community acceptance.

## Completion contract

Prime Shell has reached terminal state B: **ROUTE DISPROVED**. The proved result rules out the faithful separated-amplitude Zeta23 rank/inertia mechanism encoded by `FaithfulAmplitudeShell`, including its exact full-chain scale and cross-band separation conditions. It does not rule out connected positive-valley windows, a rebuilt source theory, or any other mechanism not represented by that structure.
