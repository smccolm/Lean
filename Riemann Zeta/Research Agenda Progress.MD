# Research Agenda Progress

**Audit date:** 29 August 2026
**Goal:** Maintain the project-integrated, kernel-checked Guth–Maynard zero-density formalization and prepare its statements and exposition for independent expert review without conflating internal verification with publication or canonicalization.

## Current Status: Internal Proof Integration Complete; External Review Open

The repository now proves the complete public density chain and a separate frozen publication layer. `RiemannZeta/PublicationContract.lean` gives exact source-facing propositions and native proofs for the displayed Guth–Maynard Theorem 1.1, the full-range Theorem 1.2, Ingham, Huxley, and the combined `30 * (1 - σ) / 13` estimate. The full-range Theorem 1.2 consumer uses Ingham below `σ = 7/10` and the native Guth–Maynard high-range theorem above it; it does not relabel the restricted internal proposition.

Shitlist #15–#19 are complete at their internal acceptance tests. The GM foundation-freeze candidate additionally has a contract-aware, filesystem-complete, zero-diagnostic canonical verifier and immutable CI configuration. These facts do not establish external semantic review, a public preprint, peer-reviewed publication, community acceptance, or canonicalization.

The project-maintained logical dependency view is [`Proof Architecture.md`](Proof%20Architecture.md). It and this progress report are synchronized with the completion contract in `Lean Alignment Fix Agenda.md`. The adversarial claim sheet and semantic crosswalk are [`Publication Readiness and Semantic Audit.md`](Publication%20Readiness%20and%20Semantic%20Audit.md).

The root-imported graph contains 301 production modules; `Audit.lean` and `Lint.lean` are the two explicit regression modules, leaving zero unclassified `RiemannZeta/**/*.lean` files. `Audit.lean` checks 7,636 explicitly registered public declarations and every one of the 14,290 discovered nonprivate project theorems, including generated declarations. Every audited theorem has only `propext`, `Classical.choice`, and `Quot.sound` among its axioms. The canonical development verifier passes the module classification, clean scans, root build, exact publication-contract gate, both retained regressions, exhaustive audit, and all 16 default linters with zero project warning or tactic-suggestion diagnostics. Pre-repair candidate `afd7b8719908b6ec642bafc9f1a8e5f9ad893f67` also passed release mode from a fresh short-path clone and has annotated local tag `gm-foundation-freeze-v1.0.0`. The first remote run was terminated by GitHub with exit `143` before artifact upload. The repaired configuration is designated for `gm-foundation-freeze-v1.0.1` and still requires its own fresh-clone PASS and SHA-bound CI artifact before any release claim.

### GM foundation freeze — 29 August 2026

- `PublishedGuthMaynardLargeValues` matches the published theorem display's closed support, positive phase, one-separated `[0,T]` set, and support-only coefficient bound. Its proof contains the endpoint/support conversion into the internal open-dyadic theorem.
- `PublishedGuthMaynardZeroDensity` has the literal range `1/2 ≤ σ ≤ 1`; its proof performs the Ingham/Guth–Maynard range split and exponent comparison.
- The exact source editions, corrected Heath-Brown attribution, Maynard–Pratt journal metadata, and ANTEDB commit/labels are frozen in `verification/SOURCE_FREEZE.md`.
- `scripts/verify_release.ps1` is the single local/CI verifier. Release mode refuses a dirty tree and emits commit-, verifier-, toolchain-, dependency-, and contract-version-bound log/JSON evidence. The Windows batch file is only a wrapper.
- The CI workflow uses a concrete Ubuntu image and immutable action commit SHAs. After the first monolithic remote attempt was terminated with infrastructure exit `143`, the workflow was split into an exact-SHA DFI cache-prime job and a dependent invocation of the unchanged canonical release command. The evidence artifact remains named by the tested commit SHA.

### Publication-readiness audit — 28 August 2026

The new #20 documentation layer separates internal proof verification from external proof digestion. Its internal package is complete: the ten principal outputs have unfolded statements and source crosswalks; zero-count, multiplicity, asymptotic, smoothing, sign, endpoint, and source-entry conventions are recorded; the ten most dangerous semantic bridges are listed; and independent checking, reproduction, hostile questions, a 50-minute talk outline, bibliography, and AI/resource disclosure are supplied. External expert exposition review, independent semantic review, any separately authorized preprint/peer-review process, and canonicalization remain open.

The audit also narrows two earlier labels. `twistedZetaFourthMoment_native` proves the mollifier-specific `T^(1+ε)` upper-bound input, not the full Hughes--Young shifted asymptotic formula. The public DFI theorem is the localized signed dyadic specialization consumed by that argument, with its equation-(2) weight and scale hypotheses explicit; it is not every generality of DFI Theorem 1.

### FR Semantic Re-Audit — 24 August 2026

The positive-slab closeout has been checked again at the proof-term and source-interface boundary. The public theorem unfolds to the requested `EpsilonPowerBound` for the multiplicity-weighted `zeroCountRect σ 1 T (2 * T)` and exponent `3 * (1 - σ) / τ₀`. Its assembly theorem directly invokes `classical_typeI_typeII_dichotomy_native`, eliminates all three literal alternatives, preserves the dichotomy's original zero count, and calls the actual Type-I and Type-II witness consumers. The Type-II chain proves the positive bounded-power and `[2 * τ₀ / 3, τ₀]` scale selection and tracks all logarithmic, harmonic, coefficient, multiplicity, displacement, and finite-power losses. The medium Type-I interface is strictly narrower than the endpoint conclusion and is discharged by `classical_medium_typeI_witness_consumer_native` from the selected source block. No conclusion-equivalent premise, projection-only wrapper, or detached cardinality certificate occurs in the final chain.

Verdict: `FR` remains complete and the diagram's green status is justified. `ZD` is now also complete: `ingham_zero_density_native` and `huxley_zero_density_native` perform the required positive-slab-to-symmetric conversion with the exact endpoint and interior cases.

The rejected `Decoupling.lean` file and both of its false contracts have been deleted. The production source now contains no direct project `axiom`, `constant` postulate, `sorry`, `admit`, or `sorryAx` dependency.

## Shitlist #1–#14 Audit Verdict

This table is the authoritative status summary for items #1–#14. “Conditional layer complete” means Lean checks a real deduction from explicit upstream propositions; it does **not** mean those analytic or arithmetic propositions have been proved.

| Item | Audit verdict | Evidence and remaining boundary |
|---:|---|---|
| 1 | **Verified complete** | `TestAxiom.lean` is absent, no file imports it, and no deliberately false replacement was introduced. |
| 2 | **Historical cleanup milestone verified; inventory claim superseded** | The files removed in the 8 August cleanup remain absent. All currently retained Lean files are now included in the principal evaluation. |
| 3 | **Verified complete** | `TestExp.lean` and `test_separated.lean` elaborate as runner stages; the unproved `test_zeta.lean` experiment is absent. |
| 4 | **Verified complete** | `test_fourier.lean` and `ZeroCountScratch.lean` are absent and have no surviving import. |
| 5 | **Verified complete** | `CombinedZeroDensityTransfer` no longer takes the unused Huxley premise; the separate full-range Huxley input belongs only to the Section 13.1 transfer. |
| 6 | **Verified complete and strengthened by the foundation freeze** | `Audit.lean` checks 7,636 explicit public declarations and all 14,290 discovered nonprivate project theorems without generated-name exclusions. Every audited declaration passes with only the permitted logical dependencies, and every publication/#15/#18/#19 output gate passes. |
| 7 | **Verified complete** | The root closure includes `NativeZeroDensity` and both retained Hughes–Young subordinate modules; no production theorem is outside the imported dependency audit. |
| 8 | **Verified complete** | The principal runner warning-checks the root build, explicit production modules, every retained top-level Lean file, and the transitive audit, then performs repository-wide proof-integrity scans. The complete run passes. |
| 9 | **Finite/source-reduction layer verified; research input discharged in #17** | The detector is the actual truncated Möbius sum, `divisorCountBound_native` proves its classical divisor input, and the uniform detector coefficient theorem now specializes unconditionally. |
| 10 | **Finite/conditional layer verified; research inputs discharged in #17** | The exact `powCoeff` expansion and conditional growth theorem are proved; `powCoeffBound_native` supplies the unconditional specialization from the native divisor and factorization estimates. |
| 11 | **Verified complete, including the analytic theorem** | `MeanValueProof.lean` proves `montgomery_mean_value_native` on `[0,T]` using an exact continuous mean-square identity, a reciprocal-log Hilbert inequality, and local Sobolev sampling. `halasz_montgomery_lemma_native` discharges the downstream premise. |
| 12 | **Conditional/concrete layer verified; all three analytic inputs discharged** | The concrete residual-zero bound follows from three named upstream propositions. Native theorems now discharge coverage, the fourth-moment reduction, and the twisted fourth moment. |
| ~~13~~ | **Verified complete, including its analytic inputs** | Shifted-bin covering, translation, phase preservation, and epsilon normalization are proved; `localZeroMultiplicityBound_native` and `beta_dependence_removal` discharge both former inputs, and `extractSeparated_native` proves the complete target. |
| ~~14~~ | **Verified complete at the planned conditional boundary** | F-01 through F-10 are assembled. `conditionalZeroDensityTransfer` derives the Type-I slab, residual bound, separated extraction, powered-coefficient estimate, dyadic-to-global reduction, and high-`σ` branch from ten individually named primitive inputs; it no longer accepts the two interim propositions. All 21 newly registered theorems pass the transitive audit. |

Accordingly, #1–#14 record completed repair and transfer milestones. Their conditional reusable interfaces remain accurately named, while all primitive inputs required by the public native theorem chain are now discharged. The repository-wide prohibited-proof scan, exhaustive 14,290-theorem dependency audit, and all-file zero-warning/linter evaluation pass.

## Highly Critical Re-Audit Findings

| Severity | Finding | Consequence |
|---|---|---|
| Resolved in #14/#17 | The circular `AlgebraicCombinationProp` postulate and `True` artifact are removed. `conditionalZeroDensityTransfer` is audit-clean and derives every intermediate layer from ten named primitive inputs; #17 now discharges both arithmetic inputs. | Goal B's conditional transfer milestone is complete; discharging its remaining analytic premises is later research. |
| Resolved in #2/#8 | The re-audit found five failing auxiliary files, numerous empty/tombstone files, stale model experiments, two elaboration-time side-effect utilities, and a runner that omitted retained examples. | The initial pass removed 30 obsolete Lean files; a later root cleanup removed 52 additional standalone probes/checks. The useful expansion idea remains as Markdown, and the two retained anonymous examples are separate warning-failing runner stages. |
| Resolved in #16 | `BetaDependence.lean` contained a `True` placeholder, an unconstrained contour error, and a conclusion-shaped pigeonhole axiom. | All seven declarations were deleted. A rational localizer and Mathlib's right-half-plane Phragmén–Lindelöf theorem now prove the exact fixed-line shift, and `extractSeparated_native` closes the extraction chain. |
| Resolved in #19 | `l2_parabola_incidence_bound` was false for arbitrary finite separated sets, and `DecouplingProp` had an off-by-one counterexample. | The entire rejected module and all dependent wrappers were deleted. The replacement follows the paper's sampling-matrix proof and introduces no postulate. |
| Resolved in #14 iteration | `k_selection` formerly omitted the upper inequality in one branch and had no uniform bound. | The theorem now proves both sides of equation (13.1) with `2 ≤ k ≤ 101`; `eventually_detectorScaleUpper_sq_le` absorbs the detector's logarithmic upper-scale loss uniformly on `7/10 ≤ σ ≤ 4/5`. |
| Resolved in #14/#19 | `GuthMaynardLargeValues` formerly had malformed positivity/eventual quantifiers and the opposite sign convention without a proof. | The corrected source-positive-sign proposition has positive constant, eventual threshold, and `V > 0`; `guthMaynardLargeValues_neg` proves the project-sign form by coefficient conjugation, and `guthMaynardLargeValues_native` now proves the analytic proposition itself. |
| Resolved in #14/#15 iteration | `MontgomeryMeanValue` formerly required `[T,2T]`, incompatible with #13's translated output. | It now uses `[0,T]`, and `montgomery_mean_value_native` proves it unconditionally. #13's translated set is consumable at height `3T`; `halasz_montgomery_lemma_native` is also kernel-checked. |
| Resolved in #10 | `polynomial_power_identity` formerly stated only the definitional equality `powPoly = detectPoly ^ k`. | It now proves the full finite `powCoeff` expansion over `m ∈ [N^k,(2N)^k]`, including `k = 0`, by expanding over tuples and regrouping by their product. |
| Resolved in #14 | The finite F-06/F-07 preparation is integrated with a finite-uniform coefficient constant for `2 ≤ k ≤ 101`, normalized threshold identities, fixed-block comparison estimates, and uniform logarithmic-loss absorption. | `typeIPositiveSlabBound_of_section13_inputs` proves the central Type-I slab estimate from the large-values, mean-value, extraction, and powered-coefficient inputs. |
| Resolved in #14 | The project count `N σ T` uses `[-T,T]`, while the detector controls positive slabs `[T,2T]`. | Zeta conjugation, preservation of analytic vanishing order, equality of negative and positive rectangle counts, finite low-height control, and the eventual dyadic summation are now proved in `ZeroCount.lean` and `DyadicTransfer.lean`. |
| Resolved in #14 | Section 13.1 invokes the new argument only on `7/10 ≤ σ ≤ 4/5` and uses Huxley's bound for `σ ≥ 4/5`; the project target runs through `σ = 1`. | The public transfer accepts the narrow `HuxleyZeroDensity` input and uses it only in the high-`σ` branch. |
| Resolved in #18 | The repaired #12 theorem exposes three source-facing proposition inputs in its reusable signature. | `typeIContourTypeIICoverOn_native`, `typeIIFourthMomentReduction_native`, and `twistedZetaFourthMoment_native` discharge all three without altering the reusable conditional interface. |
| Resolved for #13/#15/#16 | The critical audit found that `LocalZeroMultiplicityBoundProp` directly assumed the shifted, scale-filtered occupancy estimate and that the output interval and logarithmic losses were not ready for the large-values step. | The input was narrowed to ordinary unit intervals; #13 proves the shifted cover and normalization, #15 proves the narrowed proposition by a pole-safe Jensen argument, and #16 proves the beta shift. The extraction chain is now unconditional. |
| Resolved in #9/#17 | `DetectorCoeffBoundProp` chooses its constant after fixing `T` and cannot by itself support powering. | The exact detector is bounded by `n.divisors.card`; `divisorCountBound_native` proves the classical divisor estimate, so `uniformDetectorCoeffBound_of_divisorCount` now specializes without an arithmetic premise. |
| Resolved in #8/#14–#19 and foundation freeze | `Paper_Riemann_Zeta.md` formerly expected stale audit counts. | The current dependency audit checks 7,636 registered public declarations and all 14,290 discovered nonprivate theorems; all publication/#15/#18/#19 output gates pass, every project Lean file is classified and evaluated, and the direct-axiom/prohibited-proof scans are empty. |

The source comparison above follows Guth–Maynard Theorem 1.1 and Section 13.1. In particular, Section 13.1 uses the new argument on `7/10 ≤ σ ≤ 4/5`, invokes Huxley for `σ ≥ 4/5`, uses `O(log T)` dyadic scales, makes a complete two-sided choice of `N^k` in equation (13.1), extracts separated large values, and splits between the large-values and mean-value estimates. The Lean development now formalizes this deduction conditionally from the corresponding explicit source inputs.

## Verified Kernel-Checked Results

The following are genuinely proved without project-specific axioms or `sorryAx`, apart from normal Lean/Mathlib logical dependencies such as `propext`, `Classical.choice`, and `Quot.sound`.

1. Finite Dirichlet-polynomial conjugation, norm, threshold, and zero identities.
2. Cross-norm nonnegativity, factor symmetry, real-part bounds, and zero characterization.
3. Coordinate wrappers for Mathlib's completed-zeta functional equation and norm reflection, with the documented hypotheses on both conjugate zeros.
4. Hardy-type norm and zero equivalence on the critical line; the negation result remains conditional on an explicit norm-symmetry premise.
5. Translation and finite selection lemmas for separated real sets, including `weighted_separated_selection` with its necessary local-occupancy factor.
6. `EpsilonPowerBound` reflexivity, transitivity, monotonicity, and power-scaling infrastructure.
7. The complete bounded equation-(13.1) scale selection, including `2 ≤ k ≤ 101` and eventual absorption of the detector upper scale's logarithmic factor.
8. The genuine dyadic Dirichlet-polynomial definition, normalization bound, and two-factor convolution support.
9. The actual truncated Möbius detector, exact support/vanishing statements, smoothing bounds, full-divisor-cardinality bounds uniform in `T`, and the conditional theorem deriving `UniformDetectorCoeffBoundProp` from `DivisorCountBoundProp`.
10. Finite-sum L2 inequalities, exact Fourier/trigonometric integral identities, the finite Hilbert inequality, reciprocal-log kernel control, exact continuous Dirichlet-polynomial mean square, Sobolev sampling on separated sets, and `montgomery_mean_value_native`.
11. Compactness of `ZeroRectangle` and finiteness of its intersection with Mathlib's zeta-zero set; the concrete finite set and multiplicity count no longer use a project finiteness axiom.
12. The exact Type-I-plus-residual filtering identity. A residual zero is not definitionally identified with a source contour-Type-II zero.
13. The structural identity `powPoly = detectPoly ^ k`, the full finite coefficient expansion `polynomial_power_identity`, the substantive conditional bound from a uniform detector input, and the unconditional `powCoeffBound_native` obtained from the proved divisor and ordered-factorization estimates.
14. The conditional combined-exponent implication from separately assumed Ingham and Guth–Maynard zero-density estimates.
15. The unconditional base-interval Montgomery mean-value theorem and the resulting native Halász–Montgomery finite large-value count.
16. Generic residual-count comparison and epsilon-bound composition from explicit coverage, Type-II fourth-moment reduction, and twisted-fourth-moment inputs; eventual source coverage is now bridged to the concrete dyadic zeta-zero family, whose weighted count is proved equal to `residualZeroCount`, yielding a concrete conditional `ResidualZeroBoundProp` theorem.
17. F-06/F-07 finite preparation: lower-endpoint vanishing, exact wide-support decomposition, fixed-line and translated powered identities, epsilon-growth coefficient normalization, unit-norm phase-twisted coefficients, pointwise powered lower bounds, and simultaneous fixed-block/ordinate-subset pigeonholing.
18. F-09/F-10 exponent arithmetic: all three large-values terms and both mean-value terms are bounded by `T^final_exponent`; equation (13.2) is proved by an explicit completed-square certificate.
19. The former conclusion-equivalent transfer axiom and `True` artifact are gone. The audit-clean primitive-input transfer derives the central Type-I slab, residual bound, F-01 dyadic reduction, and Huxley branch internally.
20. Finite admissible dyadic scales, exact weighted pigeonholing, multiplicity aggregation, and shifted-bin covering from an ordinary unshifted unit-zero multiplicity bound.
21. Raw conditional Type-I extraction with explicit `T^δ (log T)^2` loss, exact detector-line and coefficient-phase translation identities, coefficient-norm preservation, and normalized conditional extraction into `[0,3T]` with a pure `C T^ε |W|` bound.
22. The right-half-plane zeta bound from the absolutely convergent Dirichlet series, the explicit `‖ζ(2)‖ < 5/3` estimate, the Möbius L-series norm bound, and the resulting concrete `3/5` Euler lower bound. These new theorems are audit-clean.
23. Abel-integral continuation of zeta on `Re(s) > 0` away from the pole, the pole-safe polynomial vertical bound, the Jensen divisor-to-multiplicity bridge, and `localZeroMultiplicityBound_native`.
24. Rational detector localization on the right half-plane, polynomial boundary decay, the exact `1/(3 log T)` to `1/(4 log T)` fixed-line large-value transfer `beta_dependence_removal`, and the unconditional `extractSeparated_native` theorem.
25. The classical subpolynomial divisor estimate `divisorCountBound_native`, the ordered-factorization estimate `factorizationCountBound_native`, and the resulting unconditional powered detector-coefficient theorem `powCoeffBound_native`.
26. The source-range Type-II coverage contract and concrete finite bridge, arbitrary-order Gamma decay on the detector strip, weighted whole-line Gamma integrability, global critical-line zeta growth, and `integrable_typeIIContourIntegrand`.
27. Arbitrary-scale weighted separated selection with preserved fiber weights and the radius-window bounded-overlap theorem.
28. Exact initial Möbius cancellation for the Appendix C detector, together with the `M²` convolution expansion, support, eventual `T^(1/22)` length, divisor-count coefficient bound, and exact twisted-moment algebraic reduction.
29. The complete #19 shared quantitative language: translation invariance, scaling covariance, affine reindexing, an exact seven-bin floor partition of tolerance-one additive energy, and a one-separated injection into Mathlib's exact additive energy.
30. The exact operator-norm conclusions of Guth–Maynard Lemmas 4.1–4.2: matrix energy control, the large-values cardinality inequality, maximal Gram singular-value domination, and the sixth-root trace-dispersion bound.
31. The complete native #18 Type-II fourth-moment reduction: multiplicity-preserving ordinate fibers, Jensen-controlled scaled extraction, representative Type-II zeros, the exact contour-to-critical-line Gamma convolution inequality, weighted fourth-power Hölder, arbitrary-order Gamma-tail absorption, bounded-overlap conversion to `[T/2,3T]`, and the final epsilon-power assembly. `typeIIFourthMomentReduction_native` proves the required proposition without an additional mathematical hypothesis.
32. Complete #18 smooth completed-zeta-square AFE and diagonal infrastructure. `SmoothZetaAFE.lean` proves the entire completed-xi numerator and its order bound, exact rectangle shift and reflection, vanishing horizontal edges, the critical-line and ordinary-zeta vertical limits, and the right-line divisor-L-series opening. `GammaPairBound.lean` proves symmetric Gamma cancellation first for finite Euler products and then for Gamma and `Gammaℝ`. The AFE uses a fixed admissible strength-100 Gaussian, identifies the exact coefficientwise divisor-contour factor on `w=iu`, and proves both `‖weight(t,u)‖ ≤ exp(-84u²)(2+8u²)^4` and the integrable envelope `16 exp(-68u²)`, uniformly in `t`. `twistedFourthMomentDiagonal_native` gives the exact finite `hm = kn` integral; `smoothTwistedDiagonalMajorant_le` regroups by `q = hm = kn`; and `norm_hughesYoungWeightedDiagonalSlice_le` proves the concrete height-interval estimate and feeds that exact AFE weight into the genuine harmonic majorant at every Mellin ordinate. The `AF` node is complete.
33. Complete #18 DFI/Hughes–Young off-diagonal and native twisted moment. The DFI modules formalize equations (2) and (9)–(30), construct the signed central series, and prove `exists_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale_native`. `exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le_equation80` consumes the pointwise DFI theorem; `hughesYoungConductorActiveFiniteOffDiagonal_epsilonPowerBound_native` assembles the finite off-diagonal estimate; and `twistedZetaFourthMoment_native` proves `TwistedZetaFourthMomentProp`. All four public milestones pass the transitive axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.

## Conditional Interfaces and Remaining Assumptions

An explicit proposition parameter is preferable to a hidden axiom only when its statement is mathematically faithful and strictly upstream. It still does not count as a proved analytic result.

- `MontgomeryMeanValue` is discharged by `montgomery_mean_value_native`; `halasz_montgomery_lemma_native` discharges its downstream large-value-count consequence.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp` are discharged by `divisorCountBound_native` and `factorizationCountBound_native`. Consequently `UniformDetectorCoeffBoundProp` and `PowCoeffBoundProp` have unconditional project proofs, the latter exported as `powCoeffBound_native`.
- The coverage interface has been repaired and proved: `TypeIContourTypeIICoverProp` is exactly `TypeIContourTypeIICoverOnProp (7/10)`, `typeIContourTypeIICoverOn_native` proves it, and the concrete finite bridge consumes that source range. `TypeIIFourthMomentReductionProp` is discharged by `typeIIFourthMomentReduction_native`, and `TwistedZetaFourthMomentProp` is discharged by `twistedZetaFourthMoment_native`; all three residual Type-II inputs are now proved.
- `DetectorBetaShiftProp` is discharged by `beta_dependence_removal`. `LocalZeroMultiplicityBoundProp` is discharged by `localZeroMultiplicityBound_native`; `extractSeparated_native` combines them with #13's shifted covering and normalization proof.
- `HuxleyZeroDensity (fun σ T => N σ T)` is a legitimate high-`σ` input to the conditional transfer: the source uses Huxley on `4/5 ≤ σ ≤ 1`, outside the central Section 13.1 argument. It is discharged by `huxley_zero_density_native`, and `huxleyZeroDensity_published_native` inhabits the frozen publication-facing contract.
- This Huxley dependency is internal to deriving the full-range Guth–Maynard theorem. It does not belong in `CombinedZeroDensityTransfer`, which correctly assumes the completed full-range Guth–Maynard estimate and combines that estimate only with Ingham.
- The global count convention's conjugation and multiplicity bridge is now proved. `dyadicToGlobalZeroCount` converts a positive-slab epsilon-power estimate to the full symmetric count for every nonnegative exponent.
- `ZeroCount.lean` has no direct project axiom. `ZetaBounds.lean` supplies the Abel continuation and vertical estimate used by `zeta_growth_bound_native`; the right-half-plane, Euler/Möbius lower bound, compact-zero-set, and Jensen local multiplicity results are all kernel-checked.
- The seven former `BetaDependence.lean` axioms and the two false `Decoupling.lean` axioms are gone. No direct project axiom remains.

## Completed Conditional Transfer and Remaining Premises

The Section 13.1 chain is fully assembled as a conditional theorem. The formal Shitlist #14 status is:

1. **F-01 complete:** positive-slab-to-global reduction, zeta conjugation with analytic multiplicity, dyadic summation, geometric control, and finite low-height absorption are proved;
2. **F-02/F-03:** consume the actual detector and exact Type-I/residual partition, deriving the concrete residual-zero estimate from the separately named Type-I/contour-Type-II coverage, fourth-moment reduction, and twisted-fourth-moment inputs;
3. **F-04/F-05:** derive #13's normalized separated output from the explicit beta-shift and ordinary unit-zero multiplicity inputs;
4. **F-06 complete:** exact translated normalized-detector identity, `N^σ` scaling, phase preservation, and a coefficient-growth estimate uniform over the bounded choices of `k` are proved;
5. **F-07:** finite preparation is complete: lower-endpoint vanishing, dyadic block split, powered phase identity, coefficient normalization, and simultaneous block-and-ordinate pigeonholing are kernel-checked;
6. **F-08:** complete: `k_selection` gives both sides of equation (13.1), `2 ≤ k ≤ 101`, and the detector-scale logarithmic loss is eventually absorbed;
7. **F-09 complete conditionally:** the repaired large-values hypothesis is applied to the selected normalized block and every bounded/logarithmic loss is absorbed;
8. **F-10 complete conditionally:** the normalized-block mean-value application, equation (13.2), and both exponent bounds are assembled;
9. **central/global assembly complete:** the central positive-slab theorem is extended to `N σ T`, with an explicit Huxley input on `4/5 ≤ σ ≤ 1`; and
10. **public boundary complete:** the conclusion-equivalent transfer axiom and every transfer-local `True` artifact are deleted. The public theorem takes ten individually named primitive inputs and derives the former intermediate propositions internally.

The Section 13.1 target exponent is `15(1-σ)/(3+5σ)`. The later combined Ingham/Guth–Maynard exponent is `30(1-σ)/13`; the previously recorded `30(1-σ)/(13+10σ)` expression was erroneous.

`conditionalZeroDensityTransfer` performs the entire primitive-input chain. Its remaining hypotheses are the analytic/arithmetic research statements themselves, not repackaged slab or global-count conclusions.

## Build, Audit, and Repository Status

### Repository and evaluation-scope audit — updated 29 August 2026

- The `RiemannZeta.lean` transitive project closure contains 301 production modules, including `PublicationContract.lean`; `Audit.lean` and `Lint.lean` are the two explicit regression modules. The verifier rejects any unclassified project Lean file.
- `Audit.lean` checks 7,636 explicitly registered public declarations and all 14,290 discovered nonprivate theorems, including generated declarations. `Lint.lean` runs all 16 default linters and currently reports zero findings over 9,402 source declarations plus 7,925 automatically generated declarations.
- Repository-wide lexical scans find no `sorry`, `admit`, `sorryAx`, project `axiom`/`constant`, `native_decide`, `implemented_by`, or `unsafe` proof bypass. The only `admit` substring is the English word “admits” in a comment. Two TODO comments remain in the vendored PNT+ source and do not mark admitted declarations.
- The six DOCX files have distinct roles. `Guth_Maynard_Formalization_Research_Agenda.docx` is the original objective. The superseded operational bootstrap `archive/Cold Start Sequence.docx`, `archive/Paper_Riemann_Zeta_v7.docx`, the two archived critiques, and `archive/15 Finite scale exponent assembly - Gemini 3.1 pro.docx` are historical records. Their old toolchain/count/status statements are not current proof evidence. In particular, the Gemini document contains a proposed `sorry` skeleton and is not Lean source.
- The vendored PNT+ rectangle residue layer explicitly uses a simple-pole-only residue scaffold. Its downstream rectangle theorem retains `HasSimplePolesOn` and finite-order/boundary hypotheses, so this is a scoped API limitation rather than an untracked proof of a general residue theorem.
- Static claim reconciliation found and corrected stale 44/41 file counts, an obsolete 887-theorem count, the false statement that project-axiom gates still fail, a stale “terminal Type-I remains” sentence, and the diagram's conflation of completed Poisson foundations with the unfinished trace/`S₁` work.

- `lake build` succeeds without Lean warnings for the default `RiemannZeta` library graph.
- The exhaustive transitive audit passes all 14,290 discovered theorems with only the permitted logical axioms. Its exact-type gate checks the five publication contracts in addition to the named #15/#18/#19 results.
- `Audit.lean` is a real environment-level dependency audit: it no longer excludes declarations by generated-name substrings.
- Shitlist #2 removed all five failing auxiliary files, all empty/comment-only Lean tombstones, stale zero-count-model experiments, duplicate scratch lemmas, and obsolete `#check` probes. No Lean file is empty.
- `clean_cache.lean` and `build_it.lean` were deleted. Lean elaboration can no longer trigger their cache deletion or hard-coded external process invocation.
- `Polynomial Power Expansion Notes.md` records how the formerly missing structural-to-coefficient expansion was implemented and now links its completed arithmetic specialization to `ArithmeticCoefficients.lean`.
- `TestExp.lean` and `test_separated.lean` are the only retained top-level regression examples. Runner stage 3 elaborates both without warnings; the 51 obsolete `Probe*.lean` files and `Check.lean` have been removed.
- The prohibited-proof and project-postulate scans are clean. The former beta, transfer, and decoupling artifacts are all gone.
- README, paper, progress, audit, Shitlist, and proof architecture are synchronized for the completed #15–#19 outputs.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: exact formal targets and infrastructure | **Achieved.** The corrected quantifiers/sign bridge, unconditional base-interval mean-value theorem, bounded `k` selection, powered block preparation, exponent arithmetic, exact `GuthMaynardLargeValues`, and all downstream density consumers are kernel-checked. |
| Goal B: conditional zero-density transfer | **Achieved at the primitive-input boundary.** The audit-clean theorem derives the complete full-range result from ten named analytic/arithmetic inputs and contains no conclusion-equivalent or interim slab/global-count premise. |
| Goal C: discharge classical hypotheses | **Achieved.** Beta removal, local zero multiplicity, Montgomery mean value, coefficient growth, the finite dichotomy, Appendix C coverage/reduction, DFI, the twisted fourth moment, native Ingham/Huxley, native large values, and the concrete Goal C specialization are proved. The rejected false model and its two axioms remain deleted. |
| Goal D: Guth–Maynard large-values theorem | **Achieved.** The source-localization, matrix/trace, first- and cubic-Poisson, `S₁`, quantitative reflection, native Heath–Brown, full Proposition 6.1 `S₂`, localization, affine descent, refined `S₃`, Section 11 energy, and Sections 3/12 assembly culminate in `guthMaynardLargeValues_native : GuthMaynardLargeValues`. The proof also covers the complementary low-`V`, high-`V`, near-height, and bounded-`N` ranges. |
| Goal E: reusable analytic-number-theory library | **In-project infrastructure developing.** Stable results must remain source-faithful, audited, and documented through #15–#19. Upstream Mathlib submission is optional follow-on work rather than a repository-completion blocker. |

## Final Shitlist Status

| Item | Discrete task | Inputs or defects eliminated | Required end state |
|---:|---|---|---|
| ~~15~~ | **Classical finite zero-density engine and endpoints — complete** | The actual Type-I/Type-II dichotomy and exact positive-slab theorem are consumed. | `ingham_zero_density_native` and `huxley_zero_density_native` prove the full symmetric multiplicity-weighted endpoint propositions. |
| ~~16~~ | **Beta removal — complete** | All seven former `BetaDependence.lean` axioms and malformed interfaces were deleted. | `beta_dependence_removal : DetectorBetaShiftProp` and `extractSeparated_native : ExtractSeparatedTarget` are kernel-checked and audit-clean. The proof uses rational Phragmén–Lindelöf localization, a source-faithful alternative to the agenda's Fourier-cutoff presentation. |
| ~~17~~ | **Arithmetic coefficient bounds — complete** | `divisorCountBound_native` proves `DivisorCountBoundProp`; `factorizationCountBound_native` proves `FactorizationCountBoundProp`; `powCoeffBound_native` proves `PowCoeffBoundProp` without arithmetic premises. | All five new public declarations are kernel-checked and audit-clean. The focused module and root builds emit zero warnings, and the existing native mean-value and Halász–Montgomery outputs remain audit-clean. |
| ~~18~~ | **Type-II analysis and Goal C integration — complete** | Coverage, reduction, smooth `ζ²` AFE/diagonal, DFI, Hughes–Young, and `twistedZetaFourthMoment_native` are complete. | `guthMaynardZeroDensity_of_largeValues_native` proves the exact one-premise Goal C consumer. |
| ~~19~~ | **Guth–Maynard large values and final integration — complete** | The complete Sections 3–12 chain, source localization, all complementary ranges, and native density inputs are kernel-checked. | `guthMaynardZeroDensity_native` and `combined_zero_density_native` are proved; all retained files are covered; the principal runner passes. |
| 20 | **Publication readiness and external proof digestion — open externally** | The internal hostile-review package and semantic crosswalk are complete. | Expert exposition review, independent source-to-Lean review, any separately authorized preprint/peer review, and canonicalization remain open. |

All ten premises of `conditionalZeroDensityTransfer` are discharged by native theorems. The public conditional consumer retains only the strictly upstream `GuthMaynardLargeValues` premise; its native specialization supplies `guthMaynardLargeValues_native`. The combined theorem supplies the native Ingham bound. There are no direct project axioms.

### #18 DFI and Twisted-Moment Completion Audit — 22 August 2026

- DFI equations (2) and (9)–(30) are represented in source order across the `DFI*.lean` modules. Missing Mellin, Bessel, Voronoi, delta-weight, Euler–Maclaurin, tail, and parameter-optimization dependencies were formalized recursively rather than retained as assumptions.
- `exists_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale_native` is the public localized signed dyadic DFI specialization used by the project. Its hypotheses expose equation (2), literal box support, optimized source scales, and the nonzero-shift range.
- `exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le_equation80` is the Hughes–Young pointwise consumer; `hughesYoungConductorActiveFiniteOffDiagonal_epsilonPowerBound_native` assembles the finite active off-diagonal estimate; and `twistedZetaFourthMoment_native` proves the exact public `TwistedZetaFourthMomentProp`.
- The current exhaustive audit reports only `propext`, `Classical.choice`, and `Quot.sound` for each public milestone: 7,636 registered declarations and all 14,290 discovered nonprivate theorems pass. Every publication/#15/#18/#19 output gate passes.
- This completion supersedes the 12 August quadratic-divisor research baseline and every earlier statement that the DFI error, twisted moment, or Goal C specialization was open.

For Central Type I specifically, `montgomery_mean_value_native`, `extractSeparated_native`, `powCoeffBound_native`, and `guthMaynardLargeValues_native` now discharge all four inputs of `typeIPositiveSlabBound_of_section13_inputs`. This is not #15's classical Montgomery–Halász–Huxley estimate; the proof architecture displays the two large-values dependencies as separate nodes and includes the explicit `GuthMaynardLargeValues → Central Type I` edge.

There is no deferred **Lean proof** item inside #15--#19. The owner subsequently added #20 as a separate publication/digestion contract; its external gates do not alter the proved theorem statements.

## Shitlist #15 Selected Path and Dependency Finding

The detailed contract is in the Shitlist. #15 remains one item. The former Type-II interface mismatch is resolved: `actual_typeII_powered_mhh_native` applies to arbitrary `X`, including the dichotomy cutoff `X=⌊T^(δ₂/2)⌋`. The Type-I chain consumes the enlarged-interval sharp witness with `τ=log_N T`, satisfying `N^τ=T`, and routes every physical scale through direct, powered, reflected, or Weyl estimates. `classical_endpoint_positive_slab_native` now performs the formerly disconnected analytic assembly against the literal dichotomy output and original multiplicity-weighted zero count.

1. **Truncated zeta foundation — complete:** `ZetaTruncation.lean` retains the exact finite Abel identity and absolute tail bound, and now uses a pinned, locally vendored PNT+ Poisson/Euler–Maclaurin closure. For `a = ⌊4T⌋ + 3/2`, Lean proves `4T < a ≤ 6T`, phase confinement to `[1/12,1/4]`, coefficient bounds `14` and `129`, and `norm_zeta_zero_sharp_cutoff_sum_le : ‖∑_{n≤a} n⁻ρ‖ ≤ 149 a⁻Re(ρ)` for every positive-slab zero.
2. **Targeted van der Corput/Weyl package — complete:** `SecondDerivative.lean` proves the multi-period good/bad partition and optimized second-derivative estimate; `SecondOrderMeanValue.lean` supplies the second-order bridge; `Weyl.lean` and `WeylExplicit.lean` prove the corrected A-after-B estimate; and `WeylZeta.lean` proves the weighted Weyl block bound. `TypeIFiniteEstimates.lean` applies the prefix estimate and Abel summation to the sharp cutoff. This coarse bound is valid infrastructure but is not the stationary dual-polynomial B-process required by ANTEDB's medium Type-I range.
3. **Classical large values — complete:** `LogarithmicKernel.lean` proves the Kusmin–Landau `N/|t|` and B-process `√|t|` kernel estimates. `ClassicalLargeValues.lean` proves finite phase-aligned Gram duality, harmonic separated-shell counting, localization/absorption, real floor-bin subdivision, the basic and sixth-power branches, their exact `min`, and `T^ε` absorption. The public theorem is `classical_montgomery_halasz_huxley_native`.
4. **Finite exact-`σ` Type-I transfer and slab consumer — complete:** localization, extraction, the corrected `N^σ` source normalization, smooth/reflection/deweighting, epsilon-absorbed direct MHH, exact powered extraction, weighted Weyl, and corrected `N^τ=T` scale identity are proved. `actual_typeI_branch_resolution_native` closes `ZR`; `classical_medium_typeI_witness_consumer_native` and `classical_endpoint_positive_slab_native` close the literal witness and multiplicity-aware `FR` consumers.
5. **Finite scale/exponent assembly — complete:** `FiniteScaleAssembly.lean` formalizes the MHH exponent, bounded scale reduction, Corollary-11.10 envelope, and concrete endpoint certificates. `classical_finite_scale_exponent_assembly_native` packages these with the finite MHH theorem, and `typeIEndpointScaleDispatch_native` exposes every certificate branch to the downstream `FR` range assembly.
6. **Positive-slab endpoint assembly — complete:** `ingham_endpoint_positive_slab_native` and `huxley_endpoint_positive_slab_native` consume their concrete certificates; `ingham_zero_density_native` and `huxley_zero_density_native` perform the symmetric conversion. At `σ = 3/4`, both target exponents equal `3/5`, so the boundary compatibility is encoded explicitly.

The concrete exponent check remains decisive: at `σ = 3/4`, an ordinary Type-I block with `N = T^(2/3)` lies outside the direct MHH window. The actual Type-I consumer must route this and the other certificate branches through direct MHH, powering, or Weyl before `FR` can assemble the slab. The generic finite helper alone does not resolve this range.

This route replaces an unnecessarily broad mandatory path. The proved mollifier, Jensen, rectangle, strip-growth, and critical-line second-moment work remains valid and reusable, but weighted Littlewood, Gabriel interpolation, a standalone zeta fourth moment, and right/horizontal contour moments are no longer completion dependencies for #15. The acceptance criterion is unchanged: both concrete fully quantified endpoint propositions must be kernel-checked and audit-clean.

The finite classical transfer belongs to #15. It may be reused in later work, but does not silently discharge #18's separately stated Type-I/contour-Type-II coverage or twisted fourth-moment inputs. The independently proved native fourth-moment reduction discharges the third former #18 input.

The #15 foundation pass proves Abel continuation, local multiplicity, mean value, positive-to-symmetric machinery, the exact detector/dichotomy, beta removal, extraction, powering, MHH/Weyl estimates, endpoint arithmetic, the exact positive-slab theorem, and the final native Ingham/Huxley conversion. `mediumTypeILargeValue_false` remains only a conditional exclusion where its displayed threshold comparison holds. #17 supplies the divisor and ordered-factorization estimates used in powered blocks.

Research for the dichotomy found no public kernel-checked implementation of ANTEDB Lemma 11.5 in [ANTEDB's Lean tree](https://github.com/teorth/expdb/tree/main/Expdb), [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), Mathlib, or the published [Lean zeta/L-function formalization](https://arxiv.org/abs/2503.00959). The reusable external APIs are [Mathlib L-series convolution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Convolution.html), [Möbius inversion and bounds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html), and [weighted finite pigeonhole](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Pigeonhole.html). ANTEDB's [`zero_density_estimate.py`](https://github.com/teorth/expdb/blob/main/blueprint/src/python/zero_density_estimate.py) automates later exponent calculations and does not prove the analytic split. The main mathematical implementation anchor remains [ANTEDB Lemma 11.5](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html); proof status remains determined solely by the compiled project and dependency audit.

## Historical Researched Completion Architecture — 10 August 2026

This section records the 10 August plan. All of its former #15, #18, and #19 open assessments are superseded by the 28 August final integration audit above.

### #15: finish the selected finite route

The finite dichotomy, short Type-II product, endpoint arithmetic, and terminal Type-I restriction are proved. The first accessible repair is the actual-`X` Type-II powered MHH theorem. ANTEDB Lemma 11.5 then gives the Type-I fork: smoothing and scale split; direct deweighting for short blocks; B-process followed by the same deweighting for medium blocks. The MHH/Weyl certificates resolve the resulting short polynomial. A branch-to-slab theorem must combine both branch bounds and analytic multiplicity before the endpoints can be proved.

### #18: completed analytic core and remaining Goal C boundary

The external audit found no pre-existing public Lean implementation of the required DFI/Hughes–Young chain. The project supplies Appendix C coverage and reduction, the smooth `ζ²` AFE/diagonal, DFI equations (2) and (9)–(30), the optimized signed Theorem 1 error, its Hughes–Young consumers, `twistedZetaFourthMoment_native`, and the exact one-premise `guthMaynardZeroDensity_of_largeValues_native` consumer.

### #19: discard the false model and follow the paper

`l2_parabola_incidence_bound` is false because it permits arbitrary finite separated sets while its bound is independent of containing interval and height. `DecouplingProp` has an explicit off-by-one counterexample at `K=N` with the coefficient supported at `N+1`: the left side is positive and the stated block sum is zero. Guth–Maynard does not use these propositions. The correct action is deletion of both contracts and axioms.

The implementation target is [Guth–Maynard v2, 7 April 2026](https://arxiv.org/html/2405.20552v2), Theorem 1.1 and Sections 3–12. The proof does not use parabola decoupling. Its actual chain is: finite smooth sampling matrix; Hermitian Gram spectrum and the trace-cube dispersion inequality; Poisson expansion; the `S₁/S₂/S₃` split; Section 6 smooth reflection; Heath–Brown's difference-set mean square; tolerance-one additive energy; Section 7 localization; Section 9 affine transformation; Section 10 refined `S₃`; Section 11 gcd/spacing energy; and Sections 3 and 12 finite assembly. The proved output is the exact existing proposition

`|W| ≤ C T^ε (N² V⁻² + N^(18/5) V⁻⁴ + T N^(12/5) V⁻⁴)`.

The fourteen objective packages in the Shitlist are complete through exact large-values assembly, and the later density consumers and retained-file integration are now complete as well.

Mathlib already supplies [Poisson summation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/PoissonSummation.html), [Schwartz Fourier theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.html), [matrix trace](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Trace.html), [singular values](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html), and [exact additive energy](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/Energy.html). The matrix layer now uses the Gram operator on finite Euclidean spaces, and `LargeValuesLanguage.lean` proves the seven-bin floor comparison that connects tolerance-one real energy to exact `Finset.addEnergy`. [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) can support Mellin/Fourier/Poisson work, and the Carleson [van der Corput file](https://github.com/fpvandoorn/carleson/blob/master/Carleson/Classical/VanDerCorput.lean) can support nonstationary tails. No screened public Lean repository contains Guth–Maynard Theorem 1.1, Heath–Brown's required theorem, or Proposition 9.1; those are genuine new formalization work rather than missing imports.

The #19 packages have changed both integrity status and proof infrastructure. The false module is gone. The `LargeValues*` modules prove the source-facing finite language, Lemmas 4.1–4.5, Propositions 5.1, 6.1, 8.1, 9.1, 10.1, and 11.1–11.2, Sections 3/12 assembly, all complementary ranges, and `guthMaynardLargeValues_native`. `NativeZeroDensity.lean` supplies the concrete conditional and unconditional density consumers and the combined exponent. All declarations are audit-listed, and the runner covers every retained Lean file.

The implementation was checked directly against Guth–Maynard Lemma 4.5, equations (5.4)–(5.5), and Proposition 5.1. Broad public-code searches found no Lean repository formalizing those results. Mathlib's Poisson summation, Schwartz Fourier transform, normed-ring infinite sums, matrix trace, and finite-sum APIs were reusable; the pinned PNT+ repository provides related Mellin/Poisson infrastructure but not this cubic trace argument. Consequently `LargeValuesCubic.lean` carries the new source-specific mathematics rather than wrapping an external theorem.

The quantitative reflection research was checked against [Guth–Maynard Lemma 6.2 and its proof](https://arxiv.org/html/2405.20552v2). The human proof first uses Lemma 4.3 to truncate the complete integer-frequency sum to `|m| ≲ T₀/N`, applies Mellin inversion to the fixed smooth cutoff, truncates the Mellin ordinate by rapid decay, and uses first/second-derivative oscillatory estimates to extract `T₀⁻¹ᐟ²`; it does not use a zeta functional equation. Searches of [Mathlib](https://github.com/leanprover-community/mathlib4), [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), [ANTEDB/Expdb](https://github.com/teorth/expdb/tree/main/Expdb), and public GitHub code found no formal Lemma 6.2 implementation. The project therefore proves the retained modes, measurable Mellin core/tail split, complete integer-frequency tail, arbitrary `T⁻ᴬ`, and scaled cubic-`S₂` consumer locally rather than importing them.

### Current complete-closeout assessment

The actual-`X` Type-II powered MHH application, actual Type-I witness consumer, exact scale bridge, quantitative Lemma 6.2, native Heath–Brown theorem, full Proposition 6.1, affine and energy chains, Sections 3/12 assembly, and the complete concrete density conversion are all complete.

The complete #15, #18, and #19 theorem chains, concrete density outputs, and final retained-file coverage are closed. No item in that former increasing-difficulty queue remains open.

### Historical closeout plan — 10 August 2026 (superseded)

The following list records the plan as it stood on 10 August. Every proof item it called open was later closed; it is retained only as chronology and must not be read as current status.

- **#18 — analytic chain complete through the twisted moment:** `SmoothZetaAFE.lean`, `GammaPairBound.lean`, the DFI equation chain, and `HughesYoungNativeCompletion.lean` prove the diagonal, off-diagonal, and `twistedZetaFourthMoment_native`. Only the downstream one-premise Goal C theorem remains under #18.
- **#19 — full analytic closeout complete and semantically re-audited:** the quantitative-reflection modules close Lemma 6.2, and the subsequent Heath–Brown, `S₂`, localization, affine, refined-`S₃`, energy, and Sections 3/12 modules culminate in the exact `guthMaynardLargeValues_native` theorem. Its public proposition, source entry, complementary ranges, and output gate were checked directly.
- **#15 — finite branch and slab consumers complete:** `FiniteDensityEndpoint.lean` closes arbitrary-`X` Type-II powering/MHH. `TypeIFiniteWindow.lean` applies the missing `N^σ` normalization, absorbs the harmonic loss into `T^ε`, proves the exact powered route, includes weighted Weyl, and packages both endpoint certificates. `ClassicalEndpointDensity.lean` consumes the real dichotomy and proves the exact multiplicity-weighted slab theorem and both certificate specializations. `ZD` is now open.

No screened Lean repository supplies these results. Reusable checked infrastructure is lower-level: Mathlib's `mellinInv_mellin_eq`, Schwartz/Fourier/Poisson APIs, the completed-zeta functional equation, the project's vertical Gamma package, and PNT+'s exact partial-zeta Poisson and nonstationary-mode expansions. The relevant paper statements are [Hughes–Young Sections 2.1–3](https://arxiv.org/abs/0709.2345), [Guth–Maynard Lemmas 4.3 and 6.2](https://arxiv.org/html/2405.20552v2), and [ANTEDB Lemma 11.5](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html).

**Historical implementation evidence.** `PS`, `MR`, `FD`, `IIE`, `ZR`, and `AF` were kernel-checked at that snapshot. Later work closed `ZD`, the Goal C/combined consumers, and retained-file coverage.

### Historical execution order (completed)

1. Complete #15's native Ingham/Huxley endpoint conversion from the proved multiplicity-aware slabs.
2. Apply the now-native Guth–Maynard theorem in the concrete Goal C zero-density consumer.
3. Prove the combined density output.
4. Restore elaboration coverage for every retained Lean file.
5. Run the final audit, zero-warning, documentation, and human-facing runner gates.

## Defensible Current Claim

The repository has a kernel-checked, project-integrated theorem chain and five exact publication-facing contracts, together with an exhaustive dependency audit and a diagnostic-clean canonical verifier for the recorded revision. The project has internally compared the principal statements and consumers with the fixed sources in `Publication Readiness and Semantic Audit.md` and `verification/SOURCE_FREEZE.md`. It has **not** received independent semantic review, peer-reviewed publication, community acceptance, or canonicalization. The localized DFI and mollifier-specific twisted-moment claims must be described at precisely the narrower scope recorded there.
