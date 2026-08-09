# Research Agenda Progress

**Audit date:** 9 August 2026
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Shitlist #17 Complete; Exactly Three Completion Items Remain

The repository contains a kernel-checked conditional formalization of the Section 13.1 transfer. The zeta vertical-growth foundation, Jensen local-zero theorem, Montgomery mean-value theorem, beta-removal theorem, separated Type-I extraction, divisor-count estimate, ordered-factorization estimate, and powered-coefficient estimate are now unconditional kernel-checked results. It still does **not** prove the classical Ingham/Huxley endpoints, the Type-II inputs, the Guth–Maynard large-values theorem, or an unconditional Guth–Maynard zero-density result.

Shitlist #15, #18, and #19 are the three remaining research items; #16 and #17 are complete. Each open item has a discrete mathematical output and an objective acceptance test. Completion of those three means that every primitive input is proved, every current project axiom is removed, the final concrete zero-density theorem is kernel-checked, all documentation is synchronized, and `run_lake_build.bat` returns `PASS` with exit code `0`.

The canonical logical dependency view is [`Proof Architecture.md`](Proof%20Architecture.md). Its unfinished nodes use the same #15–#19 ownership as the Shitlist; it and this progress report must change atomically with the authoritative completion contract in `Lean Alignment Fix Agenda.md`.

The five-stage principal runner covers every retained Lean file in its intended role. The latest run, `logs/overall_proof_20260809_032335.log`, passed stages 1–4 with zero warnings and synchronized 447/447 declarations. The audit fails only on the unrelated decoupling theorem, and the direct-axiom gate reports only the two declarations in `Decoupling.lean`; the honest final result is `FAIL` with exit code `1`.

The production Guth–Maynard source contains two direct project `axiom` declarations, both in `Decoupling.lean`. `BetaDependence.lean`, `ZeroCount.lean`, and `Transfer.lean` contain none. No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency.

## Shitlist #1–#14 Audit Verdict

This table is the authoritative status summary for items #1–#14. “Conditional layer complete” means Lean checks a real deduction from explicit upstream propositions; it does **not** mean those analytic or arithmetic propositions have been proved.

| Item | Audit verdict | Evidence and remaining boundary |
|---:|---|---|
| 1 | **Verified complete** | `TestAxiom.lean` is absent, no file imports it, and no deliberately false replacement was introduced. |
| 2 | **Verified complete as repository cleanup** | The tree has 43 Lean files, no empty Lean file, a 40-file transitive production graph, `Audit.lean`, and exactly two retained anonymous-example files. The obsolete tests, tombstones, and elaboration-time utilities are absent. |
| 3 | **Verified complete** | `TestExp.lean` and `test_separated.lean` elaborate as runner stages; the unproved `test_zeta.lean` experiment is absent. |
| 4 | **Verified complete** | `test_fourier.lean` and `ZeroCountScratch.lean` are absent and have no surviving import. |
| 5 | **Verified complete** | `CombinedZeroDensityTransfer` no longer takes the unused Huxley premise; the separate full-range Huxley input belongs only to the Section 13.1 transfer. |
| 6 | **Verified complete as audit infrastructure** | `Audit.lean` synchronizes 447 explicit and discovered production theorems, including 107 public vendored PNT+ theorems, and checks transitive axioms. Its nonzero result is correct: one declaration still depends on a project axiom. |
| 7 | **Verified complete** | The `RiemannZeta.lean` import closure reaches all 39 subordinate production modules; with the root file this is the 40-file production graph. |
| 8 | **Verified complete as evaluation infrastructure** | The principal runner covers the production graph, focused modules, both examples, warnings, prohibited proof devices, and direct axioms. Stages 1–4 are warning-free; the overall failure is the intended mathematical-integrity failure. |
| 9 | **Finite/source-reduction layer verified; research input discharged in #17** | The detector is the actual truncated Möbius sum, `divisorCountBound_native` proves its classical divisor input, and the uniform detector coefficient theorem now specializes unconditionally. |
| 10 | **Finite/conditional layer verified; research inputs discharged in #17** | The exact `powCoeff` expansion and conditional growth theorem are proved; `powCoeffBound_native` supplies the unconditional specialization from the native divisor and factorization estimates. |
| 11 | **Verified complete, including the analytic theorem** | `MeanValueProof.lean` proves `montgomery_mean_value_native` on `[0,T]` using an exact continuous mean-square identity, a reciprocal-log Hilbert inequality, and local Sobolev sampling. `halasz_montgomery_lemma_native` discharges the downstream premise. |
| 12 | **Conditional/concrete layer verified; analytic inputs open** | The concrete residual-zero bound follows from three named upstream propositions. Those propositions still package the Type-I/Type-II coverage and fourth-moment analysis. |
| ~~13~~ | **Verified complete, including its analytic inputs** | Shifted-bin covering, translation, phase preservation, and epsilon normalization are proved; `localZeroMultiplicityBound_native` and `beta_dependence_removal` discharge both former inputs, and `extractSeparated_native` proves the complete target. |
| ~~14~~ | **Verified complete at the planned conditional boundary** | F-01 through F-10 are assembled. `conditionalZeroDensityTransfer` derives the Type-I slab, residual bound, separated extraction, powered-coefficient estimate, dyadic-to-global reduction, and high-`σ` branch from ten individually named primitive inputs; it no longer accepts the two interim propositions. All 21 newly registered theorems pass the transitive audit. |

Accordingly, #1–#8 are complete repair/evaluation items, #9–#13 are complete only at their explicitly finite or conditional boundaries, and #14 is complete at its explicitly conditional primitive-input boundary. The project as a whole remains unaligned because the non-negotiable no-project-axiom and clean-audit gates still fail.

## Highly Critical Re-Audit Findings

| Severity | Finding | Consequence |
|---|---|---|
| Resolved in #14/#17 | The circular `AlgebraicCombinationProp` postulate and `True` artifact are removed. `conditionalZeroDensityTransfer` is audit-clean and derives every intermediate layer from ten named primitive inputs; #17 now discharges both arithmetic inputs. | Goal B's conditional transfer milestone is complete; discharging its remaining analytic premises is later research. |
| Resolved in #2/#8 | The re-audit found five failing auxiliary files, numerous empty/tombstone files, stale model experiments, two elaboration-time side-effect utilities, and a runner that omitted retained examples. | Thirty obsolete Lean files were removed, the useful expansion idea was preserved as Markdown, and the two retained anonymous examples are now separate warning-failing runner stages. |
| Resolved in #16 | `BetaDependence.lean` contained a `True` placeholder, an unconstrained contour error, and a conclusion-shaped pigeonhole axiom. | All seven declarations were deleted. A rational localizer and Mathlib's right-half-plane Phragmén–Lindelöf theorem now prove the exact fixed-line shift, and `extractSeparated_native` closes the extraction chain. |
| Critical | `l2_parabola_incidence_bound` bounds the cardinality of an arbitrary finite 1-separated real set without any height interval. This is false as stated. The block indices in `DecouplingProp` also do not match the separate block-decomposition convention. | Shitlist #19 requires statement repair before the decoupling axioms can be meaningfully discharged. |
| Resolved in #14 iteration | `k_selection` formerly omitted the upper inequality in one branch and had no uniform bound. | The theorem now proves both sides of equation (13.1) with `2 ≤ k ≤ 101`; `eventually_detectorScaleUpper_sq_le` absorbs the detector's logarithmic upper-scale loss uniformly on `7/10 ≤ σ ≤ 4/5`. |
| Resolved in #14 iteration | `GuthMaynardLargeValues` formerly had malformed positivity/eventual quantifiers and the opposite sign convention without a proof. | The source-positive-sign statement now has positive constant, eventual threshold, and `V > 0`; `guthMaynardLargeValues_neg` proves the project-sign form by coefficient conjugation. The analytic theorem itself remains an explicit unproved input. |
| Resolved in #14/#15 iteration | `MontgomeryMeanValue` formerly required `[T,2T]`, incompatible with #13's translated output. | It now uses `[0,T]`, and `montgomery_mean_value_native` proves it unconditionally. #13's translated set is consumable at height `3T`; `halasz_montgomery_lemma_native` is also kernel-checked. |
| Resolved in #10 | `polynomial_power_identity` formerly stated only the definitional equality `powPoly = detectPoly ^ k`. | It now proves the full finite `powCoeff` expansion over `m ∈ [N^k,(2N)^k]`, including `k = 0`, by expanding over tuples and regrouping by their product. |
| Resolved in #14 | The finite F-06/F-07 preparation is integrated with a finite-uniform coefficient constant for `2 ≤ k ≤ 101`, normalized threshold identities, fixed-block comparison estimates, and uniform logarithmic-loss absorption. | `typeIPositiveSlabBound_of_section13_inputs` proves the central Type-I slab estimate from the large-values, mean-value, extraction, and powered-coefficient inputs. |
| Resolved in #14 | The project count `N σ T` uses `[-T,T]`, while the detector controls positive slabs `[T,2T]`. | Zeta conjugation, preservation of analytic vanishing order, equality of negative and positive rectangle counts, finite low-height control, and the eventual dyadic summation are now proved in `ZeroCount.lean` and `DyadicTransfer.lean`. |
| Resolved in #14 | Section 13.1 invokes the new argument only on `7/10 ≤ σ ≤ 4/5` and uses Huxley's bound for `σ ≥ 4/5`; the project target runs through `σ = 1`. | The public transfer accepts the narrow `HuxleyZeroDensity` input and uses it only in the high-`σ` branch. |
| High | The repaired #12 theorem still composes three strong proposition inputs. `TypeIIFourthMomentReductionProp` packages the Gamma-decay, Hölder, separation, and local-multiplicity work rather than proving it. | The generic and concrete residual-count deductions are valid, including the eventual coverage bridge and exact multiplicity-count identity, but they do not prove Maynard–Pratt Lemma 24. |
| Resolved for #13/#15/#16 | The critical audit found that `LocalZeroMultiplicityBoundProp` directly assumed the shifted, scale-filtered occupancy estimate and that the output interval and logarithmic losses were not ready for the large-values step. | The input was narrowed to ordinary unit intervals; #13 proves the shifted cover and normalization, #15 proves the narrowed proposition by a pole-safe Jensen argument, and #16 proves the beta shift. The extraction chain is now unconditional. |
| Resolved in #9/#17 | `DetectorCoeffBoundProp` chooses its constant after fixing `T` and cannot by itself support powering. | The exact detector is bounded by `n.divisors.card`; `divisorCountBound_native` proves the classical divisor estimate, so `uniformDetectorCoeffBound_of_divisorCount` now specializes without an arithmetic premise. |
| Resolved in #8/#14–#17 | `Paper_Riemann_Zeta.md` formerly expected stale audit counts. | The current synchronized audit contains 447 declarations, including 107 public theorems in the vendored PNT+ rectangle modules. Only `l2_decoupling_bound_native` retains a forbidden dependency. |

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

## Conditional Interfaces and Remaining Assumptions

An explicit proposition parameter is preferable to a hidden axiom only when its statement is mathematically faithful and strictly upstream. It still does not count as a proved analytic result.

- `MontgomeryMeanValue` is discharged by `montgomery_mean_value_native`; `halasz_montgomery_lemma_native` discharges its downstream large-value-count consequence.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp` are discharged by `divisorCountBound_native` and `factorizationCountBound_native`. Consequently `UniformDetectorCoeffBoundProp` and `PowCoeffBoundProp` have unconditional project proofs, the latter exported as `powCoeffBound_native`.
- `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` are unproved analytic inputs. The reduction proposition contains most of the hard Appendix C work. The source coverage and generic reduction now instantiate the actual finite zeta-zero family and concrete `ResidualZeroBoundProp` without an additional zero-set assumption.
- `DetectorBetaShiftProp` is discharged by `beta_dependence_removal`. `LocalZeroMultiplicityBoundProp` is discharged by `localZeroMultiplicityBound_native`; `extractSeparated_native` combines them with #13's shifted covering and normalization proof.
- `HuxleyZeroDensity (fun σ T => N σ T)` is a legitimate high-`σ` input to the conditional transfer: the source uses Huxley on `4/5 ≤ σ ≤ 1`, outside the central Section 13.1 argument. It is stated but unproved in the project.
- This Huxley dependency is internal to deriving the full-range Guth–Maynard theorem. It does not belong in `CombinedZeroDensityTransfer`, which correctly assumes the completed full-range Guth–Maynard estimate and combines that estimate only with Ingham.
- The global count convention's conjugation and multiplicity bridge is now proved. `dyadicToGlobalZeroCount` converts a positive-slab epsilon-power estimate to the full symmetric count for every nonnegative exponent.
- `ZeroCount.lean` has no direct project axiom. `ZetaBounds.lean` supplies the Abel continuation and vertical estimate used by `zeta_growth_bound_native`; the right-half-plane, Euler/Möbius lower bound, compact-zero-set, and Jensen local multiplicity results are all kernel-checked.
- The seven former `BetaDependence.lean` axioms are gone. The two `Decoupling.lean` axioms are the only remaining direct project axioms and require statement repair as part of #19.

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

- `lake build` succeeds without Lean warnings for the default `RiemannZeta` library graph.
- The latest direct audit and principal runner synchronize 447 declarations and find exactly one forbidden dependency, the pre-existing `l2_decoupling_bound_native` dependency on the #19 decoupling postulate. `logs/overall_proof_20260809_032335.log` records stages 1–4 passing with zero warnings and the honest final `FAIL`/`1` caused by that audit failure and the two direct decoupling axioms.
- `Audit.lean` is a real transitive dependency audit for its synchronized production theorem list. The two remaining auxiliary Lean files contain anonymous `example` declarations rather than named public theorems, so the cleanup leaves no named auxiliary theorem outside the audit.
- Shitlist #2 removed all five failing auxiliary files, all empty/comment-only Lean tombstones, stale zero-count-model experiments, duplicate scratch lemmas, and obsolete `#check` probes. No Lean file is empty.
- `clean_cache.lean` and `build_it.lean` were deleted. Lean elaboration can no longer trigger their cache deletion or hard-coded external process invocation.
- `Polynomial Power Expansion Notes.md` records how the formerly missing structural-to-coefficient expansion was implemented and now links its completed arithmetic specialization to `ArithmeticCoefficients.lean`.
- `TestExp.lean` and `test_separated.lean` are the only retained non-production Lean files. They are stages 3 and 4 of the principal runner and pass without warnings.
- The prohibited-proof scan is clean for `sorry`, `admit`, and `sorryAx`. The project-axiom scan is not clean only because of the two `Decoupling.lean` declarations; the former beta and transfer `True` artifacts are gone.
- README, paper, progress, audit, Shitlist, and proof architecture are synchronized for completed #16/#17 and for the still-open #15, #18, and #19 outputs.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: exact formal targets and infrastructure | **Substantially improved but analytic inputs remain unproved.** The large-values quantifiers/sign bridge, unconditional base-interval mean-value theorem, complete bounded `k` selection, powered block preparation, and F-09/F-10 exponent arithmetic are kernel-checked. The Guth–Maynard large-values proposition remains open. |
| Goal B: conditional zero-density transfer | **Achieved at the primitive-input boundary.** The audit-clean theorem derives the complete full-range result from ten named analytic/arithmetic inputs and contains no conclusion-equivalent or interim slab/global-count premise. |
| Goal C: discharge classical hypotheses | **Partially achieved.** Beta removal, local zero multiplicity, Montgomery mean value, divisor count, ordered-factorization count, and powered-coefficient growth are proved. Two direct project axioms remain in the malformed decoupling layer, while the Ingham/Huxley and Type-II proposition inputs remain unproved. |
| Goal D: Guth–Maynard large-values theorem | **Not achieved.** `LargeValues.lean` contains no theorem proving the target; the decoupling layer is axiomatic and partly misstated. |
| Goal E: reusable analytic-number-theory library | **In-project infrastructure developing.** Stable results must remain source-faithful, audited, and documented through #15–#19. Upstream Mathlib submission is optional follow-on work rather than a repository-completion blocker. |

## Three Remaining Shitlist Items

| Item | Discrete task | Inputs or defects eliminated | Required end state |
|---:|---|---|---|
| 15 | **Classical finite zero-density engine and endpoints — in progress** | Completed foundations include the mollifier/detector algebra, local multiplicity, critical-line mollifier second moment, rectangle argument principle, strip growth, Montgomery mean value, basic Halász–Montgomery, three endpoint cases, #17 coefficient bounds, and Package A's exact zero-specialized Euler–Maclaurin truncation with uniform error. The selected remaining route is: targeted van der Corput B/A processes and the Weyl zeta bound; the full Montgomery–Halász–Huxley estimate including `T * N^4 * V⁻⁶`; and a finite exact-`σ` zero-density transfer. Weighted Littlewood/Gabriel/fourth-moment contour estimates are retained as optional infrastructure, not mandatory blockers. | Prove audit-clean `HuxleyZeroDensity (fun σ T => N σ T)` and `InghamZeroDensity (fun σ T => N σ T)`. #15 remains open until both exist. The synchronized audit covers all 447 public production theorems, including the 107-theorem imported rectangle stack. |
| ~~16~~ | **Beta removal — complete** | All seven former `BetaDependence.lean` axioms and malformed interfaces were deleted. | `beta_dependence_removal : DetectorBetaShiftProp` and `extractSeparated_native : ExtractSeparatedTarget` are kernel-checked and audit-clean. The proof uses rational Phragmén–Lindelöf localization, a source-faithful alternative to the agenda's Fourier-cutoff presentation. |
| ~~17~~ | **Arithmetic coefficient bounds — complete** | `divisorCountBound_native` proves `DivisorCountBoundProp`; `factorizationCountBound_native` proves `FactorizationCountBoundProp`; `powCoeffBound_native` proves `PowCoeffBoundProp` without arithmetic premises. | All five new public declarations are kernel-checked and audit-clean. The focused module and root builds emit zero warnings, and the existing native mean-value and Halász–Montgomery outputs remain audit-clean. |
| 18 | **Type-II analysis and Goal C integration** | `TypeIContourTypeIICoverProp`; concrete fourth-moment reduction; twisted zeta fourth moment | The three inputs are proved and a public audit-clean theorem derives the concrete zero-density bound from `GuthMaynardLargeValues` alone. |
| 19 | **Large values and final integration** | Two `Decoupling.lean` axioms; `GuthMaynardLargeValues`; all remaining repository gates | The large-values theorem and its concrete Guth–Maynard and combined zero-density consequences are kernel-checked; scans and audits are clean; builds have zero warnings; the principal runner returns `PASS`/`0`. |

The five still-unresolved premises of `conditionalZeroDensityTransfer` remain exhaustively assigned: large values to #19, Huxley to #15, and the three Type-II premises to #18. Its divisor and factorization parameters are now discharged by #17, while Montgomery mean value, local zero count, and beta shift were already proved. The additional Ingham input needed for the combined exponent remains assigned to #15. The two remaining direct project axioms are both assigned to #19.

There is no fifth deferred cleanup or proof item. If work on one row exposes a genuinely new necessary lemma, that lemma belongs inside the same row unless it changes the published mathematical target; it does not silently create an open-ended new Shitlist item.

## Shitlist #15 Selected Path and Dependency Finding

The detailed implementation and acceptance contract is recorded in the Shitlist. #15 remains one completion item. Package A is complete; three implementation nodes and the endpoint node remain open in the proof architecture.

1. **Truncated zeta relation — complete:** `ZetaTruncation.lean` proves the exact finite Abel identity, the variable-tail bound, `riemannZeta_truncation`, `zeta_zero_truncation`, and `norm_zeta_zero_truncation_error_le`. The proof reuses the project's Abel continuation and Mathlib summation by parts; it does not depend on an external theorem.
2. **Targeted van der Corput/Weyl package:** implement the B/A process instances needed for exponent pairs `(1/2,1/2)` and `(1/6,2/3)`, the Weyl critical-line zeta bound, and the medium-length reflection estimate. ANTEDB supplies the mathematical blueprint but its repository contains TeX and Python rather than reusable Lean proofs.
3. **Classical large values:** upgrade the existing basic Halász–Montgomery result to the full finite Montgomery–Halász–Huxley theorem, including the decisive `T * N^4 * V⁻⁶` branch. Completed #17 supplies its arithmetic coefficient inputs.
4. **Finite exact-`σ` density transfer:** convert zeta zeros to separated polynomial large values, control multiplicity, remove smooth weights, handle the medium-length alternative, and absorb real-part displacement through epsilon slack.
5. **Endpoint assembly:** use `τ₀ = 2 - σ` for Ingham and `τ₀ = 3 * σ - 1` plus the full large-values/Weyl inputs for Huxley. At `σ = 3/4`, both target exponents equal `3/5`, so the Huxley boundary follows from Ingham rather than requiring a separate analytic argument.

This route replaces an unnecessarily broad mandatory path. The proved mollifier, Jensen, rectangle, strip-growth, and critical-line second-moment work remains valid and reusable, but weighted Littlewood, Gabriel interpolation, a standalone zeta fourth moment, and right/horizontal contour moments are no longer completion dependencies for #15. The acceptance criterion is unchanged: both concrete fully quantified endpoint propositions must be kernel-checked and audit-clean.

The finite classical transfer belongs to #15. It may be reused in later work, but does not silently discharge #18's separately stated Type-I/contour-Type-II coverage, fourth-moment reduction, or twisted fourth-moment inputs. Accordingly the #18 status and completion test are unchanged.

The #15 foundation pass has proved Abel continuation, pole-safe vertical growth, right-half-plane and Euler/Möbius bounds, Jensen local multiplicity, Montgomery mean value, generic positive-to-symmetric machinery, the exact classical mollifier/detector layer, the critical-line mollifier second moment, the multiplicity-aware unweighted rectangle argument principle, a concrete linear classical-strip zeta bound, and three endpoint boundary cases. The new truncation pass adds nine public theorems culminating in the exact zero-specialized formula and uniform error, while `huxley_zero_density_at_three_quarters_of_ingham` formalizes the endpoint-exponent coincidence. #17 supplies divisor and ordered-factorization estimates. The synchronized audit now contains 447 public declarations.

The current implementation anchors are the [ANTEDB finite zero-density chapter](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html), the [ANTEDB source repository](https://github.com/teorth/expdb), PNT+'s [`ZetaBounds.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/ZetaBounds.lean), the [Guth–Maynard paper](https://arxiv.org/html/2405.20552v2), and the explicit [Ingham estimate](https://arxiv.org/abs/2507.15184). The ANTEDB repository is human-readable TeX plus executable Python, not a Lean library. PNT+ contains useful proved Euler–Maclaurin/Poisson infrastructure, but its current zero-density endpoint file still has admitted gaps, so it is reference material rather than a proof dependency. Proof status remains determined solely by compiled Lean and the dependency audit.

## Defensible Current Claim

The repository now has an audit-clean, noncircular, primitive-input Section 13.1 transfer, an unconditional separated Type-I extraction theorem, and unconditional arithmetic coefficient bounds through powered detector polynomials. It includes beta removal, the bounded equation-(13.1) choice, powered support and normalization, simultaneous fixed-block pigeonholing, large-values/mean-value case assembly, uniform epsilon-loss accounting, zeta-conjugation with multiplicity, dyadic-to-global summation, and a conditional high-`σ` transfer branch that consumes Huxley. The overall result remains conditional because the concrete density endpoints and other analytic inputs are not proved. Exactly three completion items remain; the two direct project axioms and the single current audit failure belong to #19.
