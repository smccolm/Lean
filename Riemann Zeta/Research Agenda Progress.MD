# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Production Build Passes; Repository Alignment and Main Mathematics Fail

The repository contains useful kernel-checked finite mathematics and several honest conditional deductions. It does **not** contain a verified formalization of the Section 13.1 zero-density transfer, the Guth–Maynard large-values theorem, or the principal analytic inputs needed by either result.

The current five-stage principal runner covers every retained Lean file in its intended role: the root build covers the 27-file production graph, `Audit.lean` runs as the explicit dependency audit, and `TestExp.lean` plus `test_separated.lean` elaborate as separate warning-failing example stages. There are 30 Lean files on disk, and all non-audit elaboration stages pass with zero warnings. The audit and direct-axiom gate still fail honestly on the known mathematical assumptions.

The production Guth–Maynard source still contains 13 direct project `axiom` declarations: seven in `BetaDependence.lean`, two in `Decoupling.lean`, and four in `ZeroCount.lean`. `Transfer.lean` no longer declares an axiom. No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency.

## Shitlist #1–#14 Audit Verdict

This table is the authoritative status summary for items #1–#14. “Conditional layer complete” means Lean checks a real deduction from explicit upstream propositions; it does **not** mean those analytic or arithmetic propositions have been proved.

| Item | Audit verdict | Evidence and remaining boundary |
|---:|---|---|
| 1 | **Verified complete** | `TestAxiom.lean` is absent, no file imports it, and no deliberately false replacement was introduced. |
| 2 | **Verified complete as repository cleanup** | The tree has 30 Lean files, no empty Lean file, 27 production files, `Audit.lean`, and exactly two retained anonymous-example files. The obsolete tests, tombstones, and elaboration-time utilities are absent. |
| 3 | **Verified complete** | `TestExp.lean` and `test_separated.lean` elaborate as runner stages; the unproved `test_zeta.lean` experiment is absent. |
| 4 | **Verified complete** | `test_fourier.lean` and `ZeroCountScratch.lean` are absent and have no surviving import. |
| 5 | **Verified complete** | `CombinedZeroDensityTransfer` no longer takes the unused Huxley premise; the separate full-range Huxley input belongs only to the Section 13.1 transfer. |
| 6 | **Verified complete as audit infrastructure** | `Audit.lean` synchronizes 173 explicit and discovered production theorems and checks transitive axioms. Its nonzero result is correct: four declarations still depend on project axioms. |
| 7 | **Verified complete** | `RiemannZeta.lean` imports all 26 subordinate production modules; with the root file this is the 27-file production graph. |
| 8 | **Verified complete as evaluation infrastructure** | The principal runner covers the production graph, focused modules, both examples, warnings, prohibited proof devices, and direct axioms. Stages 1–4 are warning-free; the overall failure is the intended mathematical-integrity failure. |
| 9 | **Finite/source-reduction layer verified; research input open** | The detector is the actual truncated Möbius sum and its uniform coefficient bound follows from explicit `DivisorCountBoundProp`. That divisor estimate remains unproved Goal C work. |
| 10 | **Finite/conditional layer verified; research inputs open** | The exact `powCoeff` expansion and conditional growth theorem are proved. `DivisorCountBoundProp` and `FactorizationCountBoundProp` remain unproved. |
| 11 | **Finite/conditional layer verified; analytic input open** | The consequence is genuinely derived from explicit `MontgomeryMeanValue`; the interval is now `[0,T]` and is compatible with #13 at height `3T`. The analytic mean-value proposition itself remains unproved. |
| 12 | **Conditional/concrete layer verified; analytic inputs open** | The concrete residual-zero bound follows from three named upstream propositions. Those propositions still package the Type-I/Type-II coverage and fourth-moment analysis. |
| 13 | **Conditional/normalized layer verified; analytic inputs open** | Shifted-bin covering, translation, phase preservation, and epsilon normalization are proved from `DetectorBetaShiftProp` and an ordinary unit-zero multiplicity bound. Those two inputs remain unproved. |
| 14 | **Open; substantial partial implementation** | Circularity is gone and F-06–F-10 finite/exponent infrastructure plus the Huxley branch is checked. `conditionalZeroDensityTransfer` still assumes `TypeIPositiveSlabBoundProp` and `DyadicToGlobalZeroCountProp`, so the primitive-input Section 13.1 transfer is not yet proved. |

Accordingly, #1–#8 are complete repair/evaluation items; #9–#13 are complete only at their explicitly finite or conditional boundaries; and #14 is not complete. The project as a whole remains unaligned because the non-negotiable no-project-axiom and clean-audit gates still fail.

## Highly Critical Re-Audit Findings

| Severity | Finding | Consequence |
|---|---|---|
| High | The circular `AlgebraicCombinationProp` postulate and `True` artifact have been removed. The replacement `conditionalZeroDensityTransfer` is audit-clean and genuinely combines the Type-I/residual partition, a separately exposed F-01 dyadic-to-global boundary, and the Huxley high-`σ` branch. It still accepts `TypeIPositiveSlabBoundProp` and `DyadicToGlobalZeroCountProp`; consequently it is an honest interim theorem, not the planned primitive-input completion of Goal B. | The integrity-critical circularity is resolved. Goal B remains incomplete until the new finite F-06/F-10 infrastructure proves the Type-I slab input from the source hypotheses and F-01 is proved rather than parameterized. |
| Resolved in #2/#8 | The re-audit found five failing auxiliary files, numerous empty/tombstone files, stale model experiments, two elaboration-time side-effect utilities, and a runner that omitted retained examples. | Thirty obsolete Lean files were removed, the useful expansion idea was preserved as Markdown, and the two retained anonymous examples are now separate warning-failing runner stages. |
| Critical | `BetaDependence.lean` contains `smooth_compact_is_schwartz ... : True`; `beta_dependence_removal` ignores its smoothing data and simply applies `pigeonhole_integral_bound`, which already supplies essentially the desired conclusion. `contour_shift_to_real_line` permits an unconstrained existential error. | The beta-removal layer is not merely unproved; several interfaces are vacuous or conclusion-shaped and require redesign before proof work. |
| Critical | `l2_parabola_incidence_bound` bounds the cardinality of an arbitrary finite 1-separated real set without any height interval. This is false as stated. The block indices in `DecouplingProp` also do not match the separate block-decomposition convention. | Shitlist #17 requires statement repair before the decoupling axioms can be meaningfully discharged. |
| Resolved in #14 iteration | `k_selection` formerly omitted the upper inequality in one branch and had no uniform bound. | The theorem now proves both sides of equation (13.1) with `2 ≤ k ≤ 101`; `eventually_detectorScaleUpper_sq_le` absorbs the detector's logarithmic upper-scale loss uniformly on `7/10 ≤ σ ≤ 4/5`. |
| Resolved in #14 iteration | `GuthMaynardLargeValues` formerly had malformed positivity/eventual quantifiers and the opposite sign convention without a proof. | The source-positive-sign statement now has positive constant, eventual threshold, and `V > 0`; `guthMaynardLargeValues_neg` proves the project-sign form by coefficient conjugation. The analytic theorem itself remains an explicit unproved input. |
| Resolved in #14 iteration | `MontgomeryMeanValue` formerly required `[T,2T]`, incompatible with #13's translated output. | It now uses the base interval `[0,T]`; #13's set lies in `[0,3T]`, so downstream use is at height `3T`. Exact coefficient phase translation is already kernel-checked. The analytic mean-value theorem remains unproved. |
| Resolved in #10 | `polynomial_power_identity` formerly stated only the definitional equality `powPoly = detectPoly ^ k`. | It now proves the full finite `powCoeff` expansion over `m ∈ [N^k,(2N)^k]`, including `k = 0`, by expanding over tuples and regrouping by their product. |
| Medium | The finite F-06/F-07 preparation is now implemented: the lower endpoint vanishes, the support is split into exactly `k` dyadic blocks, the powered fixed-line and translated identities are exact, coefficient normalization is proved, and a single block plus ordinate subset is simultaneously pigeonholed. | The remaining central obstruction is uniform asymptotic bookkeeping: bounded variable `k`, coefficient constants, logarithmic threshold losses, and block-length factors must be absorbed before applying the large-values/mean-value inputs. |
| High | The project count `N σ T` uses the full ordinate interval `[-T,T]`, whereas the Section 13.1 detector and current Type-I/Type-II layers control positive slabs `[T,2T]`. | F-01 needs a zeta-conjugation and analytic-multiplicity bridge plus an eventual dyadic summation with a finite low-height remainder. No current theorem performs this global reduction. |
| High | Section 13.1 invokes the new argument only on `7/10 ≤ σ ≤ 4/5` and uses Huxley's bound for `σ ≥ 4/5`; the project target `GuthMaynardZeroDensity` runs through `σ = 1`. | A faithful public transfer theorem must accept an explicit `HuxleyZeroDensity` or equally narrow high-`σ` hypothesis. |
| High | The repaired #12 theorem still composes three strong proposition inputs. `TypeIIFourthMomentReductionProp` packages the Gamma-decay, Hölder, separation, and local-multiplicity work rather than proving it. | The generic and concrete residual-count deductions are valid, including the eventual coverage bridge and exact multiplicity-count identity, but they do not prove Maynard–Pratt Lemma 24. |
| Resolved for #13's conditional layer | The critical audit found that `LocalZeroMultiplicityBoundProp` directly assumed the shifted, scale-filtered occupancy estimate and that the output interval and logarithmic losses were not ready for the large-values step. | The input now bounds only unshifted unit intervals. Lean proves the `2⌈H⌉+1` shifted-bin cover, raw enlarged-interval estimate, ordinate/coefficient translation to `[0,3T]`, phase-norm preservation, and pure epsilon-power normalization. The unit-zero and beta-shift propositions themselves remain unproved #15/#16 analytic inputs. |
| Resolved in #9 | `DetectorCoeffBoundProp` chooses its constant after fixing `T` and cannot by itself support powering. | The exact detector is now bounded by `n.divisors.card`, and `uniformDetectorCoeffBound_of_divisorCount` proves the full `T`-uniform estimate from the explicit classical `DivisorCountBoundProp`. The classical divisor estimate remains Goal C work. |
| Resolved in #8/#14 | `Paper_Riemann_Zeta.md` formerly expected 17 audit failures after the production audit had fallen to 6. | The current evidence is 4 dependency failures across 173 synchronized declarations; the documentation is to be read against the authoritative audit verdict above. |

The source comparison above follows Guth–Maynard Theorem 1.1 and Section 13.1. In particular, Section 13.1 uses the new argument on `7/10 ≤ σ ≤ 4/5`, invokes Huxley for `σ ≥ 4/5`, uses `O(log T)` dyadic scales, makes a complete two-sided choice of `N^k` in equation (13.1), extracts separated large values, and splits between the large-values and mean-value estimates. The present Lean development formalizes only fragments of that chain.

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
10. Finite-sum L2 inequalities and elementary complex-exponential facts. These do not prove Fourier inversion, Fourier decay, or an analytic mean-value estimate.
11. Compactness of `ZeroRectangle` and finiteness of its intersection with Mathlib's zeta-zero set; the concrete finite set and multiplicity count no longer use a project finiteness axiom.
12. The exact Type-I-plus-residual filtering identity. A residual zero is not definitionally identified with a source contour-Type-II zero.
13. The structural identity `powPoly = detectPoly ^ k`, the full finite coefficient expansion `polynomial_power_identity`, the substantive conditional bound from a uniform detector input, and `powCoeff_bound_of_divisor_and_factorization`, which exposes the two classical arithmetic inputs directly.
14. The conditional combined-exponent implication from separately assumed Ingham and Guth–Maynard zero-density estimates.
15. The conditional finite large-value count from an explicit base-interval `MontgomeryMeanValue` parameter. The analytic mean-value theorem remains unproved.
16. Generic residual-count comparison and epsilon-bound composition from explicit coverage, Type-II fourth-moment reduction, and twisted-fourth-moment inputs; eventual source coverage is now bridged to the concrete dyadic zeta-zero family, whose weighted count is proved equal to `residualZeroCount`, yielding a concrete conditional `ResidualZeroBoundProp` theorem.
17. F-06/F-07 finite preparation: lower-endpoint vanishing, exact wide-support decomposition, fixed-line and translated powered identities, epsilon-growth coefficient normalization, unit-norm phase-twisted coefficients, pointwise powered lower bounds, and simultaneous fixed-block/ordinate-subset pigeonholing.
18. F-09/F-10 exponent arithmetic: all three large-values terms and both mean-value terms are bounded by `T^final_exponent`; equation (13.2) is proved by an explicit completed-square certificate.
19. The former conclusion-equivalent transfer axiom and `True` artifact are gone. The audit-clean interim transfer combines the exact Type-I/residual partition, an explicit provisional F-01 boundary, and the proved Huxley exponent comparison.
20. Finite admissible dyadic scales, exact weighted pigeonholing, multiplicity aggregation, and shifted-bin covering from an ordinary unshifted unit-zero multiplicity bound.
21. Raw conditional Type-I extraction with explicit `T^δ (log T)^2` loss, exact detector-line and coefficient-phase translation identities, coefficient-norm preservation, and normalized conditional extraction into `[0,3T]` with a pure `C T^ε |W|` bound.

## Conditional Interfaces and Remaining Assumptions

An explicit proposition parameter is preferable to a hidden axiom only when its statement is mathematically faithful and strictly upstream. It still does not count as a proved analytic result.

- `MontgomeryMeanValue` is an explicit uniform proposition with one positive absolute constant on `[0,T]`. It is unproved; the repaired interval convention is directly consumable at height `3T` for #13's translated output.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp` are unproved classical arithmetic inputs. `UniformDetectorCoeffBoundProp` is no longer an independent obligation: it is conditionally proved from `DivisorCountBoundProp`.
- `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` are unproved analytic inputs. The reduction proposition contains most of the hard Appendix C work. The source coverage and generic reduction now instantiate the actual finite zeta-zero family and concrete `ResidualZeroBoundProp` without an additional zero-set assumption.
- `DetectorBetaShiftProp` is an unproved analytic input to #13 and belongs to the redesigned #16 Fourier/contour argument. `LocalZeroMultiplicityBoundProp` is now the narrow unproved unit-zero input: it gives a uniform multiplicity-weighted `O(log T)` bound for ordinary unshifted unit intervals of Type-I zeros. #13 proves the shifted and scale-filtered occupancy estimate from it.
- `HuxleyZeroDensity (fun σ T => N σ T)` is a legitimate high-`σ` input to the conditional transfer: the source uses Huxley on `4/5 ≤ σ ≤ 1`, outside the central Section 13.1 argument. It is stated but unproved in the project.
- This Huxley dependency is internal to deriving the full-range Guth–Maynard theorem. It does not belong in `CombinedZeroDensityTransfer`, which correctly assumes the completed full-range Guth–Maynard estimate and combines that estimate only with Ingham.
- The global count convention requires preservation of zeta zeros and analytic multiplicity under complex conjugation. No current project theorem supplies this exact bridge. #14 should prove it if practical; otherwise the conditional transfer must expose one narrowly stated provisional parameter and track its later discharge under #15.
- The four `ZeroCount.lean` axioms cover right-half-plane growth, functional-equation growth, Phragmén–Lindelöf interpolation, and an Euler-product lower bound. Compact-rectangle zero finiteness is proved independently of them.
- The seven `BetaDependence.lean` axioms and two `Decoupling.lean` axioms are not acceptable final dependencies. Several need new statements, not just proof terms.

## Main Transfer Gap

The Section 13.1 chain is partially assembled. The formal Shitlist #14 plan now has the following status:

1. **F-01:** prove the positive-slab-to-global reduction, including zeta conjugation with analytic multiplicity, eventual dyadic summation, the geometric bound, and the finite low-height remainder;
2. **F-02/F-03:** consume the actual detector and exact Type-I/residual partition, deriving the concrete residual-zero estimate from the separately named Type-I/contour-Type-II coverage, fourth-moment reduction, and twisted-fourth-moment inputs;
3. **F-04/F-05:** derive #13's normalized separated output from the explicit beta-shift and ordinary unit-zero multiplicity inputs;
4. **F-06:** prove the exact translated normalized-detector identity, `N^σ` scaling, phase preservation, and coefficient-growth estimate;
5. **F-07:** finite preparation is complete: lower-endpoint vanishing, dyadic block split, powered phase identity, coefficient normalization, and simultaneous block-and-ordinate pigeonholing are kernel-checked;
6. **F-08:** complete: `k_selection` gives both sides of equation (13.1), `2 ≤ k ≤ 101`, and the detector-scale logarithmic loss is eventually absorbed;
7. **F-09:** exponent arithmetic is complete; applying the repaired large-values hypothesis with all normalization losses uniformly absorbed remains open;
8. **F-10:** equation (13.2) and both mean-value exponent bounds are complete; the uniform normalized-block mean-value application remains open;
9. assemble the central positive-slab theorem for `7/10 ≤ σ ≤ 4/5`, extend it to the project count `N σ T`, and use an explicit Huxley input for `4/5 ≤ σ ≤ 1`; and
10. the conclusion-equivalent transfer axiom and every `True` artifact are deleted. The current public theorem is deliberately interim: it accepts `TypeIPositiveSlabBoundProp` and `DyadicToGlobalZeroCountProp`. Replace those two parameters by the planned primitive inputs after the two remaining assemblies are proved.

The Section 13.1 target exponent is `15(1-σ)/(3+5σ)`. The later combined Ingham/Guth–Maynard exponent is `30(1-σ)/13`; the previously recorded `30(1-σ)/(13+10σ)` expression was erroneous.

No theorem yet performs the entire primitive-input chain. `conditionalZeroDensityTransfer` is no longer circular: its two new provisional parameters are strictly narrower than the global conclusion and are documented as the exact remaining central-slab and F-01 obligations.

## Build, Audit, and Repository Status

- `lake build` succeeds without Lean warnings for the default `RiemannZeta` library graph.
- The current principal runner log `logs/overall_proof_20260808_140222.log` records five Lean stages. Stages 1–4 pass with zero warnings; the audit synchronizes 173/173 production theorems and passes the new #14 declarations with only permitted Lean/Mathlib logical axioms. Four declarations still have forbidden project-axiom dependencies and 13 direct project axioms remain, so the overall exit code is honestly 1.
- `Audit.lean` is a real transitive dependency audit for its synchronized production theorem list. The two remaining auxiliary Lean files contain anonymous `example` declarations rather than named public theorems, so the cleanup leaves no named auxiliary theorem outside the audit.
- Shitlist #2 removed all five failing auxiliary files, all empty/comment-only Lean tombstones, stale zero-count-model experiments, duplicate scratch lemmas, and obsolete `#check` probes. No Lean file is empty.
- `clean_cache.lean` and `build_it.lean` were deleted. Lean elaboration can no longer trigger their cache deletion or hard-coded external process invocation.
- `Polynomial Power Expansion Notes.md` now records how the formerly missing structural-to-coefficient expansion was implemented and identifies only the classical coefficient-growth inputs as remaining #10/Goal C work.
- `TestExp.lean` and `test_separated.lean` are the only retained non-production Lean files. They are stages 3 and 4 of the principal runner and pass without warnings.
- The prohibited-proof scan is clean for `sorry`, `admit`, and `sorryAx`. The project-axiom scan is not clean, and the vacuity scan still finds the pre-existing `smooth_compact_is_schwartz : True`; the former `h_bound : True` in `Transfer.lean` is gone.
- README, paper, progress, audit, and Shitlist status are synchronized for the completed #13 conditional/normalized layer and its still-open unit-zero and beta-shift analytic inputs.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: exact formal targets and infrastructure | **Substantially improved but analytic inputs remain unproved.** The large-values quantifiers/sign bridge, base-interval mean-value interface, complete bounded `k` selection, powered block preparation, and F-09/F-10 exponent arithmetic are now kernel-checked. The large-values and mean-value propositions themselves remain assumptions. |
| Goal B: conditional zero-density transfer | **Integrity repair complete; primitive-input assembly still open.** The named theorem is no longer circular and is audit-clean, but it still accepts the explicit intermediate `TypeIPositiveSlabBoundProp` and `DyadicToGlobalZeroCountProp`. Goal B is not complete until those are derived from the planned primitive inputs. |
| Goal C: discharge classical hypotheses | **Not achieved.** Thirteen direct project axioms remain, strong analytic proposition inputs are unproved, and several beta/decoupling interfaces are malformed. |
| Goal D: Guth–Maynard large-values theorem | **Not achieved.** `LargeValues.lean` contains no theorem proving the target; the decoupling layer is axiomatic and partly misstated. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** The finite-selection, asymptotic, zero-finiteness, and polynomial lemmas are candidates, but interfaces still need source-fidelity review. |

## Corrected Work Order

1. **Shitlists #2 and #8 completed:** all retained Lean files are classified, warning-failing runner stages cover both auxiliary examples, side-effect utilities are gone, and integrity scans use `--no-ignore`.
2. **Shitlist #13 conditional/normalized layer completed:** the input is an ordinary unit-zero bound; shifted covering, raw loss accounting, ordinate/coefficient translation, and epsilon normalization are kernel-checked.
3. **Shitlist #14 statement-boundary repairs completed:** positivity/eventual quantifiers, the exponential-sign bridge, and the `[0,T]` mean-value convention are kernel-checked.
4. Complete the uniform asymptotic central Type-I slab assembly from the repaired large-values and mean-value interfaces, #13 extraction, `PowCoeffBoundProp`, bounded `k`, and the finite powered-block theorems.
5. Prove F-01's zeta-conjugation/multiplicity and dyadic-summation boundary, replacing `DyadicToGlobalZeroCountProp`.
6. Replace `TypeIPositiveSlabBoundProp` and `DyadicToGlobalZeroCountProp` in the public transfer signature by the planned individually named primitive inputs.
7. Redesign the malformed beta-removal and decoupling propositions before attempting their proofs. The redesigned beta layer must eventually prove #13's pointwise beta-shift interface.
8. Prove the narrow unit-zero, beta-shift, Type-II, mean-value, Huxley, divisor-count, factorization-count, conjugation, growth, and Euler-product inputs one independently auditable obligation at a time.
9. Formalize the corrected decoupling and large-values chain only after its exact source-facing statements are stable.
10. Synchronize README, paper, progress, audit list, Shitlist, and runner evidence after each material change.

## Defensible Current Claim

The repository now has an audit-clean noncircular interim transfer and a substantially stronger Section 13.1 infrastructure layer: repaired source interfaces, complete bounded equation-(13.1) selection, exact powered support and translation identities, normalized unit coefficients, simultaneous fixed-block pigeonholing, and all F-09/F-10 exponent comparisons. It still does not verify the full primitive-input Section 13.1 transfer or the Guth–Maynard large-values theorem. The audit currently reports four pre-existing project-axiom-dependent declarations; the beta-shift and unit-zero inputs to #13 remain unproved; important beta and decoupling interfaces remain vacuous or incorrect; uniform central Type-I asymptotic bookkeeping is open; and F-01 remains the explicit `DyadicToGlobalZeroCountProp` parameter rather than a proved conjugation/dyadic theorem.
