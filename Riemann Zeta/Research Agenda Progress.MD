# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Production Build Passes; Repository Alignment and Main Mathematics Fail

The repository contains useful kernel-checked finite mathematics and several honest conditional deductions. It does **not** contain a verified formalization of the Section 13.1 zero-density transfer, the Guth–Maynard large-values theorem, or the principal analytic inputs needed by either result.

The current default build is warning-free for the root-imported production graph. That is a narrower claim than repository-wide verification. There are 60 Lean files on disk: the root library plus its 26 imported modules and `Audit.lean` form the 28-file production/audit perimeter; 32 other Lean files are outside it. Five retained auxiliary files fail standalone elaboration, and two excluded utility files execute filesystem or process actions through `#eval`. The repository therefore does not presently satisfy the all-Lean-file policy in `AGENTS.md`.

The production Guth–Maynard source still contains 14 direct project `axiom` declarations: seven in `BetaDependence.lean`, two in `Decoupling.lean`, one in `Transfer.lean`, and four in `ZeroCount.lean`. No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency.

## Highly Critical Re-Audit Findings

| Severity | Finding | Consequence |
|---|---|---|
| Critical | `Transfer.lean` defines `AlgebraicCombinationProp` to be the target zero-density conclusion, postulates that proposition, and returns it from `conditionalZeroDensityTransfer`. | Goal B has no mathematical proof progress. The current transfer is circular and must be removed, not generalized. |
| Critical | Repository-wide build coverage is false. `test_pow.lean`, `test_le_floor.lean`, `TestCauchy.lean`, `test7.lean`, and `test8.lean` fail standalone elaboration. Numerous other retained files are empty or tombstone-only. | Shitlist #2, #6, and #8 were marked complete too broadly. The runner proves only the production perimeter, not compliance of every Lean file. |
| Critical | `BetaDependence.lean` contains `smooth_compact_is_schwartz ... : True`; `beta_dependence_removal` ignores its smoothing data and simply applies `pigeonhole_integral_bound`, which already supplies essentially the desired conclusion. `contour_shift_to_real_line` permits an unconstrained existential error. | The beta-removal layer is not merely unproved; several interfaces are vacuous or conclusion-shaped and require redesign before proof work. |
| Critical | `l2_parabola_incidence_bound` bounds the cardinality of an arbitrary finite 1-separated real set without any height interval. This is false as stated. The block indices in `DecouplingProp` also do not match the separate block-decomposition convention. | Shitlist #17 requires statement repair before the decoupling axioms can be meaningfully discharged. |
| High | `k_selection` does not formalize the full scale choice in Guth–Maynard equation (13.1): its second branch proves only the lower inequality, it lacks the source upper-scale hypothesis, it does not prove the upper inequality there, and it gives no uniform bound on `k`. | The exponent/scale infrastructure is insufficient for the F-07 to F-10 transfer chain despite being axiom-free. |
| High | `GuthMaynardLargeValues` is only a proposition definition. It omits an explicit positive constant and eventual threshold, adds `1 ≤ V`, and uses `n^{-it}` whereas Theorem 1.1 is written with `n^{it}`. | Goal A's exact source-statement gate is not complete. The sign conventions are likely equivalent, but no Lean equivalence bridge proves that fact. |
| High | `polynomial_power_identity` is only the definitional equality `powPoly = detectPoly ^ k`; no theorem identifies the power with the explicit `powCoeff` convolution expansion. | Shitlist #10 completed a real conditional coefficient estimate but did not complete the polynomial-power step needed by the transfer. |
| High | The #12 theorem composes three strong proposition inputs. `TypeIIFourthMomentReductionProp` packages the Gamma-decay, Hölder, separation, and local-multiplicity work rather than proving it. | The residual-count deduction is valid, but it is not a formalization of Maynard–Pratt Lemma 24 and has no concrete zeta instantiation. |
| High | The #13 finite weighted selection and dyadic pigeonholing are substantive, but the two remaining inputs supply the nearby large detector value and the precise shifted-bin occupancy bound. | #13 completed an integrity-clean conditional combinatorial layer, not the analytic separated-extraction theorem used in the paper. Its enlarged interval and subpolynomial losses still need downstream conversion. |
| Medium | `DetectorCoeffBoundProp` chooses its constant after fixing `T`; the proved theorem is therefore only a fixed-`T` finite bound. | It is too weak to provide the source's uniform coefficient control without the separate unproved `UniformDetectorCoeffBoundProp`. |
| Medium | `Paper_Riemann_Zeta.md` still contains a reproducibility statement expecting 17 audit failures, while the current production audit reports 6. | The progress document can no longer claim that all prose artifacts are synchronized or fully honest. |

The source comparison above follows Guth–Maynard Theorem 1.1 and Section 13.1. In particular, Section 13.1 uses `7/10 ≤ σ ≤ 4/5`, `O(log T)` dyadic scales, a complete two-sided choice of `N^k` in equation (13.1), separated large values, and a large-values/mean-value case split. The present Lean development formalizes only fragments of that chain.

## Verified Kernel-Checked Results

The following are genuinely proved without project-specific axioms or `sorryAx`, apart from normal Lean/Mathlib logical dependencies such as `propext`, `Classical.choice`, and `Quot.sound`.

1. Finite Dirichlet-polynomial conjugation, norm, threshold, and zero identities.
2. Cross-norm nonnegativity, factor symmetry, real-part bounds, and zero characterization.
3. Coordinate wrappers for Mathlib's completed-zeta functional equation and norm reflection, with the documented hypotheses on both conjugate zeros.
4. Hardy-type norm and zero equivalence on the critical line; the negation result remains conditional on an explicit norm-symmetry premise.
5. Translation and finite selection lemmas for separated real sets, including `weighted_separated_selection` with its necessary local-occupancy factor.
6. `EpsilonPowerBound` reflexivity, transitivity, monotonicity, and power-scaling infrastructure.
7. Basic exponent positivity and elementary inequalities. The incomplete `k_selection` theorem is kernel-checked but should not be described as the full source scale-selection step.
8. The genuine dyadic Dirichlet-polynomial definition, normalization bound, and two-factor convolution support.
9. The actual truncated Möbius detector, exact support/vanishing statements, smoothing bounds, and the fixed-`T` coefficient bound encoded by `DetectorCoeffBoundProp`.
10. Finite-sum L2 inequalities and elementary complex-exponential facts. These do not prove Fourier inversion, Fourier decay, or an analytic mean-value estimate.
11. Compactness of `ZeroRectangle` and finiteness of its intersection with Mathlib's zeta-zero set; the concrete finite set and multiplicity count no longer use a project finiteness axiom.
12. The exact Type-I-plus-residual filtering identity. A residual zero is not definitionally identified with a source contour-Type-II zero.
13. The structural identity `powPoly = detectPoly ^ k` and a substantive conditional bound on `powCoeff` from `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp`. The structural-to-coefficient expansion remains absent.
14. The conditional combined-exponent implication from separately assumed Ingham and Guth–Maynard zero-density estimates.
15. The conditional finite large-value count from an explicit `MontgomeryMeanValue` parameter. The analytic mean-value theorem remains unproved.
16. Generic residual-count comparison and epsilon-bound composition from explicit coverage, Type-II fourth-moment reduction, and twisted-fourth-moment inputs.
17. Finite admissible dyadic scales, exact weighted pigeonholing, multiplicity aggregation, and conditional separated extraction from explicit beta-shift and local-multiplicity inputs.

## Conditional Interfaces and Remaining Assumptions

An explicit proposition parameter is preferable to a hidden axiom only when its statement is mathematically faithful and strictly upstream. It still does not count as a proved analytic result.

- `MontgomeryMeanValue` is an explicit uniform proposition with one positive absolute constant. It is unproved.
- `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` are unproved arithmetic inputs to the powered-coefficient theorem.
- `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` are unproved analytic inputs. The reduction proposition contains most of the hard Appendix C work.
- `DetectorBetaShiftProp` and `LocalZeroMultiplicityBoundProp` are unproved analytic inputs to #13. They contain the detector-large-value and local-multiplicity estimates needed before the finite selection argument can run.
- The four `ZeroCount.lean` axioms cover right-half-plane growth, functional-equation growth, Phragmén–Lindelöf interpolation, and an Euler-product lower bound. Compact-rectangle zero finiteness is proved independently of them.
- The seven `BetaDependence.lean` axioms and two `Decoupling.lean` axioms are not acceptable final dependencies. Several need new statements, not just proof terms.

## Main Transfer Gap

The Section 13.1 chain has not been assembled. A valid replacement for `conditionalZeroDensityTransfer` must explicitly implement:

1. dyadic reduction of the zero count;
2. the exact detector classification and Type-I/contour-Type-II cover;
3. beta removal and local zero multiplicity;
4. weighted separated extraction followed by interval normalization;
5. uniform detector coefficients and the explicit polynomial-power coefficient expansion;
6. the complete `k`-selection inequalities and a bounded choice of `k`;
7. the large-values/mean-value case split; and
8. the final exponent algebra yielding `30(1-σ)/(13+10σ)`.

No existing Lean theorem performs this chain. `conditionalZeroDensityTransfer` currently assumes the final conclusion through a definitionally equal wrapper.

## Build, Audit, and Repository Status

- `lake build` succeeds without Lean warnings for the default `RiemannZeta` library graph.
- The principal runner log `logs/overall_proof_20260808_110343.log` records 123 explicit and 123 discovered production theorems, 6 forbidden-dependency failures, 14 direct project axioms, warning-free production builds, and an honest overall exit code of 1.
- `Audit.lean` is a real transitive dependency audit for its synchronized production theorem list. It is **not** a repository-wide theorem audit: auxiliary/global declarations outside that list are not audited.
- Standalone audit checks found five elaboration failures outside the production graph: a duplicate declaration in `RiemannZeta/GuthMaynard/test_pow.lean`, a nonexistent Mathlib import in `test_le_floor.lean`, a syntax error in `TestCauchy.lean`, and stale removed-API usage in `test7.lean` and `test8.lean`.
- `clean_cache.lean` removes `.lake/build` during elaboration through `#eval IO.FS.removeDirAll`; `build_it.lean` invokes a hard-coded user-specific Lake executable through `#eval`. Neither belongs in an unchecked proof-source perimeter.
- Numerous zero-byte or comment-only test/scratch files remain. In particular, `ExtractSeparated_scratch.lean` says only that it was deleted, but the file itself remains. Historical Shitlist records claiming every such path was deleted are therefore not literally accurate.
- The prohibited-proof scan is clean for `sorry`, `admit`, and `sorryAx`. The project-axiom scan is not clean, and the vacuity scan finds `smooth_compact_is_schwartz : True` plus the unused `h_bound : True` in `Transfer.lean`.
- README and paper synchronization is not complete; the paper's stale expected-failure count is one confirmed discrepancy.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: exact formal targets and infrastructure | **Partially achieved, with a statement-level defect.** Useful definitions and finite infrastructure exist, but `GuthMaynardLargeValues` does not yet match the source quantifiers/sign convention exactly, auxiliary Lean coverage is incomplete, and the scale/power bridge is unfinished. |
| Goal B: conditional zero-density transfer | **Not achieved.** The only theorem with that name is circular. |
| Goal C: discharge classical hypotheses | **Not achieved.** Fourteen direct axioms remain, strong analytic proposition inputs are unproved, and several beta/decoupling interfaces are malformed. |
| Goal D: Guth–Maynard large-values theorem | **Not achieved.** `LargeValues.lean` contains no theorem proving the target; the decoupling layer is axiomatic and partly misstated. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** The finite-selection, asymptotic, zero-finiteness, and polynomial lemmas are candidates, but interfaces still need source-fidelity review. |

## Corrected Work Order

1. Restore the verification perimeter: classify, repair, or remove every auxiliary Lean file; eliminate elaboration-time side-effect utilities from proof sources; and make the human-facing runner compile every retained Lean file or explicitly classify a safe exclusion.
2. Repair the formal targets in `Statements.lean`, including positivity/eventual quantifiers and a proved bridge between the `n^{it}` and `n^{-it}` sign conventions.
3. Repair `k_selection` to match the complete equation (13.1) scale choice, including its hypotheses, both inequalities, and a bounded `k`; then prove the structural-power/explicit-coefficient expansion.
4. Redesign the malformed beta-removal and decoupling propositions before attempting their proofs. Remove every `True` placeholder and conclusion-shaped input.
5. Replace `Transfer.lean` with an explicit F-01 through F-10 conditional deduction. Do not retain `AlgebraicCombinationProp` or `algebraic_combination_unconditional`.
6. Prove the remaining local-zero, beta-shift, Type-II, mean-value, detector-uniformity, factorization, growth, and Euler-product inputs one independently auditable obligation at a time.
7. Formalize the corrected decoupling and large-values chain only after its exact source-facing statements are stable.
8. Synchronize README, paper, progress, audit list, Shitlist, and runner evidence after each material change.

## Defensible Current Claim

The repository has a warning-free production build and a useful but incomplete Lean infrastructure layer: compact zeta-zero finiteness, an actual truncated Möbius detector, finite dyadic pigeonholing, weighted separated selection, and several kernel-checked conditional deductions. It does not yet verify the Section 13.1 transfer or the Guth–Maynard large-values theorem. Fourteen project axioms remain; the transfer is circular; important beta and decoupling interfaces are vacuous or incorrect; the source-facing large-values and `k`-selection statements need repair; and the all-file verification policy is violated by excluded failing and side-effectful Lean files.
