# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Production Build Passes; Repository Alignment and Main Mathematics Fail

The repository contains useful kernel-checked finite mathematics and several honest conditional deductions. It does **not** contain a verified formalization of the Section 13.1 zero-density transfer, the Guth–Maynard large-values theorem, or the principal analytic inputs needed by either result.

The current five-stage principal runner covers every retained Lean file in its intended role: the root build covers the 27-file production graph, `Audit.lean` runs as the explicit dependency audit, and `TestExp.lean` plus `test_separated.lean` elaborate as separate warning-failing example stages. There are 30 Lean files on disk, and all non-audit elaboration stages pass with zero warnings. The audit and direct-axiom gate still fail honestly on the known mathematical assumptions.

The production Guth–Maynard source still contains 14 direct project `axiom` declarations: seven in `BetaDependence.lean`, two in `Decoupling.lean`, one in `Transfer.lean`, and four in `ZeroCount.lean`. No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency.

## Highly Critical Re-Audit Findings

| Severity | Finding | Consequence |
|---|---|---|
| Critical | `Transfer.lean` defines `AlgebraicCombinationProp` to be the target zero-density conclusion, postulates that proposition, and returns it from `conditionalZeroDensityTransfer`. | Goal B has no mathematical proof progress. The current transfer is circular and must be removed, not generalized. |
| Resolved in #2/#8 | The re-audit found five failing auxiliary files, numerous empty/tombstone files, stale model experiments, two elaboration-time side-effect utilities, and a runner that omitted retained examples. | Thirty obsolete Lean files were removed, the useful expansion idea was preserved as Markdown, and the two retained anonymous examples are now separate warning-failing runner stages. |
| Critical | `BetaDependence.lean` contains `smooth_compact_is_schwartz ... : True`; `beta_dependence_removal` ignores its smoothing data and simply applies `pigeonhole_integral_bound`, which already supplies essentially the desired conclusion. `contour_shift_to_real_line` permits an unconstrained existential error. | The beta-removal layer is not merely unproved; several interfaces are vacuous or conclusion-shaped and require redesign before proof work. |
| Critical | `l2_parabola_incidence_bound` bounds the cardinality of an arbitrary finite 1-separated real set without any height interval. This is false as stated. The block indices in `DecouplingProp` also do not match the separate block-decomposition convention. | Shitlist #17 requires statement repair before the decoupling axioms can be meaningfully discharged. |
| High | `k_selection` does not formalize the full scale choice in Guth–Maynard equation (13.1): its second branch proves only the lower inequality, it lacks the source upper-scale hypothesis, it does not prove the upper inequality there, and it gives no uniform bound on `k`. | The exponent/scale infrastructure is insufficient for the F-07 to F-10 transfer chain despite being axiom-free. |
| High | `GuthMaynardLargeValues` is only a proposition definition. It omits an explicit positive constant and eventual threshold, adds `1 ≤ V`, and uses `n^{-it}` whereas Theorem 1.1 is written with `n^{it}`. | Goal A's exact source-statement gate is not complete. The sign conventions are likely equivalent, but no Lean equivalence bridge proves that fact. |
| Resolved in #10 | `polynomial_power_identity` formerly stated only the definitional equality `powPoly = detectPoly ^ k`. | It now proves the full finite `powCoeff` expansion over `m ∈ [N^k,(2N)^k]`, including `k = 0`, by expanding over tuples and regrouping by their product. |
| High | The repaired #12 theorem still composes three strong proposition inputs. `TypeIIFourthMomentReductionProp` packages the Gamma-decay, Hölder, separation, and local-multiplicity work rather than proving it. | The generic and concrete residual-count deductions are valid, including the eventual coverage bridge and exact multiplicity-count identity, but they do not prove Maynard–Pratt Lemma 24. |
| Resolved for #13's conditional layer | The critical audit found that `LocalZeroMultiplicityBoundProp` directly assumed the shifted, scale-filtered occupancy estimate and that the output interval and logarithmic losses were not ready for the large-values step. | The input now bounds only unshifted unit intervals. Lean proves the `2⌈H⌉+1` shifted-bin cover, raw enlarged-interval estimate, ordinate/coefficient translation to `[0,3T]`, phase-norm preservation, and pure epsilon-power normalization. The unit-zero and beta-shift propositions themselves remain unproved #15/#16 analytic inputs. |
| Resolved in #9 | `DetectorCoeffBoundProp` chooses its constant after fixing `T` and cannot by itself support powering. | The exact detector is now bounded by `n.divisors.card`, and `uniformDetectorCoeffBound_of_divisorCount` proves the full `T`-uniform estimate from the explicit classical `DivisorCountBoundProp`. The classical divisor estimate remains Goal C work. |
| Resolved in #8 | `Paper_Riemann_Zeta.md` formerly expected 17 audit failures after the production audit had fallen to 6. | The paper, README, and agendas now report 6 dependency failures across the current 140 synchronized declarations. |

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
9. The actual truncated Möbius detector, exact support/vanishing statements, smoothing bounds, full-divisor-cardinality bounds uniform in `T`, and the conditional theorem deriving `UniformDetectorCoeffBoundProp` from `DivisorCountBoundProp`.
10. Finite-sum L2 inequalities and elementary complex-exponential facts. These do not prove Fourier inversion, Fourier decay, or an analytic mean-value estimate.
11. Compactness of `ZeroRectangle` and finiteness of its intersection with Mathlib's zeta-zero set; the concrete finite set and multiplicity count no longer use a project finiteness axiom.
12. The exact Type-I-plus-residual filtering identity. A residual zero is not definitionally identified with a source contour-Type-II zero.
13. The structural identity `powPoly = detectPoly ^ k`, the full finite coefficient expansion `polynomial_power_identity`, the substantive conditional bound from a uniform detector input, and `powCoeff_bound_of_divisor_and_factorization`, which exposes the two classical arithmetic inputs directly.
14. The conditional combined-exponent implication from separately assumed Ingham and Guth–Maynard zero-density estimates.
15. The conditional finite large-value count from an explicit `MontgomeryMeanValue` parameter. The analytic mean-value theorem remains unproved.
16. Generic residual-count comparison and epsilon-bound composition from explicit coverage, Type-II fourth-moment reduction, and twisted-fourth-moment inputs; eventual source coverage is now bridged to the concrete dyadic zeta-zero family, whose weighted count is proved equal to `residualZeroCount`, yielding a concrete conditional `ResidualZeroBoundProp` theorem.
17. Finite admissible dyadic scales, exact weighted pigeonholing, multiplicity aggregation, and shifted-bin covering from an ordinary unshifted unit-zero multiplicity bound.
18. Raw conditional Type-I extraction with explicit `T^δ (log T)^2` loss, exact detector-line and coefficient-phase translation identities, coefficient-norm preservation, and normalized conditional extraction into `[0,3T]` with a pure `C T^ε |W|` bound.

## Conditional Interfaces and Remaining Assumptions

An explicit proposition parameter is preferable to a hidden axiom only when its statement is mathematically faithful and strictly upstream. It still does not count as a proved analytic result.

- `MontgomeryMeanValue` is an explicit uniform proposition with one positive absolute constant. It is unproved.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp` are unproved classical arithmetic inputs. `UniformDetectorCoeffBoundProp` is no longer an independent obligation: it is conditionally proved from `DivisorCountBoundProp`.
- `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` are unproved analytic inputs. The reduction proposition contains most of the hard Appendix C work. The source coverage and generic reduction now instantiate the actual finite zeta-zero family and concrete `ResidualZeroBoundProp` without an additional zero-set assumption.
- `DetectorBetaShiftProp` is an unproved analytic input to #13 and belongs to the redesigned #16 Fourier/contour argument. `LocalZeroMultiplicityBoundProp` is now the narrow unproved unit-zero input: it gives a uniform multiplicity-weighted `O(log T)` bound for ordinary unshifted unit intervals of Type-I zeros. #13 proves the shifted and scale-filtered occupancy estimate from it.
- The four `ZeroCount.lean` axioms cover right-half-plane growth, functional-equation growth, Phragmén–Lindelöf interpolation, and an Euler-product lower bound. Compact-rectangle zero finiteness is proved independently of them.
- The seven `BetaDependence.lean` axioms and two `Decoupling.lean` axioms are not acceptable final dependencies. Several need new statements, not just proof terms.

## Main Transfer Gap

The Section 13.1 chain has not been assembled. A valid replacement for `conditionalZeroDensityTransfer` must explicitly implement:

1. dyadic reduction of the zero count;
2. the exact detector classification and Type-I/contour-Type-II cover;
3. beta removal and local zero multiplicity;
4. **kernel-checked conditionally:** weighted separated extraction from a narrow unit-zero input, shifted-bin covering, interval normalization, coefficient phase translation, and explicit epsilon-loss absorption;
5. the classical divisor-count and factorization-count inputs; the downstream uniform-detector reduction and explicit polynomial-power coefficient expansion are now kernel-checked;
6. the complete `k`-selection inequalities and a bounded choice of `k`;
7. the large-values/mean-value case split; and
8. the final exponent algebra yielding `30(1-σ)/(13+10σ)`.

No existing Lean theorem performs this chain. `conditionalZeroDensityTransfer` currently assumes the final conclusion through a definitionally equal wrapper.

## Build, Audit, and Repository Status

- `lake build` succeeds without Lean warnings for the default `RiemannZeta` library graph.
- The post-#13 principal runner log `logs/overall_proof_20260808_124518.log` records five Lean stages. Stages 1–4 pass with zero warnings; the audit synchronizes 140/140 production theorems and passes all eight new #13 theorems with only permitted Lean/Mathlib logical axioms. The same 6 unrelated forbidden-dependency failures and 14 direct project axioms remain, so the overall exit code is honestly 1.
- `Audit.lean` is a real transitive dependency audit for its synchronized production theorem list. The two remaining auxiliary Lean files contain anonymous `example` declarations rather than named public theorems, so the cleanup leaves no named auxiliary theorem outside the audit.
- Shitlist #2 removed all five failing auxiliary files, all empty/comment-only Lean tombstones, stale zero-count-model experiments, duplicate scratch lemmas, and obsolete `#check` probes. No Lean file is empty.
- `clean_cache.lean` and `build_it.lean` were deleted. Lean elaboration can no longer trigger their cache deletion or hard-coded external process invocation.
- `Polynomial Power Expansion Notes.md` now records how the formerly missing structural-to-coefficient expansion was implemented and identifies only the classical coefficient-growth inputs as remaining #10/Goal C work.
- `TestExp.lean` and `test_separated.lean` are the only retained non-production Lean files. They are stages 3 and 4 of the principal runner and pass without warnings.
- The prohibited-proof scan is clean for `sorry`, `admit`, and `sorryAx`. The project-axiom scan is not clean, and the vacuity scan finds `smooth_compact_is_schwartz : True` plus the unused `h_bound : True` in `Transfer.lean`.
- README, paper, progress, audit, and Shitlist status are synchronized for the completed #13 conditional/normalized layer and its still-open unit-zero and beta-shift analytic inputs.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: exact formal targets and infrastructure | **Partially achieved, with remaining statement-level defects.** Useful definitions and finite infrastructure exist, including the exact polynomial-power coefficient expansion and #13's normalized translated extraction interface; the auxiliary Lean tree is clean, and the runner covers every retained Lean file. `GuthMaynardLargeValues` still does not match the source quantifiers/sign convention exactly, and `k_selection` remains incomplete. |
| Goal B: conditional zero-density transfer | **Not achieved.** The only theorem with that name is circular. |
| Goal C: discharge classical hypotheses | **Not achieved.** Fourteen direct axioms remain, strong analytic proposition inputs are unproved, and several beta/decoupling interfaces are malformed. |
| Goal D: Guth–Maynard large-values theorem | **Not achieved.** `LargeValues.lean` contains no theorem proving the target; the decoupling layer is axiomatic and partly misstated. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** The finite-selection, asymptotic, zero-finiteness, and polynomial lemmas are candidates, but interfaces still need source-fidelity review. |

## Corrected Work Order

1. **Shitlists #2 and #8 completed:** all retained Lean files are classified, warning-failing runner stages cover both auxiliary examples, side-effect utilities are gone, and integrity scans use `--no-ignore`.
2. **Shitlist #13 conditional/normalized layer completed:** the input is an ordinary unit-zero bound; shifted covering, raw loss accounting, ordinate/coefficient translation, and epsilon normalization are kernel-checked.
3. Repair the formal targets in `Statements.lean`, including positivity/eventual quantifiers and a proved bridge between the `n^{it}` and `n^{-it}` sign conventions.
4. Repair `k_selection` to match the complete equation (13.1) scale choice, including its hypotheses, both inequalities, and a bounded `k`. The structural-power/explicit-coefficient expansion is complete.
5. Redesign the malformed beta-removal and decoupling propositions before attempting their proofs. Remove every `True` placeholder and conclusion-shaped input. The redesigned beta layer must eventually prove #13's pointwise beta-shift interface.
6. Replace `Transfer.lean` with an explicit F-01 through F-10 conditional deduction. Do not retain `AlgebraicCombinationProp` or `algebraic_combination_unconditional`.
7. Prove the narrow unit-zero, beta-shift, Type-II, mean-value, divisor-count, factorization-count, growth, and Euler-product inputs one independently auditable obligation at a time.
8. Formalize the corrected decoupling and large-values chain only after its exact source-facing statements are stable.
9. Synchronize README, paper, progress, audit list, Shitlist, and runner evidence after each material change.

## Defensible Current Claim

The repository has a warning-free production build, a cleaned auxiliary Lean tree, all-retained-file runner coverage, and a useful but incomplete Lean infrastructure layer: compact zeta-zero finiteness, an actual truncated Möbius detector, the exact finite polynomial-power coefficient expansion, finite dyadic pigeonholing, weighted separated selection, shifted-bin covering, exact phase translation, and a downstream-normalized conditional Type-I extraction theorem. It does not yet verify the Section 13.1 transfer or the Guth–Maynard large-values theorem. Fourteen project axioms remain; the transfer is circular; the beta-shift and unit-zero inputs to #13 are unproved; important beta and decoupling interfaces remain vacuous or incorrect; and the source-facing large-values and `k`-selection statements need repair.
