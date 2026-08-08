# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Infrastructure Partially Verified; Main Transfer and Analytic Proofs Pending

The project contains a useful collection of kernel-checked elementary lemmas, formal target statements, and provisional interfaces for the Guth–Maynard program. It does **not** yet contain a verified formalization of the Section 13.1 zero-density transfer.

The default `lake build` target imports and compiles every intended production module with zero Lean warnings. Warning-free compilation does not make the unresolved project-axiom dependencies valid.

The non-test Guth–Maynard source contains 23 direct `axiom` declarations, all of which occur in modules reachable from the default `RiemannZeta` root import. A theorem is therefore counted as proved below only when its audited dependencies contain no project-specific axiom and no `sorryAx`.

## Verified Results

The following results are genuinely proved in Lean without project-specific axioms or `sorryAx`, apart from Lean/Mathlib's standard logical axioms such as `propext`, `Classical.choice`, and `Quot.sound`.

1. **Finite Dirichlet polynomials:** Conjugation identities, norm conjugation, threshold symmetry, and zero conjugation.
2. **Cross-norm products:** Nonnegativity, factor-swap invariance, real-part upper bounds, and zero characterization.
3. **Completed zeta wrappers:** Coordinate forms of Mathlib's completed-zeta functional equation and norm reflection. The fourfold-zero theorem assumes zeros at both conjugate input points; it is not a one-zero fourfold-orbit result.
4. **Hardy-type normalization:** Norm and zero equivalence between `hardyZ t` and `riemannZeta (criticalLinePoint t)`. The negation symmetry theorem remains conditional on an explicitly supplied norm-symmetry hypothesis.
5. **Separated-set translations:** Translation preserves separation, maps `[T, 2T]` into `[0, T]`, and preserves exact cardinality.
6. **Finite separated-set selection:** `separated_selection` proves a combinatorial selection theorem from a unit-interval occupancy bound. This does not prove the zeta-specific extraction theorem `extract_separated_lemma`.
7. **Exponent arithmetic:** `k_selection`, `denom_pos`, `guth_maynard_exponent_pos`, and the elementary inequality `extractSeparated_k_selection`.
8. **Dirichlet-polynomial infrastructure:** The dyadic interval definition, bridge to the existing positive-index polynomial, normalized coefficient bound, and two-factor convolution support.
9. **Truncated Möbius detector:** `detectorDivisors` has exact membership and finite-cutoff support theorems. `norm_mobius_sum_le_cutoff`, `detectorCoeff_eq_zero_iff`, and `norm_detectorCoeff_le_cutoff` prove the magnitude and vanishing behavior of the smoothed coefficients. `detectorCoeff_bound` proves `DetectorCoeffBoundProp`, uniformly in positive `n` for each fixed `T`.
10. **Elementary smoothing and cutoff facts:** `exp_smoothing_bound`, cutoff nonnegativity, cutoff support boundary lemmas, and the upper bounds `psiCutoff_le_exp` and `psiCutoff_bounded_of_sigma_le_beta`.
11. **Elementary complex-exponential facts:** `cexp_periodic_1`, `cexp_zero_eval`, and the norm reduction `fourier_inversion_integrand_bound`. These do not constitute Fourier inversion or Fourier decay.
12. **Finite-sum inequalities:** `sum_sq_le_card_mul_sum_sq`, `complex_sum_sq_le_card_mul_sum_sq`, and the elementary nonnegativity/zero lemmas for finite L2 sums.
13. **Basic zero-rectangle set reasoning:** Rectangle membership and inclusion lemmas. Results involving `zerosInRect` or `zeroCountRect` additionally depend on the provisional axiom `riemannZeta_finite_zeros_in_rect` and are not unconditional zeta-zero-counting theorems.
14. **Type-I/residual partition identity:** `typeI_add_residual_eq_total` is a finite-set filtering identity, conditional on the provisional zero-set construction. Its second summand is now accurately named: it counts zeros satisfying `¬ IsTypeIZero` and is not identified with the contour-integral Type II condition of Maynard–Pratt Definition 22.
15. **Powered-polynomial definitional identity:** `powPoly_eval` and `polynomial_power_identity` follow from the definition `powPoly := detectPoly ^ k`. An expansion into convolution coefficients has not been completed.
16. **Conditional powered-coefficient bound:** `powCoeff_bound_of_uniform_detector_and_factorization` proves the full `PowCoeffBoundProp` conclusion from the separately stated, narrower `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` inputs. Its finite-product and convolution-sum proof is kernel-checked. The classical inputs themselves remain unproved specifications; `k_divisor_function_bound_one` proves only its stated `m = 1` boundary case.
17. **Combined exponent implication:** `combined_zero_density_transfer_native` is an axiom-free proof that assumed Ingham and Guth–Maynard zero-density bounds imply the combined exponent. It is a conditional implication and does not prove either analytic premise or instantiate the result for the project's zeta zero count. The previously unused Huxley premise has been removed from the statement.
18. **Conditional mean-value consequence:** `halasz_montgomery_lemma_of_mean_value` derives the finite large-value cardinality estimate from an explicit `MontgomeryMeanValue` parameter. The proof squares the pointwise lower bound, sums it over the separated set, applies the supplied mean-value estimate, and cancels the positive threshold. It does not prove the mean-value input itself.
19. **Conditional Type II deduction:** `residual_zero_bound_of_cover_reduction_and_fourth_moment` proves, for an arbitrary finite weighted family, the residual-zero epsilon-power bound from three explicit upstream inputs: Type-I/Type-II coverage, an Appendix C-style reduction of genuine Type II zeros to a scaled twisted fourth moment, and the twisted fourth-moment estimate. Its four supporting lemmas prove the residual-to-Type-II count comparison and the required epsilon-power scaling. These results are independent of the provisional concrete zeta-zero set and pass the dependency audit.

## Provisional or Model-Only Results

Some declarations remain provisional specifications rather than proved results.

- `DetectorCoeffBoundProp` is proved with the quantifier order currently encoded in Lean: its constant is uniform in positive `n` but may depend on the already-fixed `T`. The stronger `UniformDetectorCoeffBoundProp` and the source-faithful, `m`-uniform `FactorizationCountBoundProp` are explicit unproved inputs to the conditional powered-coefficient theorem.
- `MontgomeryMeanValue` is now a source-faithful proposition specification with one positive absolute constant chosen before `N`, `T`, the separated set, and the coefficients. The previous exact-constant-one formulation and its project axiom have been removed.
- The former misnamed `IsTypeIIZero` and `typeIIZeroCount` have been replaced by `IsResidualZero` and `residualZeroCount`. `TypeIIZeros.lean` separately defines the short Möbius polynomial, Gamma–zeta contour integral, `IsContourTypeIIZero`, and source-facing coverage/fourth-moment propositions. These definitions and conditional deductions do not prove the three analytic proposition inputs.
- The Shitlist #13 source/interface audit found that the current extraction layer is not merely unproved. `extract_1_separated_subset` is false without a local-occupancy factor; `ExtractSeparatedTarget` permits its constant to depend on `T`, demands a dyadic scale even when the scale range may be empty, and keeps beta-shifted ordinates in `[T,2T]` without justification. These statements remain present and unproved pending the planned repair; no corrected extraction theorem is yet claimed.
- The vacuous declarations `jensens_inequality_disk`, `zeta_abs_convergent_at_2`, `typeII_dyadic_sum`, and `recursive_block_decomposition` have been removed rather than retained as `True`-valued results.
- Several positivity lemmas verify only that the proposed right-hand side of a future estimate is nonnegative. They do not establish the corresponding mean-value, decoupling, or zero-count estimate.

## Unproved Results and Explicit Dependencies

### Main transfer gap

The declaration `conditionalZeroDensityTransfer` is **not** currently a proof from the explicit Guth–Maynard large-values, Type II, local-zero-count, and mean-value hypotheses.

`AlgebraicCombinationProp` is definitionally the desired conclusion
`GuthMaynardZeroDensity (fun σ T => N σ T)`, and `algebraic_combination_unconditional` assumes that proposition directly. `conditionalZeroDensityTransfer` then returns this axiom. This is equivalent to assuming the target and does not meet Goal B or the agenda's assumption-audit gate.

The Section 13.1 proof still needs to implement the following chain explicitly:

1. dyadic reduction of the global zero count;
2. integration of the now-verified truncated Möbius detector layer into the transfer argument;
3. proofs of the now source-faithful Type-I/Type-II covering, contour-to-fourth-moment reduction, and twisted fourth-moment propositions (the generic residual-to-Type-II count comparison is proved);
4. removal of beta dependence;
5. zeta-specific separated-set extraction with multiplicity control;
6. coefficient normalization and polynomial-power expansion;
7. the large-values/mean-value case split; and
8. the final exponent calculation assembled into the conditional transfer theorem.

### Remaining analytic and number-theoretic assumptions

The current source includes, among others, the following unproved declarations:

- `riemannZeta_finite_zeros_in_rect`;
- `zeta_upper_bound_disk`, `zeta_lower_bound_center`, and `jensens_inequality_disk_zero_count`;
- `zeta_right_half_plane_bound`, `zeta_functional_equation_bound`, and `phragmen_lindelof_convexity`;
- `euler_product_lower_bound_2`;
- the proposition specification `MontgomeryMeanValue`, which is passed explicitly to the conditional large-value counting theorem rather than asserted as a fact;
- `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp`, the explicit source-facing inputs used by the new generic conditional deduction. Their proofs require the Type-I/Type-II covering result, local zero-count/multiplicity control, Gamma-function truncation estimates, Hölder/separated extraction, and a twisted fourth-moment bound for the short Möbius polynomial times `riemannZeta`. The former conclusion-shaped `typeII_bound_unconditional` and its wrapper have been removed;
- `fourier_inversion_unconditional` and `fourier_decay_unconditional`;
- `cauchy_residue_dirichlet_polynomial`, `contour_shift_to_real_line`, `fourier_decay_error_bound`, and `pigeonhole_integral_bound`;
- `type_I_zeros_dyadic_sum_bound` and `dyadic_pigeonhole_lemma`;
- `vitali_covering_lemma_1D`, `extract_1_separated_subset`, and `extract_separated_lemma`;
- the proposition specifications `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp`, which replace the former module-level divisor axiom as explicit inputs rather than asserted facts;
- `l2_parabola_incidence_bound` and `l2_decoupling_bound_unconditional`; and
- `algebraic_combination_unconditional`, which is equivalent to the desired zero-density conclusion and must be removed rather than treated as an acceptable analytic hypothesis.

### Planned Shitlist #13 repair

The extraction repair will separate the finite mathematics from the analytic inputs:

1. **Pull forward zeta-zero finiteness:** the pinned Mathlib now provides `IsCompact.inter_riemannZetaZeros_finite`. Prove `ZeroRectangle` compact and replace `riemannZeta_finite_zeros_in_rect` with a theorem derived from that result. This has been researched but not implemented, so the current axiom and audit counts remain unchanged.
2. **Finite dyadic scales:** define a finite set of admissible dyadic indices, prove equivalence with the intended Type-I definition, prove its `O(log T)` cardinality for sufficiently large `T`, assign one scale witness to every Type-I zero, and prove the exact weighted pigeonhole result. This replaces `type_I_zeros_dyadic_sum_bound` and `dyadic_pigeonhole_lemma`.
3. **Weighted separated selection:** generalize the existing kernel-checked even/odd unit-bin proof in `Separated.lean` from cardinality to arbitrary natural weights. The correct conclusion contains the local unit-bin occupancy factor; the false unconditional half-size assertion and unnecessary Vitali axiom will be deleted.
4. **Two explicit analytic inputs:** state a uniform half-open-unit-interval `LocalZeroMultiplicityBoundProp` and a pointwise `DetectorBetaShiftProp`. They are narrower than the extraction conclusion and will remain visibly unproved until the Jensen/growth and Fourier/beta-removal work is completed.
5. **Shifted fibers:** choose one shifted ordinate for each zero at the winning scale, aggregate analytic multiplicities over equal shifted ordinates, prove total-weight preservation, cover the inverse image of a shifted unit bin by `O(H)` original unit bins, and apply weighted selection.
6. **Corrected asymptotic target:** choose `C` and a sufficiently-large threshold `T₀` before `T`; restrict `σ` to the intended range; permit the separated set to lie in `[T-H,2T+H]` or another explicitly controlled interval; and absorb scale-count, logarithmic, and `T^δ` losses using a fraction of the requested epsilon.
7. **Integrity cleanup:** remove all eight current `ExtractSeparated.lean` axioms and the wrappers that merely return them. The final public theorem must be a kernel-checked deduction from the two named analytic inputs, not an assumed `ExtractSeparatedTarget`.

Mathlib's `AnalyticOnNhd.sum_divisor_le` supplies the eventual Jensen inequality needed for the local multiplicity theorem, but the required zeta analyticity/nonvanishing and uniform boundary-growth estimates still have to be connected to it. That analytic proof is not part of the finite #13 completion claim.

### Admitted-proof status

No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency. The former `powCoeffBound_native`, `powCoeffBound_unconditional`, and `k_divisor_function_bound` declarations are removed. `PowCoeffBoundProp` is now conditionally proved by `powCoeff_bound_of_uniform_detector_and_factorization`; this does not prove its two explicit classical arithmetic inputs.

## Build and Audit Status

- The default `lake build` completes successfully with zero Lean warnings.
- Direct builds of `TypeIIZeros.lean`, `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` succeed with zero Lean warnings. This does not prove their remaining analytic axioms or proposition specifications.
- `TypeIIZeros.lean`, `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` are in the default import graph. `LargeValues.lean` still contains no proof of `GuthMaynardLargeValues`; the former dangling variable that assumed that target has been removed.
- `Audit.lean` imports every production module and explicitly audits 113 exported source-level theorems using `Lean.collectAxioms`. It verifies list synchronization and exits nonzero on forbidden dependencies. All detector theorems, `powCoeff_bound_of_uniform_detector_and_factorization`, `halasz_montgomery_lemma_of_mean_value`, and the five generic Type II deductions pass. Removing the Type II axiom and its wrapper reduced the current audit from 18 to 17 failing theorems, all through other project-specific axioms rather than `sorryAx`.
- The README and paper now describe the failing audit honestly; their broader mathematical claims still require continued synchronization as the remaining Shitlist items are repaired.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: formal statement and infrastructure layer | **Partially achieved.** The default root and explicit dependency audit cover every production module and all 113 exported source-level theorems. The exact detector formula, support, smoothing facts, and fixed-`T` magnitude estimate are proved. The powered-coefficient estimate, mean-value large-count consequence, and generic residual-zero bound are conditionally proved from source-faithful inputs. Residual zeros and contour Type II zeros now have distinct interfaces; the complete concrete zero-count interface remains incomplete. |
| Goal B: conditional zero-density transfer | **Not achieved.** The desired conclusion is presently assumed through `algebraic_combination_unconditional`. |
| Goal C: discharge auxiliary classical hypotheses | **Not achieved.** The Type-I/Type-II cover, local zero count, Type II contour/fourth-moment reduction, twisted fourth moment, smoothing, and related inputs remain unproved or axiomatic. The mean-value theorem, Type II inputs, and detector/factorization uniform bounds are explicit proposition inputs rather than project axioms, but are not yet proved. |
| Goal D: prove the Guth–Maynard large-values theorem | **Not achieved.** The decoupling and large-values modules now compile, but decoupling remains axiomatic and `LargeValues.lean` contains no proof of the target. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** Some finite-sum, separation, asymptotic, and polynomial lemmas may become reusable after their interfaces stabilize. |

## Next Steps

1. Pull forward Mathlib's compact-set zeta-zero finiteness theorem and remove `riemannZeta_finite_zeros_in_rect` as a project axiom.
2. Correct Shitlist #13's target quantifiers, sufficiently-large-`T` condition, admissible dyadic-scale model, multiplicity handling, and shifted interval.
3. Prove weighted separated selection and exact finite dyadic pigeonholing, then assemble the conditional extraction theorem from explicit `LocalZeroMultiplicityBoundProp` and `DetectorBetaShiftProp` inputs.
4. Prove `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp`, then instantiate the audit-clean generic Type II deduction after the concrete zero-set interface is valid.
5. Prove the source-faithful `MontgomeryMeanValue` proposition, then instantiate the kernel-checked conditional large-value counting theorem.
6. Prove `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` from classical divisor estimates, then instantiate the conditional powered-coefficient theorem.
7. Complete the equality between the structural power `powPoly` and its explicit convolution-coefficient expansion.
8. Resolve the audit's 17 currently reported theorem-dependency failures one ranked proof obligation at a time; recount after #13 rather than projecting an exact reduction.
9. Keep the root import graph and explicit audit list synchronized as modules and public theorems change.
10. Refactor `conditionalZeroDensityTransfer` to accept the individually named Goal B hypotheses and implement the real F-01 through F-10 deduction. Remove `algebraic_combination_unconditional`.
11. Synchronize the README and paper with the audited Lean status after each verified increment.

## Defensible Current Claim

The repository contains a partially verified Lean infrastructure package for a future Guth–Maynard formalization, including genuine results about the exact truncated Möbius detector, a kernel-checked conditional powered-coefficient estimate from explicit uniform arithmetic inputs, a kernel-checked large-value count from an explicit discrete mean-value input, and a kernel-checked generic residual-zero bound from explicit Type-I/contour-Type-II coverage, contour-reduction, and twisted-fourth-moment inputs. Residual zeros are now correctly separated from the source's contour-integral Type II class. The three Type II analytic propositions, mean-value proposition, two arithmetic inputs, concrete zeta-zero instantiation, Section 13.1 zero-density transfer, its other main analytic inputs, and the Guth–Maynard large-values theorem remain unproved.
