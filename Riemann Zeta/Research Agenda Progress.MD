# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Infrastructure Partially Verified; Main Transfer and Analytic Proofs Pending

The project contains a useful collection of kernel-checked elementary lemmas, formal target statements, and provisional interfaces for the Guth–Maynard program. It does **not** yet contain a verified formalization of the Section 13.1 zero-density transfer.

The default `lake build` target imports and compiles every intended production module with zero Lean warnings. Warning-free compilation does not make the unresolved project-axiom dependencies valid.

The non-test Guth–Maynard source contains 25 direct `axiom` declarations, all of which occur in modules reachable from the default `RiemannZeta` root import. A theorem is therefore counted as proved below only when its audited dependencies contain no project-specific axiom and no `sorryAx`.

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
14. **Type-I/Type-II partition identity:** `typeI_add_typeII_eq_total` is a finite-set filtering identity, conditional on the provisional zero-set construction.
15. **Powered-polynomial definitional identity:** `powPoly_eval` and `polynomial_power_identity` follow from the definition `powPoly := detectPoly ^ k`. An expansion into convolution coefficients has not been completed.
16. **Conditional powered-coefficient bound:** `powCoeff_bound_of_uniform_detector_and_factorization` proves the full `PowCoeffBoundProp` conclusion from the separately stated, narrower `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` inputs. Its finite-product and convolution-sum proof is kernel-checked. The classical inputs themselves remain unproved specifications; `k_divisor_function_bound_one` proves only its stated `m = 1` boundary case.
17. **Combined exponent implication:** `combined_zero_density_transfer_native` is an axiom-free proof that assumed Ingham and Guth–Maynard zero-density bounds imply the combined exponent. It is a conditional implication and does not prove either analytic premise or instantiate the result for the project's zeta zero count. The previously unused Huxley premise has been removed from the statement.

## Provisional or Model-Only Results

Some declarations remain provisional specifications rather than proved results.

- `DetectorCoeffBoundProp` is proved with the quantifier order currently encoded in Lean: its constant is uniform in positive `n` but may depend on the already-fixed `T`. The stronger `UniformDetectorCoeffBoundProp` and the source-faithful, `m`-uniform `FactorizationCountBoundProp` are explicit unproved inputs to the conditional powered-coefficient theorem.
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
3. the Type-I/Type-II estimates;
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
- `montgomery_mean_value_unconditional`;
- `typeII_bound_unconditional`;
- `fourier_inversion_unconditional` and `fourier_decay_unconditional`;
- `cauchy_residue_dirichlet_polynomial`, `contour_shift_to_real_line`, `fourier_decay_error_bound`, and `pigeonhole_integral_bound`;
- `type_I_zeros_dyadic_sum_bound` and `dyadic_pigeonhole_lemma`;
- `vitali_covering_lemma_1D`, `extract_1_separated_subset`, and `extract_separated_lemma`;
- the proposition specifications `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp`, which replace the former module-level divisor axiom as explicit inputs rather than asserted facts;
- `l2_parabola_incidence_bound` and `l2_decoupling_bound_unconditional`; and
- `algebraic_combination_unconditional`, which is equivalent to the desired zero-density conclusion and must be removed rather than treated as an acceptable analytic hypothesis.

### Admitted-proof status

No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency. The former `powCoeffBound_native`, `powCoeffBound_unconditional`, and `k_divisor_function_bound` declarations are removed. `PowCoeffBoundProp` is now conditionally proved by `powCoeff_bound_of_uniform_detector_and_factorization`; this does not prove its two explicit classical arithmetic inputs.

## Build and Audit Status

- The default `lake build` completes successfully with zero Lean warnings.
- Direct builds of `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` succeed with zero Lean warnings. This does not prove their remaining analytic axioms or proposition specifications.
- `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` are now in the default import graph. `LargeValues.lean` still contains no proof of `GuthMaynardLargeValues`; the former dangling variable that assumed that target has been removed.
- `Audit.lean` imports every production module and explicitly audits 110 exported source-level theorems using `Lean.collectAxioms`. It verifies list synchronization and exits nonzero on forbidden dependencies. All detector theorems and `powCoeff_bound_of_uniform_detector_and_factorization` pass. Removing the divisor axiom reduced the current audit from 21 to 20 failing theorems, all through other project-specific axioms rather than `sorryAx`.
- The README and paper now describe the failing audit honestly; their broader mathematical claims still require continued synchronization as the remaining Shitlist items are repaired.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: formal statement and infrastructure layer | **Partially achieved.** The default root and explicit dependency audit cover every production module and all 110 exported source-level theorems. The exact detector formula, support, smoothing facts, and fixed-`T` magnitude estimate are proved. The powered-coefficient estimate is conditionally proved from source-faithful uniform arithmetic inputs; the complete zero-count interface remains incomplete. |
| Goal B: conditional zero-density transfer | **Not achieved.** The desired conclusion is presently assumed through `algebraic_combination_unconditional`. |
| Goal C: discharge auxiliary classical hypotheses | **Not achieved.** The local zero count, Type II estimate, mean-value theorem, smoothing, and related inputs remain axiomatic. The detector/factorization uniform bounds are now explicit proposition inputs rather than project axioms, but are not yet proved. |
| Goal D: prove the Guth–Maynard large-values theorem | **Not achieved.** The decoupling and large-values modules now compile, but decoupling remains axiomatic and `LargeValues.lean` contains no proof of the target. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** Some finite-sum, separation, asymptotic, and polynomial lemmas may become reusable after their interfaces stabilize. |

## Next Steps

1. Remove the Montgomery mean-value axiom by proving the stated theorem or exposing only a precise, legitimate conditional interface.
2. Prove `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` from classical divisor estimates, then instantiate the conditional powered-coefficient theorem.
3. Complete the equality between the structural power `powPoly` and its explicit convolution-coefficient expansion.
4. Resolve the audit's 20 reported theorem-dependency failures one ranked proof obligation at a time.
5. Keep the root import graph and explicit audit list synchronized as modules and public theorems change.
6. Refactor `conditionalZeroDensityTransfer` to accept the individually named Goal B hypotheses and implement the real F-01 through F-10 deduction. Remove `algebraic_combination_unconditional`.
7. Synchronize the README and paper with the audited Lean status after each verified increment.

## Defensible Current Claim

The repository contains a partially verified Lean infrastructure package for a future Guth–Maynard formalization, including genuine results about the exact truncated Möbius detector, a kernel-checked conditional powered-coefficient estimate from explicit uniform arithmetic inputs, finite Dirichlet polynomials, separated finite sets, exponent arithmetic, finite-sum inequalities, and conditional exponent combination. The two arithmetic inputs, the Section 13.1 zero-density transfer, its main analytic inputs, and the Guth–Maynard large-values theorem remain unproved.
