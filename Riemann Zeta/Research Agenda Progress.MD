# Research Agenda Progress

**Audit date:** 8 August 2026  
**Goal:** Formalize the conditional Guth–Maynard zero-density transfer from explicit hypotheses, progressively discharge the classical analytic inputs, and ultimately prove the Guth–Maynard large-values estimate in Lean 4.

## Current Status: Infrastructure Partially Verified; Main Transfer and Analytic Proofs Pending

The project contains a useful collection of kernel-checked elementary lemmas, formal target statements, and provisional interfaces for the Guth–Maynard program. It does **not** yet contain a verified formalization of the Section 13.1 zero-density transfer.

The default `lake build` target currently succeeds with warnings. In particular, Lean reports that `powCoeffBound_native` uses `sorry`. Three substantive files—`HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean`—are not imported by the default root module; direct builds of the first two currently fail, and `LargeValues.lean` imports the failing decoupling module.

The non-test Guth–Maynard source contains 28 direct `axiom` declarations, 24 of which occur in modules reachable from the default `RiemannZeta` root import. A theorem is therefore counted as proved below only when its audited dependencies contain no project-specific axiom and no `sorryAx`.

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
9. **Elementary smoothing and cutoff facts:** `exp_smoothing_bound`, cutoff nonnegativity, cutoff support boundary lemmas, and the upper bounds `psiCutoff_le_exp` and `psiCutoff_bounded_of_sigma_le_beta`.
10. **Elementary complex-exponential facts:** `cexp_periodic_1`, `cexp_zero_eval`, and the norm reduction `fourier_inversion_integrand_bound`. These do not constitute Fourier inversion or Fourier decay.
11. **Finite-sum inequalities:** `sum_sq_le_card_mul_sum_sq`, `complex_sum_sq_le_card_mul_sum_sq`, and the elementary nonnegativity/zero lemmas for finite L2 sums.
12. **Basic zero-rectangle set reasoning:** Rectangle membership and inclusion lemmas. Results involving `zerosInRect` or `zeroCountRect` additionally depend on the provisional axiom `riemannZeta_finite_zeros_in_rect` and are not unconditional zeta-zero-counting theorems.
13. **Type-I/Type-II partition identity:** `typeI_add_typeII_eq_total` is a finite-set filtering identity, conditional on the provisional zero-set construction.
14. **Powered-polynomial definitional identity:** `powPoly_eval` and `polynomial_power_identity` follow from the definition `powPoly := detectPoly ^ k`. An expansion into convolution coefficients has not been completed.
15. **Special divisor-bound case:** `k_divisor_function_bound_one` proves only the stated `m = 1` boundary case. The general `k_divisor_function_bound` remains an axiom.
16. **Combined exponent implication:** `combined_zero_density_transfer_native` is an axiom-free proof that assumed Ingham and Guth–Maynard zero-density bounds imply the combined exponent. It is a conditional implication and does not prove either analytic premise or instantiate the result for the project's zeta zero count. The previously unused Huxley premise has been removed from the statement.

## Provisional or Model-Only Results

Some declarations compile and have axiom-free proofs only because their underlying definitions are simplified models rather than the objects required by the research agenda.

- `mobius_sum n T` is currently defined to be the constant `1`, not the truncated Möbius sum specified by Section 13.1. Consequently, `mobius_sum_bound` and `detector_coeff_bound_native` prove bounds for this toy coefficient model, not for the intended zero detector.
- `jensens_inequality_disk` and `zeta_abs_convergent_at_2` currently have conclusion `True`; they record no substantive analytic result.
- Several positivity lemmas verify only that the proposed right-hand side of a future estimate is nonnegative. They do not establish the corresponding mean-value, decoupling, zero-count, or detector estimate.

## Unproved Results and Explicit Dependencies

### Main transfer gap

The declaration `conditionalZeroDensityTransfer` is **not** currently a proof from the explicit Guth–Maynard large-values, Type II, local-zero-count, and mean-value hypotheses.

`AlgebraicCombinationProp` is definitionally the desired conclusion
`GuthMaynardZeroDensity (fun σ T => N σ T)`, and `algebraic_combination_unconditional` assumes that proposition directly. `conditionalZeroDensityTransfer` then returns this axiom. This is equivalent to assuming the target and does not meet Goal B or the agenda's assumption-audit gate.

The Section 13.1 proof still needs to implement the following chain explicitly:

1. dyadic reduction of the global zero count;
2. the actual truncated Möbius zero detector;
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
- `k_divisor_function_bound`;
- `bourgain_guth_broad_narrow_decomposition`, `l2_parabola_incidence_bound`, and `l2_decoupling_bound_unconditional`; and
- `algebraic_combination_unconditional`, which is equivalent to the desired zero-density conclusion and must be removed rather than treated as an acceptable analytic hypothesis.

### Outstanding `sorryAx`

`powCoeffBound_native` contains two `sorry` terms in `PolynomialPowers.lean`. Its axiom audit includes both `sorryAx` and `k_divisor_function_bound`. Although it no longer calls the standalone axiom `powCoeffBound_unconditional`, the coefficient theorem has **not** been discharged unconditionally.

## Build and Audit Status

- The default `lake build` completes successfully but emits warnings, including `declaration uses 'sorry'` for `powCoeffBound_native`.
- Direct compilation of `HalaszMontgomery.lean` currently fails in the proof of `halasz_montgomery_lemma_native`.
- Direct compilation of `Decoupling.lean` currently fails with syntax, typeclass, and missing-import/type errors.
- `LargeValues.lean` is outside the default import graph, imports `Decoupling.lean`, and presently declares only a variable assuming `GuthMaynardLargeValues`; it does not prove the large-values theorem.
- `Audit.lean` does not execute `#print axioms`. It categorizes declarations by name suffix and by `cinfo.isTheorem`, so it cannot establish the claimed absence of `sorryAx` or project axioms.
- The README and paper currently contain stronger build and proof-status claims than the source supports and should be synchronized in a later documentation pass.

## Research-Agenda Milestones

| Milestone | Current assessment |
|---|---|
| Goal A: formal statement and infrastructure layer | **Partially achieved.** Several useful definitions and statements compile, but the exact detector, source-fidelity audit, complete zero-count interface, and full build/audit coverage remain incomplete. |
| Goal B: conditional zero-density transfer | **Not achieved.** The desired conclusion is presently assumed through `algebraic_combination_unconditional`. |
| Goal C: discharge auxiliary classical hypotheses | **Not achieved.** The local zero count, Type II estimate, mean-value theorem, smoothing, divisor bound, and related inputs remain axiomatic. |
| Goal D: prove the Guth–Maynard large-values theorem | **Not achieved.** The relevant decoupling module does not compile, and `LargeValues.lean` assumes rather than proves the target. |
| Goal E: reusable analytic-number-theory library | **Early infrastructure only.** Some finite-sum, separation, asymptotic, and polynomial lemmas may become reusable after their interfaces stabilize. |

## Next Steps

1. Remove the two `sorry`s from `powCoeffBound_native` and audit its remaining dependence on the general divisor bound.
2. Replace the constant `mobius_sum` model with the actual truncated Möbius coefficients and prove their support and size properties.
3. Repair and import `HalaszMontgomery.lean` and `Decoupling.lean` so the default build covers every intended production module.
4. Replace `Audit.lean` with an explicit declaration list and `#print axioms` checks, including all agenda-critical theorems and all non-root production modules.
5. Refactor `conditionalZeroDensityTransfer` to accept the individually named Goal B hypotheses and implement the real F-01 through F-10 deduction. Remove `algebraic_combination_unconditional`.
6. Discharge the remaining hypotheses one at a time, beginning with the smallest precise combinatorial or Mathlib-bridge obligation.
7. Synchronize the README and paper with the audited Lean status after each verified increment.

## Defensible Current Claim

The repository contains a partially verified Lean infrastructure package for a future Guth–Maynard formalization, including genuine elementary results about finite Dirichlet polynomials, separated finite sets, exponent arithmetic, finite-sum inequalities, and conditional exponent combination. The Section 13.1 zero-density transfer, its main analytic inputs, and the Guth–Maynard large-values theorem remain unproved.
