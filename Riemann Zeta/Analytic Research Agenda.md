# Analytic Research Agenda: Riemann Zeta Guth-Maynard Proof

The project has a warning-free compiling algebraic, combinatorial, and asymptotic infrastructure layer, but substantial project axioms and unproved proposition specifications remain. The next work is the deep analytic phase.

The remaining assumptions are purely analytic in nature and require advanced integration with Mathlib's measure theory, complex analysis, and Fourier analysis libraries.

## Remaining Analytic Obligations

### 1. Fourier Analysis & Decoupling
- `l2_decoupling_bound_unconditional`: remains an unproved final decoupling postulate. The earlier unused broad–narrow postulate was removed; `l2_parabola_incidence_bound` remains as an unproved geometric incidence input.
- `fourier_inversion_unconditional`: Decomposed into `smooth_compact_is_schwartz` (embedding compactly supported smooth functions into the Schwartz space) and `schwartz_fourier_inversion` (the actual Fourier inversion for Schwartz functions).
- `fourier_decay_unconditional`: Upgraded to `SchwartzFourierDecayProp` forcing rapid decay bounded by any polynomial degree for Schwartz functions.

### 2. Complex Analysis & Zero Counting
- `jensens_inequality_disk_zero_count`: Counting zeros of analytic functions in a disk using Jensen's Formula.
- `phragmen_lindelof_convexity`: The Phragmén-Lindelöf principle for bounding analytic functions in vertical strips (convexity bound).
- `riemannZeta_finite_zeros_in_rect`: Proof that the Riemann Zeta function is not identically zero and thus has finitely many zeros in any compact rectangular region.

### 3. Analytic Number Theory & Integration
- `detector_fixed_line_integral_unconditional`: Decomposed into `cauchy_residue_dirichlet_polynomial` (expressing the Dirichlet polynomial as a contour integral) and `contour_shift_to_real_line` (shifting the integral to the fixed line).
- `fixed_line_coefficient_bounds_unconditional`: Decomposed into `fourier_decay_error_bound` (bounding the Fourier truncation error) and `pigeonhole_integral_bound` (using the pigeonhole principle to extract a large polynomial value).
- `extract_separated_lemma`: Decomposed into the purely combinatorial extraction `extract_1_separated_subset`, which itself is reduced to the foundational 1D finite Vitali covering lemma (`vitali_covering_lemma_1D`).
- `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp`: the two source-faithful multiplicative-number-theory inputs for the conditional powered-coefficient theorem. The former `k_divisor_function_bound` module axiom has been removed; these proposition specifications remain to be proved from classical divisor estimates.
- `euler_product_lower_bound_2`: Bounding $|\zeta(s)|$ from below on the $\Re(s)=2$ line using the Euler product formulation.
- `MontgomeryMeanValue`: the discrete Dirichlet-polynomial mean-value theorem needed in Section 13.1, stated with one absolute implied constant. It is now an explicit proposition input rather than a project axiom; `halasz_montgomery_lemma_of_mean_value` proves the downstream finite large-value count from it.
- `TypeIContourTypeIICoverProp`: the source-facing assertion that every relevant zeta zero is Type I or satisfies the Gamma–zeta contour largeness condition `IsContourTypeIIZero`. Residual zeros are now represented separately as the complement of Type I.
- `TypeIIFourthMomentReductionProp`: the Appendix C reduction bounding a generic weighted count of contour Type II zeros by `T^(1-2σ)` times the twisted fourth moment. Its proof must supply Gamma decay/truncation, Hölder, separated extraction, and local multiplicity control.
- `TwistedZetaFourthMomentProp`: the epsilon-power bound of order `T` for the fourth moment of the short Möbius polynomial times `riemannZeta` over `[T/2, 3T]`.

The former `typeII_bound_unconditional` and its misleading Halász–Montgomery wrapper have been removed. `residual_zero_bound_of_cover_reduction_and_fourth_moment` now proves the final generic residual-zero estimate from the three explicit inputs above without using the provisional zeta-zero finiteness axiom. A concrete zeta-zero instantiation remains dependent on the extraction/multiplicity and zero-set work.

## Next Steps

1. Import and align `Mathlib.Analysis.Fourier` for inversion and decay.
2. Develop the necessary `MeasureTheory` integral bounding techniques.
3. Bridge Mathlib's `riemannZeta` Dirichlet series to the Euler product form.
4. Complete the finite separated-set and local multiplicity layer needed by `TypeIIFourthMomentReductionProp`.
5. Prove the Type-I/Type-II cover, contour reduction, and twisted fourth-moment propositions, then instantiate the generic residual-zero theorem for zeta zeros.
6. Prove `MontgomeryMeanValue` using a source-faithful large-sieve or mean-value argument for separated ordinates.
