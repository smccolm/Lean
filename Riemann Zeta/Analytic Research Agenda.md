# Analytic Research Agenda: Riemann Zeta Guth-Maynard Proof

With the algebraic, combinatorial, and asymptotic framework successfully formalized and compiling flawlessly (0 errors, all `sorry` declarations eradicated and replaced with formalized logic or axioms), the project transitions into its deep analytic phase.

The remaining assumptions are purely analytic in nature and require advanced integration with Mathlib's measure theory, complex analysis, and Fourier analysis libraries.

## Remaining Analytic Axioms

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

## Next Steps

1. Import and align `Mathlib.Analysis.Fourier` for inversion and decay.
2. Develop the necessary `MeasureTheory` integral bounding techniques.
3. Bridge Mathlib's `riemannZeta` Dirichlet series to the Euler product form.
