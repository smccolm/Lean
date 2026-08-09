# Analytic Research Agenda: Riemann Zeta Guth-Maynard Proof

The project has a warning-free compiling algebraic, combinatorial, asymptotic, and initial classical-density infrastructure layer. Beta removal, local zero multiplicity, Montgomery mean value, the finite Möbius mollifier algebra, the pole-free Ingham detector, and the detector-to-Jensen divisor bridge are proved. Two direct project axioms and several unproved proposition specifications remain; the next work is the interior classical-density, arithmetic, Type-II, and large-values phase.

The remaining assumptions include both analytic and arithmetic inputs and require advanced integration with Mathlib's measure theory, complex analysis, Fourier analysis, and multiplicative number theory libraries.

## Remaining Analytic Obligations

### 1. Decoupling
- `l2_decoupling_bound_unconditional`: remains an unproved final decoupling postulate. The earlier unused broad–narrow postulate was removed; `l2_parabola_incidence_bound` remains as an unproved geometric incidence input.

### 2. Complex Analysis & Zero Counting
- `LocalZeroMultiplicityBoundProp` is complete: `localZeroMultiplicityBound_native` proves the uniform multiplicity-weighted `O(log T)` estimate for ordinary unshifted unit-height intervals of Type-I zeta zeros using Mathlib's Jensen framework.
- Compact-rectangle zeta-zero finiteness is complete: `riemannZeta_finite_zeros_in_rect` is derived from Mathlib's `IsCompact.inter_riemannZetaZeros_finite`.

### 3. Analytic Number Theory & Integration
- `DetectorBetaShiftProp` is complete: `beta_dependence_removal` moves each Type-I zero ordinate by at most `T^δ` while preserving the required large detector value on the fixed line. The proof uses rational Phragmén–Lindelöf localization rather than the originally proposed Fourier cutoff.
- Type-I separated extraction is unconditional: `extractSeparated_native` combines the beta theorem and native Jensen bound with `shifted_bin_weight_le_of_unit_bin_weight`, the raw enlarged-interval theorem, translation to `[0,3T]`, coefficient phase twisting, and epsilon-loss absorption.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp`: the two explicit classical multiplicative-number-theory inputs for `powCoeff_bound_of_divisor_and_factorization`. The source-uniform `UniformDetectorCoeffBoundProp` is derived from `DivisorCountBoundProp`, and the exact finite `powPoly`/`powCoeff` expansion is kernel-checked independently; the two classical growth inputs themselves remain to be proved.
- `euler_product_lower_bound_2` is complete and supplies the concrete lower bound on the $\Re(s)=2$ line.
- `MontgomeryMeanValue` is complete via `montgomery_mean_value_native`; `halasz_montgomery_lemma_native` supplies the downstream finite large-value count without an analytic premise.
- `ClassicalDensity.lean` now proves the exact finite Möbius convolution and cancellation, global analyticity of a pole-free Ingham detector, zeta-zero multiplicity inheritance, a general detector/Jensen divisor inequality, full unit-bin control down to `σ = 1/2`, dyadic `O(T log T)`, its symmetric exponent-one consequence, Ingham at `σ = 1/2,1`, and Huxley at `σ = 1`.
- Shitlist #15's interior classical density analysis remains open. For Ingham it requires a multiplicity-aware Littlewood rectangle theorem, finite Gabriel vertical-integral convexity, the critical-line zeta fourth moment, and mollifier boundary moments. For Huxley it requires the full classical Montgomery–Halász–Huxley estimate, especially the `T * N^4 * V⁻⁶` branch; the existing basic `halasz_montgomery_lemma_native` does not contain that branch. The remaining assembly must also prove the Huxley `σ = 3/4` boundary and both fully quantified density propositions.
- `TypeIContourTypeIICoverProp`: the source-facing assertion that every relevant zeta zero is Type I or satisfies the Gamma–zeta contour largeness condition `IsContourTypeIIZero`. Residual zeros are now represented separately as the complement of Type I.
- `TypeIIFourthMomentReductionProp`: the Appendix C reduction bounding a generic weighted count of contour Type II zeros by `T^(1-2σ)` times the twisted fourth moment. Its proof must supply Gamma decay/truncation, Hölder, separated extraction, and local multiplicity control.
- `TwistedZetaFourthMomentProp`: the epsilon-power bound of order `T` for the fourth moment of the short Möbius polynomial times `riemannZeta` over `[T/2, 3T]`.

The former `typeII_bound_unconditional` and its misleading Halász–Montgomery wrapper have been removed. `residual_zero_bound_of_cover_reduction_and_fourth_moment` proves the generic residual-zero estimate from the three explicit inputs above. `finiteTypeICover_of_typeIContourTypeII` now converts the eventual source coverage to the concrete dyadic finite zeta family, and `residualZeroBound_of_contourTypeII_reduction_and_fourthMoment` proves the project's concrete `ResidualZeroBoundProp` conditionally. The coverage theorem, Appendix C reduction, and twisted fourth moment themselves remain unproved; local multiplicity and separated extraction must be supplied inside the reduction proof rather than hidden in the concrete bridge.

## Next Steps

1. Complete #15 in two ordered parts: first prove the Littlewood/Gabriel/fourth-moment/mollifier engine and the full classical Montgomery–Halász–Huxley large-values estimate; then assemble the Ingham and Huxley exponents and transfer both to the project's symmetric multiplicity-weighted count.
2. Prove `DivisorCountBoundProp` and `FactorizationCountBoundProp`.
3. Prove the Type-I/Type-II cover, contour reduction, and twisted fourth-moment propositions, then instantiate the generic residual-zero theorem for zeta zeros.
4. Repair and prove the decoupling/incidence interfaces, then prove `GuthMaynardLargeValues` and complete final integration.
