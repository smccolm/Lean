# Analytic Research Agenda: Riemann Zeta Guth-Maynard Proof

The project has a warning-free compiling algebraic, combinatorial, asymptotic, and initial classical-density infrastructure layer. Beta removal, local zero multiplicity, Montgomery mean value, the finite Möbius mollifier algebra, the pole-free Ingham detector, the detector-to-Jensen divisor bridge, divisor-count growth, ordered-factorization growth, and powered detector-coefficient growth are proved. Two direct project axioms and several unproved analytic proposition specifications remain; the next work is the interior classical-density, Type-II, and large-values phase.

The remaining assumptions are analytic inputs requiring advanced integration with Mathlib's measure theory, complex analysis, and Fourier-analysis libraries. The arithmetic coefficient inputs formerly assigned to #17 are complete.

## Remaining Analytic Obligations

### 1. Decoupling
- `l2_decoupling_bound_unconditional`: remains an unproved final decoupling postulate. The earlier unused broad–narrow postulate was removed; `l2_parabola_incidence_bound` remains as an unproved geometric incidence input.

### 2. Complex Analysis & Zero Counting
- `LocalZeroMultiplicityBoundProp` is complete: `localZeroMultiplicityBound_native` proves the uniform multiplicity-weighted `O(log T)` estimate for ordinary unshifted unit-height intervals of Type-I zeta zeros using Mathlib's Jensen framework.
- Compact-rectangle zeta-zero finiteness is complete: `riemannZeta_finite_zeros_in_rect` is derived from Mathlib's `IsCompact.inter_riemannZetaZeros_finite`.

### 3. Analytic Number Theory & Integration
- `DetectorBetaShiftProp` is complete: `beta_dependence_removal` moves each Type-I zero ordinate by at most `T^δ` while preserving the required large detector value on the fixed line. The proof uses rational Phragmén–Lindelöf localization rather than the originally proposed Fourier cutoff.
- Type-I separated extraction is unconditional: `extractSeparated_native` combines the beta theorem and native Jensen bound with `shifted_bin_weight_le_of_unit_bin_weight`, the raw enlarged-interval theorem, translation to `[0,3T]`, coefficient phase twisting, and epsilon-loss absorption.
- `DivisorCountBoundProp` and `FactorizationCountBoundProp` are complete via `divisorCountBound_native` and `factorizationCountBound_native`. The source-uniform `UniformDetectorCoeffBoundProp` follows from the first, the exact finite `powPoly`/`powCoeff` expansion is kernel-checked independently, and `powCoeffBound_native` supplies the unconditional powered-coefficient estimate.
- `euler_product_lower_bound_2` is complete and supplies the concrete lower bound on the $\Re(s)=2$ line.
- `MontgomeryMeanValue` is complete via `montgomery_mean_value_native`; `halasz_montgomery_lemma_native` supplies the downstream finite large-value count without an analytic premise.
- `ClassicalDensity.lean` now proves the exact finite Möbius convolution and cancellation, global analyticity of a pole-free Ingham detector, zeta-zero multiplicity inheritance, a general detector/Jensen divisor inequality, full unit-bin control down to `σ = 1/2`, dyadic `O(T log T)`, its symmetric exponent-one consequence, Ingham at `σ = 1/2,1`, and Huxley at `σ = 1`.
- The unweighted multiplicity-aware rectangle argument principle is complete: the Apache-2.0 PNT+ rectangle/residue development has been ported to Lean 4.30, and `ClassicalArgumentPrinciple.lean` specializes it to the pole-free Ingham detector with finite-order and boundary-nonvanishing hypotheses explicit. The same module proves `‖ζ(s)‖ ≤ 20 |Im(s)|` on the classical strip at height at least one.
- Shitlist #15's interior classical density analysis remains open. For Ingham it still requires the weighted Littlewood logarithmic formula/inequality, a proved boundary-perturbation step, finite Gabriel vertical-integral convexity, the critical-line zeta fourth moment, and mollifier boundary moments. For Huxley it requires the full classical Montgomery–Halász–Huxley estimate, especially the `T * N^4 * V⁻⁶` branch; the existing basic `halasz_montgomery_lemma_native` does not contain that branch. The remaining assembly must also prove the Huxley `σ = 3/4` boundary and both fully quantified density propositions.
- `TypeIContourTypeIICoverProp`: the source-facing assertion that every relevant zeta zero is Type I or satisfies the Gamma–zeta contour largeness condition `IsContourTypeIIZero`. Residual zeros are now represented separately as the complement of Type I.
- `TypeIIFourthMomentReductionProp`: the Appendix C reduction bounding a generic weighted count of contour Type II zeros by `T^(1-2σ)` times the twisted fourth moment. Its proof must supply Gamma decay/truncation, Hölder, separated extraction, and local multiplicity control.
- `TwistedZetaFourthMomentProp`: the epsilon-power bound of order `T` for the fourth moment of the short Möbius polynomial times `riemannZeta` over `[T/2, 3T]`.

The former `typeII_bound_unconditional` and its misleading Halász–Montgomery wrapper have been removed. `residual_zero_bound_of_cover_reduction_and_fourth_moment` proves the generic residual-zero estimate from the three explicit inputs above. `finiteTypeICover_of_typeIContourTypeII` now converts the eventual source coverage to the concrete dyadic finite zeta family, and `residualZeroBound_of_contourTypeII_reduction_and_fourthMoment` proves the project's concrete `ResidualZeroBoundProp` conditionally. The coverage theorem, Appendix C reduction, and twisted fourth moment themselves remain unproved; local multiplicity and separated extraction must be supplied inside the reduction proof rather than hidden in the concrete bridge.

## Next Steps

1. Complete #15 in two ordered parts: extend the proved rectangle argument principle to the weighted Littlewood/boundary-perturbation theorem, then prove Gabriel/fourth-moment/mollifier estimates and the full classical Montgomery–Halász–Huxley large-values estimate; finally assemble the Ingham and Huxley exponents and transfer both to the project's symmetric multiplicity-weighted count.
2. Prove the Type-I/Type-II cover, contour reduction, and twisted fourth-moment propositions, then instantiate the generic residual-zero theorem for zeta zeros.
3. Repair and prove the decoupling/incidence interfaces, then prove `GuthMaynardLargeValues` and complete final integration.
