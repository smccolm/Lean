# Type-I Reflection: Human Proof to Lean Bijection

## Scope

This document is the line-by-line correspondence between the medium Type-I
argument in ANTEDB Lemma 11.5 and the repository's Lean implementation.  A
row marked **kernel-checked** has a theorem in the production import graph and
the transitive dependency audit.  A row marked **open** is not supplied by a
definition, a hypothesis, or a weaker phase calculation.

The source passage is [ANTEDB Lemma 11.5](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html#zero-density-from-large-values),
especially the Type-I discussion following equation (3). Mathlib supplies
the smooth-transition, Schwartz, Fourier-inversion, Mellin-inversion, and
Poisson-summation layers. The pinned PNT+ code supplies a sharp partial-zeta
Poisson identity and nonstationary phase estimates. Broad searches of
Mathlib, PNT+, the Carleson formalization, ANTEDB, and public Lean repositories
found no reusable Lean theorem giving the required uniform one-dimensional
stationary-phase main term. The implemented route therefore avoids that
unavailable black box: exact Mellin inversion factors all retained modes into
one common logarithmic reflection integral and one finite polynomial.

## Normalization correction

With Mathlib's Fourier convention, the negative mode has phase

`phi(x) = m*x - t/(2*pi)*log(x)`.

Consequently `phi'(x) = m - t/(2*pi*x)` and the stationary point is
`x0 = t/(2*pi*m)`.  For a source cutoff `psi(x/N)`, its stationary value is
therefore `psi(t/(2*pi*m*N))`.

The displayed ANTEDB formula writes `psi(2*pi*t/(m*N))`.  That cutoff argument
is incompatible with the derivative of the phase displayed in the same
formula, differing by a factor of `(2*pi)^2`.  The Lean code fixes the
normalization from the Fourier transform itself:

- `typeIReflectionFourier_neg_eq_stationaryIntegral` proves the exact phase;
- `deriv_reflectionPhase` proves its derivative;
- `deriv_reflectionPhase_stationary` proves the critical point; and
- `typeIReflection_stationary_window` proves the resulting dual-frequency
  interval.

No later theorem is permitted to reinsert the inconsistent factor.

## Exact proof correspondence

| Human analytic step | Mathematical content that must survive formalization | Lean object or theorem | Status |
|---|---|---|---|
| Start from the Type-I tail | The actual finite tail `(Y,A]`, with coefficient `n^(-sigma-it)` | `classicalZetaLongTail` | Kernel-checked |
| “Perform a smooth partition of unity” | A fixed smooth cutoff, independent of the ordinate, supported on one multiplicative annulus | `typeISmoothStep`, `typeIDyadicCutoff`, `contDiff_typeIDyadicCutoff`, the support lemmas | Kernel-checked |
| Remove the two sharp analytic edges | A globally smooth compactly supported interpolation which agrees exactly with the tail at every integer | `typeITailBoundary`, `typeITailBoundary_natCast`, `typeISourceSmoothWeight` | Kernel-checked |
| Sum the dyadic partition | Exact equality, not an asymptotic or a positivity argument | `sum_typeIDyadicCutoff_eq`, `sum_typeIDyadicCutoff_eq_one`, `classicalZetaLongTail_eq_sum_sourceSmoothBlocks` | Kernel-checked |
| Select one common block | One scale for a whole separated finite family, with the precise cardinality loss | `exists_typeISmoothBlock_large`, `exists_common_typeISmoothBlock_large` | Kernel-checked |
| Split short and medium scales | Exhaustive arithmetic alternative after the terminal estimate | `typeISmoothScaleSplit_native` together with the common block theorem | Kernel-checked |
| Short-block Fourier expansion in `log n` | Exact Fourier inversion, integrability, finite sum/integral exchange, and literal coefficient-one shifted polynomials | `fourierDeweightFiniteBlock_native`, `typeISourceSmoothBlock_fourierDeweight` | Kernel-checked |
| Apply Poisson summation to a medium block | The actual globally smooth Type-I kernel, not a sharp partial sum | `typeIReflectionKernel`, `typeIReflectionSchwartz`, `typeIReflection_poisson` | Kernel-checked |
| Identify signed modes | Negative Fourier modes have the logarithmic stationary phase; the source sum at positive integers is unchanged | `typeIReflectionKernel_natCast`, `typeIReflectionFourier_neg_eq_stationaryIntegral` | Kernel-checked |
| Locate the dual scale | The critical modes have `m` comparable to `t/(2^r Y)` | `typeIReflection_stationary_window` | Kernel-checked |
| Normalize the stationary phase | Exact phase value, rescaling to `z - 1 - log z`, curvature, sign, and quadratic control | the `reflectionPhase_*` and `stationaryNormalPhase_*` theorem families in `MediumReflection.lean` | Kernel-checked |
| Insert the actual dyadic cutoff by Mellin inversion | Exact pointwise Mellin inversion on `Re s = 1`, with Schwartz decay and the Fubini hypotheses proved | `typeIDyadicCutoff_eq_verticalMellinIntegral`, `integrable_typeIMellinReflectionIntegrand` | Kernel-checked |
| Rescale every retained mode | The substitution `v=m*x`, the corrected `mQ` cutoff scale, and one interval `[Q/2,2MQ]` shared by every `1≤m≤M` | `typeIDyadicPhysicalIntegral_rescale`, `typeIDyadicPhysicalIntegral_eq_common_mellinReflection` | Kernel-checked |
| Assemble the critical modes | A literal finite polynomial inside one Mellin integral; no Fresnel limit, pointwise main-term approximation, or stationary-mode error remains | `sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial` | Kernel-checked |
| Remove the artificial source boundary on an interior medium block | Prove that the exact tail boundary is identically one throughout the selected dyadic cutoff support | `typeISourceSmoothWeight_eq_dyadic_of_interior` and `typeIReflectionKernel_eq_dyadicPhysical_of_interior` | Kernel-checked |
| Normalize the full Poisson kernel uniformly | Rescale by the block length and bound every derivative uniformly in the source parameters | `typeINormalizedKernel_uniform_iteratedFDeriv` | Kernel-checked |
| Remove all frequencies outside the finite dual window | Obtain arbitrary-order pointwise Fourier decay and sum both infinite tails with one explicit parameter-uniform constant | `typeINormalizedFourier_uniform_decay`, `typeINormalizedFourier_far_frequency_decay`, and `typeINormalizedFarTail_bound` give the complete bound `K (1+|t|)^102 / (Q^101 M^100)` | Kernel-checked |
| Split exact Poisson into retained modes and the complete tail | Use scaled Poisson, retain the symmetric finite interval `[-M,M]`, and identify its complement exactly with the summed tail | `typeINormalizedKernel_poisson`, `typeINormalizedPoisson_split`, and the public package `mediumTypeIExactBProcess_native` | Kernel-checked |
| Write the reflected amplitude | The source factor `psi(c/m) (c/m)^(1-sigma)` in logarithmic coordinates, with corrected `c` from the stationary point | `typeIReflectedLogWeight`, `typeIReflectedLogWeight_log_nat` | Kernel-checked |
| Prove the reflected amplitude is admissible for Fourier removal | Smoothness, compact support, and a Schwartz realization | `contDiff_typeIReflectedLogWeight`, `hasCompactSupport_typeIReflectedLogWeight`, `typeIReflectedLogWeightSchwartz` | Kernel-checked |
| Fourier-deweight the reflected block | Exact integral of coefficient-one shifted dual polynomials | `typeIReflectedBlock_fourierDeweight` | Kernel-checked |
| Package a generic direct Type-I MHH bound and normalize the actual enlarged interval | Apply coefficient-uniform MHH to an explicitly supplied sharp block, derive `[0,3T]` from `[T-T^δ,2T+T^δ]`, and separately project an endpoint certificate | `typeI_finite_window_resolution_native`, `typeI_dichotomy_witness_mhh_bound_native`, `typeIEndpointScaleDispatch_native`, and the Ingham/Huxley specializations in `TypeIFiniteWindow.lean` | Kernel-checked |
| Resolve the production Type-I branch | Unpack `ClassicalTypeITypeIIDichotomyConclusion`, normalize the ordinate interval, identify `τ` with the actual `N,T` scale, prove the terminal majorant, and dispatch direct/powered/Weyl ranges | `actual_typeI_branch_resolution_native` and the Type-I branch of `classical_endpoint_positive_slab_of_medium_native` | Kernel-checked; `ZR` closed |

## Exact replacement of the stationary-main-term route

The smoothing interface and both Fourier-deweighting applications are
complete. The earlier plan required a uniform Fresnel main term for every
stationary mode. That is no longer necessary. The kernel-checked Mellin route
proves:

1. Mellin convergence and inversion for the literal dyadic cutoff;
2. absolute integrability of the two-variable Mellin/reflection integrand;
3. the exact `v=m*x` rescaling;
4. a mode-independent interval `[Q/2,2MQ]` for all retained modes;
5. a weighted `10/sqrt(tau)` bound for the common reflection integral; and
6. exact finite assembly into `typeIReflectedMellinPolynomial`.

The medium B-process interface is complete. On an interior medium block Lean
proves that `typeITailBoundary` is exactly one on the whole cutoff support, so
there is no endpoint error to estimate. After normalization it proves uniform
bounds for all iterated derivatives, converts those bounds to arbitrary-order
Fourier decay, and sums both tails outside `[-M,M]`. The public theorem
`mediumTypeIExactBProcess_native` combines scaled Poisson summation, the exact
finite central window, and the explicit remainder estimate
`K (1+|t|)^102 / (Q^101 M^100)`.

The zero and wrong-sign frequencies are not discarded or hidden in that
remainder: they remain visible members of the exact finite central window.
The production endpoint chain uses the dichotomy's exact sharp polynomial
with fixed bounded coefficients and the coefficient-uniform MHH theorem.
`actual_typeI_branch_resolution_native` performs the ordinate translation,
physical-to-logarithmic scale relation, terminal majorant, and
direct/powered/Weyl certificate dispatch. The final slab theorem consumes that
package together with the native medium consumer.

## Dependency result

The canonical corrected dependency chain is

`actual sharp Type-I witness -> enlarged-interval normalization -> coefficient-uniform finite MHH -> endpoint
scale dispatch -> branch-to-slab reduction`.

The independent analytic realization remains

`smooth common block -> exact medium B-process -> finite central window plus
summed far tail -> reflected deweighting`.

Smoothing, exact medium reflection, shared deweighting, the generic direct MHH
helper, and interval normalization are complete. The actual Type-I dichotomy
consumer `ZR`, actual-cutoff Type-II application `IIE`, and multiplicity-aware
slab reduction `FR` are also kernel-checked. The remaining #15 obligation is
`ZD`: convert the two proved positive-slab endpoint specializations to the full
symmetric Ingham and Huxley propositions.
