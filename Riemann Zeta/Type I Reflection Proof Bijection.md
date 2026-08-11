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
| Remove the noncritical Poisson modes | Uniformly bound the zero, wrong-sign, and frequencies beyond the `T^ε T/Q` window below the witness threshold, while retaining the exact tail-boundary weight | `typeIReflectionFourier_fixed_decay` and `typeIReflectionFourier_summable` prove arbitrary-order decay and absolute convergence for every fixed source block; the required constant is not yet uniform in `Y,A,r,σ,t` | **Open at the parameter-uniform estimate** |
| Write the reflected amplitude | The source factor `psi(c/m) (c/m)^(1-sigma)` in logarithmic coordinates, with corrected `c` from the stationary point | `typeIReflectedLogWeight`, `typeIReflectedLogWeight_log_nat` | Kernel-checked |
| Prove the reflected amplitude is admissible for Fourier removal | Smoothness, compact support, and a Schwartz realization | `contDiff_typeIReflectedLogWeight`, `hasCompactSupport_typeIReflectedLogWeight`, `typeIReflectedLogWeightSchwartz` | Kernel-checked |
| Fourier-deweight the reflected block | Exact integral of coefficient-one shifted dual polynomials | `typeIReflectedBlock_fourierDeweight` | Kernel-checked |
| Preserve separation after ordinate shifts | Discretize the Mellin variable, select a common shift bin, and bound the discarded cardinality | Existing generic shifted-family machinery can be reused after the noncritical remainder theorem produces the complete reflected block | Downstream in `ZR`, not part of the three interfaces |

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

The medium interface is nevertheless not complete until Lean controls the
parts of the complete source Poisson series not covered by that retained-mode
identity:

1. keep the complete `typeITailBoundary`, or prove its two transition pieces
   separately negligible;
2. split off the zero and wrong-sign Fourier modes;
3. prove a uniform summable tail beyond `M ≍ T^ε T/Q` using repeated
   integration by parts or Schwartz Fourier decay; and
4. show the aggregate discarded contribution is below a fixed fraction of
   the selected Type-I witness threshold.

The exact Mellin factorization removes the former Fresnel/Gaussian
obstruction. The remaining obstruction is narrower and explicit: a
source-weighted, scale-uniform nonstationary Fourier-tail theorem. PNT+'s
public `nonstationary_phase_integral_bound` and
`nonstationary_power_phase_expansion` cover sharp monotone power amplitudes;
they do not directly cover the compact smooth product used here. Mathlib's
Schwartz derivative/Fourier estimates provide the correct lower-level route,
but the required uniform derivative and summed-tail specialization is not yet
present.

## Dependency result

The corrected dependency chain is

`Type-I witness -> smooth common block -> {short deweighting | medium Poisson}
-> exact Mellin B-process -> noncritical-tail removal -> short dual polynomial
-> Type-I range resolution`.

Thus smoothing is genuinely complete, shared deweighting is genuinely
complete on both concrete amplitudes, and the retained critical-mode B-process
is exact. The only open edge among the three named interfaces is the
full-source boundary/wrong-sign/far-frequency remainder estimate inside the
medium B-process.
