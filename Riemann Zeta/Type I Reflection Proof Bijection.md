# Type-I Reflection: Human Proof to Lean Bijection

## Scope

This document is the line-by-line correspondence between the medium Type-I
argument in ANTEDB Lemma 11.5 and the repository's Lean implementation.  A
row marked **kernel-checked** has a theorem in the production import graph and
the transitive dependency audit.  A row marked **open** is not supplied by a
definition, a hypothesis, or a weaker phase calculation.

The source passage is [ANTEDB Lemma 11.5](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html#zero-density-from-large-values),
especially the Type-I discussion following equation (3).  Mathlib supplies
the smooth-transition, Schwartz, Fourier-inversion, and Poisson-summation
layers.  The pinned PNT+ code supplies a sharp partial-zeta Poisson identity
and nonstationary phase estimates.  Broad searches of Mathlib, PNT+, the
Carleson formalization, and public Lean repositories found no reusable Lean
theorem giving the required uniform one-dimensional stationary-phase main
term.

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
| Van der Corput B-process main term | Uniformly replace the complete Poisson series by the finite critical-mode sum, with the correct `exp(i*pi/4)/sqrt(phi''(x0))` factor and an error smaller than the selected large-value threshold | No theorem currently supplies this implication | **Open** |
| Write the reflected amplitude | The source factor `psi(c/m) (c/m)^(1-sigma)` in logarithmic coordinates, with corrected `c` from the stationary point | `typeIReflectedLogWeight`, `typeIReflectedLogWeight_log_nat` | Kernel-checked |
| Prove the reflected amplitude is admissible for Fourier removal | Smoothness, compact support, and a Schwartz realization | `contDiff_typeIReflectedLogWeight`, `hasCompactSupport_typeIReflectedLogWeight`, `typeIReflectedLogWeightSchwartz` | Kernel-checked |
| Fourier-deweight the reflected block | Exact integral of coefficient-one shifted dual polynomials | `typeIReflectedBlock_fourierDeweight` | Kernel-checked |
| Preserve separation after ordinate shifts | Discretize the Fourier variable, select a common shift bin, and bound the discarded cardinality | Existing generic shifted-family machinery can be reused only after the open stationary theorem produces the reflected block | Downstream in `ZR`, not part of the three interfaces |

## The sole missing theorem in the three-interface chain

The smoothing interface and both Fourier-deweighting applications are now
complete.  The medium interface is not complete until Lean proves a theorem
of the following mathematical strength for the concrete
`typeIReflectionKernel`:

1. split the Poisson series into zero, wrong-sign, nonstationary, stationary,
   and far-frequency pieces;
2. prove uniform summable bounds for the zero, wrong-sign, and far pieces;
3. evaluate every stationary mode with the leading factor
   `exp(2*pi*I*(phi(x0)+1/8)) / sqrt(phi''(x0))`;
4. sum the stationary errors uniformly over `m` in the dual window;
5. show the total error is below a fixed fraction of the Type-I witness
   threshold; and
6. return the concrete reflected block consumed by
   `typeIReflectedBlock_fourierDeweight`.

Phase differentiation, critical-point location, exact Poisson summation,
Schwartz support, and a coarse `O(sqrt(t))` integral bound do not imply this
theorem.  The missing ingredient is the uniform main-term comparison, which
requires a formal Fresnel/Gaussian stationary-phase argument plus
nonstationary integration by parts.  Mathlib contains damped complex Gaussian
integrals, but no theorem taking the zero-damping limit in the uniform form
needed here.

## Dependency result

The corrected dependency chain is

`Type-I witness -> smooth common block -> {short deweighting | medium Poisson}
-> stationary B-process -> reflected deweighting -> short dual polynomial
-> Type-I range resolution`.

Thus smoothing is genuinely complete, shared deweighting is genuinely
complete on both concrete amplitudes, and the only open edge among the three
named interfaces is the stationary main-term-and-remainder theorem inside the
medium B-process.
