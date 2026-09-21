# Lean extension

Current analytic progress: [Jutila physical-scale smoothing and uniform pattern bounds](#jutila-physical-scale-smoothing-and-uniform-pattern-bounds--current-checkpoint).
The moments and full-domain clauses (i)--(ii) are proved; clauses (iii)--(ix) and the full goal remain open.
Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


This directory contains the unified Lean 4.30 package. It imports both the
frozen ANTEDB compatibility subset and the canonical local `RiemannZeta`
package, including the Guth--Maynard publication contracts.

The currently kernel-checked modules provide dependency bridges, rational
function sign certificates, generated nine-clause energy denominator checks,
piecewise-envelope machinery, polyhedral witness
soundness, exact optimized-Bourgain endpoints/coverage, analytic exponent-pair
semantics with its non-asymptotic equivalence, the source-range sharp
zero-energy comparison `2A ≤ A* ≤ 3A`, equivalent unbounded-family and
epsilon--delta interfaces for the general and zeta energy regions, and
equivalent asymptotic/non-asymptotic interfaces for all three energy-bound
predicates. The general and zeta energy exponents are also proved equal to
their feasible-region suprema on the source domain by a common-subsequence
compactness argument. Indexed energy at arbitrary tolerance is explicitly
bounded by unit energy, and this is combined with bounded zero perturbations
without discarding analytic multiplicity. The native Guth--Maynard Type I
beta-removal detector has also been lifted to every analytic-multiplicity copy,
with its shifted energy returned to unit tolerance. A separation-free indexed
mixed-to-self estimate and four-coordinate coloring theorem then reduce the
Type I energy to four single-scale detector classes without collapsing equal
values. `EnergySeparation` combines the native Jensen local-multiplicity bound
with unit-bin parity/rank coloring, so the refined detector classes are also
one-separated while retaining every multiplicity copy. `DetectorPattern`
normalizes the native half-open detector on exact closed dyadic support and
turns every inhabited refined class into a source `LargeValuePattern`; the
image-finset energy is proved equal to the indexed class energy. Its maximum
scaled-coefficient normalizer is `O_epsilon(N^epsilon)` by the native proved
divisor bound, and the logarithmic detector threshold is explicitly absorbed
using admissible-scale growth. `ZeroEnergyDichotomy` separately follows the
paper's classical Type-I/Type-II split: it chooses one beta-removed ordinate
and one genuine branch/scale label for every slab zero, lifts the choice to all
analytic-multiplicity copies, transfers the native Jensen cap to shifted unit
bins, and bounds the original slab energy by four one-separated classes with
explicit coloring and perturbation losses. The Type-II branch now has an exact
closed-support `LargeValuePattern` constructor using the native normalized
sharp-mollifier coefficients, including equality of finset and indexed
energy. The Type-I branch likewise has an exact normalized weighted
pre-deweighting `LargeValuePattern` with energy equality. Its exact two-block
source decomposition now also selects a large smooth block for every indexed
ordinate and controls the original energy by four fixed-block, one-separated
classes, including the specialization to a classical Type-I branch/scale
fiber. Exact untruncated Fourier deweighting of every selected block now
produces a large coefficient-one sum on the exact active integer interval
with an explicit Fourier-`L¹` loss. An order-two Schwartz estimate now gives
a uniform-in-ordinate complementary-tail bound and the explicit window
`typeISourceFourierRadius`; explicit displacement and occupancy estimates
therefore recolor the full indexed energy unconditionally into four
one-separated coefficient-one classes. The remaining source-specific edge is
subpower/source-scale control of that radius and of the Fourier-`L¹` loss;
height-pattern packaging, the `LV*` application, and asymptotic assembly are
also recorded below as historical implementation stages. The current
checkpoint proves Add-est (i); it does not close the remaining eight clauses.
The sharper source-paper route is now also present: a fixed logarithmic bump
deweights the original sharp Type-I polynomial on `Ioc N (min (2*N) A)` with
scale-independent Fourier `L¹` loss, and a generic theorem gives its Fourier
  tail at every polynomial order. The full scale-and-cardinality tail is now
  composed with finite-window extraction, and the canonical positive-real-root
  radius makes its numerical tail premise automatic. The resulting bounded
  ordinates carry the full indexed energy with an explicit normalization loss.
  Generic bounded-multiplicity coloring now further produces four
  one-separated coefficient-one families. The abstract order-selection lemma
  already turns a power bound for the radius's defining base into a subpower
  radius. The source threshold reciprocal, sharp-cutoff base envelope, fixed
  constant and `clog` absorption, and existential order choice are all proved;
  the resulting radius is uniformly eventually `T^δ`. The coefficient-one
  active-support polynomial and its exact `LargeValuePattern` constructor
  preserve energy, and a finite general-`LV*` consumer is proved.

`ClassicalTypeIEnergyTransfer` now proves the sharper source zeta consumer.
It derives the normalized-threshold lower power bound, partitions the
expanded positive interval into three exact `[H,2H]` zeta slabs, and
absorbs the complete degree-five displacement/coloring loss. Its source-class
theorem consumes actual classical branch/scale fibers with every
analytic-multiplicity index retained. Source largeness also supplies the
upper scale bound needed to select a common subsequence with
`1 ≤ τ ≤ 1/a` and every eventual height window. `EnergyUniformity` supplies
one constant and threshold window on a neighborhood of a compact scale
interval. `ClassicalTypeIUniformity` consumes this result through the genuine
source classes and obtains `energy ≤ C*T^(B+ε)`, allowing a slightly shifted
source line and deriving all physical height windows. These deductions remain
conditional on the specified zeta energy bounds.
`ClassicalTypeIIEnergyTransfer` now derives the normalized mollifier threshold,
physical scale window, and uniform source-fiber energy estimate from general
energy bounds. `ClassicalSlabEnergyTransfer` consumes both branches, chooses
the common source parameters, and absorbs the outer multiplicity/coloring
loss to prove the positive dyadic zero-slab estimate. `ZeroEnergyAssembly`
then proves the signed dyadic assembly, including conjugate analytic
multiplicities and the finite low-height rectangle, and concludes
`IsZeroDensityEnergyBound σ (B/(1-σ))` from the specified energy hypotheses.
`zeroDensityEnergyExponent_le_sup_limsup` in module `EnergyExponentTransfer`
(namespace `TaoTrudgianYang2025`) proves the exact source supremum/limsup
inequality with no additional mathematical assumptions. Its lower-endpoint
argument uses genuine singleton patterns. The bounded-range corollary remains
open under EPZAE-33. `EnergyPoweringObstruction` proves that the exact
EPZAE-34 source claim is false: singleton patterns realize `s=2`, while
`k=2` would require an impossible output `s'≤1`. Its four theorems and
regressions are included in the root imports, runner inventory, and audit.
The owner-authorized replacement is specified in `EnergyPowering`:
`CorrectedCardinalityEnergyPowering` requires two separate cardinality/energy
witnesses in the existential projection of the real five-dimensional region.
No relation on their fifth coordinates is imposed. The finite energy-class
selection, identity/singleton regressions, and monotone/Heath--Brown consumers
are kernel-checked. The full target is now proved by
`correctedCardinalityEnergyPowering` in `CorrectedEnergyPowering`:
`EnergyPoweredPatterns` constructs the actual polynomial blocks and both
finite witnesses; `EnergyPoweringLimits` absorbs the uniform constants,
rebases the logarithmic exponents, and extracts the new double-zeta
coordinates. `InLargeValueEnergyRegion.corrected_powering` exposes the
exact two-witness conclusion. `HeathBrownEnergyFinite` now bridges actual
patterns to the native second and fourth moments; `EnergyLogLimits` and
`HeathBrownEnergy` prove the source relation at every admissible height,
including `τ < 1`. `InCardinalityEnergyRegion.heathBrown_powered` consumes
the corrected energy witness with no analytic theorem parameter. The
three-branch `τ ≤ 3/2` constraint and its powered form are proved as well.
EPZAE-34 and EPZAE-35 are complete; the bounded-range transfer corollary,
optimization, and all advertised endpoints remain open.
`EnergyPoweringBounds` completes the general-energy factor-two range reduction
and a compact-range transfer with zeta endpoint `1`. The source's stronger
zeta endpoint `2` remains unproved, so this does not complete EPZAE-33.

`ClassicalLargeValueRegions` transfers the full native Montgomery--Halász--
Huxley finite estimate, including both minimum branches. Its physical height
padding is removed exactly at the exponent level. It proves Huxley's
cardinality constraint on actual energy regions and its corrected powered
form; it is not yet the standalone uniform `LV` API for all EPZAE-19 inputs.
`EnergyClauseOneGeneral` consumes these real region constraints at powers
`k` and `k+1`, and the separate powered Heath--Brown energy witness.
Its six affine branches have exact endpoint certificates; powers two and
three cover `[8σ-4,2(8σ-4)]`. Both source sigma pieces, their `4/5` crossover,
uniform general-energy bounds, and extension to all higher heights are proved.
`energyClauseOne_of_zeta_range` remains conditional on actual zeta-energy
bounds on `[1,8σ-4)`; no final `Add-est` clause is claimed complete.

`EnergyClauseOneZeta` proves the exact six-branch zeta certificate, its
`τ=4σ-1` transition, strict slope bounds, and `σ=65/86` crossover.
Actual region membership discharges the Huxley cardinality cap and the
Heath--Brown energy relation. A uniform zeta cardinality bound is converted
to the actual region coordinate with all epsilon and constant dependencies
preserved. The resulting uniform energy bounds are conditional on the
twelfth-moment LV predicate; final assembly also retains short zeta energy
on `[1,2)`. No new dependency or unproved twelfth-moment instance is imported.

`ZetaMomentKernel` proves exact mass and separated occupancy estimates for
`1/(1+|u-t|)`, together with weighted twelfth-power Hölder.
`ZetaMomentTransfer` applies them to the literal critical-line zeta norm
on `[T/2,3T]`. For one-separated `W ⊆ [T,2T]`, the twelfth powers of its
convolutions sum to at most `L(T)^12 M₁₂(T)`, where
`L(T)=3+2 log(ceil(2T)+1)` and `M₁₂` is the actual moment integral.
`ZetaLargeValuePattern.twelfth_cardinality_of_convolution` consumes the
actual pattern and an explicit pointwise entry inequality, retaining the
physical factor `C^12 N^6`.

`ZetaMomentAsymptotics` absorbs every fixed power of `L(T)`, proves the
three-dyadic-window enlargement, and deduces the epsilon-loss moment bound
from an explicitly quantified dyadic moment hypothesis.
`zetaPattern_twelfth_cardinality_of_dyadic_and_convolution` composes all
these results on actual patterns, with a uniform physical-height threshold.
Its two upstream interfaces remain explicit; the pointwise entry is now
discharged by `ZetaPerronEntry` below. This is the critical
line, twelfth-power portion of `add-bound (ii)`, not the general source
theorem or a proved `twelfth-bound`. All 21 public theorems in these three
modules are named in the audit, root-imported, and runner-inventoried;
ten semantic regressions check the kernel, windows, real zeta function,
uniform losses, and conditional consumer signatures.

`ZetaIntervalCutoff` constructs a smooth interpolation equal to the exact
active-interval indicator at every integer, including both endpoints.
`ZetaMellinEntry` derives its right-line zeta integral by Mellin inversion
and justified interchange of sum and integral. `ZetaMellinContour` retains
the pole at `1-it`, and `ZetaMellinShift` proves absolute boundary
integrability, vanishing horizontal integrals, and the exact critical-line
formula. The actual-pattern consumer
`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin` has no independent
analytic premise. Its residue is the cutoff's Mellin transform at `1-it`.

These four modules have 36 named public theorem audits, an explicit audit of
the constructed native smooth-test object, and ten endpoint/support/sign/
residue regressions. The root imports and principal runner include them.
The contour-convergence constants in these four modules depend on the
fixed cutoff and ordinate. Uniformity is proved separately in the following
six modules, not inferred from those constants.

`ZetaCutoffDerivatives` gives endpoint-independent derivative integral
bounds of every positive order. `ZetaMellinDerivative` proves integration
by parts and its exact product of Mellin factors.
`ZetaMellinUniform` consumes actual patterns, giving
`|M_w(σ+iu)| ≤ C_j(σ) N^(σ+j-1)/(1+|u|)^j` for `σ ≥ 1/2`, `j ≥ 1`.
The constants depend only on the fixed transition, order, and real line.
`ZetaMellinLocalization` bounds the omitted integral by
`120 C_4(1/2) N^(7/2)/T²`. `ZetaPerronEntry` retains the residue,
absorbs both errors when `T ≥ N^(7/4)` and `V ≥ 2 zetaPerronError`,
and derives those hypotheses uniformly from the actual source windows
`σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`.

`ZetaTwelfthFromMoment` proves
`IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))` from the explicitly quantified
dyadic critical-line twelfth moment alone, then composes the repaired
energy chain through its preserved modular clause-(i) consumer. These six
modules now have 39 named public theorem audits, an explicit
derivative-test constructor audit, and 14 semantic regressions, with root
and principal-runner coverage.

`ZetaShortPerron` proves entry when `T ≥ N^(23/16)` and
`V ≥ 2 zetaPerronError N^(5/8)`, deriving these conditions from uniform
`σ ≥ 3/4`, `τ ≥ 3/2`, `δ ≤ 1/16` windows. The new short-height LV
consumer in `ZetaTwelfthFromMoment` uses this actual entry.
`ZetaShortPatterns` proves sharp-interval cancellation including the left
endpoint, actual eventual emptiness for `1 ≤ τ < 3/2`, and `LV_ζ = -∞`.
`EnergyClauseOneFromMoment` combines these facts with cubic energy and
the exact public-rate comparison, supplying all `[1,2]` short zeta energy
from the moment and assembling `energyClauseOne_of_dyadic_moment`.
The three added modules contain 11 public theorems; together with the
new short-height LV theorem there are 12 new named audits and eight new
semantic regressions. The genuine moment, independent endpoint-two
source theorem, other moment parameters, and final `Add-est` outputs
remain open. No short-zeta estimate is assumed by the new assembly.

`ZetaLargeValueDiscreteness` proves the exact infimum-to-uniform-bound
equivalence and collapse of negative cardinality exponents to negative
infinity. `ZetaPointwiseNonexistence` proves both directions between that
condition and uniform strict cancellation on literal sharp intervals at
positive heights. It constructs actual singleton patterns and absorbs the
factor two in the reverse height window. The new
`zetaShort_pointwise_powerSaving` is an unconditional consumer of the
existing short-range cancellation. These additions have 13 named public
theorem audits and eight regressions, with both modules root-imported and
principal-runner-inventoried. The analytic maximum estimate and twelfth
moment remain unproved.

`ZetaSquareContour` and `ZetaSquareContourShift` adapt the adjacent
one-sided squared-zeta contour argument directly to the canonical native
foundation, without importing the separate Gafni--Tao package.
`ZetaSquareDivisorKernel` proves a Gaussian majorant with one constant for
both height variables. `ZetaSquareDivisorSeries` proves integrability of
every term and summability of their integrated norms before opening the
complete ordinary-divisor series. `ZetaSquareSourceEntry` removes the
Gamma factors and gives a convergent series for `|ζ(1/2+it)|²`, including
height zero. `ZetaSquareLocalMean` derives compact-height domination,
continuity, and the termwise local-integral identity
`hasSum_zetaSquareLocalMean`. These six modules have 47 named theorem
audits and nine new regressions. The exact local identity is proved;
the sharp Atkinson estimate with uniform source-scale errors is not.
No twelfth-moment hypothesis was added to this source-entry chain.

`ZetaSquareAveraging` extends the convergent series to continuous real
weights, then uses the literal `exp(-((t-T)/G)²)` Gaussian. Its local
majorization constant is `exp(1)`, independent of `T,G,L`.
`ZetaSquareGaussianTail` constructs a global linear bound on the actual
critical zeta norm, proves whole-line integrability, and carries the
Jacobian `G` through centering. The tail is at most
`C G(1+|T|+G)² exp(-L²/2)` for all `G>0,L≥0`, with one fixed `C`.
At `L=log T`, `0<G≤T`, it is at most `G T^(-A)` past one threshold.
`exists_zetaSquareGaussian_source_approximation` consumes the actual
weighted divisor series and this tail in one theorem.

`ZetaSquareGaussianTransform` proves the exact transform for coefficient
`G^(-2)+i/(2T)` and the bound
`sqrt(pi) G exp(-(Gv)²/8)` for `T,G>0`, `G²≤2T`. It is a theorem about
that literal kernel, not a supplied approximation to the Gamma factors.
The actual phase and its integrated error are proved in the continuation
below, followed by the uniform amplitude/source remainder and finite
shortening. The smooth Voronoi/Bessel entry is proved below; sharp Atkinson estimates remain open.
The three averaging modules have 31 named
public theorem audits and nine regressions, with root/runner coverage.

### Actual Gamma-phase continuation

`ZetaDigammaLog` proves the right-half-plane estimate
`‖digamma z-log z‖ ≤ 4/|Im z|` for `|Im z|≥1` from the pinned reciprocal
series and a unit-interval logarithmic comparison. There is no assumed
Stirling formula. `ZetaSquareGammaPhase` constructs
`phi(t)=GammaR(1/2-it)/GammaR(1/2+it)`, proves `|phi|=1`, the actual
zeta functional equation, and the exact factorization of the source's
Gamma normalization. Its derivative is `i d(t) phi(t)`, where
`d(t)=log(pi)-Re digamma(1/4+it/2)` and
`|d(t)+log(t/(2pi))|≤9/t` for `t≥2`.

`ZetaSquareGammaQuadratic` gives the actual phase replacement on
`|x|≤r≤T/2`, `T≥4`, with error `(18/T+2r²/T²)|x|`. Its integrated
consumer pays `2r²(18/T+2r²/T²)` and identifies the exact quadratic
coefficient and frequency `v-log(T/(2pi))`.
`ZetaSquareGammaTransform` adds both physical Gaussian tails, giving
total error `2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)` for `G>0`.
The final consumer actually uses the prior quadratic frequency bound.

These are now 26 named public theorem audits and 12 phase regressions
in four root-imported, runner-inventoried modules. The additional named
audit is the exact Gamma derivative reused by the amplitude proof below.
Weighted divisor truncation, Voronoi/stationary phase, Atkinson errors,
and the actual twelfth moment are not claimed proved.


### Uniform shifted amplitude and complete reflected source

Preserve the seven modules `ZetaGammaShiftLog`, `ZetaGammaShiftAmplitude`,
`ZetaSquarePoleShift`, `ZetaSquareNearKernel`, `ZetaSquareGammaInverse`,
`ZetaSquareKernelApproximation`, and `ZetaSquareLeadingDivisor`.
They add 44 public theorem audits; the promoted actual Gamma derivative
`hasDerivAt_gammaReal` adds one further named audit. Fourteen new
regressions retain zero shift/height/coefficient, both contour signs,
closed shift and central-contour boundaries, and the uniform source consumer.

For `t≥4`, `Re w≥0`, `‖w‖≤t/2`, put
`ell(t)=log(t/(2pi))-i*pi/2` and `B=(17‖w‖+2‖w‖²)/t`.
The literal squared Gamma ratio, normalized by `exp(-w ell)`,
differs from one by at most `B exp(B)`. This follows from the actual
digamma series, principal-branch path geometry, the exact derivative,
and Gronwall. The actual squared pole factor is bounded by 9 and
differs from one by at most `12‖w‖/t`.

`exists_norm_zetaSquareRightKernel_sub_leading_le` combines the near
estimate with the far inverse-Gamma/reflection estimate. One constant,
independent of `t≥4`, bounds the complete normalized reflected kernel
error by `C exp(-90u²)(1+|u|)^12`. The majorant is integrable.
`hasSum_zetaSquareLeadingDivisorContribution` proves convergence of
the full leading ordinary-divisor series.
`exists_norm_zetaSquareDivisorIntegral_sub_leading_le` consumes that
series and the actual source integral to give one uniform `O(1)`
remainder, with no analytic theorem premise.

This closes the amplitude/complete reflected-series remainder. The
following continuation proves actual weight control, height variation,
freezing and the local Gaussian-window comparison with a complete
quadratic divisor sum. The later continuation also proves source-scale
finite shortening and the actual smooth Voronoi/Bessel entry. Uniform
stationary phase,
sharp Atkinson errors, scale/spacing assembly and genuine dyadic twelfth
moment remain open. Do not substitute a full-series absolute bound
for the needed oscillatory estimate. EPZAE-21/37 and final outputs stay open.

Keep all seven modules, all 45 newly named audits and the regressions
in root imports and in the inventory behind
`run_tao_trudgian_yang_build.bat`. Update and rerun that exact batch
entry point and the foundation runner whenever this chain changes.
The original counterexample, independent corrected fifth coordinates,
proved powering/Heath--Brown results, source pins, and full
EPZAE-00--41 goal remain unchanged.

### Actual divisor weights, freezing and Gaussian source assembly

Nine further modules are preserved: `ZetaDivisorWeightKernel`,
`ZetaDivisorWeightReflection`, `ZetaDivisorWeightSource`,
`ZetaDivisorWeightVariation`, `ZetaDivisorWeightMass`,
`ZetaDivisorWeightFreezing`, `ZetaFrozenDivisorGaussian`,
`ZetaSquareRealSource`, and `ZetaSquareFrozenWindow`.
They add 78 named public theorem audits and 20 semantic regressions.

The actual Mellin weight `W(q)` satisfies `W(q)+W(-q)=1` and
`W(0)=1/2`, proved by its contour residue and integrable tails.
On each fixed imaginary strip, `‖W(q)‖≤C min(1,exp(-Re q))`.
The actual divisor argument is
`q(T,n)=log n-log(T/(2pi))+i*pi/2`, not a real cutoff.
For `T>0`, `n>0` and `|x|≤T/2`, its weight variation is at most
`C (|x|/T) min(T/(2pi n),2pi n/T)`.
The coefficient mass is `Oε(T^(1/2+ε))`, uniformly in the
oscillatory height; it is derived from the convergent divisor L-series,
not a postulated pointwise divisor estimate.

`exists_norm_zetaSquareLeadingDivisor_sub_frozen_le` freezes only
this weight, with error `Cε |x| T^(-1/2+ε)` on `T≥8`, `|x|≤T/2`.
The phase and Dirichlet oscillation remain at `T+x`.
`zetaSquareNorm_eq_reflected_source` proves the conjugate pairing
and the factor two for the actual real zeta square, including height zero.
`exists_abs_zetaSquareNorm_sub_frozen_le` consumes the actual
normalized contour remainder and this pairing.

`hasSum_zetaFrozenDivisorGaussianMean` proves the complete Gaussian
series exchange after absolute integrated-norm summability.
Write `M(T)=Σ_n ‖zetaFrozenDivisorCoefficient T n‖`, and let `Q(T,G)`
be the defined convergent quadratic divisor sum, retaining its exact
complex weight and actual central phase. The public consumer
`exists_abs_zetaSquareGaussianWindow_sub_quadratic_le` proves
for `T≥8`, `G>0`, `G²≤2T`, `0≤r≤T/2`:

```text
| actual Gaussian zeta window on T±r - 2 Re Q(T,G) |
 ≤ Cε r (1 + r T^(-1/2+ε))
   + M(T) [4r²(18/T+2r²/T²) + 6sqrt(2pi)G exp(-(r/G)²/2)].
```

This theorem consumes the real zeta source, frozen weights, actual
Gamma-phase transform, and both Gaussian tails. It has no analytic
theorem premise. It is a complete-series comparison, not the shortened
Ivić/Atkinson sum or the genuine twelfth moment.

The following continuation combines the proved whole-line zeta tail,
uniform logarithmic window and frequency shortening into the actual
local-mean-square entry to a finite divisor source; the continuation
also proves smooth Voronoi/Bessel entry. Uniform stationary estimates,
the Atkinson inequality and
dyadic moment remain open, as does the analytic input to
`energyClauseOne_of_dyadic_moment`. All nine unconditional `Add-est`
clauses and other public outputs remain required by the full
EPZAE-00--41 goal; no continuation narrows that goal.

Keep all nine modules in root imports, all 78 public audits and all
20 regressions in the inventory behind `run_tao_trudgian_yang_build.bat`.
Update that exact batch interface's backing inventory whenever the chain
changes, and rerun it and `run_lake_build.bat`; do not bypass their gates.
The original Lemma 62 counterexample, corrected independent fifth
coordinates, powering/Heath--Brown proofs and pinned sources are unchanged.

### Finite divisor shortening and the source-scale local mean

Preserve six further modules: `ZetaQuadraticDivisorBand`,
`ZetaQuadraticDivisorShortening`, `ZetaSourceLogScales`,
`ZetaSourceErrorScales`, `ZetaShortDivisorSource`, and
`ZetaShortDivisorGeometry`. Their 29 public theorems have named
dependency audits and 18 additional semantic regressions.

The band is a literal finite set of positive integers, with exact
closed membership condition
`G abs(log n-log(T/(2pi)))≤L`.
The upper index bound is proved, not a separate truncation premise.
The finite sum `S(T,G,L)=zetaShortQuadraticDivisorSum T G L`
retains the actual complex Mellin weight, divisor coefficient, central
Gamma phase and quadratic Gaussian transform.
`norm_zetaFrozenDivisorQuadraticSum_sub_short_le` bounds the omitted
sum by `M(T) sqrt(pi) G exp(-L²/8)`.
For every real `A`, one threshold before all widths makes the
`L=log T` tail at most `G T^(-A)`.

For each `δ>0`, one height threshold covers every
`0<G≤T^(1/2-δ)`. The half-height window, `G²≤2T` and `G≤T`
are derived from these scales. The mass loss is chosen as `δ/4`;
the actual freezing and phase errors are then `Oδ(G log T)`.
The source consumers prove

```text
| integral_R exp(-((t-T)/G)^2) |zeta(1/2+it)|^2 dt
    - 2 Re S(T,G,log T) | ≤ Cδ G log T,

integral_[T-G,T+G] |zeta(1/2+it)|^2 dt
 ≤ 2 exp(1) Re S(T,G,log T) + Cδ G log T.
```

These are `exists_zetaSquarePhysicalGaussian_short_approximation`
and `exists_zetaSquareLocalMean_le_short_divisor`, with one constant
and one threshold depending only on `δ`. No moment, Voronoi,
stationary-phase or result-shaped theorem premise is present.

On the lower source scale `T^δ≤G`, the actual band satisfies
`abs(n-T/(2pi))≤T log T/(pi G)` and
`T/(4pi)≤n≤T/pi`, uniformly beyond one threshold.
`zetaShortQuadraticDivisorSum_eq_divisor_test` identifies the
literal finite sum with `Σ d(n) zetaShortDivisorTestFunction(T,G,n)`.
This exact real-variable test function retains its complex weight.

The following continuation constructs a smooth positive-support cutoff
of this actual test, pays its change from the frequency tails, and
applies native Voronoi and both literal Bessel bridges. The hard finite
band itself is not declared smooth. Uniform oscillatory estimates and
the sharp Ivić/Atkinson inequality remain required; do not assume the
source inequality or bound the entire retained oscillatory sum absolutely.

EPZAE-21/37, the genuine dyadic twelfth moment, every unconditional
`Add-est` output and the complete EPZAE-00--41 contract remains in force.
The original Lemma 62 counterexample, independent corrected fifth
coordinates and proved powering/Heath--Brown relations are unchanged.

Keep all six modules directly imported by the root, all 29 named
audits and all 18 regressions covered by
`run_tao_trudgian_yang_build.bat`. Update the exact batch interface's
backing inventory as this chain changes and rerun it together with
`run_lake_build.bat`; the full goal and existing gates are not narrowed.

## Verification

The package currently:

1. pin one Lean toolchain and one mathlib revision;
2. import at least one selected ANTEDB foundation module and one local
   Guth--Maynard publication-contract module from source;
3. keeps analytic results distinct from finite certificate results;
4. build with zero warnings;
5. include a real root import, semantic regression module, and axiom audit; and
6. be covered by a runner that clearly distinguishes bootstrap success from
   paper-theorem completion.

Run `..\run_tao_trudgian_yang_build.bat --no-pause`; direct focused Lake
builds are useful during development but are not the project acceptance gate.

### Actual smooth Voronoi and literal Bessel source

Eight new modules now construct and consume the genuine smooth divisor
source: `ZetaDivisorWeightSmooth`, `ZetaDivisorTestSmooth`,
`ZetaDivisorBandCutoff`, `ZetaSmoothDivisorTest`,
`ZetaDivisorVoronoi`, `ZetaSmoothDivisorTail`,
`ZetaSquareVoronoiSource` and `ZetaDivisorBesselSource`.
They add 43 named public theorem audits and 18 semantic regressions.

The literal Mellin weight is entire in its complex logarithmic argument.
`hasDerivAt_zetaDivisorWeight` differentiates its actual contour integral
using a locally uniform integrable Gaussian majorant; real smoothness
of all orders follows from holomorphy. The evaluated Gaussian transform
and positive-axis complex power then prove smoothness of the actual
`zetaShortDivisorTestFunction` for positive arguments.

For `A=T/(2pi)`, set
`a=A exp(-2L/G)`, `b=A exp(-L/G)`,
`c=A exp(L/G)`, `d=A exp(2L/G)`. The actual cutoff is

```text
chi(x) = smoothTransition((x-a)/(b-a))
       * smoothTransition((d-x)/(d-c)),
g(T,G,L,x) = chi(x) zetaShortDivisorTestFunction(T,G,x).
```

For `T,G,L>0`, it lies in `[0,1]`, equals one throughout `[b,c]`,
and vanishes outside `[a,d]`. The closed transition endpoints are
proved. Its positive support gives global real smoothness of the
product, including at zero. `zetaSmoothDivisorVoronoiTest` constructs
the native test object; smoothness and support are not hypotheses.

`norm_zetaSmoothDivisorSum_sub_short_le` bounds the actual difference
from the earlier finite source by
`M(T) sqrt(pi) G exp(-L²/8)`, where
`M(T)=Σ norm(zetaFrozenDivisorCoefficient T n)`.
For `L=log T`, this is at most `G T^(-B)` for every fixed real
`B`, beyond one threshold uniform in all positive widths with
`G²≤2T`. Thus every smooth transition term has a proved cost.

The modulus-one native Voronoi theorem is now applied to this object,
not to an independently supplied test. Both native transforms are
then identified with their literal Bessel integrals:

```text
V0 = integral_(x>0) (log x + 2 gamma) g(x) dx,
VY = sum_n d(n) (-2pi) integral_(x>0) g(x) Y0(4pi sqrt(nx)) dx,
VK = sum_n d(n) 4 integral_(x>0) g(x) K0(4pi sqrt(nx)) dx.
```

Here `Y0` and `K0` are the native classical real-integral kernels,
not uninterpreted symbols. The zero index is handled by the actual
`d(0)=0`; it is not passed to a positive-index bridge.
`exists_zetaSquarePhysicalGaussian_bessel_approximation` and
`exists_zetaSquareLocalMean_le_bessel` prove, for every `δ>0`,
one `Cδ>0` and one `T0≥8`, uniformly for
`T≥T0` and `0<G≤T^(1/2-δ)`:

```text
| integral_R exp(-((t-T)/G)^2) |zeta(1/2+it)|^2 dt
    - 2 Re(V0+VY+VK) | ≤ Cδ G log T,

integral_[T-G,T+G] |zeta(1/2+it)|^2 dt
 ≤ 2 exp(1) Re(V0+VY+VK) + Cδ G log T.
```

This closes the actual smooth Voronoi/Bessel **entry**, not the
stationary-phase estimate or Ivić Theorem 6.2. The following continuation
proves the complete modified-Bessel branch negligible; the later
phase-adjusted continuation also bounds and removes its actual main term.
Derive the oscillatory Neumann-kernel reduction with uniform amplitudes, tails and source
scales. The sharp Atkinson inequality, physical dyadic/Gram assembly,
genuine twelfth moment, EPZAE-21/37 and every unconditional `Add-est`
output remain open. No target-shaped analytic input is assumed.

Preserve the original Lemma 62 counterexample and the corrected
independent fifth coordinates. Keep these eight modules directly
imported, all 43 public audits and 18 regressions covered by
`run_tao_trudgian_yang_build.bat`, and update its backing inventory
as the chain changes. Run it and `run_lake_build.bat` after Lean
changes. Do not narrow the complete EPZAE-00--41 goal or its gates.

### Negligible complete K0 branch and actual reduced source

Seven new modules now prove and consume the complete modified-Bessel
branch estimate: `ZetaBesselK0Decay`,
`ZetaSmoothDivisorSupport`, `ZetaSmoothDivisorMass`,
`ZetaBesselK0Integral`, `ZetaBesselK0Series`,
`ZetaBesselK0Scales` and `ZetaSquareBesselMinusSource`.
All 29 public theorem audits and 16 semantic regressions are in the
root import graph and the exact batch-runner inventory.

The kernel estimate begins with the literal integral
`K0(y)=integral_(u>0) exp(-y cosh u) du`.
It proves `K0(y)≤exp(-y/2) K0(y/2)` for `y>0`, hence
`abs(K0(y))≤2exp(-y/2)` for `y≥2`. The real exponential
series then gives, for every natural `k`,

```text
abs(K0(y)) ≤ Bk/(y^2)^k,
Bk = 2 * 2^(2k) * (2k)!.
```

For `T≥16`, `G,L>0` and `8L≤G`, the full smooth
source—including both transitions—has support in `[T/16,T]`.
The exponentiated outer-band endpoints are proved first, not supplied
as a support hypothesis. Thus every positive divisor index satisfies
`(4pi sqrt(nx))^2≥Tn` on the actual support.
The genuine test has a uniform bound `norm(g(x))≤C G` and
integrated mass at most `C G T` when `G²≤2T`.
These deliberately coarse absolute bounds are used only for the
exponentially decaying branch, not as a replacement for oscillatory
cancellation in the main or Neumann terms.

The actual K0 source integrand is proved measurable and absolutely
integrable. For every `k`, its integral has bound
`Ck G T/(T^k n^k)`, uniformly before choosing `T,G,L,n`.
For `k≥2`, summation uses the genuine ordinary-divisor Dirichlet
series at `s=2`. `hasSum_zetaBesselK0SourceTerm` identifies the
complete arithmetic series with `zetaDivisorBesselPlus`; the zero
index has its actual zero divisor coefficient.

`exists_zetaDivisorBesselPlus_powerSaving` proves, for every
`δ>0` and every real `A`, one threshold `T0≥16` such that

```text
T≥T0, T^δ≤G≤T^(1/2-δ)
  implies norm(zetaDivisorBesselPlus(T,G,log T)) ≤ G T^(-A).
```

All scale conditions, cutoff widths and constants are derived
uniformly, before choosing `G`. The lower width `G≥T^δ` is
explicit: this is the source range, not the earlier wider
Voronoi-entry range with arbitrary positive `G`.

The public source consumers
`exists_zetaSquarePhysicalGaussian_main_minus_approximation`
and `exists_zetaSquareLocalMean_le_main_minus` use this proved
power saving, not a supplied transform-error premise. On that range,
one constant and threshold depending only on `δ` give

```text
| integral_R exp(-((t-T)/G)^2) |zeta(1/2+it)|^2 dt
    - 2 Re(V0+VY) | ≤ Cδ G log T,

integral_[T-G,T+G] |zeta(1/2+it)|^2 dt
 ≤ 2 exp(1) Re(V0+VY) + Cδ G log T.
```

Here `V0` is the unchanged logarithmic main integral and `VY`
the actual oscillatory Neumann-kernel divisor sum. The next section
reapplies Voronoi with the source-required lattice phase. The later
continuation proves the phase-adjusted main bound. Next derive the
sharp Y0 stationary reduction with uniform amplitudes, tails and
source scales. The sharp Ivić/Atkinson
inequality, physical dyadic/Gram assembly, genuine twelfth moment,
EPZAE-21/37 and every unconditional `Add-est` output remain open.
No new analytic theorem assumption is introduced.

The original Lemma 62 counterexample, corrected independent fifth
coordinates and proved powering/Heath–Brown results remain unchanged.
The full EPZAE-00--41 goal is not narrowed. Keep all seven modules,
29 named audits and 16 regressions covered by
`run_tao_trudgian_yang_build.bat`; update its backing inventory
as needed and rerun it together with `run_lake_build.bat` after
Lean changes.

### Source-aligned lattice phase and exact saddle geometry

The pinned Ivić Orsay 83.06 scan, printed page 110, equation (6.36),
inserts `exp(2pi i n)=1` before applying Voronoi. Our divisor source
has the conjugate sign `x^(-1/2+iT)`, so its continuous test must
instead be multiplied by `alpha(x)=exp(-2pi i x)`.
The unadjusted identities above remain valid, but their continuous
saddle equations are different; do not use them as the source's
Atkinson stationary phase.

Six additional modules are installed: `ZetaDivisorLatticePhase`,
`ZetaAtkinsonVoronoi`, `ZetaAtkinsonK0`,
`ZetaAtkinsonReducedSource`, `ZetaAtkinsonPhase` and
`ZetaAtkinsonSaddle`. They have 40 named public theorem audits
and 22 semantic regressions.

For the actual new test `gA=alpha*g`, every natural-index value,
pointwise norm and support is proved unchanged. Its globally smooth
positive-support native test is constructed. Applying native Voronoi
again gives new logarithmic main, Y0 and K0 integrals, not equalities
between the old and new continuous integrals. The K0 pointwise
majorant transfers by unit norm; actual integrability, complete
arithmetic summability and `HasSum` are proved for the new branch.
`exists_zetaAtkinsonBesselPlus_powerSaving` gives
`norm(VK_A)≤G T^(-A)` for every fixed real `A` on
`T^δ≤G≤T^(1/2-δ)` beyond one threshold depending only on
`δ,A`.

The actual consumers
`exists_zetaSquarePhysicalGaussian_atkinson_reduced` and
`exists_zetaSquareLocalMean_le_atkinson_reduced` remove that
proved branch. They retain only `zetaAtkinsonVoronoiMain` and
`zetaAtkinsonBesselMinus`, with uniform error `Cδ G log T`,
the same factors `2` and `2 exp(1)`, and one constant and
threshold before all allowed widths. No analytic estimate is a
theorem parameter.

The exact source factorization keeps the cutoff, complex Mellin
weight, Gamma factor and quadratic Gaussian in
`zetaAtkinsonAmplitude`. Its carrier, after multiplication by
`exp(4pi i b sqrt(x))`, is

```text
Phi(T,b,x) = T log x - 2pi x + 4pi b sqrt(x),
A = T/(2pi), r = (b + sqrt(b^2 + 4A))/2.
For T>0 and x>0: Phi'(x)=0 iff x=r^2,
Phi''(r^2) = -pi (2r-b)/r^3 < 0.
```

These are proved for every real `b`, including zero for the main
term and both signs of `sqrt(n)` for the prospective Bessel
carriers. The main saddle is exactly `T/(2pi)`.
This is exact carrier calculus, not a proved Y0 asymptotic expansion
or a uniform stationary-phase approximation. The amplitude is still
complex and variable; its required derivative bounds may not be
silently discarded.

The following continuation proves the **phase-adjusted** main-term
estimate. The literal Y0 expansion is now proved below. Continue with uniform
amplitudes and tails, then the sharp
Atkinson inequality and physical dyadic/Gram assembly. The genuine
twelfth moment, EPZAE-21/37 and every unconditional `Add-est`
output remain open. The preserved Lemma 62 counterexample and proved
corrected independent fifth-coordinate powering/Heath–Brown chain
are unchanged. The full EPZAE-00--41 goal remains active.

Keep all six modules directly imported, all 40 named audits and
22 regressions covered, and update the backing inventory of
`run_tao_trudgian_yang_build.bat` whenever this chain changes.
Both that exact batch interface and `run_lake_build.bat` remain
mandatory after Lean changes; do not replace their gates with a
focused build or narrow the goal.

### Actual logarithmic main integral bounded and removed

Nine additional modules now bound the **phase-adjusted** logarithmic
main integral and consume the bound in the actual physical zeta
source: `IntervalAmplitudeBounds`, `ZetaMainElementaryWeights`,
`ZetaMainMellinProfile`, `ZetaLogGaussianVariation`,
`ZetaQuadraticGaussianDerivative`,
`ZetaQuadraticLogGaussianVariation`, `ZetaAtkinsonMainWeight`,
`ZetaAtkinsonMainIntegral` and `ZetaAtkinsonMinusSource`.
All 38 public theorem audits and 20 semantic regressions are covered
by root imports and the exact batch-runner inventory.

The literal `IntervalC1Bound` records smoothness, the norm bound
and the integral of the norm of the actual derivative. These are
constructed for every source factor, not assumed in the final
source theorem. The two monotone cutoff transitions have uniformly
bounded variation independent of their widths. The actual complex
Mellin weight becomes a fixed smooth profile on `[1/16,1]`
after `x/T` rescaling; its contour definition is unchanged.
The square-root, logarithmic and unit Gamma factors retain their
actual values.

Differentiating the exact complex quadratic Gaussian gives its
damped derivative, not a constant majorant over the whole support.
The logarithmic Gaussian envelope has variation at most two. This
proves the uniform complex-transform variation bound
`4 sqrt(pi) G` on the full physical support, with `G²≤2T`.
Combining every factor gives one constant independent of `T,G,L`
such that the complete main amplitude has norm and variation at
most `C G sqrt(T) log T`.

The native `norm_weighted_gmReflectionIntegral_le` applies to
the exact carrier `T log x - 2pi x` and supplies
`10/sqrt(T)` cancellation. The actual main integrand is proved
absolutely integrable; the positive-support restriction and exact
reflection identity are proved. Consequently
`exists_norm_zetaAtkinsonVoronoiMain_le` gives

```text
norm(zetaAtkinsonVoronoiMain(T,G,L)) ≤ C G log T
for T≥16, log T≥1, G>0, G²≤2T, L>0 and 8L≤G.
```

The source-scale theorem derives these conditions uniformly at
`L=log T`, with a threshold before every
`T^δ≤G≤T^(1/2-δ)`. The public consumers
`exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_minus` now prove

```text
| integral_R exp(-((t-T)/G)^2) |zeta(1/2+it)|² dt - 2 Re(VY_A) |
  ≤ Cδ G log T,
integral_[T-G,T+G] |zeta(1/2+it)|² dt
  ≤ 2 exp(1) Re(VY_A) + Cδ G log T.
```

Here `VY_A=zetaAtkinsonBesselMinus(T,G,log T)` is the
complete actual phase-adjusted divisor sum with the literal Y0
kernel and its `-2pi` normalization. Both removed branches are
paid for by proved bounds; no amplitude, transform-error or moment
theorem is a parameter. The old unadjusted integral is not used in
place of the new source.

The literal Y0 expansion is now proved and consumed below. Next prove
the uniform oscillatory stationary reduction, retaining the complex amplitude
and complete arithmetic tails. The sharp Atkinson inequality,
physical dyadic/Gram assembly, genuine twelfth moment, EPZAE-21/37
and every unconditional `Add-est` output remain open.
The main-integral substep is complete, not the full Atkinson theorem.

The full EPZAE-00--41 goal, preserved Lemma 62 counterexample and
proved independent-coordinate powering/Heath–Brown chain remain
intact. Keep all nine modules, 38 named audits and 20 regressions
covered by `run_tao_trudgian_yang_build.bat`, update its backing
inventory as needed, and run it together with `run_lake_build.bat`
after Lean changes. Neither the goal nor verification scope is narrowed.

### Literal Neumann expansion and complete two-term zeta source

Thirteen production modules now prove and consume a two-term expansion
of the literal native `dfiBesselY0`. This is a kernel-checked source
component of EPZAE-21, not completion of that item or of Add-est.
They have 71 named public theorem audits and 25 semantic regressions.

The entry is proved from the existing Schläfli integral definition.
`NeumannContourKernel`, `NeumannContourShift` and
`NeumannSchlafliEntry` construct a Cauchy rectangle, prove absolute
integrability of its vertical rays and vanishing of the top side,
and pass the angular endpoint to the ray through one. The separate
principal powers `(1-z)^(-1/2)(1+z)^(-1/2)` keep both branches
explicit. `NeumannLaplaceRepresentation` cancels the actual
Schläfli tail and gives an exact decaying-ray formula for Y0.

`NeumannLaplaceAmplitude` proves, for every real u,

```text
|(1+iu)^(-1/2) - 1 + iu/2| ≤ 3u²/8.
```

`NeumannRayFactorization` links that amplitude to the actual ray.
`NeumannLaplaceMoments` evaluates its three required moments by
the Gamma integral and proves the exact coefficient `(1+i)/2`.
`NeumannLaplaceRemainder` integrates the error only after proving
integrability. `NeumannTwoTermExpansion` defines

```text
P(x) = sqrt(pi)/pi *
       ((sin x-cos x) x^(-1/2) - (sin x+cos x) x^(-3/2)/8),
K = (2/pi) (9/128) sqrt(pi) > 0,
|Y0(x)-P(x)| ≤ K x^(-5/2),  for every x>0.
```

The sign and both coefficients are exact; the error is proved, not
a DLMF assumption. `NeumannSourceBounds` proves measurability and
links `x≥T/16`, `T≥16`, `n≥1` to the literal argument
`4pi sqrt(nx)`. Its error is at most
`K T^(-5/4) n^(-5/4)`.

`ZetaNeumannRemainder` uses the actual phase-adjusted test
`gA=zetaAtkinsonDivisorTest(T,G,L)`. Both retained kernels and
their difference are integrable; the uniform mass bound gives a
remainder integral at most `C G n^(-5/4)`.
`ZetaNeumannSeries` consumes native Voronoi summability of the
original branch and the genuine ordinary-divisor series at 5/4.
It handles the zero coefficient explicitly and proves summability
of the complete new series

```text
W(T,G,L) = sum_n d(n) (-2pi) integral_(x>0) gA(x) P(4pi sqrt(nx)) dx,
|VY_A(T,G,L)-W(T,G,L)| ≤ C G.
```

The latter bound holds uniformly for `T≥16`, `G>0`,
`G²≤2T`, `L>0`, `8L≤G`. It is a complete arithmetic
replacement, not a finite-index or pointwise-only statement.

`ZetaAtkinsonTwoTermSource` derives all source scale hypotheses
at `L=log T` and consumes this replacement in the actual zeta
theorems. For each δ>0, one Cδ>0 and threshold T₀≥16 work for
every `T≥T₀` and `T^δ≤G≤T^(1/2-δ)`:

```text
|integral_R exp(-((t-T)/G)²) |zeta(1/2+it)|² dt - 2 Re W(T,G,log T)|
  ≤ Cδ G log T,
integral_(T-G)^(T+G) |zeta(1/2+it)|² dt
  ≤ 2 exp(1) Re W(T,G,log T) + Cδ G log T.
```

The public consumers are
`exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_twoTerm`. They assume
no amplitude, Bessel-expansion, summability, stationary-phase or
moment theorem. All actual source constants and normalizations
are retained.

Next evaluate this oscillatory series with uniform stationary
estimates for both signs, the actual complex amplitude and the
complete arithmetic tails. Exact saddle geometry alone does not
supply this estimate. The sharp Atkinson inequality, physical
dyadic/Gram assembly, genuine critical-line twelfth moment,
EPZAE-21/37 and every unconditional Add-est output remain open.

The original Lemma 62 counterexample remains byte-for-byte preserved.
The full EPZAE-00--41 goal and corrected independent-coordinate
powering/Heath–Brown chain are unchanged. Keep all thirteen modules,
71 named audits and 25 regressions in the root import graph and
the backing inventory of `run_tao_trudgian_yang_build.bat`.
Run that exact interface and `run_lake_build.bat` after Lean,
audit or inventory changes; neither verification scope is narrowed.

### Uniform signed-carrier bounds on the actual source

Ten further production modules prove frequency-uniform cancellation
for the actual power-weighted source, identify all four retained
Neumann carriers, and consume the complete series in the physical
zeta theorems. They have 43 named public theorem audits and 24
semantic regressions.

With `x=y²`, the exact normalized carrier is
`q(T,b,y)=(T/pi)log y-y²+2by`.
`zetaAtkinsonPhase_sq` proves the identity with the original
carrier, including its `2pi` normalization.
`AtkinsonRootPhase` differentiates q and its slope and factors
the slope at the actual positive saddle root r:

```text
q'(y)=2(r-y)(1+(r-b)/y),   r-b>0.
```

`AtkinsonFirstDerivative` consumes the pinned native monotone
reciprocal-slope estimate in both orientations. Beyond r±1 the
slope has magnitude at least 2. `AtkinsonRootIntegral` combines
the two tails with a central interval of length at most 2, proving

```text
|integral_a^c exp(2pi i q(T,b,y)) dy| ≤ 4
for every T>0, b real, and 0<a≤c.
```

`AtkinsonAmplitudeIntegral` proves that the square substitution
preserves the actual derivative-norm integral. Integration by parts
then gives the weighted bound `8M` for a concrete C1 amplitude
whose supremum and total variation are at most M.
`AtkinsonPowerWeight` constructs that bound from the actual
cutoff, rescaled power/Mellin profile, unit Gamma factor and
damped quadratic Gaussian. No amplitude estimate is a source premise.

`AtkinsonPowerIntegral` proves the positive-support restriction
and exact Jacobian identity. Its public consumer
`exists_norm_atkinsonPowerIntegral_le` gives, for every fixed
real α, one Cα>0 such that

```text
Iα(T,G,L,b)=integral_(x>0) gA(x) x^(-α) exp(4pi i b sqrt(x)) dx,
|Iα(T,G,L,b)| ≤ Cα G T^(-α)
```

for all `T>0`, `G>0`, `G²≤2T`, `L>0`, `8L≤G`
and every real b. In particular both `b=±sqrt(n)` are covered.

`AtkinsonCarrierAlgebra` and `AtkinsonCarrierIntegrals`
identify the actual two-term Neumann integral with its four
quarter-power carriers. Integrability is proved before using
linearity. The leading coefficients are `-(1±i)/2`;
the correction coefficients are `(1∓i)/2`, with the original
outer `sqrt(pi)/pi`, minus sign and `1/8` correction retained.
The Bessel-argument powers are linked to x and n exactly.
The full series retains `d(n)(-2pi)`, handles n=0 and is
proved summable by equality with the already convergent actual source.

`AtkinsonCarrierBounds` consumes the uniform integral estimates
in `exists_norm_zetaAtkinsonTwoTerm_le`. One pair C,D>0 works
for every admissible source and every natural n:

```text
|twoTermSummand(n)| ≤ |d(n)| G
  (C T^(-1/4)n^(-1/4) + D T^(-3/4)n^(-3/4)).
```

`AtkinsonCarrierSource` proves
`exists_zetaSquarePhysicalGaussian_carrier_approximation` and
`exists_zetaSquareLocalMean_le_carriers`. They retain the complete
signed-carrier series, source factors 2 and 2 exp(1), and the same
uniform `Cδ G log T` error on `T^δ≤G≤T^(1/2-δ)`, beyond
one threshold. They assume no analytic theorem.

These are cancellation bounds and exact source identities, not a
stationary main-value asymptotic. The displayed per-summand
majorants are not summable over all n and are never used as if they
were. Next prove the sharper far-frequency estimates and arithmetic
tail control, then the actual stationary main values with their
uniform source-scale error. The sharp Atkinson inequality, physical
dyadic/Gram assembly, genuine twelfth moment, EPZAE-21/37 and all
unconditional Add-est outputs remain open.

Keep these ten modules, 43 public audits and 24 regressions in the
root and backing inventory of `run_tao_trudgian_yang_build.bat`;
run it and `run_lake_build.bat` after relevant changes. Preserve
the original Lemma 62 counterexample byte-for-byte and the proved
independent-coordinate powering/Heath–Brown chain. The full
EPZAE-00--41 goal and both verification scopes remain unchanged.

### Complete correction removed; leading source retained

Four further production modules and a generalized weighted-primitive
lemma now prove the required summable correction estimate.
There are 19 new named public theorem audits and 16 semantic
regressions, in the root and exact batch-runner inventory.

`AtkinsonFrequencyTail` proves that on the full square-root
support `[sqrt(T/16),sqrt(T)]`, every `b≥8sqrt(T)` has

```text
q'(T,b,y) ≥ b,     q'(T,-b,y) ≤ -b.
```

Both phases have decreasing slope. The pinned native
first-derivative estimate and the proved actual amplitude variation
give `|Iα(T,G,L,±b)|≤Cα G T^(-α)/b`.
This holds on `T>0, G>0, G²≤2T, L>0, 8L≤G`.
`IntervalC1Bound.atkinsonRoot_of_primitive_bound` supplies
the weighted deduction; the earlier frequency-uniform bound is
also now a consumer of that proved lemma.

`AtkinsonCorrectionBounds` uses the uniform bound for
`sqrt(n)<8sqrt(T)` and the reciprocal-frequency gain in the
complement, including the equality boundary. For T≥1 the actual
correction pair has norm at most `C G/sqrt(n)` for n>0.
Its exact `n^(-3/4)` coefficient supplies the missing decay:

```text
|correctionTerm(n)| ≤ C G |divisorDirichletTerm(5/4,n)|,
|completeCorrection| ≤ C G.
```

The zero coefficient is handled separately. The genuinely
convergent ordinary-divisor series at 5/4 proves absolute
summability. `AtkinsonLeadingSeries` identifies the exact
leading-minus-correction decomposition and proves summability
of the complete leading source from the actual two-term source.
Neither phase, complex coefficient nor `d(n)(-2pi)` factor
is discarded. `exists_norm_zetaAtkinsonTwoTermSum_sub_leading_le`
consumes the full correction estimate, not just a pointwise bound.

`exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_leading` now retain
only the complete leading signed-carrier series. They preserve
source factors 2 and 2 exp(1) and uniform `Cδ G log T` error
on `T^δ≤G≤T^(1/2-δ)`, beyond one threshold, with no
analytic theorem premise.

This closes the complete correction removal, not the leading
stationary main values or a sharp tail estimate for the leading
series. Those remain next, followed by the sharp Atkinson
inequality and physical dyadic/Gram assembly. The genuine twelfth
moment, EPZAE-21/37 and all unconditional Add-est outputs remain
open; the full EPZAE-00--41 goal is unchanged.

Keep these four modules, the weighted-primitive helper, all 19
audits and 16 regressions covered by
`run_tao_trudgian_yang_build.bat`; update its backing inventory
and rerun it and `run_lake_build.bat` after relevant changes.
Preserve the original counterexample byte-for-byte and the proved
independent-coordinate powering/Heath–Brown chain.

### Actual second-order Fourier tails and finite leading source

Fifteen further production modules construct the actual second derivatives,
apply Fourier integration by parts, and consume the resulting arithmetic
tail in both physical zeta theorems. All 59 public theorems have named
dependency audits; 20 additional regressions check the actual source,
both frequency signs, closed scale boundaries, zero coefficients and
uniform source-consumer signatures.

For fixed real α, the new amplitude retains the power/Mellin profile,
actual exponential-edge cutoff, unit Gamma factor, quadratic Gaussian
and nonlinear phase. Its positive-root extension is smooth and supported
in [1/4,1]; the existing band supplies a neighbourhood of zero on which
it vanishes. No extra cutoff or assumed derivative bound is introduced.
On T≥1, G>0, G²≤2T, L≥1 and 8L≤G, its constructed C2 bound has
size Cα G T^(-α) and derivative scale T. The actual Gaussian second
derivative and both cutoff transition-width lower bounds are proved.

With ψ(u)=2log(u)-2pi u², the exact source identity is

```text
Iα(T,G,L,b) = 2sqrt(T) exp(i T log T) Fourier(Fα)(-2b sqrt(T)).
(1+|ξ|)² |Fourier(Fα)(ξ)| ≤ Cα G T^(-α) T².
b² |Iα(T,G,L,b)| ≤ Cα G T^(-α) T sqrt(T).
```

The source's square-root Jacobian, both signed frequencies and constant
unit phase are preserved. Native Fourier integration by parts is consumed
only after actual global smoothness, support and derivative bounds are proved.
The exact leading coefficient then gives

```text
|leadingTerm(n)| ≤ C G T^(5/4) |divisorDirichletTerm(5/4,n)|,
|leadingSum - sum_(n<N) leadingTerm(n)|
  ≤ C G T^(5/4) N^(-1/8)      (N>0),
|leadingSum - sum_(n<N) leadingTerm(n)| ≤ C G    (N≥T^10).
```

The true ordinary-divisor Dirichlet series at 9/8 sums the tail.
`exists_zetaSquarePhysicalGaussian_atkinson_finite_approximation` and
`exists_zetaSquareLocalMean_le_atkinson_finite` consume it on
T^δ≤G≤T^(1/2-δ), beyond one threshold depending only on δ>0,
for every natural N≥T^10. They retain the actual finite leading integrals,
source factors 2 and 2exp(1), and uniform Cδ G log T error, with no
analytic theorem premise.

This closes a **coarse polynomial truncation**, not the sharp Atkinson
inequality. The later continuations below prove evaluated stationary mains
and source-scale localization. A sufficiently strong summed stationary error
and final main assembly still precede sharp Atkinson and the physical
dyadic/Gram argument. The genuine twelfth moment, EPZAE-21/37 and all
unconditional Add-est outputs remain open.
The full EPZAE-00--41 completion contract is unchanged.

Maintain all fifteen modules, 59 named audits and 20 regressions in the
root graph and backing inventory of `run_tao_trudgian_yang_build.bat`;
update that runner as needed and rerun it and `run_lake_build.bat`
after relevant changes. Preserve the original Lemma 62 counterexample
byte-for-byte and the proved independent-coordinate powering/Heath–Brown chain.

### Actual finite-window stationary reduction and paired source phases

Twelve further production modules, from `AtkinsonSaddleNormalization`
through `AtkinsonStationaryPhysical`, now have 71 named public theorem
audits and 22 semantic regressions. The original counterexample and the
proved independent-coordinate powering/Heath–Brown chain are unchanged.

The actual positive saddle r=r(T/(2pi),b) satisfies r(b)r(-b)=T/(2pi).
The source logarithmic argument log(r²)-log(T/(2pi)) is exactly
2arsinh(b/(2sqrt(T/(2pi)))); the literal source
phase f(T,n) is linked to both b=±sqrt(n), including (-1)^n and both
pi/4 signs. The two actual quadratic Gaussians agree. On G²≤2T,
T>0 and G>0 their norm is bounded by
sqrt(pi) G exp(-G² n/(12T)) for n≤T. The cutoff and Mellin weights
at the two saddles are retained separately, not assumed conjugate.

Unlike the earlier Fourier amplitude, the stationary amplitude does
not include the nonlinear phase. Its constructed C2 size is
Cα G T^(-α) and derivative scale G/sqrt(T), on the actual root support.
The proof uses the true Gaussian damping in Q' and Q'', with fixed
profile, cutoff, power and unit Gamma factors. The cubic logarithmic
remainder gives the actual kernel error 4T|y-r|³/r³ on |y-r|≤r/2.
The outer weighted integrals are bounded using the actual total
variation and the proved reciprocal-slope test.

Write c=1+(T/(2pi))/r² and
F(c,H)=integral_(-H)^H exp(-2pi i c z²) dz. The finite main term is

```text
Mα(T,G,L,b,H) = 2 Wα(T,G,L,r²) exp(2pi i q(T,b,r)) F(c,H).
|Iα - Mα| ≤ Cα G T^(-α)
  [4/(pi H) + 4(G/sqrt(T)) H² + 16T H⁴/r³].
```

`exists_atkinsonPowerIntegral_finite_stationary_approximation`
proves this for all fixed real α, with one Cα before T,G,L,b,H,
on T>0, G≥1, G²≤2T, L≥1, 8L≤G, H>0,
[r-H,r+H]⊆[sqrt(T)/4,sqrt(T)] and H≤r/2.
It starts at the actual positive-support carrier integral, not a
separately supplied local integral or an assumed stationary estimate.

`exists_atkinsonPowerIntegral_small_n_pair_approximation` derives
all saddle/window conditions for both b=±sqrt(n) from
10000n≤T and H≤sqrt(T)/12. Its common bound replaces
16T H⁴/r³ by 432H⁴/sqrt(T). The signed-main identities consume
the exact phase and Gaussian bridges. The finite quadratic window
has not been replaced by an unproved Fresnel value.

The Fresnel limiting value, quantitative finite-window tail and sharp
source-scale localization are proved in the continuations below.
A sufficiently strong summed stationary error and final main assembly
remain before the sharp Atkinson local-mean inequality and physical
dyadic/Gram argument. This reduction does not prove the genuine twelfth moment. EPZAE-21/37, all unconditional
Add-est outputs and the full EPZAE-00--41 goal remain open.

Maintain all twelve modules, 71 named audits and 22 regressions in
the root and backing inventory of `run_tao_trudgian_yang_build.bat`;
update it as needed and rerun it and `run_lake_build.bat` after
relevant changes. Preserve Lemma 62's counterexample byte-for-byte,
the two separate corrected witnesses and every frozen public output.

### Evaluated Fresnel main terms and physical power saving

Nine additional modules, from `ContinuousKernelPrimitive` through
`AtkinsonStationaryPowerSaving`, now replace the finite quadratic window
by its proved limiting value. All 35 public theorems have named audits;
16 new regressions cover zero damping, the square-root branch, both
phase signs, the closed power-balance boundary and actual source consumers.

For c>0 and H>0 the locally proved statements are

```text
F(c,H) -> (1-i)/(2sqrt(c)) = exp(-i pi/4)/sqrt(2c),
|F(c,H) - exp(-i pi/4)/sqrt(2c)| <= 2/(c H pi).
```

The proof uses genuinely integrable positive-damping Gaussians, a
damping-uniform tail, and a zero-damping limit on each finite interval.
It does not assert a whole-line Lebesgue integral at zero damping.

`exists_atkinsonPowerIntegral_stationary_approximation` consumes that
tail and the constructed saddle amplitude. Its evaluated main is
Mα = 2 Wα(r²) exp(2pi i q(T,b,r)) exp(-i pi/4)/sqrt(2c).
The error retains the previous bracket with a larger uniform Cα.
`AtkinsonEvaluatedPhases` proves both actual signed identities:
the positive phase is exp(if(T,n)); the negative is -i exp(-if(T,n)).
Both retain (-1)^n, the central phase and their separate cutoff/Mellin
profiles, with the actual shared quadratic Gaussian.

Choosing H=T^η/12, for 0<η≤1/10 and 1≤G≤T^(1/2-3η), gives

```text
|Iα(T,G,L,b) - Mα(T,G,L,b)| <= Cα G T^(-α) T^(-η),
T>=1, L>=1, 8L<=G, |b|<=sqrt(T)/100.
```

The theorem derives G²≤2T and the actual saddle-window conditions.
`exists_atkinsonPowerIntegral_source_power_saving` then takes
η=min(δ/3,1/10), L=log T and T^δ≤G≤T^(1/2-δ), beyond one
threshold for δ>0, proving both b=±sqrt(n) estimates for 10000n≤T
with one Cα independent of all physical parameters.

This remains a **per-carrier** estimate, not the full sharp Atkinson sum.
The source-scale truncation and linked cutoff proved below now resolve
the earlier N≥T^10 versus 10000n≤T mismatch. A sufficiently strong
summed stationary error is still needed before the sharp Atkinson inequality and physical
dyadic/Gram assembly. The genuine twelfth moment, EPZAE-21/37,
unconditional Add-est and the full EPZAE-00--41 goal remain open.

Maintain the nine root imports, 35 named audits, 16 regressions and
exact backing inventory of `run_tao_trudgian_yang_build.bat`; update
the runner as needed and rerun it and `run_lake_build.bat` after relevant
changes. Preserve the Lemma 62 counterexample byte-for-byte and the
proved independent-coordinate powering/Heath–Brown chain. No false
s scaling or third s-preserving witness may be reintroduced.

### Source-scale truncation and linked stationary cutoff

Eleven further modules, from `AtkinsonSaddleSupport` through
`AtkinsonSourceCutoff`, prove the actual source-scale tail and consume
it in both physical zeta theorems. All 53 public theorems have named
audits; 22 regressions cover both signs, cutoff endpoints, closed scale
boundaries, ceiling rounding and the actual uniform source statements.

The original smooth cutoff at either saddle forces |b|≤3sqrt(T)L/G.
Thus the evaluated stationary mains vanish for n>9T(L/G)².
The actual carrier, however, is not zero there: it is restricted exactly
to the original root band, whose length is at most 4sqrt(T)L/G.
Both true slopes are bounded away from zero once |b|≥6sqrt(T)L/G.
Two integrations by parts use the actual quotient amplitude, constructed
natural C2 bounds and proved vanishing endpoints to give

```text
|Iα(T,G,L,±sqrt(n))| <= Cα G² T^(-α) L / (sqrt(T) n),
n >= 36 T(L/G)²,
T>0, G>=1, G²<=2T, L>=1, 8L<=G.
```

The ordinary-divisor Dirichlet series at 5/4 then sums the complete
leading tail: `exists_norm_atkinsonLeadingSum_sub_band_finite_le`
bounds it by C G² L T^(-3/4) for every N≥36T(L/G)².
`exists_atkinsonLeading_source_band_bound` proves O(G) on the
original physical width range T^δ≤G≤T^(1/2-δ), L=log T, eventually.
No tail estimate, endpoint condition or source support is assumed.

`exists_zetaSquarePhysicalGaussian_atkinson_band_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_band` consume that tail.
They retain the actual leading finite sum, source factors 2 and
2exp(1), and Cδ G log T error, now requiring only
N≥36T(log T/G)² rather than N≥T^10.

The explicit choice `atkinsonSourceCutoff = ceil(36T(L/G)²)`
satisfies the tail requirement. Eventually 10000N≤T on the lower
power-width range; `exists_atkinsonSourceCutoff_carrier_approximation`
therefore proves both existing evaluated stationary estimates for every
retained n<N. The earlier mismatch between the truncation range and
the small-frequency stationary range is resolved.

The symmetric continuation below now proves a **summed stationary error**
at and above the fourth-root width, with both actual physical zeta consumers.
The smaller-width error and remaining main-amplitude/source assembly still
precede the full sharp Atkinson inequality and physical dyadic/Gram argument.
The earlier per-carrier estimate alone is not claimed to establish this sum.
The genuine twelfth moment, EPZAE-21/37, unconditional Add-est and
the full EPZAE-00--41 goal remain open.

Maintain all eleven root imports, 53 named audits, 22 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`;
update the runner as needed and execute it and `run_lake_build.bat`
after relevant changes. Preserve the original Lemma 62 counterexample
byte-for-byte and the proved independent-coordinate powering/
Heath–Brown chain. Never restore false s scaling.

### Symmetric stationary summation and physical zeta consumers

Ten further modules, from `StationaryOddRemainder` through
`AtkinsonStationaryZetaSource`, now have 43 named public theorem audits
and 24 regressions. The actual symmetric quadratic window cancels both
the amplitude's linear term and the phase's cubic term. Constructed C2
bounds and the true logarithmic quartic remainder control what remains.
The original outer tails and the proved Fresnel value are consumed.

The new balance is G X²≤sqrt(T), X⁴≤sqrt(T). Choosing
X=T^(1/4)/sqrt(G), H=X/12, derives these inequalities on
T≥1 and T^(1/4)≤G≤sqrt(T). For both b=±sqrt(n), 10000n≤T,
L≥1 and 8L≤G, the actual carrier estimate is

```text
|Iα(T,G,L,b)-Mα(T,G,L,b)| <= Cα G sqrt(G) T^(-α-1/4).
```

`atkinsonStationaryLeadingSum` retains the original divisor weights,
Bessel coefficients, both evaluated mains and their separate cutoff/
Mellin profiles. Its finite support follows from the original saddle
cutoff, and its sum equals the finite sum at the same explicit
`atkinsonSourceCutoff` used by the physical source.

Absolute convergence of the actual divisor Dirichlet series at 1+ε
gives a quarter-weighted prefix bound Cε N^(3/4+ε).
Ceiling rounding gives N≤37T L²/G². Combining these linked scales
and absorbing logarithms proves a retained error Oε(T^(1/4+ε)),
eventually on T^δ≤G≤T^(1/2-δ) with G≥T^(1/4).
The complete leading-series difference is O(G+T^(1/4+ε)).

`exists_zetaSquarePhysicalGaussian_stationary_approximation` and
`exists_zetaSquareLocalMean_le_stationary` consume this complete error.
They retain the source factors 2 and 2exp(1), and prove error
Cδ,ε (G log T+T^(1/4+ε)). Their `above_fourthRoot` consumers
give Cδ,κ G log T when G≥T^(1/4+κ), κ>0.
All thresholds and constants precede T and G; no stationary, arithmetic
or zeta-source estimate is assumed.

This is not the full-width Ivić Theorem 6.2. Continue with the smaller-width
stationary error and remaining main-amplitude/source assembly. Any route
that omits smaller widths in the twelfth-moment argument must first prove
the corresponding lower-value-range reduction; do not assume that the new
fourth-root restriction is harmless. The sharp Atkinson theorem, physical
dyadic/Gram assembly, genuine twelfth moment, EPZAE-21/37, unconditional
Add-est and the full EPZAE-00--41 goal remain open.

Maintain all ten root imports, 43 named audits, 24 regressions and the exact
PowerShell inventory behind `run_tao_trudgian_yang_build.bat`; update it
as needed and execute it and `run_lake_build.bat` after relevant changes.
Preserve Lemma 62's counterexample byte-for-byte and the independent
ρ/k and ρ*/k witnesses with their proved Heath–Brown application.
Never restore false fifth-coordinate scaling or a third s-preserving witness.

## Normalized main terms and actual Abel consumer

Five production modules now continue the stationary series:
`AtkinsonMainNormalization`, `AtkinsonSignedPhaseSeries`,
`AtkinsonMainWeightBounds`, `AtkinsonMainPartialSummation` and
`AtkinsonMainZetaConsumer`. Their 30 public theorems have named audits;
24 `NormalizedMainAbelRegression` examples cover zero/one-index cases,
both signs, exact coefficients and all four physical consumer signatures.

The real saddle power and curvature cancel together. At alpha=1/4,
`atkinsonSaddleProfile_div_curvature` extracts the common factor
1/(sqrt(2) sqrt(sqrt(b²+2T/pi))) from the actual saddle profile.
The remaining factor is the actual Mellin profile times the original
cutoff, evaluated separately at b and -b; the Gamma phase is retained.

For n>0 the exact fourth-root coefficient is

```text
a(T,n) = (1/sqrt(2)) n^(-1/4) (n+2T/pi)^(-1/4).
```

The zero-index term is also handled with the original zero divisor weight.
`atkinsonStationaryLeadingSum_eq_signed` derives, from the original
Bessel coefficients and the proved finite-support theorem,

```text
stationary sum = (1+i) GammaPhase(T) exp(i centralPhase(T)) (Splus-Sminus).
```

Each S retains its own weight a(T,n) times the common actual quadratic
Gaussian times its separate cutoff/Mellin profile, multiplied by
(-1)^n d(n) exp(±i f(T,n)). Both sums use the same explicit source ceiling.
Only the raw negative-phase sums are proved conjugate to the positive
ones; no conjugacy or equality of the two weights is assumed.

`exists_norm_atkinsonMainWeights_le` constructs a uniform constant,
before T,G,L,n, bounding both actual weights by
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) for n≤T,
T,G,L>0, G²≤2T and 8L≤G. It consumes the actual cutoff support,
the compact Mellin bound and the actual saddle Gaussian.

`atkinsonMainAbelBound` is the explicit endpoint term plus a finite sum
of literal differences of the two weights times raw phase partial sums.
Mathlib's finite summation-by-parts identity proves the bound at every
natural cutoff, including 0 and 1. It is not an assumed variation estimate.
The actual Gaussian consumer now has the normalized signed main term;
the actual local-mean consumer is bounded by 4exp(1) times this Abel quantity
plus Cδ,ε(G log T+T^(1/4+ε)), eventually on
T^δ≤G≤T^(1/2-δ), G≥T^(1/4). The corresponding above-fourth-root
consumers have Cδ,κ G log T error when G≥T^(1/4+κ), κ>0.

The continuation below proves uniform variation of these actual weights
and the actual source-block bound. The newest continuation also proves
global dyadic assembly. The phase-sum/Gram estimate, source-form bridge,
and smaller-width error or a proved lower-value-range reduction remain required.
This is not the full sharp Atkinson theorem or the genuine twelfth moment.
EPZAE-21/37, every unconditional Add-est clause and the full goal remain OPEN.

Maintain these five root imports, all 30 named audits, all 24 regressions
and the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and execute
it and `run_lake_build.bat` after relevant changes. Preserve the original
counterexample byte-for-byte and the proved independent-coordinate
powering/Heath–Brown chain; never restore the false fifth-coordinate scaling.

## Damped main-weight variation and actual source blocks

Six additional production modules now close the uniform variation step:
`FiniteWeightVariation`, `AtkinsonGaussianVariation`,
`AtkinsonSaddleSamples`, `AtkinsonResidualVariation`,
`AtkinsonMainVariation` and `AtkinsonPhaseBlockBound`.
All 36 public theorems have named dependency audits; 24
`DampedWeightVariationRegression` examples check the actual objects,
both signs, empty blocks and closed physical boundaries.

`FiniteVariationBound f N M` records three proved inequalities:
M is nonnegative, every norm at indices 0 through N is at most M,
and the sum of adjacent norm differences over indices below N is at
most M. It is not an assumed zeta or exponential-sum estimate.
The generic product and ordered-sampling rules are applied to all four
factors of each actual normalized main weight.

For E(G,v)=exp(-(Gv)²/8), the actual complex Gaussian increment from
0≤a≤b is bounded by 2sqrt(pi) G (E(G,a)-E(G,b)).
The proof integrates the already proved actual derivative bound using
the exact real envelope primitive. The increasing saddle frequency
2arsinh(sqrt(pi n/(2T))) then gives a telescoping, damped variation bound.

The positive and negative normalized saddle roots are respectively
increasing and decreasing. On 10000(m+N)≤T their samples lie in [1/4,1],
where the actual Mellin profile has a constructed uniform Lipschitz bound.
Each original cutoff transition has variation at most one; their
product has variation at most two, independently of transition width.
The actual fourth-root coefficient is decreasing for positive indices.
These facts prove, for both separate weights Wplus and Wminus,

```text
sup_(0<=i<=N) |W(T,G,L,m+i)| <= B,
sum_(0<=i<N) |W(T,G,L,m+i+1)-W(T,G,L,m+i)| <= B,
B = C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)).
```

`exists_finiteVariationBound_atkinsonMainWeights` constructs one C>0
before T,G,L,m,N. Its range is T,G,L>0, G²≤2T, m>0 and
10000(m+N)≤T. No 8L≤G premise or equality of the two residual weights
is needed. The supremum and variation are each bounded by B; their
sum is not asserted to be at most B.

`atkinsonStationaryBlock` is the sum of the original stationary
Bessel/divisor terms at m through m+N-1. Let A(T,m,N) be the maximum,
over 0≤j≤N, of the norm of the actual raw positive-phase sum at
m through m+j-1. Finite partial summation, both separate weight bounds
and the exact common source phase prove

```text
|atkinsonStationaryBlock(T,G,L,m,N)|
  <= C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)) A(T,m,N).
```

`exists_atkinsonSourceCutoff_block_bound` is the actual-source consumer.
For each δ>0 it derives all preceding scale hypotheses beyond one
threshold T₀≥40000, from T^δ≤G≤T^(1/2-δ), L=log T,
m>0 and m+N≤atkinsonSourceCutoff(T,G,log T).
In particular, it consumes the proved eventual smallness of that exact
ceiling cutoff; small-frequency geometry is no longer a premise here.
This block theorem applies throughout the original power-width range.
It does not alter the earlier stationary-error estimate, which still
requires G≥T^(1/4).

The next continuation now assembles the complete source with a faithful
finite dyadic partition and a truncated last block below the same cutoff.
The required maximal phase-sum/Gram estimate remains open.
A maximum of partial sums is not silently identified with Ivić's
endpoint-plus-integral expression. Smaller-width stationary errors or a
genuine lower-value-range reduction also remain required.
The sharp full-width Atkinson theorem, critical twelfth moment,
EPZAE-21/37, every unconditional Add-est clause and the full
EPZAE-00--41 goal remain OPEN. ZVB is green only for the proved variation
and actual source-block consumer.

Maintain all six root imports, 36 named audits, 24 regressions and the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed; execute
it and `run_lake_build.bat` after relevant changes.
Preserve the original Lemma 62 counterexample byte-for-byte and the
proved independent ρ/k and ρ*/k witnesses with their actual Heath–Brown
application. Never restore false fifth-coordinate scaling or a third
s-preserving witness.

## Complete dyadic source assembly and physical zeta consumers

Three production modules, `TruncatedDyadicPartition`,
`AtkinsonDyadicMain` and `AtkinsonDyadicZetaConsumer`, now have
20 named public theorem audits and 24 semantic regressions.
They consume the previously proved actual block estimates rather than
assuming a bound for an abstract main sum.

For a natural cutoff N, block j starts at M=2^j and has length
min(M,N-M). The index range is j<clog(2,N), the natural ceiling
logarithm. Every retained block has positive length, starts strictly
below N and ends at or before N. At an exact power of two the last
block is full and no extra empty block is retained. The zero and one
cutoffs have no blocks.

`sum_range_eq_truncatedDyadic` proves the exact partition for every
additive sequence whose zero coefficient vanishes. The induction first
partitions a prefix ending at min(N,2^J); it never extends the source
to a larger power-of-two cutoff.
`atkinsonStationaryLeadingFiniteSum_eq_dyadic` applies that theorem
to the original stationary Bessel/divisor terms and their proved zero
coefficient. Both signs and their separate weights remain in each block.

Define A(T,M,K) as the maximum of the actual raw phase-prefix norms
on indices M through M+K-1. The complete stationary series is bounded
by C G T^(-1/4) times

```text
D(T,G,N) = sum_(j<clog(2,N))
  M^(-1/4) exp(-G²M/(12T)) A(T,M,min(M,N-M)),  M=2^j.
```

`exists_norm_atkinsonStationarySum_le_dyadic` sets
N=atkinsonSourceCutoff(T,G,log T), consumes the actual finite-support
identity and source-cutoff block theorem, and derives all support and
width hypotheses from T^δ≤G≤T^(1/2-δ), eventually for each δ>0.
Its constant and threshold precede T and G. This stationary-main bound
does not require G≥T^(1/4).

For later height estimates, `atkinsonPhaseBlockMax_mono` proves that
each shortened last-block phase maximum may be enlarged to A(T,M,M).
Only the raw phase maximum is enlarged: no stationary term, cutoff
support or small-frequency estimate is applied beyond N.
The resulting full-block sum is `atkinsonFullDyadicPhaseBound`,
denoted Dfull below. The public complete-series consumer
`exists_norm_atkinsonStationarySum_le_fullDyadic` proves the same
bound with Dfull in place of D.

Four physical consumers now apply this complete-series estimate to the
actual Gaussian and local zeta means. For both
I=integral_R exp(-((t-T)/G)²)|zeta(1/2+it)|² dt and
I=integral_(T-G)^(T+G)|zeta(1/2+it)|² dt, they prove

```text
I <= C_(delta,epsilon) [
  G T^(-1/4) Dfull(T,G,atkinsonSourceCutoff(T,G,log T))
  + G log T + T^(1/4+epsilon)],
```

eventually on the original power-width range with G≥T^(1/4).
Their `above_fourthRoot` versions replace the last two terms by
G log T when G≥T^(1/4+κ), κ>0. The original source factors are
absorbed into a uniform positive C, not dropped. The Gaussian theorem
is an upper bound, not an approximation identity after discarding
the main term's sign.

ZDA is green for exact dyadic assembly and these actual physical
consumers only. The continuation below proves finite Gram duality with
height-dependent maximizing prefixes directly on [M,M+j), and its
actual physical consumers. Uniform truncated phase-difference estimates
and separated-height summation remain open. The adjacent common-prefix
theorem on (K,2K] is not imported; any reuse of its analytic estimates
still requires the correct endpoint/general-prefix bridge.
A maximum of raw phase prefixes
is still not identified with Ivić's endpoint-plus-integral expression.
Smaller-width stationary errors or a proved lower-value-range reduction
remain required as well. The genuine critical twelfth moment,
EPZAE-21/37, all unconditional Add-est clauses and the full
EPZAE-00--41 goal remain OPEN.

Maintain all three root imports, 20 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and run
it and `run_lake_build.bat` after relevant changes.
Preserve the Lemma 62 counterexample byte-for-byte and the proved
independent ρ/k and ρ*/k witnesses and actual Heath–Brown application.
No false fifth-coordinate scaling or third s-preserving witness returns.

## Actual height-dependent maximal Gram consumers

The eight production modules are `FinitePrefixGram`,
`AtkinsonPrefixVectors`, `AtkinsonMaximalGram`,
`AtkinsonCoefficientEnergy`, `AtkinsonDyadicGramBudget`,
`AtkinsonPacketGram`, `AtkinsonLocalMeanGram` and
`AtkinsonGramPhysicalCutoff`. All 41 public theorems have named
axiom audits; 24 regressions cover the real objects and final signatures.

Let f(t,n) be the already proved actual source phase in radians,
A(t,M,N) the actual raw phase-prefix maximum, and

```text
E(M,N) = sum_(i<N) |d(M+i)|²,
Q(M,j;t,u) = sum_(i<j) exp(i [f(u,M+i)-f(t,M+i)]),
B(M,N;t,u) = max_(0<=j<=N) |Q(M,j;t,u)|.
```

The coefficient is the actual d(n)(-1)^n. Its sign cancels in its
squared norm. Each height t separately attains its maximum at j(t)≤N.
The exact vector inner product is Q(M,min(j(t),j(u));t,u), not
Q(M,N;t,u). Zero prefixes, unequal prefixes and both height orders
are covered. The direct masking proof uses [M,M+j), with no appeal
to the adjacent common-prefix theorem on (K,2K].

`sum_atkinsonPhaseBlockMax_sq_le_selectedGram` first proves the
inequality with these actual selected pairwise prefixes.
`sum_atkinsonPhaseBlockMax_sq_le_gramMax` then proves, for every
finite W,

```text
(sum_(t in W) A(t,M,N))² <= E(M,N) sum_(t,u in W) B(M,N;t,u).
```

No spacing or analytic Gram estimate is a premise.
B(M,N;t,t)=N is proved exactly; B is symmetric and nonnegative.
The separate `exists_atkinsonBlockCoefficientEnergy_le` theorem
uses the native ordinary-divisor bound at ε/2 to prove, uniformly
for 0<M and N≤M, E(M,N)≤Cε M^(1+ε).
Its block-level consumer is also proved. This is an epsilon-power
estimate, not a claimed M log³M bound.

For J=clog(2,N), define the literal nonnegative budget

```text
Gamma(N,W) = J sum_(j<J)
  (M^(-1/4))² E(M,M) sum_(t,u in W) B(M,M;t,u),  M=2^j.
```

The damped full-dyadic source majorant is bounded by the undamped
sum U(t,N)=sum_(j<J) M^(-1/4) A(t,M,M).
Finite Cauchy–Schwarz in j consumes the actual maximal Gram theorem:
(sum_(t in W) U(t,N))²≤Gamma(N,W). The Gaussian is removed by an
upper bound, not an identity. Gamma still uses literal E; the separate
epsilon-energy theorem is substituted in the later numerical budget below.

The source-cutoff maximum over W is derived, not supplied as a premise.
For H≥1, G>0 and W contained in [H,2H], monotonicity of the actual
ceiling cutoff proves

```text
max_(t in W) atkinsonSourceCutoff(t,G,log t)
 <= atkinsonSourceCutoff(2H,G,log(2H))
  = ceil(72H(log(2H)/G)²).
```

Only nonnegative phase/Gram majorants are enlarged; no stationary
term is extended beyond its own source cutoff.

`exists_atkinsonStationaryPacket_sq_le_physicalGram` consumes the
complete actual stationary Bessel/divisor sum S(t,G,log t) and proves

```text
(sum_(t in W) |S(t,G,log t)|)²
 <= Cδ G² H^(-1/2) Gamma(ceil(72H(log(2H)/G)²),W).
```

For every δ>0 its Cδ>0 and H0≥40000 precede H,G,W. The hypotheses
are H0≤H, G>0, H≤t≤2H and t^δ≤G≤t^(1/2-δ) for each t in W.
There is no fourth-root-width restriction for this stationary-only bound.

The final two `exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram`
theorems consume the actual local zeta integral
I(t,G)=integral_(t-G)^(t+G)|zeta(1/2+iv)|² dv.
They bound the square of the sum of max(0,I(t,G)-error) by the same
physical Gamma expression with a uniform positive factor D.
For δ,ε>0 the error is Cδ,ε(G log t+t^(1/4+ε)) and G≥t^(1/4)
remains required. The `above_fourthRoot` version has error
Cδ,κ G log t for κ>0 and G≥t^(1/4+κ). All constants and thresholds
precede the physical parameters. The original local-source factor
2 exp(1) is retained in the deduction and absorbed into D.

ZMG is green for this finite maximal-prefix argument and its actual
stationary/local-excess consumers. The continuation below proves
uniform cancellation for every truncated Q(M,j;t,u), derives the full
mean-value endpoint geometry at the physical cutoff and substitutes
the arithmetic coefficient-energy bound. ZPC records those actual
numerical consumers. ZGB retains separated-height summation and scale
optimization as open. No full-block estimate is substituted for an
unknown prefix.

The raw maximum is still not identified with Ivić's endpoint-plus-integral
expression. The source-form bridge, smaller-width stationary errors or
a proved lower-value-range reduction, and the genuine critical twelfth
moment remain open. EPZAE-21/37, every unconditional Add-est clause and
the full EPZAE-00--41 goal remain OPEN; this checkpoint does not narrow
their acceptance tests.

Maintain all eight root imports, 41 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and
execute it and `run_lake_build.bat` after relevant changes.
Preserve the Lemma 62 counterexample byte-for-byte and the proved
independent ρ/k and ρ*/k witnesses and actual Heath–Brown application.
Never restore false fifth-coordinate scaling or a third s-preserving
witness. Keep the full goal active until all original completion tests pass.

## Uniform truncated phase cancellation and arithmetic gap packets

Thirteen modules add 79 named public theorem audits and 30 regressions:
`AtkinsonIndexPhase`, `AtkinsonIndexCurvature`,
`AtkinsonIndexHeight`, `AtkinsonIndexScales`,
`AtkinsonIndexBProcess`, `AtkinsonIndexFirstDerivative`,
`AtkinsonPrefixCancellation`, `AtkinsonPrefixGapBound`,
`AtkinsonGramCutoffGeometry`, `AtkinsonGapBudget`,
`AtkinsonGapPacketConsumers`, `AtkinsonGapArithmetic` and
`AtkinsonArithmeticGapPackets`.

The first six adapt the inspected adjacent real-index proofs locally.
The real phase restricts exactly to the already connected
`atkinsonSourcePhase`; there is no new source-entry assumption or
adjacent conditional moment import. For T,x>0 its first derivative is
sqrt(2πT/x+π²), and its second derivative is
-πT/[x² sqrt(2πT/x+π²)]. The height derivative of the positive
curvature magnitude and two mean-value arguments derive the literal
uniform increment and second-difference bounds.

For ordered heights 0<u<t≤2u, M>0 and M+N+2≤u, put
Δ=t-u, B=M+N+2, D=M+N+1 and

```text
sMinus(u,x) = sqrt(2*pi*u/x),
sPlus(u,x)  = sqrt((2*pi+pi²)*2*u/x),
lambda     = pi*Delta/(2*B²*sPlus(u,M)),
Lambda     = pi*Delta/(M²*sMinus(u,B)),
L          = pi*Delta/(D*sPlus(u,M)),
U          = pi*Delta/(M*sMinus(u,D)).
```

Both curvature parameters are positive and are proved bounds for the
actual phase differences. For every j≤N,

```text
|Q(M,j;t,u)| <= (N*Lambda/(2*pi)+2) *
  (2*pi/sqrt(lambda)+2*(sqrt(lambda)/lambda+1)).
```

`norm_atkinsonPrefixGram_le_bProcess` applies the native B-process
to the restricted actual second-difference bounds. Its full ambient
M,N parameters are independent of j. The empty prefix is included.
The same argument bounds the maximum over all j≤N.

When U≤π, `norm_atkinsonPrefixGram_le_firstDerivative` proves
|Q(M,j;t,u)|≤2π/L=2D sPlus(u,M)/Δ. The positive-slope orientation is
the conjugate Gram entry; its exact conjugacy and decreasing unit
increments are proved. The period-endpoint conditions are derived
from the actual lower/upper slope scales, not assumed as a cancellation
theorem.

Let F(M,N;t,u)=`atkinsonPrefixGapMajorant M N t u`. On the diagonal
F=N exactly. Off the diagonal, the larger height is placed first.
F is the minimum of N and the B-process bound; when U≤π it also
takes the minimum with the first-derivative bound. The triangle bound,
both cancellation alternatives, symmetry and the bound for every
actual truncated Gram entry are proved. F is a literal numerical
expression, not a new name for the unevaluated phase maximum.

The required endpoint geometry is now derived at the physical cutoff.
For δ>0, eventually and uniformly for H^δ≤G,

```text
2*atkinsonSourceCutoff(2H,G,log(2H))+2 <= H.
```

The proof uses (2H)^(δ/2)≤H^δ for H≥2 and the earlier source-ceiling
smallness theorem at exponent δ/2. Therefore every M=2^j with
j<clog(2,atkinsonSourceCutoff(2H,G,log(2H))) has
M+M+2≤H. If t,u belong to [H,2H], the positivity and dyadic height
conditions also follow. No free endpoint or curvature hypothesis
remains in the final physical consumer.

`exists_atkinsonPhysicalGramBudget_le_gapBudget` replaces every
actual Gram maximum by F. It derives H^δ≤G from any member of a
nonempty actual packet satisfying t^δ≤G; the empty packet is proved
separately. No artificial nonemptiness or extra width assumption is
introduced into the source theorem.

The next arithmetic step consumes the already proved ordinary-divisor
energy bound, rather than merely citing it nearby. For η>0,
`exists_atkinsonPhysicalGapBudget_le_arithmetic` replaces the
coefficient-energy sum in every block. The identity
(M^(-1/4))² M^(1+η)=M^(1/2+η) supplies the exact final weight.
Define the fully numerical budget, J=clog(2,N),

```text
Psi(eta,N,W) = J sum_(j<J)
  M^(1/2+eta) sum_(t,u in W) F(M,M;t,u),  M=2^j.
```

`exists_atkinsonStationaryPacket_sq_le_arithmeticGap` proves

```text
(sum_(t in W) |S(t,G,log t)|)²
 <= C_(delta,eta) G² H^(-1/2) Psi(eta,ceil(72H(log(2H)/G)²),W).
```

Its C>0 and H0≥40000 precede H,G,W. It consumes the actual complete
stationary Bessel/divisor series, with H0≤H, G>0, H≤t≤2H and
t^δ≤G≤t^(1/2-δ) for every t in W. It has no fourth-root-width
restriction and no assumed analytic estimate.

The two `exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap`
consumers prove the analogous bound for the square of the sum of
max(0,I(t,G)-error), with I the actual local zeta-square integral.
The error remains Cδ,ε(G log t+t^(1/4+ε)) for G≥t^(1/4), or
Cδ,κ G log t for G≥t^(1/4+κ). Their constants and threshold precede
the physical parameters, and the source factor 2 exp(1) remains
accounted for through the earlier actual-source deduction.
The preceding three `physicalGap` consumers, retaining literal E,
are also proved and audited.

ZPC is green for these uniform truncated estimates, derived physical
geometry and actual numerical source consumers. ZGB remains OPEN:
sum the explicit gap expressions using physical height separation,
simplify their radical scales uniformly and optimize the resulting
height/index ranges. Psi's finite double sum does not itself estimate
separated-height occupancy. No such summation theorem is a premise
of the current result or is silently claimed as proved.

The source-form bridge, smaller-width stationary error or a proved
lower-value reduction, genuine critical twelfth moment and every
unconditional Add-est clause remain open. EPZAE-21/37 and the full
EPZAE-00--41 completion contract are unchanged.

Maintain all thirteen root imports, 79 named audits, 30 regressions
and the exact PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`. Update the batch interface and
its implementation as needed, and run it and `run_lake_build.bat`
after relevant changes. Preserve the original Lemma 62 counterexample
byte-for-byte and the proved independent ρ/k and ρ*/k witnesses and
actual Heath–Brown application. Never restore false fifth-coordinate
scaling or a third s-preserving witness. Keep the full goal active.

## Constructed covering and local-mean counts — preceding checkpoint

EPZAE-21 now proves a sixth-power superlevel counting estimate for
the actual critical-line local zeta integral. For every δ>0, ε>0
and ν>0 there are C,D>0 and H0≥40000, before H,G,Y,W, such that

```text
card {t in W : C*(G*log(t)+t^(1/4+ε)) + Y
                 <= integral_(t-G)^(t+G) |zeta(1/2+i*u)|^2 du}
 <= D*H^ν * (H/(G*Y^2) + H^2/Y^6).
```

The hypotheses are H≥H0, G>0, Y>0, G-separation of W, and for
each t in W, `H<=t<=2H`,
`t^δ<=G<=t^(1/2-δ)`, and `t^(1/4)<=G`.
The above-fourth-root version instead has error `C*G*log(t)`
and requires `t^(1/4+κ)<=G`, κ>0. All source restrictions
remain explicit. Both theorems count the literal integral's
superlevel set; no analytic packet estimate, prescribed covering,
absorption inequality or cardinality bound is a premise.

The preceding physical packet theorem remains installed:
the square of the sum of actual excesses is at most
`D0*H^a*(R*H/G+R^2*sqrt(G*L))`, with uniform constants
before the localization interval. Its cutoff/logarithmic optimization,
including the literal source ceiling and derived width bounds,
is unchanged.

The new deduction constructs the length and bins. Put
`A=D0*H^a` and `L=(Y^2/(4*A))^2/G`. Then L>0 and

```text
sqrt(G*L) = Y^2/(4*A)
2*A*sqrt(G*L) <= Y^2.
```

The bin of t is `floor((t-H)/L)`. Its actual fiber is contained
in `[H+k*L,H+(k+1)*L]`; the bins partition W for
`0<=k<floor(H/L)+1`. This includes the terminal height 2H,
even when H/L is integral. Separation and every original source
range are inherited by each fiber.

On a fiber whose actual excess is at least Y, the packet inequality
and the proved absorption give `R<=2*A*H/(G*Y^2)`.
Summing the exact fiber cardinalities and paying the final bin gives

```text
card(W) <= 2*A*H/(G*Y^2) + 32*A^3*H^2/Y^6.
```

Choosing the packet exponent a=ν/3 and absorbing constants yields
the displayed global estimate. The exact positive-threshold
equivalence between excess≥Y and integral≥error+Y is proved,
then used on the actual filtered superlevel set.

Four root-reachable modules are installed:
`AtkinsonCardinalityAbsorption`, `AtkinsonHeightCover`,
`AtkinsonGlobalCardinality` and `AtkinsonLocalMeanCounting`.
All 17 new public theorems have named audits. The 27 new regressions
cover every public theorem type, exact chosen-length arithmetic,
empty fibers, unit/terminal bins, zero threshold geometry and the
complete source-consumer signatures. Earlier work remains installed.

ZLC is complete for constructed covering, absorption and actual
local-mean superlevel counting. This is not yet a pointwise zeta
large-value count: the entry from point values to these local
integrals, a compatible physical width choice, an occupancy-preserving passage
from unit-separated points to G-separated local windows, and the
remaining value-range reduction are still required. ZGB, ZAT, the genuine
critical twelfth moment ZTM, all unconditional Add-est conclusions,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Preserve the original Lemma 62 counterexample byte-for-byte.
The corrected independent ρ/k and ρ*/k witnesses, independent
fifth coordinates and actual Heath–Brown application are unchanged.
Never restore false s-scaling or a third s-preserving witness.
Maintain and update `run_tao_trudgian_yang_build.bat` and its
backing implementation as needed; its exact inventory includes
all four new modules. Run it and `run_lake_build.bat` after
relevant changes. Keep the full goal active.

Semantic acceptance evidence:

- `atkinsonAbsorptionLength_radical` proves the exact physical
  square-root identity; `atkinsonAbsorptionLength_absorbs`
  discharges the needed numerical absorption. L is not a freely
  supplied scale left for a later argument.
- `atkinsonHeightFiber_interval` proves the translated location
  of each floor fiber, and `atkinsonHeightFiber_card_partition`
  supplies the exact finite partition including the last endpoint.
- `atkinson_card_le_of_local_packets` is an explicitly conditional
  reusable finite deduction. Its localized packet premise is narrower
  than the global count, and is not an unconditional source theorem.
- Both `exists_atkinsonLocalMeanExcess_card_le` versions discharge
  that premise with the actual `localizedPhysical` source theorem
  on every subset/fiber. They derive inherited separation, locations,
  widths and absorption rather than assuming these conclusions.
- Both `exists_atkinsonLocalMean_superlevel_card_le` versions
  use `atkinsonLocalMeanExcess_threshold_iff` to count the literal
  integral's filtered superlevel set. No pointwise-value or
  moment bound is hidden in the set's definition.

Next acceptance obligation: prove the pointwise critical-zeta
value-to-local-integral entry, choose a physical G compatible with
both the threshold and the retained fourth-root source range,
and handle the remaining lower-value range through a genuine source
or moment reduction. Then assemble the pointwise large-value count
and critical twelfth moment. The present integral superlevel bound
must not be relabeled as any of these still-open endpoints or as
an unconditional Add-est theorem.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions and linter
failures. The target audited 2,847 declarations (2,842 discovered
target theorems plus five imported contracts); all 27 new regressions
passed. Exact commands, logs, hashes and coverage are in the current
Reproduction Manifest. This verifies local-integral superlevel counting,
not pointwise zeta large values, the twelfth moment or Add-est.

## Point-entry kernels and literal zeta overlap — preceding checkpoint

The preserved Lemma 62 counterexample and the proved corrected two-witness
powering/Heath–Brown chain are unchanged. EPZAE-21 now additionally proves
the Gamma-kernel and bounded-overlap components needed for point-value entry.

For every 0<δ≤1/4 and a,b independently chosen from {δ,-δ}, the
literal product

```text
P(a,b,u,w) = |Gamma(a+i*w)| |Gamma(b+i*(u-w))|
```

is integrable in w, and a single absolute C>0 gives
`integral P <= (C/δ)*exp(-|u|)`. The public consumer
`exists_pointMeanGammaProduct_integral_le` derives integrability and
uses both proved shifted-Gamma bounds and the numerical convolution.
Its height-linked companion
`exists_pointMeanGammaProduct_log_integral_le` substitutes
δ=1/log(t), derives 0<δ≤1/4 from t≥exp(4), and proves
`integral P <= C*log(t)*exp(-|u|)`. Both displacement signs and
zero ordinate are retained; no Gamma or convolution estimate is assumed.

For a unit-separated finite W, the actual exponential kernels satisfy
`sum_(t in W) exp(-|t-u|) <= 4`. The moving-window consumer
`sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment` proves

```text
sum_(t in W) integral_(t-L)^(t+L)
  exp(-|t-u|) |zeta(1/2+i*u)|^2 du
 <= 4 * integral_(center-G)^(center+G) |zeta(1/2+i*u)|^2 du.
```

It assumes G,L≥0, W⊂[center-G/2,center+G/2],
G/2+L≤G and unit separation. It derives every interval enlargement
and finite integral interchange. The cost is the absolute factor four,
not the cluster occupancy or the physical width G.

The previously proved local-integral superlevel count remains:
`card <= D*H^ν*(H/(G*Y^2)+H^2/Y^6)`, with all original physical
width restrictions, actual source errors, positive thresholds and
uniform constant dependencies retained. This new overlap theorem does
not yet connect pointwise zeta largeness to that count.

Eight root-reachable modules are installed: `PointMeanDigamma`,
`PointMeanGammaShift`, `PointMeanGammaDecay`, `PointMeanGammaKernel`,
`PointMeanGammaConvolution`, `PointMeanExponentialOverlap`,
`PointMeanIntegralOverlap` and `PointMeanGammaProduct`.
All 38 public theorems have named audits; 46 new regressions cover
their exact types and shell endpoints, empty sets, zero ordinates,
and the negative displacement. Seven modules adapt inspected node-74
proofs to the existing target/native imports and actual
`zetaMomentCriticalNorm`; the eighth supplies new literal Gamma consumers.
No adjacent package, dependency pin, source archive, or frozen foundation
has been changed.

ZGK is complete only for the literal Gamma convolution and its
height-linked logarithmic bound. ZEO is complete only for the actual
exponential local-integral overlap. The complete contour proof of
Heath–Brown Lemma 3 is NOT yet installed in this target. Its residue,
displaced zeta bounds, horizontal edges, truncated tail and compact range
remain to be assembled. Pointwise large-value counting also still needs
occupancy-aware clustering, compatible G selection and the lower-value
reduction. ZGB, ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and the full
EPZAE-00–41 completion contract remain OPEN.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte. Never restore
false s-scaling or a third s-preserving witness. The independent ρ/k and
ρ*/k witnesses and actual Heath–Brown application remain intact.
Maintain and update `run_tao_trudgian_yang_build.bat` and its backing
implementation as needed, including all eight modules in the exact
inventory. Run it and `run_lake_build.bat` after relevant changes.
Keep the full goal active.

Semantic acceptance and next analytic input:

- The coefficient-one real-part digamma estimate comes from the actual
  convergent series. Gronwall and Gamma reflection give exponential decay;
  recurrence gives both displaced lines without dropping δ+|v|.
- The stronger rate 4/3 leaves an exponential reserve. Its square is
  bounded by 1/(δ²+x²), whose integral is π/δ. The subsequent
  `pointMeanGammaProduct` consumer applies this to the actual Gamma
  functions, rather than claiming a numerical majorant alone is a source theorem.
- The overlap proof constructs integer distance shells, proves at most
  two points per shell using unit separation, and sums a geometric series.
  The final specialization consumes the literal continuous zeta-square integrand.
- The next source target is the actual weighted Lemma 3 inequality
  `|zeta(1/2+i*t)|² <= C*log(t)*(1+integral_(-log²t)^(log²t)
  exp(-|u|)*|zeta(1/2+i*(t+u))|² du)`, for every t≥10.
  The adjacent `HeathBrownLemmaThreeTail` and
  `HeathBrownEquation44Native` contain proved consumers, but they are
  NOT imports of this package and their conclusions are not yet target theorems.
  Narrow their Mellin/contour prerequisites onto the current native foundation,
  then assemble the residue and all analytic errors without a Lemma-3 hypothesis.
- After that entry is proved, use the installed overlap to keep cluster
  multiplicities when moving to G-separated windows. Merely thinning the
  unit-separated points loses a factor G and does not meet acceptance.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions or linter
failures. The target audited 2,890 declarations (2,885 discovered
target theorems plus five imported contracts); all 46 new regressions
passed. The foundation audit covered 14,290 declarations and its
manifest reports PASS with no failed stages. Exact logs and hashes
are in the current Reproduction Manifest. This verifies the Gamma
and overlap components, not the still-open pointwise zeta entry,
twelfth moment or unconditional Add-est.

## Heath–Brown point-to-local-mean entry — historical checkpoint

The original Lemma 62 counterexample is preserved byte-for-byte. The corrected
independent cardinality and energy witnesses, and their proved Heath–Brown
application, are unchanged. This checkpoint closes an analytic input to the
remaining zeta/Add-est branch; it does not change the frozen public outputs.

`heathBrownLemmaThree_native` now proves the complete source-shaped estimate:
one absolute C>0 works for every t≥10,

```text
|zeta(1/2+i*t)|^2
 <= C*log(t)*(1 + integral_(-log(t)^2)^(log(t)^2)
      exp(-|u|)*|zeta(1/2+i*(t+u))|^2 du).
```

The proposition and moment definitions unfold to this literal integral.
The proof derives the smoothed divisor Mellin identity, both pole residues,
the infinite shifts, both displaced-line estimates, the finite rectangle's
four edge bounds, the full-to-truncated tail estimate and the compact range.
The strong Gamma reserve makes the nested integral lose only δ⁻¹;
δ=1/log(t) is linked to the source height. None of these estimates is an
analytic hypothesis of the final theorem.

`heathBrown_equation44_native` consumes that theorem and the actual
factor-four exponential-overlap theorem. For R=card(W) it proves

```text
V^2*R <= C*log(T)*(R + 4*integral_(center-G)^(center+G)
                                  |zeta(1/2+i*u)|^2 du).
```

Here T≥10, V>0, G,L≥0; W is unit-separated and contained in
[center-G/2,center+G/2]⊂[10,T]; every t∈W has log(t)^2≤L;
G/2+L≤G; and every t∈W satisfies V≤|zeta(1/2+i*t)|.
All parameters follow the absolute constant. The final consumer has no
Lemma-3 hypothesis and does not discard cluster occupancy.

Nineteen additional production modules are root-reachable and included in
the exact inventory behind `run_tao_trudgian_yang_build.bat`.
There are 129 new public theorem audits and 136 new regressions, including
the unfolded literal source inequality and the endpoints t=10 and t=exp(4).
The adjacent node-74 proof bodies were inspected and adapted to existing
target/native imports; unrelated import chains were not added. No package
pin, source archive, counterexample or adjacent project was changed.

ZL3 is complete for the full source Lemma 3; ZQ44 is complete for its
literal finite peak-to-local-integral consumer. ZGB still needs constructed
occupancy-aware clusters, compatible physical width selection, absorption
of the actual local-source error, and the remaining value ranges.
The installed local-integral superlevel count still has its original
fourth-root width restrictions. ZAT, ZTM, unconditional Add-est,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Keep the complete goal active. Preserve `EnergyPoweringObstruction.lean`
and the independent fifth coordinates; never reintroduce false s-scaling
or a third s-preserving witness. Maintain the principal
`run_tao_trudgian_yang_build.bat`, its backing implementation, root imports,
exact inventory, audits and regressions as the proof grows. After relevant
changes, run both it and the foundation's `run_lake_build.bat`.

### Exact dependency and next-obligation audit

- `heathBrown_smoothed_divisor_eq_right_mellin` proves actual summation/integration
  interchange from absolute convergence and exponential Mellin inversion.
- `heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical` consumes
  the two proved pole shifts. The moving double pole is 1-s; the Gamma pole
  is 0. The residue constants and retained line are subsequently bounded.
- `exists_heathBrown_offCritical_plus_strong_le` and its reflected minus
  companion use the actual zeta square and convergent critical-line moment.
  Functional reflection uses the pinned GammaR equation and conjugation.
- `integral_strongKernel_mul_strongMoment_le` proves product-space
  integrability, translation and Fubini with the π/δ bound. The finite
  source rectangle then yields the full weighted moment with only log(t).
- `exists_heathBrownFullCriticalMoment_le_truncated` pays the complete tail
  at log(t)^2. `heathBrownLemmaThree_native` absorbs its constant and
  derives the remaining compact t≥10 range from continuity.
- `heathBrown_equation44_of_lemmaThree` is intentionally a conditional
  finite deduction. `heathBrown_equation44_native` explicitly discharges
  that premise using the new full theorem and retains the literal integral.
- Next construct G-separated centers with the original point multiplicities.
  Choose G in the existing Atkinson source range, derive a local-integral
  excess threshold from each cluster's equation-(44) bound, and apply
  `exists_atkinsonLocalMean_superlevel_card_le` (or its
  `above_fourthRoot` form) with every source error and width condition paid.
  Preserve and sum occupancy classes; thinning points without their
  multiplicities is not an acceptable bridge.
- The lower-value reduction and any upper-value exclusion must use proved
  genuine zeta estimates. Assemble the actual dyadic critical twelfth moment
  before consuming the existing moment-to-LV/energy transfers. Do not replace
  it with a new moment hypothesis or mark Add-est complete from the point-entry
  theorem alone. All other open EPZAE tasks remain part of the full goal.

Verification (2026-09-21): both principal scripts were polled to terminal
exit 0. The target reports `LEAN VERIFICATION PASS`, covering all 299
package files and 3,104 audited declarations (3,099 discovered target
theorems plus five imported contracts). All 129 new named audits and
136 new regressions pass. The foundation reports `PASS`, with 14,290
discovered theorems audited and all six stages passed. Neither final
evaluation has a Lean error, warning, tactic suggestion or linter failure.
Exact logs, hashes and the repaired intermediate comment-scan failure are
recorded in the current Reproduction Manifest. The counterexample hash is
unchanged. This verifies Lemma 3 and the finite point-entry consumer;
occupancy-aware counting, the genuine twelfth moment, unconditional Add-est
and the full goal remain open.

## Occupancy-preserving peak count and derived growth — historical checkpoint

The printed Lemma 62 counterexample is still byte-preserved. The proved
corrected two-witness powering, independent fifth coordinates and actual
Heath–Brown energy application are unchanged.

Three additional EPZAE-21 consumers are now proved:

- `exists_pointValue_card_le_with_width` counts the original unit-separated
  zeta peaks, retaining every cluster occupancy. Half-G floor bins keep
  occupied centers in [H,2H], including the terminal endpoint. Both parity
  classes are G-separated. The actual equation-(44) entry and Atkinson
  excess count bound each occupancy superlevel; exact layer-cake summation
  and the inverse-square sum recover all points with no factor G loss.
- `exists_pointValue_card_le_source_range` constructs
  G=V²/(K log(3H)²), absorbs the actual source error and derives all window
  and width conditions. For δ,κ,ν>0 with δ≤1/4, there are K,D>0 and H₀≥40000,
  chosen before H,V,W, such that for H≥H₀ and V>0,
  `K log(3H)² (2H)^(1/4+κ) ≤ V² ≤ K log(3H)² H^(1/2−δ)`,
  every unit-separated W⊂[H,2H] with |ζ(1/2+it)|≥V satisfies
  `card(W) ≤ D H^ν (H log(3H)^4/V^6 + H² log(3H)^6/V^12)`.
  The fourth-root margin is retained, not removed.
- `exists_zetaMomentCriticalNorm_lt_sixth_power` proves that for every ε>0
  there is H₀≥40000 such that H≥H₀ and H≤t≤2H imply
  |ζ(1/2+it)|<H^(1/6+ε). A singleton peak at H^(1/6+η),
  η=min(ε,1/48), satisfies the proved source range but its cardinality bound
  is eventually less than one. This derives the actual zeta growth estimate;
  it does not assume one or substitute a Dirichlet-block estimate.

The six modules `FiniteOccupancy`, `PointClusters`, `PointClusterEntry`,
`PointClusterCounting`, `PointValueWidth` and `PointValueGrowth` are covered
by the root and exact production inventory. Their 29 public theorems have
named audits, and 37 added regressions check every public type plus actual
endpoints, occupancy, parity and the unfolded zeta-growth conclusion.

Architecture nodes ZOC, ZVW and ZPG record these exact consumers as DONE.
ZGB remains OPEN for the remaining value-range reductions and their
moment-ready aggregation. ZAT's smaller-width/source-form bridge, the genuine
dyadic twelfth moment ZTM, all unconditional Add-est clauses, EPZAE-19/21/37
and the full EPZAE-00–41 goal remain OPEN. This critical-line growth result
does not complete the distinct exponent-pair-to-mu contract EPZAE-15.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation as
needed: root imports, exact inventory, named/exhaustive audits and regressions
must grow together. Run both principal scripts after relevant changes.
Preserve the counterexample and do not restore false s-scaling or a third
s-preserving witness. No dependency pin, source archive or adjacent proof
was changed in this checkpoint.

### Consumer audit and remaining analytic work

The constructed centers are cₙ=H+nG/2. An occupied fiber inherits unit
separation and the original peak threshold. Its points lie in
[cₙ−G/2,cₙ+G/2]; equation (44) is applied with T=3H and
L=log(3H)². The global assumptions G≤H and 2log(3H)²≤G derive
the entire interval and logarithmic-window entry.

For A=V²/(16P log(3H)), the proved peak-mass absorption gives
I(cₙ,G)≥2RₙA. If Rₙ≥m≥1 and the true local error is at most A,
then I(cₙ,G)≥error+mA. Each parity image is injective and G-separated.
The actual source count gives m⁻² and m⁻⁶ superlevel decay, and
`sum_nat_occupancy_eq_sum_superlevel` recovers ΣRₙ=card(W).
Both colors and Σm≥1 m⁻²≤2 are paid in the final constant; neither
maximal occupancy nor a thinning loss appears.

The selected K=16PC+1 makes the actual C G log(cₙ) error at most A.
The amplitude interval derives t^δ≤G≤t^(1/2−δ) and
t^(1/4+κ)≤G for every t∈[H,2H]. No local-mean source estimate,
point-entry theorem, cluster existence or window condition remains as
an analytic hypothesis of the selected-width consumer.

At V=H^(1/6+η), the count simplifies exactly to
D log(3H)^4/H^(5η) + D log(3H)^6/H^(11η).
Positive exponent gaps absorb the logarithms. The singleton contradiction
proves growth directly from the actual local-zeta chain and works at both
closed height endpoints.

Next use this derived growth to control the upper value range and
the first term of the peak count; derive the remaining low-value estimate
from genuine zeta moment inputs. Construct the finite-to-continuous
aggregation with all interval endpoints and separation colors accounted
for, then prove the actual dyadic critical twelfth moment. Only that theorem
can discharge the moment premise of `zetaTwelfth_largeValueBound_of_dyadic`
and `energyClauseOne_of_dyadic_moment`. Their existing conditional proofs
are not evidence that the moment has already been proved.

Continue the full frozen public contract, not a replacement goal consisting
only of these supporting results. All other open EPZAE tasks remain required.

Verification (2026-09-21): both principal runners reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 305 package files, 316 Lean
files in its integrity scan, 3,187 audited declarations (3,182 discovered
target theorems plus five imported contracts), all 29 new named audits and
all 37 added regressions passed. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final evaluations
have zero Lean errors, warnings, tactic suggestions or linter failures.
The counterexample SHA256 is unchanged. Exact logs, hashes and repaired
focused-build diagnostics are recorded in the current Reproduction Manifest.
This verifies the occupancy/width consumers and actual critical-line growth,
not the genuine twelfth moment, unconditional Add-est or the full goal.

## High-value twelfth moment and fourth-moment reduction — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. Corrected
cardinality/energy powering, the independent ρ/k and ρ*/k witnesses with
independent fifth exponents, and the actual Heath–Brown energy application
remain unchanged.

The following actual-zeta consumers are now proved. Write
S(H,V)={t∈[H,2H] : |ζ(1/2+it)|≥V}. For every ε>0 and sufficiently large H,
uniformly for V≥H^(1/8+ε):

- `exists_pointValue_twelfth_weighted_card_le` gives
  card(W) V^12≤H^(2+ε) for every unit-separated W⊂S(H,V).
  There is no upper-amplitude hypothesis: the proved actual growth estimate
  controls that range, and the source-width and logarithmic margins are paid.
- `exists_volume_pointValueSuperlevel_le` gives
  volume(S(H,V))≤2H^(2+ε)/V^12. A maximal finite separated family is
  constructed from the proved cardinality bound; its closed unit balls
  cover the entire superlevel set, with the factor two accounted for.
- `exists_zeta_twelfth_high_integral_le` proves
  integral over S(H,H^(1/8+ε)) of |ζ(1/2+it)|^12≤H^(2+ε).
  The actual measure bound, actual height-cube bound for |ζ|^12 and exact
  logarithmic layer-cake integral are composed without analytic hypotheses.

`zeta_twelfth_integral_le_high_add_fourth` proves the exact low/high
reduction: the full twelfth moment on [H,2H] is at most the high-set
integral plus V^8 times the unweighted fourth moment on [H,2H].
`zeta_twelfth_dyadic_of_fourth` performs the full deduction but is
explicitly CONDITIONAL on the genuine upstream estimate

```text
for every η>0 there exist C≥0 and H₀, chosen before H, such that
H≥H₀ and H>0 imply integral_H^(2H) |ζ(1/2+it)|^4 dt ≤ C H^(1+η).
```

That unweighted fourth-moment instance is still OPEN. The foundation's
`twistedZetaFourthMoment_native` instead bounds the fourth power of a
short Möbius polynomial multiplied by ζ; its factor cannot simply be
removed. No mollified result is claimed to prove the unweighted estimate.

The six modules `PointValueRanges`, `PointValueMeasure`,
`TruncatedLayerCake`, `PointValueTailIntegral`,
`PointValueHighMoment` and `PointValueLowMoment` are in the root and exact
production inventory. All 24 public theorems have named audits; 30 new
regressions cover their exact signatures, boundary cases and the literal
high-value zeta integral. ZHR/ZHM and the reduction ZLF are DONE; ZGB now
identifies the missing genuine fourth-moment source theorem. ZTM, ZAT,
EPZAE-19/21/37, unconditional Add-est and the full EPZAE-00–41 goal remain OPEN.
No other frozen public output or acceptance test is weakened.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed, including root imports, exact module coverage, named/exhaustive
audits and regressions. Run both principal scripts after relevant changes.
Preserve the counterexample, never restore false s-scaling or a third
s-preserving witness, and keep the full goal active. No source pin,
archive or adjacent/native proof was changed in this checkpoint.

### Proof and source audit for this checkpoint

The counting consumer chooses η=min(ε/16,1/1000), retaining the proved
fourth-root source margin. For nonempty W the actual growth bound gives
V≤H^(1/6+η); the two weighted count terms become
D log(3H)^4 H^(2+7η) and D log(3H)^6 H^(2+η).
All logarithms are absorbed using positive exponent gaps; W=∅ is handled
explicitly. The cardinality-to-measure proof maximizes finite cardinalities
in a bounded finite set of naturals and extends an allegedly non-covering
family by one point. It assumes no compactness or covering theorem that
already contains the desired measure conclusion.

`TruncatedLayerCake` uses the pinned Mathlib
`Integrable.integral_eq_integral_Ioc_meas_le` and proves
integral_0^M C/max(A,t) dt=C(1+log(M/A)) for 0<A≤M.
The actual restricted measure tail at s is at most C/max(V^12,s);
the positive twelfth root converts the upper branch to a zeta superlevel.
The terminal high-set theorem takes η=min(ε/2,1/100), uses the proved
|ζ|^12≤H^3, and absorbs the remaining logarithm. Every actual point of
the measurable superlevel set is included; there is no thinning or
unproved finite-to-continuous aggregation.

The low-set theorem needs no assumption V>0: if that set is nonempty,
its actual nonnegative norm is less than V. The proof derives
|ζ|^12≤V^8|ζ|^4 there and integrates over the actual interval complement.
The full conditional theorem exposes every quantifier of the remaining
fourth-moment estimate.

No external source revision was added. The Mathlib layer-cake, interval
integration and real-power APIs and the local actual-zeta source chain
were inspected directly at the existing pins. The foundation's
`twistedZetaMomentIntegrand` is
|shortMobiusPolynomial · ζ|^4, not |ζ|^4; the distinction remains explicit
in the source obligation and audit.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 311 package files, 322 Lean
files in its integrity scan, 3,232 audited declarations (3,227 discovered
target theorems plus five imported contracts). All 24 new named audits
and all 30 added regressions pass. The foundation reports `PASS`: all six
stages passed, with 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample SHA256 is unchanged; source and runner hashes
were rechecked after both gates. Exact logs, hashes and repaired focused
diagnostics are in the current Reproduction Manifest. These gates verify
the high-value bound and explicitly conditional fourth-moment deduction,
not the missing fourth-moment instance, unconditional Add-est or full goal.

## Actual fourth-moment contour bounds and mixed-line truncation — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. The
authorized corrected cardinality/energy powering, independent ρ/k and
ρ*/k witnesses (with independent fifth exponents), and actual Heath–Brown
energy application remain unchanged. False s-scaling is not restored.

The new source is genuinely unweighted zeta. Write
J(t)=zetaSquareDivisorIntegral(-t)/zetaSquareGammaNormalization(t).
`zetaSquareNorm_eq_two_re_fourthRightPiece` proves
|ζ(1/2+it)|²=2 Re J(t), and `zeta_fourth_le_four_mul_rightPiece_sq`
proves |ζ|⁴≤4|J|². The actual Gamma quotient and pole factors are retained;
the native mollified fourth-moment theorem is not substituted.

`exists_norm_zetaFourthKernel_le` proves, for each c>0, a constant K_c>0
chosen before t and u such that t≥4 and t≥4c imply
|K(t,c+iu)|≤K_c t^c exp(-98u²) on the complete line. Near-height
Gronwall bounds and far-height Gamma bounds are both consumed.
A separate, height-dependent strip bound justifies holomorphy,
integrability and disappearing horizontal sides; it is not advertised
as the uniform moment bound.

`zetaFourthContribution_line_eq` proves equality of each actual
integrated ordinary-divisor contribution on any two positive lines.
`hasSum_zetaFourthContribution` transports the convergent integrated
series from c=1. This does NOT assert pointwise Dirichlet-series
convergence to the left of its half-plane.

For t≥0, a,b>0 and any finite S, the actual source now satisfies
J(t)=Prefix(t,a,S)+Tail(t,b,S). The prefix is proved equal to the
integral of the finite ordinary-divisor polynomial times the actual kernel.
For b>3/2, one constant K_b>0 works for all t≥max(4,4b) and all S:
|Tail|≤K_b t^b Σ_(n∉S) d(n)n^(-1/2-b).
The displayed positive tail is summable, not an assumed small error.
`exists_zeta_fourth_le_prefix_add_weightTail` consumes these results
to bound the literal |ζ|⁴ by eight times the squared prefix norm plus
eight times the squared displayed tail bound.

Twelve new `ZetaFourth*` modules are root-reachable and in the exact
production inventory; 53 public theorems have named dependency audits.
Sixty new regressions cover every signature, zero/empty/singleton cases,
different contour lines and literal critical-zeta consumers. The final
principal-runner evidence is recorded below.

Z4K (uniform kernel) and Z4C (actual mixed-line truncation) are supporting
results, not the unweighted fourth-moment theorem. ZGB still requires the
finite-polynomial mean square, quantitative cutoff-tail decay and their
integrated assembly. Thus ZGB/ZTM/ZAT, EPZAE-19/21/37, unconditional Add-est
and the full EPZAE-00–41 goal remain OPEN. No frozen public contract is
weakened, and no source pin, archive or adjacent/native proof is changed.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed: exact module coverage, root imports, named/exhaustive audits and
regressions are part of the goal. Run it and `run_lake_build.bat` after
relevant changes; a passing audit establishes integrity, not completion
of the missing moment or of all advertised Add-est clauses.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 323 package files, 334 Lean
files in its integrity scan, 3,296 audited declarations (3,291 discovered
target theorems plus five imported contracts). All 53 new named audits
and 60 added regressions pass. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample is byte-preserved; all source/runner hashes
were rechecked after both gates. Exact logs, hashes and the repaired
comment-scanner false positive are in the current Reproduction Manifest.
These gates verify the actual contour and truncation consumers, not the
missing fourth-moment integral, unconditional Add-est or the full goal.

## Unweighted moments and Add-est (i) — historical checkpoint

The printed Lemma 62 singleton counterexample is preserved byte-for-byte.
The corrected theorem still returns independent ρ/k and ρ*/k witnesses,
with independent existential fifth coordinates. No false s'/s scaling or
third s-preserving witness is restored.

`zeta_fourth_dyadic` now proves the genuine unweighted estimate: for every
η>0, constants C≥0 and H₀ are chosen before H, and H≥H₀, H>0 imply
integral_H^(2H) |ζ(1/2+it)|⁴ ≤ C H^(1+η).
It consumes the actual normalized divisor-contour source, not the native
mollified fourth moment and not an assumed fourth-moment bound.

The finite prefix is exactly {1,...,2^M}, including its first coefficient.
Unit-modulus endpoint twists prove a mean square uniform under every real
imaginary translation u, including the reflected phase u-t. The ordinary
divisor coefficient-square bound is derived from the native divisor bound.
Weighted Cauchy–Schwarz, product integrability and Fubini are proved for the
actual Gaussian kernel and complete finite polynomial.

The separate right line b=2+2/δ gives an actual bounded tail when
N≥H^(1+δ), uniformly for H≤t≤2H. A dyadic N between H^(1+q) and
2H^(1+q), with q=min(η,1)/20, pays the block-count loss. The exact exponent
1+5q+2q² is at most 1+7q≤1+η. Neither the cutoff error nor the polynomial
mean square remains a theorem parameter.

`zeta_twelfth_dyadic` applies the installed high/low decomposition to this
proved fourth moment. For every ε>0 it gives constants D≥0 and H₀ before H:
integral_H^(2H) |ζ(1/2+it)|¹² ≤ D H^(2+ε).
`zetaTwelfth_largeValueBound` and its short-height companion discharge
the actual Perron consumers: LV_ζ≤2τ−12(σ−1/2) for σ≥1/2, τ≥2,
and for σ≥3/4, τ≥3/2, respectively.

`add_est_i` in `NewAdditiveEnergy.lean` proves the literal printed clause on the entire
closed interval 3/4≤σ≤5/6:

```text
A*(σ)(1−σ) ≤ max((18−19σ)/(2(3σ−1)), 4(10−9σ)/(5(4σ−1))).
```

The actual declarations are `add_est_i`, `add_est_i_bound` and
`add_est_i_zero_energy` in `NewAdditiveEnergy.lean`.
The last exposes ∀ε>0 ∃C≥1 ∃δ>0 ∀T≥C, with the genuine shifted zero
energy at σ−δ, preserving analytic multiplicities and unit tolerance.
The epsilon--delta bound is proved first; the extended-real infimum
inequality is its consequence, not a substitute. At σ=3/4 the rate is
3/2 and A*≤6; at σ=5/6 the rate is 6/7 and A*≤36/7.

The dependency chain consumes corrected powering, the actual Heath–Brown
energy relation, certified general/zeta optimization, the proved twelfth
moment, and the proved endpoint-one zero-energy transfer. The separate
EPZAE-33 endpoint-two theorem is not assumed and remains open.

Seventeen new production modules are root-reachable and explicitly listed
in the batch runner's inventory. All 49 new public theorems have named
dependency audits. Sixty-one new regressions cover every public signature,
literal zeta integrals, coefficient/prefix endpoints, negative translated
intervals, both LV threshold boundaries and both printed energy endpoints.

ZGB, ZTM and clause (i)'s actual zeta/short-energy consumers are proved.
The other eight Add-est clauses, their remaining optimization certificates,
the separate sharp Atkinson source-form theorem, the other EPZAE-19/21
inputs, and the exponent-pair/density outputs remain OPEN. EPZAE-36/37 and
the full EPZAE-00–41 goal are not complete; the frozen contract is unchanged.

Keep `run_tao_trudgian_yang_build.bat` and its backing implementation
synchronized with root imports, exact inventory, named/exhaustive audits
and regressions. Run it and `run_lake_build.bat` after relevant changes.
This checkpoint's terminal gate evidence is recorded in the Reproduction
Manifest; earlier checkpoint PASS records are historical.

Verification (2026-09-21): both principal BAT scripts reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 340 package files,
351 integrity-scanned Lean files and 3,357 audited declarations
(3,352 discovered target theorems plus five imported contracts).
All 49 new named audits and all 61 new regressions pass.
The foundation reports PASS: all six stages passed, with 14,290
discovered theorems audited. Both final logs contain zero Lean errors,
warnings, tactic suggestions or linter failures. The counterexample
SHA256 is unchanged. Exact logs, source/runner hashes and repaired
focused diagnostics are recorded in the current Reproduction Manifest.
These gates verify the genuine moments and full-domain Add-est (i),
not clauses (ii)--(ix) or completion of the full goal.

## Add-est (ii): repaired powering to actual zero energy — verified checkpoint

Printed Lemma 62 remains disproved. Its singleton counterexample is
byte-preserved (SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The authorized replacement still uses independent cardinality-preserving
ρ/k and energy-preserving ρ*/k witnesses with independent existential fifth
coordinates. No false s'/s scaling or third witness is restored.

`add_est_ii`, `add_est_ii_bound`, and `add_est_ii_zero_energy` in
`NewAdditiveEnergy.lean` prove the complete second printed clause on
the closed interval 7/10 ≤ σ ≤ 3/4:

```text
A*(σ)(1−σ) ≤ max(5(18−19σ)/(2(5σ+3)), 2(45−44σ)/(2σ+15)).
```

The actual shifted-zero epsilon--delta bound is proved first, with analytic
multiplicity and unit-tolerance energy retained. The extended-real
infimum inequality follows from it. At σ=7/10 the rate is 47/26 and
A*≤235/39; at σ=3/4 the rate is 16/11 and A*≤64/11.
These endpoint checks supplement, not replace, the full interval proof.

For general patterns, `energyClauseTwo_general_bound` proves the rate on
2≤τ≤4. Actual mean-square and Guth--Maynard cardinality consumers use the
ρ/k witness at k and k+1. The actual Heath--Brown relation uses independent
energy witnesses at k and k−1, where k is two or three. All nine affine
branches are checked; the exceptional branches consume the first powered
energy inequality. Every height and coordinate is linked to its original
region point. Compactness promotes the region result to a uniform bound.

For zeta patterns, sixth-order decay is applied to the actual critical
Mellin integrand. Both the residue and the complete far tail
240 C₆ N^(11/2)/T⁴ are retained before absorption at T≥N^(11/8).
`zetaTwelfth_lower_short_largeValueBound` consumes the proved dyadic
twelfth moment and this entry bridge for σ≥7/10, τ≥7/5.
Actual cancellation gives eventual emptiness for 1≤τ<2σ on the clause
interval; mean-square powering and the twelfth-moment cap handle
2σ≤τ≤2 through nine exact branches with crossing τ=4σ−1.
`energyClauseTwo_short_zeta` therefore supplies all of [1,2].

`energyClauseTwo` composes the two uniform ranges with the already proved
endpoint-one bounded-range zero-energy transfer. The separate printed
endpoint-two transfer (EPZAE-33) is neither assumed nor marked complete.
Clause (i) remains proved. Clauses (iii)--(ix), the remaining optimization
projections, the source-form sharp Atkinson obligation, the other
EPZAE-19/21 inputs, and the exponent-pair/density/release outputs remain OPEN.
EPZAE-36/37 and the full EPZAE-00–41 objective are unchanged and incomplete.

Eleven new production modules are root-reachable and explicitly included
in the principal runner inventory. Eighty-four new public theorems have
named dependency audits; 92 added regressions cover all signatures and
literal physical/source endpoints. Keep `run_tao_trudgian_yang_build.bat`
and its backing inventory synchronized; run it and `run_lake_build.bat`
after relevant changes. Current gate evidence belongs in the Reproduction
Manifest; earlier PASS records are historical.

Verification (2026-09-21): both principal BATs reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 351 package files, 362
integrity-scanned Lean files and 3,504 audited declarations (3,499 discovered
target theorems plus five imported contracts). All 84 new named audits and
92 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions or linter failures. The
counterexample and all 18 recorded source/runner hashes were rechecked.
Exact log paths and hashes appear in the current Reproduction Manifest.
These gates verify full-domain Add-est (ii), not the other seven clauses or
completion of the unchanged whole-proof goal.

## Jutila source entry and uniform powered moments — verified checkpoint

The printed Lemma 62 counterexample is preserved unchanged. Corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Four new production modules advance the missing EPZAE-19 Jutila input:
`JutilaGram`, `JutilaPatternEntry`, `JutilaPoweredMoments`, and
`JutilaReflectedEntry`. They do **not** yet prove Jutila's large-values
estimate or another Add-est clause.

`jutila_smooth_amplified_gram` proves actual phase-aligned smoothed duality,
removes the diagonal before Hölder, and gives, for every positive integer k,
either R V² ≤ 2N² or R² V^(4k) ≤ (2N)^(2k) times the actual off-diagonal
2k-th trace moment. No moment or cardinality bound is assumed.

`LargeValuePattern.jutila_gram_entry` consumes an actual source pattern.
Its fixed smoothed subfamily retains at least a third of the ordinates,
the exact threshold (V−1)/3, unit separation, the actual height, and
N/2 ≤ Q ≤ 2N. The spaced consumer keeps the explicit packing loss
6(2⌈δ⌉+1). `jutila_reflected_pattern_entry` then consumes complete native
reflection on that same subfamily, with one common dual cutoff M.
The main factor uses the actual |u−t|. Mellin truncation, omitted-frequency,
and zero-mode errors all remain in `jutilaReflectionEnvelope`.

`jutila_weighted_power_moment_uniform` proves the actual critical-line
2k-th ordered-difference moment bound. With U=2^k N^k and R=|W|, its RHS is
C (U^η)² T^ε (R² + R U + R^(5/4) T^(1/2)).
C and the height threshold depend only on k, ε, η, and are chosen before
N, T, W. The proof consumes the uniform divisor bound, actual powered
coefficients, dyadic decomposition, coefficient majorant, and the proved
native weighted Heath--Brown theorem. That second-moment theorem is an
input to this deduction, not a substitute for Jutila's large-values theorem.

Remaining: pass from complete reflected prefixes to uniformly bounded
powered difference moments, sum the reflected integrals with all errors,
and perform the local-to-global large-values optimization. Then establish
the actual region and uniform exponent consumers before using them in the
seven remaining energy optimizations. EPZAE-19, 33, 36, 37 and the full
EPZAE-00–41 goal remain open; the distinct endpoint-two transfer, source-form
sharp Atkinson obligation, and other exponent-pair/density/release tasks
are unchanged.

The four modules are included in the root and the exact production
inventory of `run_tao_trudgian_yang_build.bat`. Thirteen new public theorems
have named audits and sixteen regressions cover their exact signatures,
literal diagonal removal, the k=13 power, and all reflected error terms.
Keep that BAT and its backing inventory synchronized, and execute it and
`run_lake_build.bat` after relevant changes. Terminal verification evidence
for this checkpoint is recorded below and in the Reproduction Manifest.

Verification (2026-09-21): both principal BAT runners reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 355 package files, 366
integrity-scanned Lean files, and 3,530 audited declarations (3,525 discovered
target theorems plus five imported contracts). All 13 new named audits and
16 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions, or linter failures. All eleven
recorded source/runner hashes were rechecked unchanged after the gates,
including the original counterexample. Repository scans found no forbidden
proof terms; the twelve raw postulate-pattern matches are the same ten
comments and two rational structure fields already reviewed. Git
`diff --check` passes (Git's LF/CRLF notices are not Lean diagnostics).
Exact commands, logs and hashes are in the Reproduction Manifest.
These gates verify the Jutila entry and powered-moment inputs, not the
remaining Jutila large-values theorem, other seven Add-est clauses, or
completion of the unchanged whole-proof goal.

## Jutila reflected-prefix moments and near/far assembly — verified history

The printed Lemma 62 counterexample is preserved unchanged. The corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Six new production modules advance EPZAE-19: `JutilaPolynomialMoments`,
`JutilaPrefixMoments`, `JutilaReflectionIntegrals`, `JutilaTraceBins`,
`JutilaBinnedPatterns`, and `JutilaHybridPatterns`.

`jutila_source_power_moment_uniform` handles arbitrary unit coefficients,
with constants chosen before their values and the physical length.
`jutila_reflected_prefix_moment_uniform` consumes the actual complete
reflected prefix, including n=1. With U=(2M)^k, R=|W|, and L=ceil(log₂ M),
its bound is C (L+1)^(2k) U (U^η)² T^ε
(R² + R U + R^(5/4) T^(1/2)). The constant is uniform in M, T, W and
the translation parameter. Neither the initial term nor a power of U is
discarded.

`jutila_reflected_bin_integral_moment_uniform` applies interval Jensen and
the proved full ordered-pair majorant before restricting to a difference
bin. Its extra interval factor is exactly (2H)^(2k).
`jutila_binned_pattern_bound` connects those estimates to the actual
source pattern, with bin-dependent positive dual lengths and all Mellin,
omitted-frequency, and zero-mode errors retained.

`jutila_hybrid_pattern_bound` additionally consumes native square-root
cancellation of the complete nonzero Poisson tail below the stationary
scale, keeping the separate zero-mode decay. Above that scale it uses the
actual ceiling length max(1,ceil(2^j H/Q)). The same subfamily retains
the packing loss 6(2 ceil(δ)+1), threshold (V−1)/3, N/2 ≤ Q ≤ 2N, the
actual height, and δ-separation. The condition 4H ≤ δ derives reflection
admissibility on occupied bins; it is not an independently assumed bin
estimate. The three new majorant definitions are notation, not proofs.

Remaining: bound this explicit near/far sum at source scale, absorb all
errors and logarithmic losses uniformly, perform the local-to-global
large-values optimization, and prove the exponent/energy-region consumers.
The target remains
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k), k ≥ 1.
Only then can k=13 enter Add-est (iii) and the other remaining optimizations.
EPZAE-19, 33, 36, 37 and the full EPZAE-00–41 goal remain open. The distinct
endpoint-two transfer, sharp source-form Atkinson bridge, exponent-pair,
density, and release obligations are unchanged.

All six modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Seventeen new public theorems have
named audits; 23 regressions cover their exact signatures, the n=1 term at
k=13, zero interval width, the literal ceiling, and both schedule branches.
Both that BAT and `run_lake_build.bat` remain required evaluation gates.
This is finite-scale proof progress, not completion of Jutila or another
Add-est clause.

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 361 package files, 372
integrity-scanned Lean files, and 3,564 audited declarations (3,559 discovered
target theorems plus five imported contracts). All 17 new named audits and
23 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All seventeen
recorded source/build hashes are unchanged after the gates, including the
original counterexample. Repository scans find no forbidden proof terms;
the twelve raw postulate-pattern matches are the previously reviewed ten
comments and two rational structure fields. Git `diff --check` passes.
Exact commands, logs, hashes, and the corrected initial scan failure are
recorded in the Reproduction Manifest. These checks certify the stated
finite-scale scope, not the remaining Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

## Jutila physical-scale smoothing and uniform pattern bounds — current checkpoint

The printed Lemma 62 counterexample remains byte-for-byte unchanged. The
authorized independent cardinality and energy witnesses remain the powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Seven new production modules advance EPZAE-19: `JutilaDualScales`,
`JutilaPhysicalMain`, `JutilaPhysicalPatterns`, `JutilaSmoothingErrors`,
`JutilaSmoothingProfile`, `JutilaSmoothingLosses`, and
`JutilaSmoothedPatterns`.

`jutila_reflection_main_core_le` cancels each actual powered dual length
against its own displacement denominator before imposing the common cap.
`jutila_physical_pattern_bound` consumes the complete near/far pattern
theorem, retaining all main terms, logarithmic/divisor costs, and sharp
reflection errors. The common ceiling is used only for losses.

Native smoothing uses H=max(1,ceil(T^θ)) and derivative order
q=max(2,ceil(4/θ)+1). The zero mode and all three reflection errors are
controlled by proved native estimates, not assumed numerical certificates.
The smoothing-error bridge explicitly requires Q≤2T. The complete profile
is uniformly O(T^(2θ)); its full powered cost, including the bin count,
is O(T^((16k+3)θ)). The actual thinning cost is at most 108 T^θ.

`jutila_smoothed_pattern_bound` chooses positive B and T₀≥2 before every
actual `LargeValuePattern`. For scale≥30, V>1, T≥T₀, and **N≤T**, it
constructs a subset W of the reflected ordinates and Q with N/2≤Q≤2N.
Writing R=|W| and V'=(V−1)/3, the original count is at most B T^ν R,
W is 1-separated in the actual height interval, and either

- R (V')² ≤ 2Q²; or
- R² (V')^(4k) ≤ B T^ν (2Q)^(2k)
  (R²Q^k + R T^k + R^(5/4) T^(1/2) Q^k).

This holds for every k≥1 and ν>0. The choice of θ absorbs both losses
without changing the physical height or assuming the desired LV estimate.
The N≤T restriction derives Q≤2T and is not silently removed.

Remaining: solve the cardinality recurrence with its value threshold,
cover the complementary short-height range, perform the local-to-global
optimization, and prove the actual uniform LV and energy-region consumers.
The unchanged target is
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k).
Only then can k=13 enter Add-est (iii) and the other seven-clause work.
EPZAE-19, 33, 36, 37 and the whole EPZAE-00–41 goal remain open. The
distinct endpoint-two transfer, sharp source-form Atkinson, exponent-pair,
density and release obligations are unchanged.

All seven modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Twenty-one new public theorems
have named audits. Twenty-seven regressions cover every exact signature
plus the actual k=13 source-pattern consumer, its three literal terms,
the empty-family boundary, ceiling padding, genuine zero-mode decay,
and the derived thinning cost. Both that BAT and `run_lake_build.bat`
remain mandatory; build integrity is separate from source completeness.
