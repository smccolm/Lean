# Lean extension

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
also not yet proved, so no advertised paper theorem is claimed complete.
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
estimate. Continue with literal Y0 asymptotic reduction, uniform
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

Next prove the literal Y0 asymptotic expansion and the uniform
oscillatory stationary reduction, retaining the complex amplitude
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
