# Whole-proof operational goal prompt

## Objective

Produce a reproducible, kernel-checked Lean 4 formalization of every new
mathematical output in Tao--Trudgian--Yang, arXiv `2501.16779v1`, while reusing
the live ANTEDB Lean foundations and the completed local Guth--Maynard
formalization where their exact interfaces agree.

The work is complete only when the source statements, Lean statements,
dependency graph, audit, documentation, and build runner agree. Python
optimization, numerical checks, and prose derivations may generate
certificates, but they may not serve as proof oracles.

## Frozen public theorem contract

Authorized supporting-lemma correction (20 September 2026): preserve the
kernel-checked counterexample to printed `power-energy` (Lemma 62), and
replace EPZAE-34 with the cardinality/energy two-witness theorem specified
below and in `Tao-Trudgian-Yang Energy Powering Repair.md`. Drop the false
`s' ≤ s/k` restrictions and the third, `s`-preserving witness. This is an
explicit correction to a supporting lemma, not to the advertised outputs.
Keep the original paper, the definitions of `S` and `E`, and the
counterexample unchanged. All public theorem statements below remain frozen.

The release layer must expose source-facing theorems for the following labels.

### Exponent-pair output

`new-exp-pair` must prove that each of the following is an exponent pair:

```text
(89/1282, 997/1282)
(652397/9713986, 7599781/9713986)
(10769/351096, 609317/702192)
(89/3478, 15327/17390)
```

The predicate must unfold to the paper's analytic exponential-sum estimate;
membership in a finite list or a convex polygon is not by itself the intended
claim.

### Zero-density outputs

With `A(sigma)` interpreted through the paper's zero-count convention and
epsilon-loss asymptotics, prove:

1. `hb-density2`:
   `A(sigma) <= 3 / (10*sigma - 7)` for `7/10 < sigma <= 1`.
2. `bourgain-density-improved`:
   `A(sigma) <= max (2/(9*sigma-6)) (9/(8*(2*sigma-1)))`
   for `17/22 <= sigma <= 4/5`, with the two stated subranges certified.
3. `bourgain-zero-density-optimized`: the exact eight-piece rational bound
   recorded in the crosswalk for `3/4 < sigma < 1`.

The final theorem chain must consume actual zeta zeros with multiplicity and
must prove the bridge from the local project's rectangle convention to the
paper's `Re rho >= sigma`, `|Im rho| <= T` convention.

### Additive-energy output

`Add-est` must prove all nine source clauses for
`A*(sigma) * (1-sigma)`, over their exact closed intervals and with the exact
maxima of rational functions shown in the paper. Additive energy must count
the intended approximate additive relations at unit tolerance, including
multiplicity and the paper's epsilon-loss normalization.

## Supporting source results in scope

The release outputs require faithful formal versions of:

- cheap asymptotic notation and automatic uniformity;
- model phase functions and `beta(alpha)`;
- exponent pairs, their convexity, A/B/C processes, the Sargos D-process, and
  beta/exponent-pair duality;
- the Heath--Brown derivative bound and all beta-table segments actually used
  by the four new pairs;
- zeta growth and the exponent-pair-to-`mu` bridge;
- large-value patterns, `LV`, zeta large values `LV_zeta`, subdivision,
  powering, and the cited classical/Guth--Maynard/Bourgain estimates;
- zero-density exponents and the Type I/Type II transfer from large values;
- the Bourgain zero-density theorem and its admissibility side conditions;
- additive energy, `LV*`, `LV*_zeta`, the five-dimensional energy regions,
  the corrected cardinality/energy powering theorem, and the Heath--Brown
  relation; and
- exact rational/polyhedral optimization certificates for every final
  envelope and interval split.

An upstream theorem may be imported only after its quantifiers, interval
conventions, coefficient normalization, sign convention, epsilon losses, and
constant dependencies are matched by a proved bridge.

### Corrected EPZAE-34 contract

Define `E₄(σ,τ,ρ,e) := ∃ s, E(σ,τ,ρ,e,s)`. For every fixed integer
`k ≥ 1` and every `E₄(σ,τ,ρ,e)`, prove:

```text
∃ eCard, E₄(σ, τ/k, ρ/k, eCard) ∧ eCard ≤ e/k;
∃ rEnergy, E₄(σ, τ/k, rEnergy, e/k) ∧ rEnergy ≤ ρ/k.
```

These are two potentially different witnesses. Their existential fifth
coordinates have no asserted relation to the input `s` or to `s/k`.
The full Lean target is `CorrectedCardinalityEnergyPowering`, now proved by
`correctedCardinalityEnergyPowering` in `CorrectedEnergyPowering.lean`.
Maintain that complete proof from actual powered Dirichlet polynomials,
uniform coefficient normalization, finite cardinality/energy selection,
and coordinate-preserving subsequence limits. The target's proposition
definition alone is not proof evidence; neither witness may be assumed.

Use the cardinality witness for large-value constraints and the energy
witness for the Heath--Brown relation, whose right side is nondecreasing
in cardinality and independent of `s`. Feed those justified constraints
into exact energy optimization and the nine unchanged `Add-est` clauses.

EPZAE-35 is now proved by `InLargeValueEnergyRegion.heathBrown_relation`;
`InCardinalityEnergyRegion.heathBrown_powered` composes the two proved
inputs without a separate analytic hypothesis. Maintain its exact source
signature and full `τ ≥ 0` domain. The finite derivation uses the native
second and fourth moments, with proved reflection, support, energy-count,
constant-dependency, and height-padding bridges. It does not use the
mismatched `N` factor in the archived `hbt` proof. The small-height
three-branch constraint and its powered consumer are available for EPZAE-36;
their existence does not complete any final projection or `Add-est` clause.
Keep these modules, their explicit audits and semantic regressions covered
by `run_tao_trudgian_yang_build.bat`, updating its PowerShell inventory and
the root imports whenever this proof chain changes.
Do not infer arbitrary polytope closure or use any scaled `s` constraint.
Keep `energyPowering_source_counterexample` as a permanent audited regression.

The clause-(i) general intermediate `imphb-lver-ineq` is now proved by
`InLargeValueEnergyRegion.energyClauseOneGeneral_lower_piece` and
`InLargeValueEnergyRegion.energyClauseOneGeneral_upper_piece`, with exact
range `[8σ-4,2(8σ-4)]`, closed crossover `σ=4/5`, and full upper endpoint
`σ=5/6`. `energyClauseOneGeneral_uniform_bound` and
`energyClauseOneGeneral_high_height_bound` supply uniform general bounds.
Maintain their actual dependency on corrected cardinality witnesses at
`k,k+1` and the separate corrected energy witness. The Huxley energy-region
bridge is proved in `ClassicalLargeValueRegions`; the six-branch rational
certificate is in `EnergyClauseOneGeneral`. Do not infer arbitrary region
closure from these specific, proved deductions.

`energyClauseOne_of_zeta_range` retains the real zeta-energy bounds
on `[1,8σ-4)` as its modular inputs. The continuation below now derives
that complete range from the dyadic twelfth moment. Prove the moment
before claiming `Add-est (i)`; the independent source endpoint-two
reduction remains part of EPZAE-33.
The other eight final clauses remain in scope. Keep both new modules and
their endpoint/consumer regressions in `run_tao_trudgian_yang_build.bat`
coverage, updating the root imports, explicit audit, and runner inventory.

The clause-(i) zeta rational certificate is now proved in
`EnergyClauseOneZeta`: six affine branches, the exact `τ=4σ-1` height
transition, `σ=65/86` crossover, and domination by the advertised maximum.
Preserve its distinction from the analytic estimate. The actual-region
consumer derives its Huxley cap from corrected cardinality powering and
its Heath--Brown relation from the proved native analytic chain; it still
requires the independent twelfth-moment cardinality inequality.
`InZetaLargeValueEnergyRegion.rho_le_of_largeValueBound` proves the exact
uniform-LV-to-region bridge, and the resulting uniform zeta-energy bounds
remain conditional on `IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))`.

`energyClauseOne_of_twelfth_and_short_zeta` now gives end-to-end assembly
with precisely the modular short zeta-energy input on `[1,2)` and the
twelfth-moment LV input on `[2,8σ-4)`. The latter now follows from the
dyadic critical-line moment through `ZetaTwelfthFromMoment` below.
The short-zeta continuation below supplies the former from the same
moment, so only that moment remains in the assembled clause-(i) signature.
Prove it before claiming clause (i). The nearby Gafni--Tao `HeathBrownTwelfthStatement`
file contains a proposition and conditional consumers, not an importable
proof of the full twelfth-moment estimate. Do not treat it as an axiom or
completed analytic input. Keep `EnergyClauseOneZeta`, all named audits,
closed-endpoint regressions, and conditional signatures in
`run_tao_trudgian_yang_build.bat` coverage.

The critical-line, twelfth-power summation step of `add-bound (ii)` is now
proved in `ZetaMomentKernel` and `ZetaMomentTransfer` on the actual zeta
function and the source interval `[T/2,3T]`. `ZetaMomentAsymptotics` proves
logarithmic-loss absorption and dyadic/source-window normalization, with
a consumer on actual `ZetaLargeValuePattern` objects. Preserve the exact
physical `C^12 N^6` normalization and uniform height threshold.
The low-level finite consumer explicitly assumes pointwise entry and the
dyadic critical-line moment separately. Preserve that modular interface;
`ZetaPerronEntry` now discharges the pointwise premise and
`ZetaTwelfthFromMoment` proves the uniform epsilon--delta LV deduction.
The moment hypothesis itself remains open. A conditional deduction does
not discharge `twelfth-bound`.
Do not assume away a Perron residue, smoothing loss, or support endpoint.
Keep all three modules, their 21 named public audits, and ten semantic
regressions in the root imports and `run_tao_trudgian_yang_build.bat`
inventory; update the runner whenever this analytic chain changes.

The exact coefficient-one source identity is now proved in
`ZetaIntervalCutoff`, `ZetaMellinEntry`, `ZetaMellinContour`, and
`ZetaMellinShift`. Preserve the actual-pattern consumer
`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin`: the original
sharp polynomial equals the whole critical-line zeta integral plus
`mellin cutoff (1-it)`. The cutoff equals the active indicator at every
integer; both endpoints, the negative phase, and the moving pole are exact.
The native smooth-test object is constructed from this cutoff. Boundary
integrability, horizontal decay, and the contour shift are proved, with
constants permitted to depend on the fixed cutoff and ordinate.

Quantitative Mellin bounds, source-window localization, and residue/tail
absorption are now proved in the six-module continuation below. Preserve
their actual dependencies; do not replace them by fixed-cutoff convergence
or an independently assumed entry estimate. Keep these four identity
modules, their
36 named public theorem audits, the explicit cutoff-constructor audit, and
ten semantic regressions in the root imports and
`run_tao_trudgian_yang_build.bat` inventory. Update and rerun that principal
runner whenever the analytic chain, audit, or production coverage changes.
The preserved Lemma 62 counterexample and all final publication contracts
remain unchanged.

The uniform continuation consists of `ZetaCutoffDerivatives`,
`ZetaMellinDerivative`, `ZetaMellinUniform`, `ZetaMellinLocalization`,
`ZetaPerronEntry`, and `ZetaTwelfthFromMoment`. For `j ≥ 1`,
the cutoff derivative integral is bounded independently of its endpoints,
and for `σ ≥ 1/2` the Mellin estimate is
`|M_w(σ+iu)| ≤ C_j(σ) N^(σ+j-1)/(1+|u|)^j`.
The omitted critical integral is at most
`120 C_4(1/2) N^(7/2)/T²`; the residue is at most
`C_4(1) N^4/(1+|t|)^4`. The actual-pattern `perron_entry` absorbs both
when `T ≥ N^(7/4)` and `V ≥ 2 zetaPerronError`.
`exists_zetaPerron_uniform_threshold` derives these physical conditions
from the source windows, uniformly for `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`.

`zetaTwelfth_largeValueBound_of_dyadic` proves the full uniform
`IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))` from the genuine dyadic
critical-line twelfth moment alone. Its constants and approximation
radius precede the actual pattern. No pointwise entry or cardinality
conclusion is an assumed input.
`energyClauseOne_of_dyadic_moment_and_short_zeta` composes this theorem
with corrected powering, Heath--Brown energy, and the exact optimizations.
Its two-input signature is preserved as a modular consumer. The short-zeta
continuation below supplies its energy premise from the same dyadic moment.
Prove that moment; do not reintroduce the discharged short-zeta premise.
Other source moment parameters, other eight energy clauses, and the
complete EPZAE-00--41 contract remain in scope.

Keep all six continuation modules, their 39 named public theorem audits,
the constructed derivative-test audit, and 14 regressions in root imports
and `run_tao_trudgian_yang_build.bat` coverage. Update and rerun that
runner as this chain changes. Neither a passing runner nor a conditional
moment consequence proves the missing moment or any final `Add-est` clause.

### Short-zeta completion and remaining clause-(i) obligation

`ZetaShortPerron` proves threshold-relative entry for actual patterns:
`T ≥ N^(23/16)` and `V ≥ 2 zetaPerronError N^(5/8)` suffice. Its uniform
threshold derives these from `σ ≥ 3/4`, `τ ≥ 3/2`, `δ ≤ 1/16` source
windows. `zetaTwelfth_short_largeValueBound_of_dyadic` consumes this
entry and gives the exact same twelfth-moment cardinality exponent.

`ZetaShortPatterns` preserves the full closed sharp interval, including
its left endpoint, and proves
`|polynomial(t)| ≤ 2 + 200 sqrt(t) + 12 pi N/t` for `1 ≤ t ≤ N²`.
The bound uses the native first/second derivative estimates on actual
prefixes, not an assumed cancellation hypothesis. Its uniform consumer
proves eventual emptiness for `σ ≥ 3/4`, `1 ≤ τ < 3/2`, hence
`zetaShort_largeValueExponent_eq_bot` and every candidate energy bound.

`energyClauseOne_short_cubic_bound` certifies
`3(2τ-12(σ-1/2)) ≤ energyClauseOnePublicRate(σ) τ` for `σ ≥ 3/4`,
`0 ≤ τ ≤ 2`. The actual short-zeta consumer combines this with cubic
energy and the two height ranges. `energyClauseOne_of_dyadic_moment`
then proves the exact zero-energy bound throughout `3/4 ≤ σ ≤ 5/6`,
conditional only on the explicitly quantified genuine dyadic twelfth
moment. No short-zeta, cardinality, energy, or density conclusion is a
theorem parameter. It uses the proved endpoint-one transfer; it does not
silently replace that endpoint with two.

Maintain `ZetaShortPerron`, `ZetaShortPatterns`,
`EnergyClauseOneFromMoment`, their original 11 public theorems, and the new
short-height LV theorem in `ZetaTwelfthFromMoment`: 12 new named audits
and eight boundary/consumer regressions. Keep all of them in the root
imports and `run_tao_trudgian_yang_build.bat` inventory; update and rerun
the runner whenever this chain changes. Preserve the counterexample and
all public contracts. The actual twelfth moment is the next missing
analytic input for clause (i). The general endpoint-two source theorem,
other eight energy clauses, and full EPZAE-00--41 scope remain required.

### Zeta discreteness and the remaining moment route

Preserve `ZetaLargeValueDiscreteness`, `ZetaPointwiseNonexistence`, and
`zetaShort_pointwise_powerSaving`: 13 additional named public theorem
audits and eight semantic regressions. The exact infimum/uniform-bound
equivalence, negative-exponent collapse, and positive-height pointwise
power-saving equivalence are proved for actual sharp-interval patterns.
Their singleton construction is genuine; the reverse direction absorbs
the `[T,2T]` factor two by shrinking the radius and enlarging the threshold.
Keep both modules in the root imports and the inventory behind
`run_tao_trudgian_yang_build.bat`; update and rerun that batch entry point
and the foundation runner after changes.

The online ANTEDB Lemma 8.11 uses a maximum. Theorem 9.7's displayed proof
switches it to a minimum without justification. Use the proved
`zetaLargeValueExponent_le_double_of_le_max`: for `a ≥ 0` the maximum
is `2a`; for `a < 0`, actual cardinality discreteness gives negative
infinity. This algebraic step does not prove Ivić's analytic estimate.
The pinned Ivić scan gives the underlying route in Theorem 7.1,
Corollary 7.2, and the local mean-square Theorem 6.2. Its title pages
identify *Topics in Recent Zeta Function Theory*, Orsay report 83.06,
not the book edition cited by ANTEDB. The sharp local mean-square
inequality, subsequent scale/spacing assembly, and the actual dyadic
twelfth moment still need proofs. The exact divisor-series entry is
proved in the continuation below. Do not import the nearby Gafni--Tao proposition as an
instance or regard its Atkinson Gram estimate as the missing zeta entry.
The preserved powering counterexample, final source contracts, and full
EPZAE-00--41 goal are unchanged.

### Exact local mean-square source entry

Preserve the six proved modules `ZetaSquareContour`,
`ZetaSquareContourShift`, `ZetaSquareDivisorKernel`,
`ZetaSquareDivisorSeries`, `ZetaSquareSourceEntry`, and
`ZetaSquareLocalMean`. The first two adapt the adjacent one-sided
contour proof to canonical native imports, not the separate Gafni--Tao
package. The complete right-line expansion uses the actual coefficients
`n.divisors.card`, proves every term integrable and the integrated norms
summable, and identifies both reflected contours by their limits.

`hasSum_zetaSquareNormalizedContribution` removes the Gamma normalization
and gives the actual critical-line squared norm, including height zero.
`hasSum_zetaSquareLocalMean` proves the complete coefficientwise local
integrals sum to `∫[a,b] |ζ(1/2+it)|²`, for every `a ≤ b`.
It derives compact-height domination and continuity before interchanging
the sum and integral. No local mean-square or moment theorem is assumed.

This identity does not discharge Ivić's uniform Theorem 6.2. The
averaging continuation below is now proved; continue through the
proved uniform shifted-Gamma/complete-series bridge and the remaining
divisor-shortening/Voronoi/stationary-phase reduction, with physical parameter ranges, sharp tail and remainder
bounds, and scale/spacing assembly, to the genuine dyadic twelfth moment.
The Gaussian convergence majorant and compact-dependent constants are
not the required uniform Atkinson estimate. Keep EPZAE-21/37 open until
the advertised analytic and final energy conclusions actually follow.

Maintain all six modules, their 47 named public theorem audits, and nine
source-entry regressions in the root imports and the inventory behind
`run_tao_trudgian_yang_build.bat`. Update and rerun that batch entry point
and the foundation runner whenever the chain changes. Preserve the
counterexample and both corrected witnesses; no source pin, fifth-coordinate
restriction, public output, or full EPZAE-00--41 obligation is changed.

### Uniform Gaussian averaging and the remaining phase bridge

Preserve `ZetaSquareAveraging`, `ZetaSquareGaussianTail`, and
`ZetaSquareGaussianTransform`, their 31 named public theorem audits,
and nine regressions. Weighted divisor-series convergence is proved
for continuous real weights. The local Gaussian majorization uses
`exp(1)` independently of `T,G,L`. Centering preserves the exact
Jacobian `G`, and the whole-line actual-zeta integral is integrable.
One constant controls the tail by
`C G(1+|T|+G)² exp(-L²/2)`. On the source logarithmic window, for
every real `A`, one threshold works for all `0<G≤T` and gives
`G T^(-A)`. `exists_zetaSquareGaussian_source_approximation` consumes
both the weighted divisor identity and the actual tail, with no
moment or source-entry premise.

The quadratic coefficient is exactly `G^(-2)+i/(2T)`. The transform
and its frequency estimate `sqrt(pi) G exp(-(Gv)²/8)` are proved for
`T,G>0` and `G²≤2T`, including the closed boundary and both frequency
signs. The actual unit-phase approximation and integrated error are
proved below. The following amplitude continuation also proves a uniform
complete reflected-source remainder. The shortened divisor sum is not
proved by either the phase-only transform or that remainder;
continue through Voronoi/stationary phase, uniform remainders, physical
scale/spacing assembly, and the actual dyadic twelfth moment.
EPZAE-21/37 and all final public outputs remain open.

Keep all three modules in the root imports and the inventory behind
`run_tao_trudgian_yang_build.bat`; update and rerun that exact entry
point and the foundation runner when the analytic chain changes.
The original counterexample, corrected two-witness powering, proved
Heath--Brown energy relation, source pins, and full EPZAE-00--41
contract remain unchanged.

### Actual Gamma phase and the amplitude continuation

Preserve `ZetaDigammaLog`, `ZetaSquareGammaPhase`,
`ZetaSquareGammaQuadratic`, and `ZetaSquareGammaTransform`, their 26
named public theorem audits, and 12 regressions. The actual digamma
series proves `‖psi(z)-log(z)‖≤4/|Im z|` for `Re z>0`, `|Im z|≥1`.
No Stirling or phase-asymptotic theorem is assumed.

The reflected phase is exactly
`phi(t)=GammaR(1/2-it)/GammaR(1/2+it)`. Preserve its unit norm, actual
zeta functional-equation consumer, exact Gamma-normalization factorization,
and real-frequency differential equation. Its frequency differs from
`-log(t/(2pi))` by at most `9/t` for `t≥2`. On the closed window
`|x|≤r≤T/2`, `T≥4`, the phase differs from
`phi(T) exp(-i[x log(T/(2pi))+x²/(2T)])` by at most
`(18/T+2r²/T²)|x|`.

`norm_zetaSquareGammaGaussianTransform_sub_quadratic_le` consumes the
finite integrated comparison and both Gaussian tails. For `G>0`, its
error is `2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)`, uniformly in
the real frequency `v`. The following norm-bound consumer uses the
proved quadratic damping at frequency `v-log(T/(2pi))`, on `G²≤2T`.

The actual source contains
`[GammaR(1/2-it+w)/GammaR(1/2-it)]²`, the pole-removal factors, and
the contour/divisor weights. Their uniform kernel approximation and
complete reflected-series remainder are proved in the continuation below.
Next justify weight bounds, height variation and the shortened divisor
range, then continue through Voronoi/stationary phase and the sharp
Atkinson inequality to the dyadic twelfth moment.
Do not replace those amplitudes by `1` or call the unit-phase transform
an unconditional local zeta mean-square theorem. EPZAE-21/37 remain open.

Keep all four modules in root imports and in the inventory behind
`run_tao_trudgian_yang_build.bat`; update and rerun that exact batch
entry point and the foundation runner whenever the chain changes.
Preserve the original counterexample, corrected two witnesses,
Heath--Brown energy theorem, all source pins and public outputs, and
the entire EPZAE-00--41 goal.


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
quadratic divisor sum. Shortening, Voronoi/stationary phase, sharp
Atkinson errors, scale/spacing assembly and the genuine dyadic twelfth
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

Continue by combining the proved whole-line zeta tail with this window
comparison, choosing the source's logarithmic window uniformly, and
shortening the actual quadratic divisor series using its frequency
damping. Then prove the required Voronoi/stationary-phase reduction,
Atkinson inequality and dyadic moment, and discharge the remaining
`energyClauseOne_of_dyadic_moment` input. All nine unconditional
`Add-est` clauses and other public outputs remain required by the full
EPZAE-00--41 goal; this continuation does not narrow that goal.

Keep all nine modules in root imports, all 78 public audits and all
20 regressions in the inventory behind `run_tao_trudgian_yang_build.bat`.
Update that exact batch interface's backing inventory whenever the chain
changes, and rerun it and `run_lake_build.bat`; do not bypass their gates.
The original Lemma 62 counterexample, corrected independent fifth
coordinates, powering/Heath--Brown proofs and pinned sources are unchanged.

## Source and dependency boundary

1. Primary paper: arXiv `2501.16779v1`, submitted 28 January 2025.
2. Paper-time ANTEDB snapshot: commit
   `9953003a48f46fe8075ccf9534321f98f656032e`, the last repository commit before
   the arXiv v1 submission time.
3. Current ANTEDB Lean snapshot: commit
   `088040634e8300f87e80f431d8bdc38c42cc8e11`, dated 4 September 2026.
4. Completed local Guth--Maynard foundation: the canonical source under
   `../71 Guth-Maynard, 2026/`, pinned by that project's own reproduction
   manifest and release tag.
5. Mathlib and `PrimeNumberTheoremAnd`: use only through a single selected
   toolchain/dependency graph after EPZAE-01 is resolved.

The paper-time snapshot is for historical reproduction of the optimization.
The current snapshot is for reusable Lean foundations. Never blur the two.

## Proof architecture

The project has three layers:

1. **Analytic semantics:** definitions and theorems about phase functions,
   exponential sums, zeta zeros, large-value patterns, and energy.
2. **Exact finite certificates:** rational arithmetic, affine envelopes,
   polyhedra, projection witnesses, interval partitions, and maximum/minimum
   comparisons.
3. **Public assembly:** the new exponent-pair, zero-density, and energy
   endpoints, consuming both previous layers through explicit theorems.

The finite-certificate layer must not assert that an analytic hypothesis is
true. The analytic layer must not bury an optimization result inside a
definition. The public layer must consume the actual upstream objects.

## Proposed production modules

```text
TaoTrudgianYang2025/
  AsymptoticBridge.lean
  PhaseBridge.lean
  RationalCertificates.lean
  PiecewiseEnvelope.lean
  PolyhedralCertificates.lean
  ExponentPair.lean
  ExponentPairProcesses.lean
  SargosDProcess.lean
  BetaDuality.lean
  HeathBrownDerivative.lean
  BetaTable.lean
  NewExponentPairs.lean
  ZetaGrowth.lean
  LargeValuePattern.lean
  LargeValueExponent.lean
  LargeValueSubdivision.lean
  LargeValuePowering.lean
  ClassicalLargeValues.lean
  ClassicalLargeValueRegions.lean
  GuthMaynardBridge.lean
  BourgainLargeValues.lean
  ZetaLargeValues.lean
  ZetaMomentKernel.lean
  ZetaMomentTransfer.lean
  ZetaMomentAsymptotics.lean
  ZetaIntervalCutoff.lean
  ZetaMellinEntry.lean
  ZetaMellinContour.lean
  ZetaMellinShift.lean
  ZetaCutoffDerivatives.lean
  ZetaMellinDerivative.lean
  ZetaMellinUniform.lean
  ZetaMellinLocalization.lean
  ZetaPerronEntry.lean
  ZetaShortPerron.lean
  ZetaShortPatterns.lean
  ZetaLargeValueDiscreteness.lean
  ZetaPointwiseNonexistence.lean
  ZetaSquareContour.lean
  ZetaSquareContourShift.lean
  ZetaSquareDivisorKernel.lean
  ZetaSquareDivisorSeries.lean
  ZetaSquareSourceEntry.lean
  ZetaSquareLocalMean.lean
  ZetaSquareAveraging.lean
  ZetaSquareGaussianTail.lean
  ZetaSquareGaussianTransform.lean
  ZetaDigammaLog.lean
  ZetaSquareGammaPhase.lean
  ZetaSquareGammaQuadratic.lean
  ZetaSquareGammaTransform.lean
  ZetaGammaShiftLog.lean
  ZetaGammaShiftAmplitude.lean
  ZetaSquarePoleShift.lean
  ZetaSquareNearKernel.lean
  ZetaSquareGammaInverse.lean
  ZetaSquareKernelApproximation.lean
  ZetaSquareLeadingDivisor.lean
  ZetaTwelfthFromMoment.lean
  EnergyClauseOneFromMoment.lean
  ZeroCountBridge.lean
  ZeroDensityExponent.lean
  ZeroDensityTransfer.lean
  ImprovedHeathBrownDensity.lean
  ImprovedBourgainDensity.lean
  BourgainOptimizedDensity.lean
  AdditiveEnergy.lean
  EnergyExponents.lean
  ZeroEnergyMultiplicity.lean
  EnergyRegions.lean
  EnergyRegionAsymptotics.lean
  EnergyBoundAsymptotics.lean
  EnergyPowering.lean
  EnergyPoweredPatterns.lean
  EnergyPoweringLimits.lean
  CorrectedEnergyPowering.lean
  EnergyPoweringBounds.lean
  EnergyPoweringObstruction.lean
  EnergyLogLimits.lean
  HeathBrownEnergyFinite.lean
  HeathBrownEnergy.lean
  EnergyClauseOneGeneral.lean
  EnergyClauseOneZeta.lean
  EnergyCertificates.lean
  NewAdditiveEnergy.lean
  PublicTheorems.lean
  SemanticRegression.lean
  Audit.lean
```

Module names may be refined, but every dependency edge in the architecture
must remain visible and audited.

## Integrity contract

- No `sorry`, `admit`, project `axiom`, conclusion-shaped theorem parameter,
  `native_decide`, `implemented_by`, or unsafe proof bypass.
- No floating upstream branch, unpinned source archive, or silently updated
  generated certificate.
- Generated Lean certificate files must be deterministic, reviewed, imported
  by the root module, and checked by the kernel.
- Every public theorem must have an explicit transitive axiom audit.
- Every source convention bridge must have semantic regression examples at
  endpoints and overlap points.
- All production modules must be in the default import graph and principal
  runner.
- Zero project warnings and linter diagnostics are required for release.

## Principal verification runner

`run_tao_trudgian_yang_build.bat` is a required part of the project contract,
not optional convenience tooling. It must be updated in the same change
whenever the package layout, production-module inventory, toolchain,
dependency pins, generated certificates, semantic regressions, public theorem
list, or axiom audit changes.

The runner must resolve the project from its own location, preserve a complete
timestamped log, support `--no-pause`, and return a nonzero exit code if any
required inventory, source hash, build, warning, semantic, integrity, or audit
gate fails. While no Lean package exists it must say `PLANNING SCAFFOLD ONLY`
and must not describe its result as a Lean build. Once the package is
installed, a release claim requires executing this exact runner successfully;
a direct `lake build` alone is insufficient.

## Release acceptance gates

A release may be called complete only when all of the following pass:

1. all frozen public statements elaborate exactly;
2. all supporting analytic inputs are proved or imported through exact proved
   bridges, with no remaining mathematical theorem parameter;
3. every rational and polyhedral certificate is replayed in Lean;
4. paper-time Python reproduction agrees with the frozen endpoint tables;
5. the source hashes and both ANTEDB pins pass;
6. the repository-wide shortcut scans pass;
7. `run_tao_trudgian_yang_build.bat --no-pause` covers all production modules
   and completes with zero warnings;
8. the exhaustive dependency audit reports only permitted Lean/Mathlib logical
   axioms;
9. the architecture, checklist, crosswalk, research agenda, README, and
   reproduction manifest state the same completion status; and
10. semantic regression tests verify zero-count conventions, interval
    endpoints, multiplicity, epsilon-loss quantifiers, convex-hull membership,
    and every piecewise crossover;
11. the corrected two-witness powering theorem is proved on its full domain,
    and every powered optimization constraint is justified without the false
    fifth-coordinate scaling; and
12. the original Lemma 62 counterexample remains imported, explicitly audited,
    and covered by `run_tao_trudgian_yang_build.bat`, alongside the repaired
    theorem and its downstream consumers.

Until then, use the status terms **planned**, **defined/stated**,
**conditionally proved**, or **kernel-checked helper** as appropriate. Do not
say the paper or any advertised output is formalized.
