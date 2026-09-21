# Tao--Trudgian--Yang 2025 formalization

This directory is the planning and source-control baseline for a Lean 4
formalization of Terence Tao, Tim Trudgian, and Andrew Yang,
*New exponent pairs, zero density estimates, and zero additive energy
estimates: a systematic approach*, arXiv `2501.16779v1` (2025).

**Current status:** the unified package, audited dependency bridges, exact
certificate kernel, analytic exponent-pair semantics, exact Guth--Maynard
large-value bridge, and additive-energy foundations are installed and pass
the principal runner. The energy layer includes the extended-real general
and zeta comparisons `2LV ≤ LV* ≤ 3LV`, the necessary region constraints,
and exact general/zeta feasible-region supremum characterizations on the
source domain. No advertised final output from the paper is claimed
formalized yet; the four exponent pairs, density bounds, and energy bounds
still require their analytic derivations.

**Preserved discovery and authorized repair:** the kernel-checked singleton
counterexample disproves printed Lemma 62's `s' ≤ s/k` requirement; see
[the obstruction report](Tao-Trudgian-Yang%20Energy%20Powering%20Obstruction.md).
The owner authorized replacing EPZAE-34 by separate cardinality- and
energy-preserving witnesses with independent, unrestricted fifth exponents.
[The repair](Tao-Trudgian-Yang%20Energy%20Powering%20Repair.md) is now proved:
`correctedCardinalityEnergyPowering` constructs both actual witnesses for
every positive integer power, with no remaining mathematical hypothesis.
EPZAE-35 is also proved: `InLargeValueEnergyRegion.heathBrown_relation`
derives the exact two-max inequality from native second/fourth moments.
`InCardinalityEnergyRegion.heathBrown_powered` composes it with the repaired
energy witness without any remaining analytic theorem parameter.
The counterexample, source archives, and advertised final outputs are unchanged.

The corrected witnesses now also give the exact general-energy intermediate
bound in `Add-est (i)`: `EnergyClauseOneGeneral` proves both sigma pieces,
their crossover, the compact height interval, uniform epsilon-loss bounds,
and extension to every higher general height. `EnergyClauseOneZeta` now
certifies the zeta six-branch optimization and its `65/86` crossover.
Its actual-region and uniform-bound consumers now obtain the needed
cardinality estimate from the genuine dyadic twelfth-moment hypothesis.
That moment theorem remains unproved. `EnergyClauseOneFromMoment` now
derives the short-zeta input too and assembles clause (i) from this moment
alone. The independent source endpoint-two theorem remains open under
EPZAE-33, but is not needed by this clause-(i) route.

The moment-transfer analysis has progressed: `ZetaMomentKernel`,
`ZetaMomentTransfer`, and `ZetaMomentAsymptotics` prove the separated
convolution estimate for the actual critical-line zeta function, with
weighted twelfth-power Hölder, logarithmic-loss absorption, and a proved
dyadic-to-`[T/2,3T]` window bridge. The low-level transfer exposes the
pointwise entry and moment inputs separately. The new source-entry chain
below discharges the former; the genuine dyadic twelfth-moment theorem
remains unproved, not postulated.

The source entry now has an exact proved identity:
`ZetaIntervalCutoff`, `ZetaMellinEntry`, `ZetaMellinContour`, and
`ZetaMellinShift` turn each actual sharp coefficient-one polynomial into
its whole critical-line zeta integral **plus the pole residue**. Both integer
endpoints and the negative phase are preserved; the smooth cutoff and all
contour-shift hypotheses are derived, not assumed. The Mellin estimates used
to justify the shift are for each fixed cutoff and ordinate.
`ZetaCutoffDerivatives`, `ZetaMellinDerivative`, `ZetaMellinUniform`,
`ZetaMellinLocalization`, and `ZetaPerronEntry` now also prove uniform
physical-scale bounds, localization to `[T/2,3T]`, and residue/tail
absorption. `exists_zetaPerron_uniform_threshold` covers the actual
source exponent windows for `σ ≥ 1/2`, `τ ≥ 2`.

`ZetaTwelfthFromMoment` proves the complete uniform deduction
`LV_ζ(σ,τ) ≤ 2τ-12(σ-1/2)` conditional only on the genuine dyadic
critical-line twelfth moment. `ZetaShortPerron` extends the entry to
`σ ≥ 3/4`, `τ ≥ 3/2` by absorbing the error relative to `V`.
`ZetaShortPatterns` proves actual nonexistence, hence `LV_ζ = -∞`, for
`σ ≥ 3/4`, `1 ≤ τ < 3/2`, using native first/second derivative bounds.
The cubic energy bound supplies `[3/2,2]` from the moment.
`energyClauseOne_of_dyadic_moment` therefore reaches clause (i) with just
the dyadic critical-line twelfth moment as its analytic theorem parameter.
That moment is not proved; no final `Add-est` clause is claimed complete.

The zeta nonexistence semantics now have a complete positive-height bridge:
`ZetaLargeValueDiscreteness` and `ZetaPointwiseNonexistence` prove that a
negative exponent, negative infinity, eventual emptiness of actual patterns,
and a uniform strict power saving for every sharp interval are equivalent.
The singleton entry preserves the literal interval; the reverse direction
pays for the `[T,2T]` factor two. `zetaShort_pointwise_powerSaving` consumes
the proved short-range cancellation. The analytic twelfth moment remains
open; the maximum-to-double branch lemma is not that analytic estimate.

The next source-entry layer is now proved in six `ZetaSquare*` modules:
the reflected contour opens into an absolutely convergent ordinary-divisor
series, normalizes back to `|ζ(1/2+it)|²`, and can be integrated termwise
on every finite local interval. `hasSum_zetaSquareLocalMean` consumes the
actual zeta function with no analytic theorem parameter. This is an exact
identity, not Ivić's uniform Atkinson local mean-square estimate; the
oscillatory reduction, uniform remainders, and twelfth moment remain open.
All six modules, 47 named theorem audits, and nine regressions are covered
by the root imports and `run_tao_trudgian_yang_build.bat` inventory.

The Gaussian averaging continuation now has uniform physical scales:
`ZetaSquareAveraging` proves weighted series convergence and bounds the
local second moment by `exp(1)` times its Gaussian average.
`ZetaSquareGaussianTail` identifies the whole-line physical integral and
proves a tail of at most `G T^(-A)` outside `T ± G log T`, uniformly for
`0 < G ≤ T` beyond one threshold depending on `A`. Its actual-source
consumer combines this with the weighted divisor series.
`ZetaSquareGaussianTransform` evaluates the quadratic Gaussian kernel and
proves frequency damping for `G² ≤ 2T`. The continuation below handles
the actual reflected phase. The shifted amplitude and complete reflected
source remainder are proved below; divisor shortening, Voronoi/stationary
phase, and the final twelfth moment remain open.
These three modules add 31 named theorem audits and nine regressions.

Four further modules (`ZetaDigammaLog`, `ZetaSquareGammaPhase`,
`ZetaSquareGammaQuadratic`, `ZetaSquareGammaTransform`) prove the actual
Gamma-phase approximation. They derive `‖ψ(z)-log z‖ ≤ 4/|Im z|`,
identify the reflected quotient with the zeta functional-equation phase,
and approximate its whole-line Gaussian transform by the quadratic one.
For `T≥4`, `0≤r≤T/2`, `G>0`, the error is at most
`2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)`, uniformly in frequency.
The phase's frequency damping is proved when `G²≤2T`. This does not
remove the shifted-Gamma amplitude from the actual divisor contour.
The four modules now have 26 named public audits and 12 phase regressions,
covered by the root imports and principal batch runner. The full goal
and all final publication contracts are unchanged.

Seven further modules now prove the actual shifted-Gamma and pole
amplitudes and a uniform complete reflected-source remainder.
`exists_norm_zetaSquareRightKernel_sub_leading_le` bounds the whole
normalized contour error by `C exp(-90u²)(1+|u|)^12`, uniformly for
`t≥4`. `exists_norm_zetaSquareDivisorIntegral_sub_leading_le` consumes
the actual convergent ordinary-divisor series and gives one uniform
`O(1)` remainder. No Gamma asymptotic, mean-square, or moment theorem
is assumed. The continuation adds 44 public audits, the promoted
Gamma derivative audit, and 14 regressions. Root imports and the
inventory behind `run_tao_trudgian_yang_build.bat` include all seven.
Nine further modules now prove actual divisor-weight control, the
`Oε(T^(1/2+ε))` coefficient mass, and freezing with error
`Cε |x| T^(-1/2+ε)`. They preserve the actual Gamma phase and divisor
oscillation. Conjugation proves the factor-two entry for the real zeta
square; `exists_abs_zetaSquareGaussianWindow_sub_quadratic_le`
combines the source freeze, Gaussian tails and actual phase transform
into a comparison with the complete quadratic divisor sum.
The 78 public audits and 20 regressions are in the root imports and
the inventory behind `run_tao_trudgian_yang_build.bat`.
Six more modules now prove finite frequency shortening and the uniform
source-scale assembly. For each `δ>0`, beyond one threshold for all
`0<G≤T^(1/2-δ)`, the actual Gaussian mean differs from twice the real
part of the finite divisor source by at most `Cδ G log T`.
`exists_zetaSquareLocalMean_le_short_divisor` gives the unsmoothed
local-second-moment consumer. On `G≥T^δ`, the retained indices lie
within `T log T/(pi G)` of `T/(2pi)` and remain comparable with `T`.
All 29 public audits and 18 regressions are in the root and batch inventory.
Eight further modules now construct the actual smooth positive-support
source, pay its transition error, and apply native modulus-one Voronoi.
The literal `Y0` and `K0` bridges preserve every transform constant.
`exists_zetaSquareLocalMean_le_bessel` links the actual local zeta
second moment to these Bessel integrals with uniform `Cδ G log T`
error. Its 43 public audits and 18 regressions are covered by the root
and batch inventory. Seven further modules now prove the complete
`K0` branch negligible: for every fixed `A` and `δ>0`, its norm is
at most `G T^(-A)` on `T^δ≤G≤T^(1/2-δ)` beyond one uniform
threshold. The proof consumes the full smooth support, literal kernel
integral, absolute integrability and actual divisor series at two.
`exists_zetaSquareLocalMean_le_main_minus` now leaves only the
logarithmic main term and oscillatory `Y0` sum, with error
`Cδ G log T`. All 29 additional public audits and 16 regressions
are in the root and exact batch inventory. Six further modules now
insert the source-required lattice phase `exp(-2pi i x)`: integer
coefficients, norms and support are unchanged, but the continuous
integrals are not identified with the old ones. Native Voronoi is
reapplied; the new complete K0 bound and actual source removal are
proved. `exists_zetaSquareLocalMean_le_atkinson_reduced` is the
phase-corrected source consumer. Exact amplitude/carrier factorization
and the unique nondegenerate saddle are also kernel-checked for both
signs. The 40 public audits and 22 regressions are included in the
root and batch inventory. Nine further modules now prove and consume
the phase-adjusted main-integral bound `C G log T`. Every actual
amplitude factor has proved uniform variation; native logarithmic
reflection provides the square-root cancellation. The new consumer
`exists_zetaSquareLocalMean_le_atkinson_minus` retains only the
complete phase-adjusted Y0 divisor sum, with uniform `Cδ G log T`
error. The 38 public audits and 20 regressions are covered by the
root and batch inventory. Thirteen further modules now prove the literal
Y0 decaying-ray representation and two-term expansion with explicit
`K x^(-5/2)` error for every `x>0`. The actual error series is
summed at divisor exponent `5/4`; the complete replacement costs
at most `C G`. `exists_zetaSquareLocalMean_le_atkinson_twoTerm`
and its physical Gaussian companion consume it with uniform
`Cδ G log T` error and no analytic premise. All 71 public audits
and 25 regressions are covered by the root and exact batch inventory.
Ten further modules prove frequency-uniform cancellation for the actual
signed carriers after the exact square substitution, with
`|Iα(T,G,L,b)|≤Cα G T^(-α)` for every real b.
All four leading/correction carriers are identified, integrable and
summed through the genuinely convergent source. The actual summands have
proved `n^(-1/4)` and `n^(-3/4)` bounds; these majorants are not
summable and are not used for absolute summation.
`exists_zetaSquareLocalMean_le_carriers` and its physical Gaussian
companion retain the complete carrier series and the uniform source
error. All 43 public audits and 24 regressions are in the root and
exact batch inventory. Four further modules and the generalized
weighted-primitive lemma now prove reciprocal-frequency decay on
the full support, summability and `C G` control of the complete
correction, and both physical zeta consumers with only the leading
signed carriers retained. Their 19 new public audits and 16
regressions are covered. Fifteen further modules now construct actual C2
amplitude bounds and the exact signed Fourier/source identity. They prove
the leading tail bound `C G T^(5/4) N^(-1/8)`, hence `C G` for
`N≥T^10`. Both physical zeta consumers retain the finite actual leading
sum with the same uniform `Cδ G log T` error. All 59 new public
audits and 20 regressions are in the root and batch-runner inventory.
This is coarse polynomial truncation. The later checkpoints below prove
evaluated stationary mains and source-scale localization. The summed
stationary error, sharp Atkinson assembly and genuine twelfth moment
remain open. These source consumers assume no analytic theorem. The full goal and counterexample
are unchanged; the exact batch interface remains part of the goal.

## Exact intended outputs

The initial completion contract covers all results advertised by the paper as
new:

1. the four exponent pairs in `new-exp-pair`;
2. the improved Heath--Brown zero-density theorem `hb-density2`;
3. the improved Bourgain density-hypothesis bound
   `bourgain-density-improved`;
4. the eight-piece optimized Bourgain zero-density bound
   `bourgain-zero-density-optimized`; and
5. all nine clauses of the additive-energy theorem `Add-est`.

The exact statements and rational endpoints are frozen in
[`Tao-Trudgian-Yang Crosswalk.md`](Tao-Trudgian-Yang%20Crosswalk.md). A
release is not complete until the public Lean statements match those formulas,
the source-to-Lean dependency edges are proved, and every theorem passes the
project integrity and semantic audits.

## Main research finding

The live [ANTEDB repository](https://github.com/teorth/expdb) now has a real
Lean library. At commit
`088040634e8300f87e80f431d8bdc38c42cc8e11` it contains proved foundations for
cheap asymptotic notation, automatic uniformity, model phase functions,
exponential sums, the exponent-sum growth function, Euler--Maclaurin, and
Fourier/L2 estimates. It does **not** yet contain Lean modules for exponent
pairs, large-value exponents, zero-density exponents, or additive-energy
exponents.

That upstream is therefore a foundation, not a complete formalization of this
paper. Its upstream Lean toolchain is `v4.32.0`; the completed local
Guth--Maynard foundation is on `v4.30.0`. EPZAE-01 resolved that boundary by
compiling an attributed, hash-pinned subset of ANTEDB on the local Lean 4.30
graph.

## Layout

- `Tao-Trudgian-Yang Goal Prompt.md` -- immutable whole-project contract.
- `Tao-Trudgian-Yang Research Agenda.md` -- staged implementation plan and
  risk register.
- `Tao-Trudgian-Yang Architecture.md` -- dependency graph with checklist
  ownership.
- `Tao-Trudgian-Yang Checklist.md` -- acceptance tests for every work package.
- `Tao-Trudgian-Yang Crosswalk.md` -- paper labels, formulas, and planned Lean
  consumers.
- `Tao-Trudgian-Yang Sources.md` -- literature, repositories, and reuse survey.
- `Tao-Trudgian-Yang Reproduction Manifest.md` -- pins and verification policy.
- `Sources/` -- the primary paper, source archive, figures, and frozen ANTEDB
  snapshots.
- `Dependencies/` -- attributed frozen ANTEDB compatibility subset and
  dependency decision record.
- `Extension/` -- unified Lean package and production modules.
- `Tools/` -- source-integrity, build, regression, and audit implementation.
- `run_tao_trudgian_yang_build.bat` -- principal human-facing verification
  runner; it builds the unified package and runs every currently installed
  integrity, regression, and audit gate.

## Current implementation frontier

EPZAE-00--05, EPZAE-07--08, EPZAE-16--17, EPZAE-20, EPZAE-22--23,
EPZAE-25, EPZAE-31--32, and EPZAE-34--35 are complete. EPZAE-33 now includes a
multiplicity-safe bounded-perturbation theorem, an explicit return from
arbitrary tolerance to unit energy, and a lift of the native Guth--Maynard
Type I beta-removal detector to every analytic-multiplicity copy. Its new
indexed mixed-energy and four-coordinate coloring theorems reduce the Type I
energy to four actual single-scale detector classes with explicit losses.
`EnergySeparation` now refines those colors by unit-bin parity and local rank;
the native Jensen bound controls the number of rank colors, and
`typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies` produces
four multiplicity-safe, one-separated, single-scale detector classes.
`DetectorPattern` now normalizes the native coefficients on the exact closed
dyadic support and packages every inhabited class as a `LargeValuePattern`;
`finsetAdditiveEnergy_image_eq` proves that this passage preserves the indexed
energy exactly. Its maximum coefficient normalizer is proved to be
`O_epsilon(N^epsilon)` from the native kernel-checked divisor bound. The
remaining native-detector Type I work is the quantitative scale/threshold
application of the `LV*` estimate. `ZeroEnergyDichotomy` now completes the
multiplicity-safe finite extraction for the paper's classical Type-I/Type-II
route: every zero copy inherits a beta-removed ordinate and genuine branch and
dyadic scale, the shifted Jensen cap yields one-separated color classes, and
`classicalSlabZeroEnergy_le_separated_branch_scale_class_energies` bounds the
full slab energy by four such classes with explicit losses. Converting the
classical Type II classes to the paper interface is also kernel-checked:
`exists_classicalTypeIIClassPattern` uses the native sharp-mollifier
normalization and preserves indexed energy exactly; its `_native` corollary
discharges the coefficient bound from the proved divisor estimate. Classical Type I pattern
conversion now also has an exact normalized weighted `LargeValuePattern` with
energy preservation. The exact source decomposition into two smooth blocks is
now used pointwise and at energy level: four fixed-block, one-separated
classes control the full Type-I class energy, and the same construction is
specialized to an actual classical Type-I branch/scale fiber. Exact
untruncated Fourier deweighting now turns every selected block into a large
literal coefficient-one Dirichlet sum on the exact active integer interval,
with an explicit Fourier-`L¹` loss.
The Fourier tail is now quantitative: order-two Schwartz decay bounds the
complementary integral uniformly in the original ordinate, and
`typeISourceFourierRadius` gives the explicit window
`max 1 (4 * card * seminorm / V)`. Consequently
`exists_separated_explicitTypeISourceFourier_energy_classes` unconditionally
selects bounded ordinates, retains the complete indexed energy through
tolerance normalization, and recolors it into four one-separated
coefficient-one classes. What remains analytically is source-scale/subpower
control of the block Fourier `L¹` majorant and seminorm radius, followed by
height-pattern packaging, applying `LV*`, and the dyadic/asymptotic assembly.
In parallel, the source-faithful sharp-block route now avoids the endpoint
smoothing entirely: `classicalTypeILogProfileSchwartz` is one fixed translated
profile for every dyadic scale,
`dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight` is its exact active-
interval identity, and `integral_norm_fourier_schwartz_compl_Icc_le_order`
provides tail decay of every polynomial order.
`exists_bounded_coefficientOne_shift_of_classicalTypeI` composes the full
sharp-block tail with finite-window extraction. The canonical positive-real
root `classicalTypeIFourierRadius` now makes the required numerical tail
inequality automatic at every order greater than one, and
`exists_classicalTypeI_explicitBoundedOrdinate_family` lifts the resulting
witnesses to the complete indexed family with explicit tolerance-normalized
energy transfer. `exists_separated_classicalTypeI_explicitFourier_energy_classes`
then performs the generic occupancy coloring and produces four one-separated
coefficient-one families. Subpower control of the canonical radius, including
the fixed seminorm and source `clog` loss, is now complete:
`exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow`
chooses one decay order and proves a uniform eventual `T^δ` radius for all
source-large scales and ordinates. Height-interval pattern packaging is now
complete: `classicalTypeICoefficientOneCoeff` realizes the active interval
inside the full dyadic block, and
`indexedClassicalTypeICoefficientOnePattern` constructs a paper
`LargeValuePattern`. `exists_classicalTypeI_explicitFourier_patterns` packages
all four color fibers on their common expanded interval, and
`IsLargeValueEnergyBound.classicalTypeI_explicitFourier_energy_transfer`
applies one finite-scale `LV*` witness to all four and transfers the resulting
bound back to the original indexed energy.
`classicalSlab_expanded_height_in_rpow_window` also proves that the beta and
Fourier expansions preserve the required height exponent window after a
fixed-factor absorption.

`ClassicalTypeIEnergyTransfer` now supplies the source's zeta-specific step.
The normalized source threshold is exactly `N^σ` divided by the fixed
Fourier norm, dyadic count, and `T^D`; its lower exponent window is proved
uniformly when `T^a ≤ N` and `D ≤ a*δ/2`. Three height colors place the
coefficient-one families in genuine zeta intervals `[H,2H]`, preserving the
active integer support and indexed energy. The complete perturbation and
coloring loss is bounded by `429981696*(1+d)^5` and absorbed into an
arbitrarily small scale power.
`IsZetaLargeValueEnergyBound.classicalTypeI_source_class_energy_bound`
consumes an actual classical Type-I branch/scale fiber, derives its separation
and source lower bound from its label, and proves the fixed-parameter
epsilon estimate. `exists_classicalTypeI_source_scale_subsequence` derives
`N ≤ 6T` from genuine source largeness and selects one physical exponent
`1 ≤ τ ≤ 1/a`, together with all required height windows, along a common
subsequence. `EnergyUniformity` and `ClassicalTypeIUniformity` now strengthen
this to a compact-range estimate: a single threshold window is chosen before
the source line and cutoff powers, and the actual multiplicity-preserving
Type-I fibers satisfy `energy ≤ C*T^(B+ε)`. Small excursions beyond the
physical scale endpoints and a slightly left-shifted source line are included.
`ClassicalTypeIIEnergyTransfer` supplies the corresponding uniform estimate
for the actual normalized mollifier fibers, using the proved divisor bound.
`ClassicalSlabEnergyTransfer` selects the common cutoffs and shifted line,
consumes both genuine source branches, and absorbs the outer multiplicity and
coloring losses. Its public
`classicalSlabZeroEnergy_bound_of_uniform_energy_bounds` proves the positive
dyadic zero-slab estimate from the specified zeta and general energy bounds.
`ZeroEnergyAssembly` now proves the symmetric-rectangle bridge by a signed
dyadic coloring, conjugate multiplicity copies, and a fixed low-height
rectangle. `isZeroDensityEnergyBound_of_uniform_energy_bounds` concludes the
paper's shifted `A*` predicate. `EnergyExponentTransfer` now removes those
conditional hypotheses using the actual exponent supremum and limsup. Its
`zeroDensityEnergyExponent_le_sup_limsup` proves the exact `zeroe-from-large`
inequality for `1/2 < σ < 1`, including the zeta supremum starting at `τ=1`.
EPZAE-33 remains open for the bounded-range corollary `zeroe-large-cor-0`;
EPZAE-34 is complete for the authorized two-witness repair, not the disproved
fifth-coordinate scaling. `EnergyPoweredPatterns` constructs normalized
powered blocks with exact closed/half-open support bridges and separate
cardinality/energy selections. `EnergyPoweringLimits` chooses realizing
scales after the coefficient constants and proves the required limits.
`CorrectedEnergyPowering` assembles the full theorem and its source-facing
consumer. `HeathBrownEnergyFinite`, `EnergyLogLimits`, and `HeathBrownEnergy`
complete EPZAE-35 through exact energy/phase/support bridges, physical-scale
limits, and full-domain height-padding removal. The small-height three-branch
constraint and its corrected powered form are also proved. The bounded-range
EPZAE-33 corollary and the remaining exact optimizations stay open. No advertised
new energy bound in `Add-est` is claimed complete.
The clause-(i) **general** optimization is now proved in
`EnergyClauseOneGeneral`, using the actual Huxley cardinality constraints in
`ClassicalLargeValueRegions` and the proved powered Heath--Brown relation.
`energyClauseOne_of_zeta_range` supplies conditional final assembly with
only the real zeta bounds on `[1,8σ-4)` remaining as its mathematical premise.
`EnergyClauseOneZeta` discharges the zeta rational certificate, the corrected
Huxley cap, and the uniform-cardinality-to-region bridge. Its end-to-end
`energyClauseOne_of_twelfth_and_short_zeta` explicitly retains only
short zeta energy on `[1,2)` and the twelfth-moment cardinality bound on
`[2,8σ-4)`. It is conditional; the other optimization clauses and the
missing analytic inputs are not assumed proved.
The refined consumer `energyClauseOne_of_dyadic_moment_and_short_zeta`
now derives the uniform cardinality input from the dyadic critical-line
moment, using the proved exact Perron entry, uniform localization, and
physical exponent windows. Its modular two-input interface is preserved.
`energyClauseOne_of_dyadic_moment` now supplies the short-zeta premise
through proved cancellation, threshold-relative Perron entry, and the
exact cubic-energy comparison. Only the genuine moment remains as an
analytic input to the assembled clause-(i) theorem.
`EnergyPoweringBounds` now transfers uniform energy bounds via that proved
witness and reduces all high general scales to `[τ₀,2τ₀]`. Its compact-range
zero-energy consumer still uses zeta endpoint `1`; reaching the printed
endpoint `2` remains an EPZAE-33 source obligation, independently of the
clause-(i) route that now supplies the full endpoint-one range.
The next exponent-pair analytic
frontier is EPZAE-09: the remaining endpoint/reflection and converse direction
of beta/exponent-pair duality.
The deterministic certificate extractor in the principal runner now
reproduces the four output coordinates, derives the paper's complete
eight-piece Bourgain rational table, and extracts all nine public
additive-energy clause tables from the frozen blueprint. EPZAE-06 remains open
until it also reproduces every underlying energy-projection witness and the
archived Python environment is pinned.

## Non-claims

- ANTEDB's Python output is discovery evidence, not Lean proof evidence.
- A checked rational inequality is not a proof that its analytic input is an
  exponent pair or a large-value theorem.
- The completed Guth--Maynard theorem supplies `guth-maynard-lvt` only through
  the explicit, kernel-checked support, reflection, phase, coefficient, and
  epsilon-loss conversions in `GuthMaynardBridge.lean`; it does not
  automatically prove the other large-value inequalities used in the paper.
- A theorem parameterized by the desired exponent-pair, density, or energy
  conclusion is conditional and cannot satisfy the release contract.
- The source paper itself describes its computation as not formally
  certified. This project must replay every optimization through
  kernel-checked certificates.

## Repository synchronization

Use the repository-root `push_to_github.bat` only when deliberately requested.
Do not add a second synchronization workflow here. A suitable future commit
message for this scaffold is:

`plan Tao-Trudgian-Yang 2025 formalization and pin primary sources`

## Finite stationary reduction checkpoint

The actual carrier now has a proved approximation by its finite quadratic
stationary main term. `AtkinsonStationaryPhysical` derives the window
conditions from 10000n≤T and H≤sqrt(T)/12, for both signed frequencies.
The exact source phase, (-1)^n, both pi/4 signs and common damped Gaussian
are proved; the two actual cutoff/Mellin profiles remain distinct.
Natural amplitude derivatives have scale G/sqrt(T), not the earlier
Fourier amplitude's scale T. Twelve modules, 71 named audits and
22 regressions are included in the root and exact batch-runner inventory.

The Fresnel limiting value is now proved below; the sharp Atkinson estimate remains open.
The twelfth moment and all unconditional Add-est outputs remain open.
The full goal, corrected powering/Heath–Brown chain and byte-preserved
counterexample remain unchanged. Keep `run_tao_trudgian_yang_build.bat`
updated with this chain and run both principal evaluation scopes.
See the Goal Prompt and Reproduction Manifest for exact statements and evidence.

## Evaluated stationary main and physical power saving

Nine further modules prove the Fresnel value, explicit 2/(c H pi) tail
and their use in the actual stationary main. Both saddle phases are
evaluated without dropping either amplitude.
`exists_atkinsonPowerIntegral_source_power_saving` derives error
Cα G T^(-α) T^(-η) for both ±sqrt(n), 10000n≤T, with
η=min(δ/3,1/10), L=log T and T^δ≤G≤T^(1/2-δ), eventually.

All 35 new public theorems and 16 regressions are in the root, audit
and exact `run_tao_trudgian_yang_build.bat` inventory.
Sharp localization, summed errors, sharp Atkinson, the genuine twelfth
moment and unconditional Add-est remain open. The counterexample and
corrected powering/Heath–Brown chain are unchanged. See the Goal Prompt
and Reproduction Manifest for the continuing contract and verification.

## Source-scale truncation checkpoint

The actual complete leading tail is now O(G) for
N≥36T(log T/G)² on the original physical width range, eventually.
Both physical zeta consumers use this shorter finite sum with Cδ G log T
error. The explicit ceiling cutoff also lies in the proved stationary
range: every retained index receives both evaluated carrier estimates.

Eleven modules, 53 named audits and 22 regressions are in the root and
`run_tao_trudgian_yang_build.bat` inventory. The original counterexample
and corrected powering/Heath–Brown chain are unchanged.
Summed stationary errors and final main-amplitude/source assembly remain
before sharp Atkinson and the genuine twelfth moment; unconditional
Add-est remains open. The Goal Prompt retains the full completion
contract, and the Reproduction Manifest records both runner results.

## Symmetric stationary sum checkpoint

Both actual physical zeta consumers now use the complete evaluated
stationary series. At G≥T^(1/4) the proved error is
Cδ,ε (G log T+T^(1/4+ε)); at G≥T^(1/4+κ), κ>0, it is Cδ,κ G log T.
The original power-width hypotheses remain in both statements.

Ten modules, 43 named audits and 24 regressions are in the root and
exact batch-runner inventory. The goal and architecture retain the
smaller-width error, remaining source main assembly and genuine twelfth
moment as open obligations. No unconditional Add-est clause is closed.
The counterexample and corrected powering/Heath–Brown chain are unchanged.

## Normalized main and partial-summation checkpoint

Five new modules, 30 named audits and 24 regressions derive the actual
common fourth-root coefficient from the original saddle power, curvature
and Bessel constants. Both signed main sums retain separate cutoff/Mellin
weights. Only the raw phase sums are conjugated.

The actual weights have a proved uniform bound
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) on n≤T,
T,G,L>0, G²≤2T and 8L≤G. The exact Abel bound retains literal finite
weight differences. Both physical zeta consumers are linked to the same
explicit source cutoff and normalized mains. Errors remain
Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or Cδ,κ G log T above
T^(1/4+κ), within the original power-width range.

The continuation below proves uniform damped variation and the actual
source-block bound. Global dyadic/Gram assembly, smaller source widths or
a proved lower-value-range reduction, and the genuine twelfth moment remain open. No unconditional Add-est clause is closed.
The original counterexample and corrected powering/Heath–Brown chain
are unchanged. The exact `run_tao_trudgian_yang_build.bat` inventory
is synchronized; maintain it and rerun both principal evaluation scopes.

## Damped variation and source-block checkpoint

Six new modules, from `FiniteWeightVariation` through
`AtkinsonPhaseBlockBound`, have 36 named public audits and 24 regressions.
The actual Gaussian increments telescope against a decreasing real
envelope. Ordered actual saddle samples, the constructed Mellin bound,
both original cutoff transitions and the decreasing fourth-root
coefficient give uniform variation for both separate normalized weights.

`exists_finiteVariationBound_atkinsonMainWeights` bounds both the
supremum on indices 0..N and the adjacent-difference sum by
C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)), for
T,G,L>0, G²≤2T, m>0 and 10000(m+N)≤T.
No 8L≤G condition or conjugacy of residual weights is assumed.

The actual stationary Bessel/divisor block at m..m+N-1 is bounded by
that same shape times the maximum of the actual raw phase partial sums,
with a larger uniform C. `exists_atkinsonSourceCutoff_block_bound`
derives its small-frequency and scale conditions for every retained
block from the original power-width range and the exact source ceiling
cutoff, beyond a δ-dependent threshold.

ZVB records these proved consumers; the continuation below also proves
global dyadic assembly. The phase-sum/Gram bound, smaller-width stationary errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
The block theorem has no fourth-root-width restriction; the earlier
stationary-error/zeta consumer still does. No unconditional Add-est
clause or full EPZAE-00--41 completion is claimed.

The original counterexample and independent-coordinate powering/
Heath–Brown chain are unchanged. The exact
`run_tao_trudgian_yang_build.bat` root/audit/PowerShell inventory is
synchronized; maintain it and rerun both principal evaluation scopes.
See the Reproduction Manifest for the semantic audit and terminal evidence.

## Complete dyadic-source checkpoint

Three new modules, `TruncatedDyadicPartition`, `AtkinsonDyadicMain`
and `AtkinsonDyadicZetaConsumer`, have 20 named public audits and
24 regressions. The exact partition uses M=2^j and block length
min(M,N-M), for j<clog(2,N). Every retained endpoint stays at or below
the original cutoff; zero/one cutoffs and exact powers of two are covered.

The actual complete stationary Bessel/divisor series is now bounded by
C G T^(-1/4) times the sum of
M^(-1/4) exp(-G²M/(12T)) times the actual block phase-prefix maximum.
The same source ceiling cutoff supplies every block's small-frequency
geometry. Enlarging only the last raw phase maximum to a full block
does not enlarge the stationary source.

Four Gaussian/local-mean consumers use this complete dyadic bound.
Their error remains Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or
Cδ,κ G log T for G≥T^(1/4+κ), within the original power-width range.
The stationary-main bound itself has no fourth-root-width restriction.
ZDA records this exact assembly and these physical consumers.

Global dyadic assembly is now proved. The maximal phase-sum/Gram
estimate, the source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.
