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
That moment theorem remains unproved. The final clause also needs short zeta
energy on `[1,2)`, or the source endpoint-two transfer. Neither analytic
gap is claimed closed; see the checklist's EPZAE-21/33/36/37 entries.

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
critical-line twelfth moment. Its
`energyClauseOne_of_dyadic_moment_and_short_zeta` reaches clause (i)
conditional on that moment and short zeta energy on `[1,2)`.
Neither remaining input is claimed proved; no final `Add-est` status changes.

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
physical exponent windows. Only that moment and short zeta energy remain
as analytic theorem inputs to this consumer.
`EnergyPoweringBounds` now transfers uniform energy bounds via that proved
witness and reduces all high general scales to `[τ₀,2τ₀]`. Its compact-range
zero-energy consumer still uses zeta endpoint `1`; reaching the printed
endpoint `2` is the remaining short-zeta-scale obligation in EPZAE-33.
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
