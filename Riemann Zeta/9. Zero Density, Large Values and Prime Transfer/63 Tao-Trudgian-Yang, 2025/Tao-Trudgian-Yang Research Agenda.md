# Tao--Trudgian--Yang 2025 research agenda

Current analytic progress: [Robert–Sargos zero-r row](#robertsargos-zero-r-row--current-checkpoint).
The actual signed zero-r row and its A-times-A cost at the source floor scales are proved. The zero-q column, diagonal and remaining fourth-derivative assembly are OPEN; completion stays 29/42.

Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


## Executive assessment

The repaired energy branch is now complete through all nine Add-est
outputs (EPZAE-36/37). The exact density/energy transfers and their source
corollaries are also complete (EPZAE-24/33). Exponent-pair, new density
outputs and full-release obligations
remain; see the current checkpoint for exact scope and build evidence.

This project is feasible as a staged extension of two unusually strong local
assets:

- ANTEDB's newer Lean foundation already models the paper's cheap asymptotic
  language and exponential-sum growth function; and
- the neighboring Guth--Maynard project already proves the deepest large-value
  and zero-density input used by the 2025 paper.

The main difficulty is not rational arithmetic. It is building faithful
interfaces between four semantic layers: asymptotic exponential sums,
large-value patterns, zeta zero counts, and additive energy. The optimization
should be formalized as proof-producing exact finite certificates only after
those meanings are fixed.

## Historical implementation baseline (19 September 2026)

EPZAE-00--05, EPZAE-07--08, EPZAE-16--17, EPZAE-20, EPZAE-22--23,
EPZAE-25, and EPZAE-31 pass. The project now has one Lean 4.30 graph,
an attributed frozen ANTEDB subset, exact rational/piecewise/polyhedral
certificate kernels, and the paper's analytic exponent-pair definition with a
proved non-asymptotic equivalence, an exact multiplicity-weighted zero-
rectangle bridge, the extended-real density exponent with its epsilon-loss
interface, and exact shifted-convention bridges for the native Ingham,
Huxley, and Guth--Maynard estimates, faithful general/zeta large-value
patterns and least-exponent interfaces, and the exact `guth-maynard-lvt`
bound obtained from the native publication theorem through proved support,
reflection, phase, norm, threshold, and epsilon-loss conversions, together
with unit-tolerance indexed-
multiset energy and its quadratic/cubic bounds. These bounds now induce the
extended-real general and zeta exponent comparisons `2LV ≤ LV* ≤ 3LV`, even
at infinite infima, together with the unconditional zero-density comparison
`2A ≤ A* ≤ 4A` and the sharp source-range comparison `2A ≤ A* ≤ 3A` for
`1/2 < σ`. The upper factor three follows from a uniform local-multiplicity
bound for the full symmetric zero rectangle: positive ordinates use the
Jensen cap, negative ordinates use conjugation, and bounded heights use a
fixed zero count. The non-asymptotic energy regions imply the necessary
`ρ ≤ τ` and `2ρ ≤ ρ* ≤ 3ρ` constraints, and their general/zeta energy-coordinate
suprema are proved bounded above by the corresponding `LV*` exponents. The
remaining checklist items are open; none of the advertised
paper outputs is complete.

## Phase 0: freeze and compatibility

**Complete.** The selected ANTEDB subset was backported to the local Lean 4.30
graph with two documented compatibility edits, and the two-source import spike
is part of the default build and audit.

1. Preserve arXiv v1 PDF and TeX source with hashes.
2. Preserve the paper-time ANTEDB snapshot and the current Lean-enabled
   snapshot as separate archives.
3. Compare Lean `v4.30.0` (local Guth--Maynard) with ANTEDB `v4.32.0`.
4. Choose one route and document it:
   - port the selected ANTEDB modules back to the local `v4.30.0` graph;
   - upgrade the Guth--Maynard dependency graph to `v4.32.0`; or
   - upstream the new work directly in ANTEDB and build a separately pinned
     bridge to the local foundation.
5. Prove a two-module import spike before creating the full package.

Recommended route: first test a narrow backport of ANTEDB's `Basic` and
`ExponentialSums` modules to the local `v4.30.0` mathlib revision. Their source
surface is small enough to evaluate, while upgrading the completed
Guth--Maynard tree is high risk.

## Phase 1: exact certificate kernel

**Core acceptance test complete (EPZAE-03--05).** Exact denominator signs for
all displayed output formulas, generic envelope/polyhedral soundness, and the
optimized Bourgain endpoint/coverage certificates are kernel-checked. The
deterministic generator now extracts the four new-pair coordinates, derives
the complete eight-piece Bourgain rational table from the frozen driver, and
normalizes all nine public energy-clause tables from the frozen blueprint. Its
remaining EPZAE-06 work is the underlying energy-projection witness set and a
pinned run of the archived Python stack. `EnergyCertificates.lean` consumes
the emitted clauses and kernel-checks interval ordering and denominator
positivity for every rational function.

Build reusable, domain-independent machinery for:

- normalized rational functions with denominator-positivity side conditions;
- affine bounds over closed/open rational intervals;
- exact crossover computation;
- maxima and minima of finite families;
- convex combinations and convex-hull witnesses;
- rational polyhedra represented by finite inequalities;
- projection certificates carrying explicit eliminated-variable witnesses;
- piecewise envelope coverage and endpoint agreement.

The certificate format must be deterministic and small enough to audit. A
Python script may emit rational witnesses, but Lean must check every equation,
inequality, interval cover, and sign condition.

First milestone: certify a harmless subset of the beta table and prove that a
specified affine line dominates on its stated interval.

## Phase 2: exponent pairs and beta

**In progress.** EPZAE-07--08 are complete. Convexity and beta duality are the
next open analytic edge.

1. Reuse ANTEDB's `exponentSumGrowthExponent` and non-asymptotic equivalence.
2. define the analytic `ExponentPair` predicate;
3. prove monotonicity and convexity;
4. prove beta/exponent-pair duality, including endpoint and reflection handling;
5. formalize or import exact versions of A, B, C, and Sargos D;
6. formalize Heath--Brown's kth-derivative beta bound;
7. certify every beta-table segment needed by the four output pairs; and
8. prove the four `new-exp-pair` conclusions from global affine bounds.

The D-process sentence in the paper says it “in practice” yields an exponent
pair. Lean must contain the actual duality argument; it may not record D as an
unproved constructor.

## Phase 3: large-value semantics

**In progress.** EPZAE-16--17 and EPZAE-20 are complete. In particular,
`guthMaynard_largeValueBound` proves the source maximum of all three affine
exponents from the native publication theorem. Elementary/classical and
zeta-specific large-value inputs remain under EPZAE-18--19 and EPZAE-21.

1. Define large-value patterns with exact interval, separation, coefficient,
   phase-sign, and normalization conventions.
2. Define `LV(sigma,tau)` and `LV_zeta(sigma,tau)` with explicit epsilon-loss
   quantifiers rather than an informal least exponent if that gives a cleaner
   public API.
3. Prove equivalence with the paper's least-exponent formulation.
4. Formalize subdivision, lower bounds, L2 mean value, raising to a power, and
   zeta-specific bounds.
5. Bridge the completed local Guth--Maynard theorem to equation
   `guth-maynard-lvt` with all coefficient and interval conversions visible.
6. Formalize only the portions of Bourgain/Jutila/Huxley/Heath--Brown needed by
   the target certificates, then broaden after the endpoints compile.

## Phase 4: zero density

1. Define the paper's multiplicity-weighted `N(sigma,T)`.
2. Prove its equality/inequality bridge to the local `zeroCountRect` convention.
3. Define the density exponent `A(sigma)` and its epsilon-loss API.
4. Formalize the Type I/Type II zero-density-from-large-values theorem and the
   corollaries used by the paper.
5. Reuse local Ingham, Huxley, and Guth--Maynard results only through exact
   bridges.
6. Prove `hb-density2`.
7. Prove `bourgain-density-improved` and both subrange simplifications.
8. Formalize Bourgain's exponent-pair density theorem and its side conditions.
9. Certify the eight-piece optimized bound, including all crossover points and
   admissibility conditions.
10. Treat the full best-known table as a corollary/validation artifact, not as
    the definition of `A`.

## Phase 5: additive energy

1. Define finite multisets of ordinates and approximate additive energy with
   the source tolerance and multiplicity.
2. Prove the elementary energy inequalities and stability under bounded
   perturbation used in the zero-to-large-value transfer.
3. Define `LV*`, `LV*_zeta`, `A*`, `E`, and `E_zeta` faithfully.
4. Prove the non-asymptotic energy-region equivalence.
5. Finish the zero-density-energy transfer's bounded-range corollary.
   The source's weakened powering lemma is now disproved even with separate
   witnesses. Use the now-proved owner-authorized cardinality/energy
   replacement from EPZAE-34, with no fifth-coordinate scaling. See the
   preserved obstruction and repair evidence below.
6. Formalize Heath--Brown's five-variable max inequality.
7. Turn every polyhedral projection used by `Add-est` into an exact certificate.
8. Prove all nine clauses and their interval endpoints.

The reverse zero-energy comparison `A* ≤ 3A` is now kernel-checked on the
source range `1/2 < σ`. Its uniform local-multiplicity bridge covers the full
symmetric paper rectangle `|Im ρ| ≤ T`: it applies the Guth--Maynard Jensen cap
on positive unit bins, transfers negative bins by multiplicity-preserving
conjugation, and absorbs bounded-low-height zeros into a fixed count. The
source-facing unbounded-family energy regions are now proved equivalent to
their fully quantified non-asymptotic forms. The general, zeta-restricted, and
zero-density energy-bound predicates likewise have proved asymptotic/
non-asymptotic equivalences. `EnergyRegionSupremum` completes EPZAE-32:
failure of a uniform bound produces a bounded logarithmic counterexample
family, one common subsequence supplies all three auxiliary exponents, and
both the general and zeta energy exponents equal their feasible-region
suprema on the source domain.

The additive-energy section has the highest semantic risk because informal
subsequence selection can silently identify witnesses that the paper
explicitly warns may differ.

EPZAE-33 now has a kernel-checked bounded-perturbation core.  Pointwise
displacement by `d` maps every tolerance-`r` relation to a tolerance-`r+4d`
relation on the same index type, and its zero-specific corollary keeps the
full `ZeroCopy` analytic multiplicity.  `ToleranceNormalization` now proves
that tolerance-`R` indexed energy is at most `(4 * ceil R + 6)` times unit
energy, and `zeroAdditiveEnergy_le_mul_perturbed_unit` combines the two steps
without changing the multiplicity index.  `ZeroEnergyTypeI` additionally lifts
the native Guth--Maynard beta-dependence-removal theorem to every analytic-
multiplicity copy of every Type I zero: `typeIZeroCopy_exists_shifted_detector`
selects a nearby ordinate with the actual detector lower bound, and
`typeIZeroAdditiveEnergy_le_shifted_detector_energy` returns the resulting
energy to unit tolerance.  `EnergyPartition` proves the separation-free,
indexed mixed-to-self inequality and the four-coordinate finite-coloring
theorem `exists_energy_color_classes`.  The specialized theorem
`typeIZeroAdditiveEnergy_le_detector_scale_class_energies` now combines these
steps: the actual Type I zero energy is controlled by four single-scale
detector-class energies with explicit tolerance and fourth-power scale-count
losses.  `EnergySeparation` further colors by unit-bin parity and rank.
`typeIZeroCopy_shifted_unitBin_card_le` identifies copy occupancy with the
analytic-multiplicity sum and applies the native Jensen/finite-covering bound;
the composed theorem
`typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies` therefore
produces four one-separated single-scale classes without discarding a copy.
`DetectorPattern` normalizes the native half-open detector on closed support,
proves its exact phase-sum identity, and constructs a `LargeValuePattern` from
every inhabited class.  `finsetAdditiveEnergy_image_eq` proves that the image
finset retains the complete indexed energy, while
`typeIDetectorClass_energy_eq_zero_or_exists_pattern` handles empty classes
without a spurious scale.  The native kernel proof
`divisorCountBound_native` now yields
`exists_detectorPatternNormalization_le_const_mul_rpow`, so the coefficient
normalizer has the required epsilon-power loss.  Quantitatively matching the
pattern's height and threshold to `LV*`, the Type II transfer, and the final
dyadic assembly needed to finish `zeroe-from-large` remain open.

`ZeroEnergyDichotomy` now supplies the complete finite, multiplicity-safe
source-classical extraction.  `ClassicalSlabZeroCopy` has cardinality exactly
the native weighted `zeroCountRect`; `classicalZero_exists_shifted_branch_scale`
derives a beta-removed ordinate and genuine Type-I or Type-II dyadic scale for
every distinct zero from the source inequalities; and
`classicalSlabZeroEnergy_le_separated_branch_scale_class_energies` lifts those
choices to all analytic-multiplicity copies, transfers the native Jensen cap,
and bounds the slab energy by four one-separated fixed-branch/fixed-scale
classes with explicit perturbation and color losses.
`exists_classicalTypeIIClassPattern` additionally converts every inhabited
Type-II class to the exact closed-support paper `LargeValuePattern` using the
native normalized sharp-mollifier coefficients and proves exact energy
preservation; `exists_classicalTypeIIClassPattern_native` discharges its
coefficient majorant from the proved divisor bound.
`exists_classicalTypeIWeightedClassPattern` now supplies the exact normalized
weighted pre-deweighting pattern with energy equality.
`exists_large_typeISourceSmoothBlock_of_sharp_large` uses the exact source
two-block identity to select a block of size at least half the sharp sum, and
`exists_typeISourceSmoothBlock_energy_classes` retains the energy quantity by
coloring the indexed family into four fixed-block, one-separated classes.
`exists_classicalTypeISourceSmoothBlock_energy_classes` specializes this
construction to a genuine Type-I branch/scale fiber.
`exists_large_coefficientOne_shift_of_typeISourceSmoothBlock` packages the
exact Fourier identity with a positive block-specific `L¹` majorant and
extracts a literal coefficient-one sum; its chosen-block corollary applies
this pointwise to the deterministic two-block selection.
`integral_norm_fourier_schwartz_compl_Icc_le` proves an explicit order-two
Schwartz Fourier tail, and `norm_typeILogWeight_fourier_tail_integral_le_half`
combines it with the active-sum cardinality bound. Thus
`typeISourceFourierRadius = max 1 (4 * card * seminorm / V)` works uniformly
for every original ordinate. The resulting deterministic ordinate has a
proved `2πR` displacement bound, while
`unitBinFinset_perturbation_card_le_natCeil` and
`exists_separated_explicitTypeISourceFourier_energy_classes` retain the full
indexed energy, normalize its enlarged tolerance, and unconditionally produce
four one-separated coefficient-one classes. The remaining Type-I edge is
source-scale/subpower control of this radius and the block Fourier `L¹` loss;
height-pattern packaging, the corresponding `LV*` use, and asymptotic assembly
then remain.

The source-faithful sharp route now removes the artificial endpoint issue.
`dirichletPoly_classicalZetaLongLineCoeff_eq_active_sum` identifies the exact
interval `Ioc N (min (2*N) A)`, and a fixed bump equal to one on every dyadic
log interval gives
`dirichletPoly_classicalZetaLongLineCoeff_fourierDeweight`. Its `L¹` loss
depends only on the fixed line `σ`, while
`integral_norm_fourier_schwartz_compl_Icc_le_order` gives arbitrary-order
tail decay. `norm_classicalTypeI_fourier_tail_integral_le_order` includes the
physical scale and active cardinality, and
`exists_bounded_coefficientOne_shift_of_classicalTypeI` turns the resulting
numerical tail inequality into a bounded coefficient-one witness. The
indexed theorem `exists_classicalTypeI_boundedOrdinate_family` now selects all
of these witnesses simultaneously and proves the perturbation/tolerance
energy transfer without dropping an index. The canonical positive-real root
`classicalTypeIFourierRadius` makes that numerical premise automatic for every
order greater than one; its single-ordinate and indexed-family corollaries no
longer ask a caller for a tail proof.
`exists_separated_classicalTypeI_explicitFourier_energy_classes` composes the
existing occupancy and energy-coloring machinery and produces four
one-separated coefficient-one families with no dropped indices. The
order-selection theorem `classicalTypeIFourierRadius_le_rpow_of_base_growth`
already converts any `T^α` bound for the defining base, together with
`α ≤ δ(k-1)`, into the desired `T^δ` radius. The final epsilon absorption is
now complete: `eventually_classicalTypeIFourier_clog_loss_le_rpow` absorbs the
fixed seminorm and `clog`, while
`exists_order_eventually_classicalTypeIFourierRadius_sharpCutoff_le_rpow`
chooses one order and proves the uniform source-level radius bound. The next
height and finite-scale transfer steps are also kernel-checked:
`exists_classicalTypeI_explicitFourier_patterns` packages all four classes on
the expanded interval, and
`IsLargeValueEnergyBound.classicalTypeI_explicitFourier_energy_transfer`
applies one `LV*` witness to them and propagates the energy estimate through
the explicit perturbation and coloring losses.
`classicalSlab_expanded_height_in_rpow_window` converts a half-width source
height window into the full window for the expanded interval, absorbing the
factor five exactly.

`ClassicalTypeIEnergyTransfer` now proves the normalized source threshold
identity and its uniform lower power bound. It constructs exact zeta patterns
on three positive dyadic height slabs, including the sharp active interval's
excluded left endpoint. The finite zeta transfer is composed with the
Fourier extraction, and the full loss is at most
`429981696*(1+d)^5`, allowing it to be absorbed into any prescribed scale
epsilon loss. The theorem
`IsZetaLargeValueEnergyBound.classicalTypeI_source_class_energy_bound`
consumes actual classical branch/scale fibers, deriving largeness and
separation from their source labels. Its physical lower scale estimate
includes the floor cutoff. Separately,
`exists_classicalTypeI_source_scale_subsequence` derives the upper scale
bound from genuine source largeness and selects `1 ≤ τ ≤ 1/a` and all
height windows along one subsequence.

`EnergyUniformity` now uses a finite open cover to select one constant and
threshold window on a neighborhood of any compact height-exponent interval.
`ClassicalTypeIUniformity` derives that neighborhood condition uniformly from
the physical source bounds, applies it to the three genuine zeta slabs, and
absorbs the Fourier losses. Its public
`classicalTypeI_uniform_source_class_energy_bound` consumes the actual Type-I
color fiber returned by source extraction, retains analytic-multiplicity
indices, and concludes `energy ≤ C*T^(B+ε)`. The threshold window is chosen
before the source line and threshold power, and a slightly left-shifted
real-part line is allowed. No separately assumed height window remains.

`ClassicalTypeIIEnergyTransfer` now derives the exact normalized mollifier
threshold, absorbs its divisor and logarithmic losses, and consumes the actual
Type-II color fiber. Its compact physical scale window is derived from the
source floors and dyadic label. The same slightly shifted real-part line is
allowed in this general-energy estimate.

`ClassicalSlabEnergyTransfer` bounds the outer source extraction loss by
`K*T^(13*θ)`, retaining the genuine local analytic-multiplicity cap. The public
`classicalSlabZeroEnergy_bound_of_uniform_energy_bounds` then chooses the
cutoffs, threshold power, source line, and displacement in dependency order,
consumes both branch consumers, and proves a shifted positive dyadic zero-slab
bound `C*T^(B+ε)`. The impossible `none` source color contributes zero, proved
from the extraction assertion rather than assumed. This theorem takes only
the stated zeta energy bounds for `τ ≥ 1` and general energy bounds beyond a
fixed positive scale threshold as mathematical inputs.

`ZeroEnergyAssembly` now proves index-injective energy restriction, exact
reflection, and transfer of subfamilies into their actual positive slabs.
The negative-height bridge uses the proved conjugate analytic vanishing
orders. Signed dyadic coloring covers the symmetric rectangle, including
closed slab edges and the terminal partially occupied slab; bounded heights
are absorbed using the actual finite zero energy. The logarithmic coloring
loss is an arbitrary height power. The public
`isZeroDensityEnergyBound_of_uniform_energy_bounds` composes this assembly
with the source slab theorem and concludes the exact shifted paper predicate
`IsZeroDensityEnergyBound σ (B/(1-σ))`.

`EnergyExponentTransfer` now derives the uniform energy bounds from real
upper bounds on the extended-real exponents via the proved feasible-region
compactness theorem. Genuine singleton patterns prove nonnegativity of the
general energy exponent and hence of the transfer envelope. The public
`zeroDensityEnergyExponent_le_sup_limsup` concludes the exact source
`zeroe-from-large` inequality on `1/2 < σ < 1`, with zeta supremum over
`τ ≥ 1` and the genuine general-energy limsup. It has no remaining
mathematical theorem parameter and consumes the complete analytic transfer.

EPZAE-33 remains open for `zeroe-large-cor-0`. Its v1 statement starts the
bounded zeta supremum at `2`, unlike the preceding lemma's endpoint `1`;
that additional short-scale reduction must be proved, not silently changed.
The bounded general-energy reduction now consumes the proved corrected
energy witness: `IsLargeValueEnergyBound.of_powered` transfers the complete
uniform epsilon-loss bound, and
`isLargeValueEnergyBound_of_bounded_power_range` covers all `τ ≥ τ₀` from
`[τ₀,2τ₀]`. `isZeroDensityEnergyBound_of_bounded_energy_ranges` feeds this
into the actual transfer, with zeta inputs on `[1,τ₀)`. It is explicitly
not the source endpoint-two corollary. The exact five-coordinate source claim is still disproved,
as recorded below; it cannot be used as an upstream theorem.

### EPZAE-34 source obstruction (20 September 2026)

`EnergyPoweringObstruction` proves actual membership of `(3/4,2,0,0,2)`
using singleton large-value patterns and all approximation quantifiers.
Every energy-region point has `s ≥ 2`, so the printed `k=2` conclusion
`s' ≤ 1` is impossible even for one output witness.
`energyPowering_source_counterexample` is kernel-checked and explicitly
audited; this is a disproved source claim, not an unimplemented proof.
The live ANTEDB blueprint repeats the claim, and no correction was found
in the primary sources checked. Full evidence and scope are in
`Tao-Trudgian-Yang Energy Powering Obstruction.md`.

The owner has now authorized the documented replacement below. The original
source, counterexample, and advertised final output statements remain
unchanged. No inference is made that the advertised estimates are false.
The completed `zeroe-from-large` proof is independent of the invalid
powering statement.

### Authorized two-witness repair (20 September 2026)

`EnergyPowering` defines the actual projected region
`InCardinalityEnergyRegion σ τ ρ e := ∃ s, InLargeValueEnergyRegion σ τ ρ e s`
and the exact two-output target `CorrectedCardinalityEnergyPowering`.
One witness preserves `ρ/k` and bounds energy above by `e/k`; the other
preserves `e/k` and bounds cardinality above by `ρ/k`. Their fifth
coordinates are independent existential values. There is no `s/k` bound.

The following are kernel-checked: the exact expanded five-coordinate
specification equivalence; identity-power and singleton regressions;
`exists_energy_preserving_color` with loss `9 * card(colors)^4`; separate
monotone cardinality/energy consumers and their intersection rule; the
Heath--Brown right side's monotonicity in cardinality; and the powered
Heath--Brown consumer. The latter takes the two actual output witnesses and
the independently stated analytic relation as explicit upstream inputs.
It proves the required deduction without mentioning `s`, not either input.

The full analytic theorem is now kernel-checked:
`correctedCardinalityEnergyPowering : CorrectedCardinalityEnergyPowering`.
Its production chain is:

1. `EnergyPoweredPatterns` proves the loss-one endpoint removal, exact zero
   padding back to closed support, and uniform construction of all normalized
   dyadic blocks. `exists_normalized_powered_subpatterns` selects two actual
   patterns with respective losses `k` and `9*k^4`.
2. `exists_powering_input_family` in `EnergyPoweringLimits` chooses realizing
   scales after the accuracy-dependent coefficient constants. Their logarithms
   divided by `log N` tend to zero. The scale and threshold limit lemmas
   prove `log_N M → k`, `log_M T → τ/k`, and `log_M V' → σ`.
3. `energyRegion_subsequence_of_log_limits` derives a compact box from actual
   nonempty patterns and extracts all three coordinates. Applying it to
   the two separately selected families preserves exactly `ρ/k` or `ρ*/k`
   and bounds the other coordinate above. The two new double-zeta exponents
   are independently extracted, not inherited from the input.
4. `InLargeValueEnergyRegion.corrected_powering` exposes the full source-facing
   conclusion. The reusable conditional
   `InCardinalityEnergyRegion.powered_heathBrown_relation` takes an independently
   stated analytic relation; `InCardinalityEnergyRegion.heathBrown_powered`
   now supplies that input from its full proof.

EPZAE-34 and EPZAE-35 are complete. The newer unconditional
`InCardinalityEnergyRegion.heathBrown_powered` discharges the analytic input
of the earlier conditional consumer described above.
EPZAE-36 must replay all optimization constraints using the justified
four-coordinate rules, and EPZAE-37 must derive all nine unchanged endpoints.

The repair report includes a mathematical proof route and a static audit of
the pinned optimizer. Its Heath--Brown `2a` alternatives have zero `s`
coefficient, but historical five-coordinate transforms and finite boxes
must not be used as though arbitrary polytope closure followed from the repair.
No full certificate replay is
claimed. Authorization is no longer a blocker.

### Completed EPZAE-35: native moment derivation

`InLargeValueEnergyRegion.heathBrown_relation` proves the exact displayed
two-max source inequality, not a conclusion-shaped conditional interface.
The immediate proof chain is:

1. `finsetAdditiveEnergy_eq_native` identifies the two actual ordered
   quadruple encodings. Reflection preserves that energy and cardinality;
   the half-open reflected polynomial equals the original phase convention
   exactly, after the explicit one-point `V-1` threshold loss.
2. `heathBrown_largeValuePattern_energy_squared` consumes native
   `gmApproxAddEnergy_largeValues_native`, `gmDiscreteRatioSecondMoment_native`,
   `gmDiscreteFourthMoment_native`, and the finite third-moment Hölder bound.
   The epsilon-dependent constants precede the physical pattern quantifier.
   The mixed fourth-moment factor is the correct `E^(3/4) |W|`; the archived
   `hbt` proof's discrepant `N` factor is not used.
3. `PoweringInputFamily.heathBrown_energy_padded` consumes actual region
   witnesses and the linked logarithmic limits. `EnergyLogLimits` handles
   positive products, powers, maxima and sums. Physical height `max N T`
   has exponent `max 1 τ`; constants and the endpoint loss disappear only
   after taking the limit. `heathBrownEnergyRHS_max_one` removes this padding
   using the already proved `ρ ≤ τ`, so no `τ ≥ 1` restriction remains.
4. `InCardinalityEnergyRegion.heathBrown_powered` applies the analytic
   theorem to the corrected energy-preserving witness. Both upstream
   results are proved; no analytic theorem parameter remains.
5. `InLargeValueEnergyRegion.heathBrown_small_height` proves the source
   three-branch constraint for `τ ≤ 3/2`, and
   `InCardinalityEnergyRegion.heathBrown_small_height_powered` supplies its
   corrected powered version for optimization.

The three modules and their current 19 named public theorems are root-imported,
runner-inventoried, and explicitly audited. Regressions check the expanded
source inequality, arbitrary positive powers, the original counterexample
as an input, low height at `σ=1`, the closed `τ=3/2` endpoint, and the exact
energy-count bridge. The repair report records the semantic completion gate.
This completes the analytic HB node, not EPZAE-36's final projections,
EPZAE-33's zeta-endpoint-two reduction, or any EPZAE-37 `Add-est` clause.

### Completed general-energy half of `Add-est (i)`

`ClassicalLargeValueRegions` now bridges the actual patterns to the native
Montgomery--Halasz--Huxley estimate, with reflected ordinates, conjugated
coefficients, and the explicit `V-1` endpoint loss. Its logarithmic limit
theorem consumes `PoweringInputFamily`, removes `max 1 τ` padding, and gives
the genuine energy-region cardinality inequality. Corrected cardinality
powering then supplies that inequality at every positive integer power.
This completes the region bridge, not the standalone uniform `LV` API or
the other classical bounds in EPZAE-19.

`EnergyClauseOneGeneral` proves the exact source `imphb-lver-ineq`:
for `3/4 ≤ σ ≤ 5/6` and `8σ-4 ≤ τ ≤ 2(8σ-4)`, every actual energy-region
point satisfies

- `ρ*/τ ≤ (18-19σ)/(2(3σ-1))` when `σ ≤ 4/5`;
- `ρ*/τ ≤ 7(1-σ)/(3σ-1)` when `4/5 ≤ σ`.

The proof covers the height interval by powers `k=2,3`, derives the two
cardinality caps from separate corrected witnesses at `k` and `k+1`, and
uses the corrected energy witness in the proved Heath--Brown relation.
Six explicit affine branches are certified on their exact closed intervals,
including the `σ=4/5` crossover. No fifth-coordinate box, arbitrary polytope
closure, or optimization inequality is assumed. The actual-region consumer
implies a uniform `IsLargeValueEnergyBound`; corrected powering extends it
to every higher general height. These are completed sub-results of
EPZAE-36/37, whose remaining zeta and other-clause obligations stay open.

`energyClauseOne_of_zeta_range` then assembles the advertised clause (i)
bound conditionally on explicit uniform zeta-energy bounds on
`[1,8σ-4)`. This is a genuine remaining analytic input, not a completed
final estimate. The source zeta range starts at `2`; both its bound and
the missing short-scale transfer must still be proved. The two new modules,
all 22 named public theorems, and the two additional logarithmic-limit
lemmas are root-imported, runner-inventoried, and explicitly audited.
Semantic regressions cover actual region consumers, both height endpoints,
the rational crossover, and the exact conditional zeta-range signature.

### Completed zeta certificate; analytic inputs remain open

`EnergyClauseOneZeta` now proves the exact finite `imphb-zlver-ineq`
certificate from the two cardinality caps `ρ ≤ 4-4σ` and
`ρ ≤ 2τ-12(σ-1/2)`. The six Heath--Brown branches are checked at `τ=2`
or at `τ=4σ-1`, and the strict slope bounds propagate the comparisons
in the correct direction. The two rational functions cross at `σ=65/86`;
both closed pieces and domination by the unchanged advertised maximum
are proved. This completes the clause-(i) zeta rational sub-result of
EPZAE-36, not its required analytic input or the other eight clauses.

The actual-region theorem derives Huxley's cap using the corrected
cardinality witness at power two and consumes the proved Heath--Brown
relation. Its twelfth-moment cardinality hypothesis is explicit.
`InZetaLargeValueEnergyRegion.rho_le_of_largeValueBound` absorbs the uniform
constant after choosing the epsilon window, then uses genuine large-scale
region witnesses. Compactness gives the uniform zeta-energy conclusion
from the separately supplied uniform twelfth-moment LV predicate.
`energyClauseOne_of_twelfth_and_short_zeta` assembles the final clause
conditionally on just that LV input over `[2,8σ-4)` and the modular
short zeta energy over `[1,2)`. Both now follow from the dyadic moment
through the continuations below. No energy or zero-density conclusion is
hidden in the twelfth-moment premise.

The nearby Gafni--Tao `HeathBrownTwelfthStatement.lean` was inspected:
`HeathBrownDiscreteTwelfthMoment` is a proposition and its dyadic theorem
assumes it. The surrounding local modules do not export a proof of that
proposition. No such instance is imported or postulated here. EPZAE-21
still needs the twelfth-moment theorem; its coefficient-one pattern bridge
and uniform LV deduction are now proved below. EPZAE-33 still needs the
independent endpoint-two source reduction.
Useful existing supporting exports were also inspected:
`heathBrown_equation44_native` gives the local critical-zeta second-moment
entry inequality, and `heathBrownAtkinson_lemma71_source_average_unfolded`
retains the exact physical spacing and diameter in the Atkinson bound.
`heathBrownEquation61_to_equation7` is only the final algebraic conversion:
it still assumes the equation-(61) cardinality estimate. Those modules
are research candidates, not an installed or verified target dependency;
their full assembly and a single pinned foundation graph must be resolved
before reuse.

All 11 new public theorems are explicitly audited and the module is
root-imported and runner-inventoried. Eight regressions test the two sigma
endpoints, rational crossover, height transition, actual Huxley-region
consumer, closed upper height, and exact conditional assembly signature.

### Completed critical-zeta convolution and normalization helpers (EPZAE-21)

The source proof of `add-bound (ii)` has three distinct analytic parts:
pointwise Perron entry, weighted convolution summation, and a critical-line
moment estimate. The middle part is now proved for the twelfth power in
`ZetaMomentKernel` and `ZetaMomentTransfer`, using the real zeta function.
The separated shell bound allows an arbitrary integration center, preserves
the possible central ordinate, and gives the explicit logarithmic loss
`L(T)=3+2 log(ceil(2T)+1)`. The exact kernel mass and weighted Hölder yield
`Σ F_T(t)^12 ≤ L(T)^12 M₁₂(T)` on the paper's `[T/2,3T]` interval.

`ZetaLargeValuePattern.twelfth_cardinality_of_convolution` unpacks the
actual pattern's source interval and separation. Its pointwise entry
premise implies the finite estimate with physical normalization
`|W| V^12 ≤ C^12 N^6 L(T)^12 M₁₂(T)`. It does not assume a large-values,
energy, or density conclusion. This modular entry premise is now discharged
by `ZetaPerronEntry` in the continuation below.

`ZetaMomentAsymptotics` proves every fixed logarithmic power is absorbed
by any positive height power and proves the source window is bounded by
three genuine dyadic moment integrals. From the explicit uniform dyadic
moment hypothesis it deduces `L(T)^12 M₁₂(T) ≤ T^(2+ε)` eventually, then
composes this with the actual-pattern consumer at a uniform height threshold.
The source interval normalization and logarithmic losses are thus proved;
the twelfth-moment height estimate itself is not.

The remaining critical twelfth-power input is the genuine dyadic moment
theorem. The localized Perron estimate and uniform epsilon--delta LV
deduction are now proved below. Other EPZAE-21 moment parameters and
inputs remain open, separately from EPZAE-33's endpoint-two
obligation. No final
`Add-est` clause has changed status. The three new modules have 21 named
public audits, ten semantic regressions, root imports, and synchronized
`run_tao_trudgian_yang_build.bat` inventory. No new dependency, source
archive edit, or change to the Lemma 62 counterexample was needed.

### Completed exact Mellin source identity (EPZAE-21)

`ZetaIntervalCutoff` now interpolates the exact coefficient-one integer
interval smoothly, retaining both endpoints, and derives its physical
support from the actual pattern. `ZetaMellinEntry` proves Mellin inversion
and absolute interchange for the actual sharp polynomial on a right line.
`ZetaMellinContour` proves the moving-pole residue formula, and
`ZetaMellinShift` justifies the infinite-height contour shift by absolute
boundary integrability and vanishing horizontal integrals.

`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin` gives the
actual sharp polynomial as the whole critical-line zeta integral plus
`mellin cutoff (1-it)`, without independent analytic hypotheses.
`exists_critical_zeta_mellin_large` uses one common exact cutoff for
every large ordinate. Its smooth-test properties, phase, and residue are
derived from the actual objects, not supplied as conclusion-shaped inputs.

The fixed-cutoff decay constants cannot be used as if they were uniform
in `N` or the ordinate. The quantitative continuation below now proves
those uniform estimates independently and supplies the source-window
entry and uniform LV deduction. The dyadic twelfth moment itself and
EPZAE-33's independent endpoint-two source theorem remain open. The short
energy range is supplied from the moment below. All four identity modules, 36 public
theorem audits, the cutoff-constructor audit, and ten new regressions are
in the root and `run_tao_trudgian_yang_build.bat` coverage. No final
`Add-est` status or publication contract changed.

### Completed uniform source entry and conditional twelfth-moment LV (EPZAE-21)

`ZetaCutoffDerivatives` proves endpoint-independent derivative integral
bounds of every positive order, using the two nonoverlapping transitions.
`ZetaMellinDerivative` constructs the derivative test functions and proves
integration by parts with the exact Mellin factors. `ZetaMellinUniform`
then gives the actual-pattern bound
`|M_w(σ+iu)| ≤ C_j(σ) N^(σ+j-1)/(1+|u|)^j`.
Its critical `j=1` kernel is `C sqrt(N)/(1+|u|)`; its residue bound is
`C_j(1) N^j/(1+|t|)^j`. Constants depend only on the fixed transition,
order, and real line, never on the source pattern.

`ZetaMellinLocalization` proves the shifted-window geometry and controls
the whole omitted integral by `120 C_4(1/2) N^(7/2)/T²`.
`ZetaPerronEntry` proves the near convolution bound and retains both
residue and far errors before absorbing them. Its actual `perron_entry`
uses `T ≥ N^(7/4)` and `V ≥ 2 zetaPerronError`.
`exists_zetaPerron_uniform_threshold` derives these conditions for all
source exponent windows `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`, from one threshold.
The entry is therefore a proved physical-scale consumer, not a pointwise
estimate supplied by a theorem parameter.

`ZetaTwelfthFromMoment` proves the exact uniform predicate
`IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))`, conditional only on the
dyadic critical-line twelfth moment. The source window, logarithmic losses,
coefficient-one entry, and epsilon--delta conversion are all consumed.
`energyClauseOne_of_dyadic_moment_and_short_zeta` then performs the
downstream clause-(i) deduction from that genuine moment and short zeta
energy on `[1,2)` in its preserved modular signature. The short-zeta
continuation below now derives the latter from the former. The moment
and independent endpoint-two source theorem remain unproved; all nine
final clauses remain open.

The next analytic task is to prove the dyadic twelfth moment itself from
its primary source, or to prove the independent endpoint-two source
reduction. Do not import the nearby conditional statement as an instance.
The six continuation modules now have 39 named public theorem audits, an
explicit derivative-test constructor audit, and 14 regressions, all in
root and `run_tao_trudgian_yang_build.bat` coverage. No source archive,
counterexample, dependency pin, or publication contract changed.

### Short-zeta input discharged; clause (i) reduced to the moment (EPZAE-21/37)

`ZetaShortPerron` absorbs the proved error against the actual large-value
threshold. The physical conditions `T ≥ N^(23/16)` and
`V ≥ 2 zetaPerronError N^(5/8)` follow from one common threshold and all
windows `σ ≥ 3/4`, `τ ≥ 3/2`, `δ ≤ 1/16`.
`zetaTwelfth_short_largeValueBound_of_dyadic` supplies the exact uniform
twelfth-moment cardinality exponent on this extended range, consuming the
actual Perron entry rather than accepting it as a premise.

`ZetaShortPatterns` bridges native first/second derivative estimates to
the exact coefficient-one interval, including the left support endpoint.
It proves `|polynomial(t)| ≤ 2 + 200 sqrt(t) + 12 pi N/t` for
`1 ≤ t ≤ N²`. For `σ ≥ 3/4`, `1 ≤ τ < 3/2`, a positive exponent gap
then excludes all actual large ordinates at a uniform threshold.
`zetaShort_largeValueExponent_eq_bot` records the genuine `LV_ζ=-∞`
consequence. The empty set is a proved outcome, not a changed definition.

`EnergyClauseOneFromMoment` proves the exact cubic-energy comparison on
`0 ≤ τ ≤ 2` and uses it on `[3/2,2]`. Below `3/2` it consumes the proved
nonexistence. Consequently `energyClauseOne_short_zeta_of_dyadic` supplies
the whole `[1,2]` energy range from the genuine moment, and
`energyClauseOne_of_dyadic_moment` assembles the exact zero-energy bound
for `3/4 ≤ σ ≤ 5/6` with that moment as its sole mathematical theorem input.
The endpoint-one transfer is used without altering its domain; EPZAE-33's
separate endpoint-two source statement has not thereby been proved.

All 12 new public theorems (11 in the three added modules and one in
`ZetaTwelfthFromMoment`) have named audits and runner coverage. Eight
regressions check the scaled error, closed `τ=3/2` window, `t=N` derivative
transition, `τ=1` nonexistence, zero cardinality exponent at `τ=3/2`, the
`τ=2` cubic boundary, `σ=5/6`, and the final moment-only signature.
The remaining clause-(i) analytic work is the actual dyadic twelfth-moment
theorem; no final output is claimed complete. The other eight clauses and
the complete EPZAE-00--41 goal remain in force.

### Zeta discreteness and primary-source check (EPZAE-17/21)

`ZetaLargeValueDiscreteness` proves the exact infimum/uniform-bound
equivalence and the negative-exponent collapse by forcing actual finite
cardinalities below one. `ZetaPointwiseNonexistence` proves both directions
between negative infinity and a uniform strict power saving for every
sharp interval at positive heights. The forward singleton preserves the
actual coefficients and height; the reverse proof uses a quarter-radius
window and a common threshold to absorb the factor two. The actual
short-range consumer is `zetaShort_pointwise_powerSaving`. The two new
modules and that consumer add 13 named audits and eight regressions.

The live [zeta-moment blueprint](https://teorth.github.io/expdb/blueprint/zeta-moment-chapter.html)
was rechecked on 20 September 2026. Theorem 9.7's proof displays a minimum
where its cited [Lemma 8.11](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html)
supplies a maximum. The proved branch reduction keeps `max(a,2a)` and
uses negative-exponent discreteness when `a < 0`; it does not claim an
analytic estimate from that algebra alone.

The existing adjacent Ivić scan was inspected at printed pages 107--115
and 127--133 (PDF pages 112--120 and 132--138). Its Theorem 6.2 supplies
the missing local zeta mean-square entry into weighted Atkinson sums;
Theorem 7.1, Lemma 7.1, and Corollary 7.2 describe the subsequent
spacing/diameter and twelfth-moment assembly. Its title pages identify
*Topics in Recent Zeta Function Theory*, Orsay report 83.06, a different
text from the book edition referenced by the blueprint. The nearby Lean
`heathBrown_equation44_native` proves a genuine zeta-to-local-second-moment
entry, and `heathBrownAtkinson_lemma71_source_average` proves the aggregate
terminal-plus-averaged-prefix estimate, but neither supplies Theorem 6.2's
zeta-to-Atkinson bridge. `HeathBrownDiscreteTwelfthMoment` remains a
proposition without a proved instance. None of these modules was imported
into the canonical dependency graph in this continuation.

The next analytic obligation is therefore still the genuine dyadic
twelfth moment, not a renamed cardinality conclusion. The actual smooth
zeta-square/reflection entry and Gaussian averaging are proved in the
continuations below, as is the uniform amplitude/complete reflected-source
remainder, finite divisor shortening and actual smooth Voronoi/Bessel
entry. The stationary-phase reduction with uniform errors and subsequent
physical scale assembly must still be checked
before that source route can close EPZAE-21/37.

### Exact one-sided local mean-square entry (EPZAE-21)

The six-module `ZetaSquare*` continuation now proves the exact square
entry described above. `ZetaSquareContour` and `ZetaSquareContourShift`
adapt the adjacent one-sided proof to the canonical native imports.
The finite rectangle, reflected left line, horizontal limits, and
two-right-contour limit are kernel-checked. No Gafni--Tao package or
twelfth-moment proposition is imported.

`ZetaSquareDivisorKernel` opens the actual divisor L-series on
`Re w = 1`, so `Re(s+w) = 3/2`. Its Gaussian-polynomial majorant has
one constant independent of the central and contour heights; the pole
normalization has norm at least `1/16`. `ZetaSquareDivisorSeries` proves
each coefficient term integrable and their integrated norms summable,
then obtains the completed-zeta identity by the actual contour limits.

`ZetaSquareSourceEntry` uses the functional equation and actual zeta
conjugation to remove the nonzero Gamma normalization. Its `HasSum`
conclusion is literally `|ζ(1/2+it)|²`. `ZetaSquareLocalMean` proves
height continuity and compact domination before the second sum--integral
exchange. `hasSum_zetaSquareLocalMean` reaches the actual local second
moment for every finite ordered interval, without an analytic input.
All 47 public theorems have named audits; nine new regressions test
height zero, reflection, actual coefficients at zero/one, uniformity,
summability, and both local-window and degenerate-interval consumers.

This closes only the exact local source identity, not the uniform
Atkinson inequality of Theorem 6.2. Averaging is proved in the next
continuations, including the actual unit phase. The remaining EPZAE-21
route after the proved amplitude/source remainder, weight control and
quadratic Gaussian-window comparison and source-scale shortening is
the smooth actual source for native Voronoi, then stationary reduction,
uniform source-scale remainders, then scale/spacing and twelfth-moment
assembly. A compact-dependent bound is not that source estimate.
EPZAE-21/37 and all final output contracts remain open. The corrected
powering and Heath--Brown energy proofs remain unchanged, as does the
preserved Lemma 62 counterexample. Root imports, the audit, regressions,
goal, and `run_tao_trudgian_yang_build.bat` inventory are synchronized.

### Uniform Gaussian source averaging and quadratic transform (EPZAE-21)

`ZetaSquareAveraging` proves weighted local divisor-series convergence
for continuous real weights. It constructs the literal physical Gaussian
and proves the local second moment is at most `exp(1)` times the
Gaussian-window integral whenever `G>0,L≥1`, with no scale-dependent
implicit constant. Its series consumer uses the proved weighted entry.

`ZetaSquareGaussianTail` proves a global linear bound on the actual
critical zeta norm, whole-line integrability, and the affine change of
variables with the exact Jacobian `G`. It derives one constant for the
tail `C G(1+|T|+G)² exp(-L²/2)`, then a common threshold for the source
logarithmic window: `0<G≤T` and every real `A` give a tail at most
`G T^(-A)`. `exists_zetaSquareGaussian_source_approximation` composes
this with the complete weighted divisor series for the literal whole-line
mean; neither an entry nor a tail estimate is a theorem premise.

`ZetaSquareGaussianTransform` evaluates the kernel with coefficient
`G^(-2)+i/(2T)` using Mathlib's genuine complex Gaussian integral. Its
public physical-scale consumer proves the frequency bound
`sqrt(pi) G exp(-(Gv)²/8)` for `T,G>0`, `G²≤2T`; a further consumer
keeps the frequency cutoff explicit. This is not a proof that the
Gamma-normalized source equals its quadratic approximation. The actual
unit phase and its integrated error are proved in the next continuation.
The following amplitude continuation controls the complete reflected-source
remainder; subsequent continuations prove the shortened divisor weights
and actual smooth Voronoi/Bessel entry. Uniform stationary phase remains open.

These three modules have 31 named public theorem audits and nine new
regressions. Two precise helper nodes are green; the Atkinson source
inequality and twelfth moment remain red under EPZAE-21. The clause-(i)
energy assembly still has the same genuine moment premise. The goal,
root imports, and `run_tao_trudgian_yang_build.bat` inventory are updated;
the original counterexample and all output contracts are preserved.

### Actual reflected Gamma-phase approximation (EPZAE-21)

Four modules prove this analytic component, now with 26 named
public theorem audits and 12 semantic regressions. `ZetaDigammaLog`
compares actual reciprocal terms with their unit-interval logarithmic
integrals. A telescoping majorant is uniform in the truncation length;
the pinned digamma series and harmonic limit then give
`‖psi(z)-log(z)‖≤4/|Im z|` throughout `Re z>0`, `|Im z|≥1`.
The real-part bound retains the real coordinate explicitly.

`ZetaSquareGammaPhase` constructs the actual quotient
`phi(t)=GammaR(1/2-it)/GammaR(1/2+it)`, proves its norm is one, and
consumes the actual completed-zeta functional equation. Its source
Gamma-normalization factorization is exact, including the remaining
shifted-Gamma amplitude. The derivative equation
`phi'(t)=i d(t) phi(t)` has real
`d(t)=log(pi)-Re psi(1/4+it/2)`; the proved estimate is
`|d(t)+log(t/(2pi))|≤9/t` for `t≥2`.

`ZetaSquareGammaQuadratic` uses the genuine derivative equation and
the logarithmic Taylor bound on the entire closed window. For `T≥4`,
`|x|≤r≤T/2`, the error against
`phi(T) exp(-i[x log(T/(2pi))+x²/(2T)])` is at most
`(18/T+2r²/T²)|x|`. Its physical integral consumer has error
`2r²(18/T+2r²/T²)` and exactly matches the existing quadratic Gaussian
kernel at frequency `v-log(T/(2pi))`.

`ZetaSquareGammaTransform` proves whole-line integrability, bounds both
omitted tails, and assembles the actual phase transform with error
`2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)`, for `G>0` and all
real `v`. `norm_zetaSquareGammaGaussianTransform_le` actually consumes
the prior quadratic frequency bound on the closed domain `G²≤2T`.
No phase-asymptotic or moment hypothesis appears in this chain.

The next continuation controls the nonconstant factor
`[GammaR(1/2-it+w)/GammaR(1/2-it)]²`, together with the actual pole and
contour weights. Weighted divisor truncation, Voronoi/stationary phase,
sharp Atkinson remainders, and twelfth-moment scale/spacing assembly
remain open. The phase-only
transform is not a local zeta mean-square estimate. The original
counterexample and full publication contract are unchanged; all four
modules and regressions are covered by the principal batch runner.

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


## Phase 6: release integration

1. Assemble `PublicTheorems.lean` with source-facing names and statements.
2. Add endpoint, crossover, and convention checks to
   `SemanticRegression.lean`.
3. Import all production modules from the root module.
4. Maintain an exhaustive theorem/axiom audit.
5. Add the warning-failing build runner, source-hash checks, snapshot checks,
   deterministic certificate regeneration check, and Python reproduction test.
6. Synchronize every planning/control document.

## Risk register

| Risk | Why it matters | Mitigation |
|---|---|---|
| Lean 4.30/4.32 split | Local and upstream foundations cannot share incompatible oleans | Resolve EPZAE-01 before architecture hardens |
| Cheap-asymptotic semantics | Sequence/subsequence arguments hide uniformity and choice | Reuse ANTEDB's proved API and expose every subsequence |
| Zero convention mismatch | Paper uses `|Im rho| <= T`; local work uses rectangles/slabs | Dedicated proved `ZeroCountBridge` plus regressions |
| Phase and coefficient conventions | `n^{it}` vs `n^{-it}`, support-only vs ambient coefficient bounds | Explicit conjugation and extension-by-zero lemmas |
| Optimization trusted accidentally | Python/SciPy output is not a theorem | Rational witnesses checked in Lean |
| Denominator signs | Rational bounds can reverse under multiplication | Carry interval-specific positivity lemmas in certificates |
| Open/closed endpoints | Several tables mix `<` and `<=` | Formal interval cover with overlap equality proofs |
| Additive-energy multiplicity | Set simplification changes the theorem | Use multisets or indexed families from the start |
| False fifth-coordinate powering | Singleton patterns contradict `s' ≤ s/k` already for `k=2` | Counterexample preserved and full authorized two-witness repair proved; prohibit scaled `s` constraints in all new certificates |
| Invalid projection closure | Separate witnesses do not imply arbitrary polytope closure | Apply checked coordinatewise monotonicity consumers, audit finite boxes, and replay every endpoint certificate |
| Source editorial slips | TeX contains minor variable/label inconsistencies | Maintain an errata ledger in the crosswalk |
| Over-formalizing literature | Full books/papers would swamp the target | Formalize the exact consumed theorem surfaces first |

## Historical next sprint (superseded by current checkpoint)

1. Prove exponent-pair convex closure directly from the analytic estimate.
2. Prove the easy direction “exponent pair implies affine beta bound.”
3. Prove the converse, including the `alpha = 0,1` endpoints and beta
   reflection bookkeeping.
4. Extend the installed deterministic extractor and byte-for-byte runner diff
   gate to every certificate table.
5. Begin exact A/B/C process theorem surfaces only after duality compiles.

Triangle membership and affine arithmetic remain prerequisites, not claims
that any of the four advertised points is already an exponent pair.

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

The current Sources note identifies the inspected point-entry reference.
Retain its window and additive term, and prove the occupancy-preserving
separation change; thinning a point set by a factor G does not close
the required pointwise bound.

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

### Exact next source obligation and consumer

Prove the displayed unweighted fourth-moment estimate for the literal
`zetaMomentCriticalNorm`, with all η-dependent constants preceding H.
Inspect the actual square approximate functional equation and mean-value
inputs, or a source theorem with exactly this integrand. The native
`TypeIIZeros` definition and `HughesYoungNativeCompletion` theorem are
mollified: neither supplies this missing instance. The exact contour/limit
identities in `SmoothZetaAFE` are useful inputs, not moment bounds by
themselves. Do not assume the twelfth moment or hide it in a new interface.

Then apply `zeta_twelfth_dyadic_of_fourth`: η=ε/20 and
V=H^(1/8+η) give a low contribution at most C H^(2+9η), and the already
proved high contribution is at most H^(2+η). The complete bound has
D=1+C and the maximum of the two height thresholds. This is a strict
upstream fourth-moment input, not an equivalent restatement of the desired
twelfth moment. The interval partition, integrability and zero-measure
endpoints are already proved.

Only after the actual full moment is established may it discharge
`zetaTwelfth_largeValueBound_of_dyadic` and
`energyClauseOne_of_dyadic_moment`. Continue the remaining energy
optimization and every advertised Add-est clause, together with all other
open exponent-pair and density obligations. The new high-set theorem is
not a replacement goal or evidence that those outputs are complete.

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

### Exact next analytic obligation

Use `zetaFourthPrefix_eq_integral` with S={n : n≤N},
N approximately H^(1+δ), and a small positive line a. Apply weighted
Cauchy–Schwarz using the proved Gaussian kernel bound, then integrate over
H≤t≤2H. The finite Dirichlet-polynomial mean square must be uniform under
the imaginary translation u; retain its actual coefficients d(n)n^(-1/2-a).
The native `integral_norm_sq_dirichletTime_le` is a dyadic-block input,
not yet the needed complete-prefix estimate. Its `endpointTwist` and
`norm_endpointTwist` provide the norm-preserving coefficient translation;
the positive t-u phase must also be bridged to its negative-phase convention.
The native `divisorCountBound_native` in `ArithmeticCoefficients`
already supplies d(n)≤C_ε n^ε for n>0. Prove its actual divisor-square
consumer and the complete dyadic assembly, paying every logarithmic loss.

On the independent right line b>3/2, bound the actual tail by
O_b(t^b N^(3/2-b)); the elementary d(n)≤n bound is enough here.
Choose b after δ and before H so this is O(1) for N≈H^(1+δ).
Do not replace the displayed summable tail with a presumed small number.
Prove all height-interval integrability and interchange requirements.

Assemble, for each η>0, constants C≥0 and H₀ chosen before H such that
H≥H₀ and H>0 imply integral_H^(2H) |ζ(1/2+it)|⁴≤C H^(1+η).
Then the installed `zeta_twelfth_dyadic_of_fourth` supplies the genuine
full twelfth moment; only that instance may discharge
`zetaTwelfth_largeValueBound_of_dyadic` and
`energyClauseOne_of_dyadic_moment`. Continue energy optimization, every
Add-est clause, and all other open exponent-pair/density outputs.
The contour checkpoint is not a replacement goal or a claimed impasse.

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

### Continuation under the full objective

The old fourth-moment/twelfth-moment obligation is now discharged; do not
re-prove it or reintroduce it as a premise. Preserve the exact full-domain
`add_est_i` consumer and the counterexample. Continue clauses (ii)--(ix)
against the unchanged nine-row source table, rebuilding every powered
constraint from the correct independent witnesses and proving each actual
region-to-uniform-to-zero-energy consumer. Start with clause (ii)'s
[7/10,3/4] interval and its exact two-function maximum; a rational
certificate alone does not discharge its analytic inputs.

Retain the separate EPZAE-33 endpoint-two obligation, all remaining
EPZAE-19/21 inputs (including the exact source-form Atkinson obligation),
and the open exponent-pair, beta, density and release tasks. A completed
clause (i) is meaningful progress toward the original whole-proof goal,
not a replacement goal or permission to mark EPZAE-37 complete.
Maintain and execute both named BAT runners as part of that objective.

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

Source check (2026-09-21): the frozen paper cites Matti Jutila,
“Zero-density estimates for L-functions,” Acta Arithmetica 32(1)
(1977), 55–62, equation (1.4). The original
[PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa32/aa3216.pdf) and publisher
download returned HTTP 403; no downloaded Jutila PDF was added or pinned.
The author's [1975–76 survey](https://www.numdam.org/item/SDPP_1975-1976__17_1_A6_0.pdf)
identifies the reflection and coefficient-majorant inputs. Exact formulas
were also checked in the existing local Ivić scan, PDF pages 180–184
(printed pages 175–179), §9.5–6, especially (9.38)–(9.44).
That scan is read-only in node 74's Sources folder; it is not a new pinned
dependency of this package. Current code uses the already pinned native
reflection, divisor, and weighted moment proofs, not an external oracle.

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

## Jutila physical-scale smoothing and uniform pattern bounds — verified history

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

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 368 package files, 379
integrity-scanned Lean files, and 3,619 audited declarations (3,614 discovered
target theorems plus five imported contracts). All 21 new named audits and
27 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All twenty-four
recorded source/build hashes are unchanged after the gates, including the
original counterexample and all ten earlier Jutila modules. Repository
scans find no forbidden proof terms; the twelve raw postulate-pattern
matches are the previously reviewed ten comments and two rational
structure fields. Git `diff --check` passes. Exact commands, logs and hashes
are recorded in the Reproduction Manifest. These checks certify the
stated finite-pattern scope, not the final Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

## Full Jutila theorem and corrected energy-region constraints — verified history

The complete source `jutila-lvt` inequality is now proved, not just its
physical-pattern precursor. For every positive integer k, fixed
1/2 ≤ σ ≤ 1 and τ ≥ 0, `jutila_largeValueBound` gives the uniform
epsilon--delta bound on actual large-value patterns with exponent

```text
max(2-2σ, τ+4-2/k-(6-2/k)σ, τ+(6-8σ)k).
```

`largeValueExponent_le_jutila` gives the paper's least-exponent
conclusion; `zetaLargeValueExponent_le_jutila` gives the valid zeta
specialization. No cutoff, moment estimate, physical absorption threshold,
or assumed cardinality bound remains in these source-facing signatures.

### Mathematical dependency and semantic checks

`jutila_local_pattern_cardinality` consumes both alternatives returned by
the proved `jutila_smoothed_pattern_bound`. It solves the actual Gram
recurrence, pays the thinning loss, and retains the endpoint correction
(V−1)/3. `jutila_local_cardinality_uniform` exposes the three physical
terms N²/(V−1)², T^k N^(2k)/(V−1)^(4k), and
T N^(6k)/(V−1)^(8k), with one arbitrary epsilon loss.

`LargeValuePattern.localized` constructs genuine floor-bin patterns:
coefficients, support, threshold and N are unchanged. Their cards sum to
the original card. `jutila_subdivided_cardinality_native` applies the
local theorem to these objects and uses the already constructed smooth
cutoff. The original T is unrestricted, including T<N and a chosen
local height larger than T.

`jutila_largeValueBound_of_local_exponent` chooses the actual local
height L=N^ℓ, derives the absorption threshold from σ>3/4, and removes
V−1 using the actual exponent windows. Constants and the positive window
radius precede every pattern. The optimized ℓ is
min((4−2/k)σ−(2−2/k), (8k−2)σ−6k+2).
`jutila_optimization_identity` identifies the exact three-term maximum.
The σ≤3/4 range uses the proved obvious bound; ℓ<1 uses the proved
`meanSquare_largeValueBound`, derived from the actual finite MHH
estimate with height padding removed. Thus no short-height gap remains.

`InLargeValueEnergyRegion.rho_le_of_largeValueBound` compares the
uniform bound with actual feasible-region witnesses.
`InCardinalityEnergyRegion.jutila_cardinality_powered` consumes the
cardinality branch of `correctedCardinalityEnergyPowering`, giving
ρ/q ≤ jutilaLargeValueExponent k σ (τ/q) for q≥1.
The literal k=13 consumer gives the two affine terms
τ/q+50/13−76σ/13 and τ/q+78−104σ needed for Add-est (iii).
Different powering applications remain independent. No relation between
either fifth coordinate and s/q is asserted.

### Scope, preservation, and continuation

The full Jutila subnode of EPZAE-19 is DONE. EPZAE-18 and EPZAE-19 as whole
checklist items remain OPEN: the other elementary/classical interfaces
still require their own acceptance tests, including the standalone
uniform Huxley API. EPZAE-36/37 still have Add-est (iii)--(ix) OPEN;
clauses (i)--(ii), corrected two-witness powering, and the full
Heath--Brown energy relation remain proved. The endpoint-two transfer,
sharp Atkinson source-form bridge, exponent-pair/density work, and full
EPZAE-00--41 release contract remain in scope.

The printed Lemma 62 counterexample is preserved byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the paper nor the advertised Add-est statements are changed.

Eleven new production modules are root-imported and included in the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`JutilaRecurrence`, `JutilaLocalCardinality`, `JutilaLocalAlgebra`,
`JutilaLocalUniform`, `LargeValueSubdivision`, `JutilaSubdivision`,
`JutilaPowerWindows`, `JutilaWindowBound`, `ClassicalMeanSquareBound`,
`JutilaLargeValues`, and `JutilaEnergyRegions`.
All 32 new public theorems have named dependency audits. There are
43 new semantic regressions: 32 exact signatures plus 11 localization,
endpoint, short-height, uniform-pattern and corrected-witness consumers.
Both human-facing BATs remain mandatory and must be updated as needed.

### Completed verification

Both mandatory BAT processes terminated with exit 0 and PASS on
21 September 2026. The target ran 9,234 build jobs, all 43 new semantic
regressions, deterministic regeneration, the exact 379-file package
inventory, and the 390-file integrity scan. All 3,669 audited declarations
(3,664 discovered target theorems plus five imported contracts) have
permitted dependencies; all 32 new named theorem audits are present.

The foundation's six stages also passed: 8,857 root build jobs, 7,636
explicit public declarations, and 14,290 discovered nonprivate theorems.
Its classification remains 301 root modules, two regressions, zero
excluded and zero unclassified. Both final gates have zero Lean errors,
warnings, tactic suggestions or linter failures; there are no failed
stages. Only standard Lean/Mathlib logical axioms occur.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
Git `diff --check` passes; Git's LF-to-CRLF notices are file-conversion
notices, not Lean diagnostics. No scan or warning policy was weakened.
All 35 source/integration/runner hashes match across the gates, including
the original counterexample. Exact commands, log paths, hashes and
checkout identity are in the Reproduction Manifest. This verifies the
full Jutila source theorem and the stated consumers, not the seven
remaining Add-est clauses or the unchanged whole-proof goal.

## Add-est (iii) from corrected powering — verified history

The complete third printed Add-est clause is now proved on
173/229 ≤ σ ≤ 443/586. `NewAdditiveEnergy.lean` exports
`add_est_iii`, `add_est_iii_bound`, and
`add_est_iii_zero_energy`. Their exact source rate is

```text
max((173−270σ)/(16(93−125σ)),
    (653−890σ)/(10(93−125σ)),
    (1151−1190σ)/(20(15σ−2))).
```

The first theorem bounds A*(σ)(1−σ); the last states the fully quantified
epsilon--delta estimate for `zeroAdditiveEnergy (σ−δ) T`. This is the
actual unit-tolerance energy of the paper's zeros with analytic
multiplicity, not a numerical certificate or an assumed energy estimate.
No large-value, moment, powering, or transfer theorem remains an input.

### Source-to-consumer checks

`InCardinalityEnergyRegion.energyClauseThree_cardinality_caps`
applies the proved k=13 Jutila theorem to separate corrected cardinality
witnesses at q and q+1, with q=2 or 3 linked to the original height.
The companion witness gives ρ/q ≤ 3−3σ. The actual Guth--Maynard
consumer supplies the other cardinality cap.

`InCardinalityEnergyRegion.energyClauseThree_general` consumes
those caps and the independent corrected energy witness: power q at
local height at least 6/5, and power q−1 below 6/5. The nine-branch
Heath--Brown relation is used only through its proved monotonicity in
cardinality. No fifth coordinate is scaled or identified.

The 67 closed-interval rational certificates cover both sigma ranges
split at 241/319, all three short-height pieces, both tall-height
pieces, and the nine short-zeta branches. The first two printed fractions
are explicitly normalized by reversing numerator and denominator signs;
`energyClauseThreeRate_eq_printed` proves the exact displayed formula.
The 4359/5770 equality of the first two rates is regression-checked.

`energyClauseThree_short_zeta` supplies the entire [1,2] range:
actual cancellation below 3/2, then the proved dyadic twelfth moment and
the actual Heath--Brown relation on [3/2,2]. Thus
`energyClauseThree` uses the already proved endpoint-one transfer,
with both general [2,4] and short-zeta hypotheses derived. It does not
assume or complete the independent source endpoint-two corollary.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseThreeCaps`, `EnergyClauseThreeRates`,
`EnergyClauseThreeLowCertificates`, `EnergyClauseThreeHighCertificates`,
`EnergyClauseThreeTallCertificates`, `EnergyClauseThreeBranches`,
`EnergyClauseThreeGeneral`, `EnergyClauseThreeZetaCertificates`, and
`EnergyClauseThree`. The existing public `NewAdditiveEnergy` module
now exports clauses (i)--(iii). All 89 new public theorems have named
audits; 103 new regressions include every exact signature, both closed
sigma endpoints, height transitions, the rate crossover and actual
corrected-witness/region consumers.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The archived paper and all advertised outputs remain frozen.

EPZAE-36/37 now have clauses (i)--(iii) DONE and (iv)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
EPZAE-33's endpoint-two corollary, other classical inputs, the sharp
Atkinson source-form bridge, exponent-pair/density outputs, and every
remaining EPZAE-00--41 acceptance condition stay in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,243 build jobs and all 103 new regressions.
Its complete inventory covers 388 package files and 399 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,780 audited declarations (3,775 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 45 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete third source clause and its real consumers,
not the other six clauses or the whole EPZAE-00--41 goal.

## Add-est (iv) from corrected powering — verified history

The complete fourth printed Add-est clause is now proved on the exact
closed interval 443/586 ≤ σ ≤ 373/493. The public
`NewAdditiveEnergy` module exports `add_est_iv`,
`add_est_iv_bound`, and `add_est_iv_zero_energy`, with rate

```text
max((593−810σ)/(5(171−230σ)),
    4(266−275σ)/(5(55σ−7))).
```

The first public theorem bounds A*(σ)(1−σ). The final consumer gives the
uniform epsilon--delta estimate for the actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height
and with the paper's unit tolerance and analytic zero multiplicities.
No analytic, powering, moment or transfer theorem is accepted as input.

### Source-to-consumer checks

`jutila_twelve_formula` specializes the proved full Jutila theorem to
the literal k=12 maximum. The actual-region consumer
`InCardinalityEnergyRegion.energyClauseFour_cardinality_caps`
applies it to separate corrected cardinality witnesses at q and q+1.
Here q=2 or 3 is chosen from the original τ∈[2,4]; τ/q∈[1,3/2]
and τ/(q+1)≤1 are derived. The companion witness gives
ρ/q≤3−3σ, and the actual Guth--Maynard bridge gives the second cap.

`InCardinalityEnergyRegion.energyClauseFour_general` then consumes
the independent corrected energy witness at q when τ/q≥6/5, or
at q−1 below 6/5. The sigma split is 409/541. All nine Heath--Brown
branches and all three short-height pieces are checked. The 67 exact
closed-interval certificates also cover both tall-height pieces and
all nine short-zeta branches. Numerical exploration is not proof evidence.

`energyClauseFourRate_eq_printed` proves equality with the printed
fractions after explicitly reversing both signs in the first fraction.
Both the Jutila affine-term equality and the two-rate equality at
409/541 are regression-checked, along with denominator signs and every
shared domain endpoint.

`energyClauseFour_short_zeta` supplies all of [1,2]: actual
cancellation below 3/2, and the proved twelfth moment plus the actual
Heath--Brown energy relation on [3/2,2]. `energyClauseFour` uses
the proved endpoint-one transfer with both required energy ranges
derived. The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new production modules are root-imported and covered by the exact
PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFourCaps`, `EnergyClauseFourRates`,
`EnergyClauseFourLowCertificates`, `EnergyClauseFourHighCertificates`,
`EnergyClauseFourTallCertificates`, `EnergyClauseFourBranches`,
`EnergyClauseFourGeneral`, `EnergyClauseFourZetaCertificates`, and
`EnergyClauseFour`. The existing public output module now exports
clauses (i)--(iv). All 89 new public theorems have named audits.
There are 104 new regressions: 89 exact signatures and 15 endpoint,
split, sign, height-transition and actual independent-witness consumers.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the original paper nor any advertised output was changed.
No powered fifth-coordinate bound is reintroduced.

EPZAE-36/37 now have clauses (i)--(iv) DONE and (v)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
The independent endpoint-two transfer, other classical inputs, the
sharp Atkinson source-form bridge, exponent-pair/density outputs, and
all remaining EPZAE-00--41 requirements remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,252 build jobs and all 104 new regressions.
Its complete inventory covers 397 package files and 408 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,888 audited declarations (3,883 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 54 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fourth source clause and its real consumers,
not the other five clauses or the whole EPZAE-00--41 goal.

## Add-est (v) from corrected powering — verified history

The complete fifth printed Add-est clause is now proved on the exact
closed interval 373/493 ≤ σ ≤ 103/136. `NewAdditiveEnergy` exports
`add_est_v`, `add_est_v_bound`, and `add_est_v_zero_energy`, with rate

```text
max((533−730σ)/(30(26−35σ)),
    3(26−33σ)/(85σ−62),
    (174−185σ)/(31σ+2)).
```

These give the literal A*(σ)(1−σ) inequality and the uniform
epsilon--delta bound for actual `zeroAdditiveEnergy (σ−δ) T`.
The constants precede the height; unit tolerance and analytic zero
multiplicities are preserved. There is no analytic, moment, powering
or transfer theorem parameter.

### Source-to-consumer checks

`jutila_eleven_formula` specializes the proved Jutila theorem to k=11.
`InCardinalityEnergyRegion.energyClauseFive_cardinality_caps`
consumes actual corrected cardinality witnesses at q and q+1, with
q=2 or 3 selected from the original height τ∈[2,4]. It derives
τ/q∈[1,3/2], the literal Jutila cap, the Guth--Maynard cap and
ρ/q≤3−3σ. No property of an independently chosen witness is
silently transferred to another point.

`InCardinalityEnergyRegion.energyClauseFive_general` applies the
independent energy witness at q−1 for short local height and at q
for the middle/tall ranges. The Jutila sigma split is 171/226.
For σ above that split the energy-power switch is
h(σ)=(31σ+2)/22, not the preceding clause's fixed 6/5 switch.
Both the ninth q−1 branch and the first q branch meet the third
printed rate at h(σ); the exact identities are regression-checked.

All 60 closed-interval rational certificates feed actual consumers:
27 low-sigma short certificates, 18 high-sigma short certificates,
two middle certificates, four tall certificates and nine short-zeta
certificates. Numerical exploration is not proof evidence.
`energyClauseFiveRate_eq_printed` proves the first fraction's
simultaneous sign reversal and preserves the complete three-rate maximum.

`energyClauseFive_short_zeta` supplies [1,2] explicitly: actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. `energyClauseFive` then consumes
the proved endpoint-one transfer, with both energy ranges derived.
The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFiveCaps`, `EnergyClauseFiveRates`,
`EnergyClauseFiveLowCertificates`, `EnergyClauseFiveHighCertificates`,
`EnergyClauseFiveTallCertificates`, `EnergyClauseFiveBranches`,
`EnergyClauseFiveGeneral`, `EnergyClauseFiveZetaCertificates`, and
`EnergyClauseFive`. All 85 new public theorems have named audits.
There are 104 new regressions: 85 exact signatures and 19 endpoint,
split, sign, witness-switch and actual independent-witness checks.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged: `EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the frozen source nor an advertised output was altered.
No scaled fifth-coordinate restriction is reintroduced.

Clauses (i)--(v) are proved; (vi)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 acceptance condition remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,261 build jobs and all 104 new regressions.
Its complete inventory covers 406 package files and 417 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,995 audited declarations (3,990 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 85
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 63 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fifth source clause and its real consumers,
not the other four clauses or the whole EPZAE-00--41 goal.

## Add-est (vi) from corrected powering — verified history

The complete sixth printed Add-est clause is proved on the exact
closed interval 103/136 ≤ σ ≤ 42/55. `NewAdditiveEnergy` exports
`add_est_vi`, `add_est_vi_bound`, and `add_est_vi_zero_energy`,
with the unchanged rate

```text
max((72−91σ)/(7(11σ−8)),
    5(18−19σ)/(2(5σ+3))).
```

The proof also establishes the larger blueprint theorem
`imp-energy-bound4` on its full interval [664/877,31/40].
`energyClauseSix` gives the actual uniform zero-energy bound there;
`energyClauseSix_blueprint` gives the literal source-facing A*
maximum, with (1−σ) inside both printed denominators.
`energyClauseSixRate_div_eq_blueprint` proves that normalization.
The paper theorem is a proved interval restriction, not a weaker
replacement for the blueprint statement.

### Source-to-consumer checks

`jutila_ten_formula` specializes the full Jutila theorem to k=10.
`InCardinalityEnergyRegion.energyClauseSix_cardinality_caps`
derives the literal cap from the actual corrected cardinality witness
at q, and the companion cap ρ/q≤3−3σ from a separate witness at q+1.
It derives τ/q∈[1,3/2] from the original τ∈[2,4] with q=2 or 3.
The actual Guth--Maynard bridge supplies the tall-height cap.

`InCardinalityEnergyRegion.energyClauseSix_general` consumes the
independent energy witness at q−1 below the moving switch and at q
above it. The sigma split is 281/371; the two switches are
77σ/2−28 and (14σ+1)/10. Their agreement at the split and the
actual branch-balance identities are regression-checked.
The companion cardinality point is never identified with the
energy-preserving point, and no fifth coordinate is scaled.

All 53 exact closed-interval certificates feed the actual consumers:
18 low-sigma short, 18 high-sigma short, four middle, four tall and
nine short-zeta certificates. Numerical exploration is not evidence
for any theorem. The low switch realizes the first rate; the tall
cardinality crossover realizes the second rate.

`energyClauseSix_short_zeta` supplies all of [1,2], using actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. The final source theorem consumes
the proved endpoint-one transfer with both required energy ranges
derived. It does not assume the independent endpoint-two corollary.
The epsilon--delta public conclusion uses actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height,
unit tolerance, and analytic zero multiplicities.

### Inventory and remaining whole-proof scope

Nine production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseSixCaps`, `EnergyClauseSixRates`,
`EnergyClauseSixLowCertificates`, `EnergyClauseSixHighCertificates`,
`EnergyClauseSixTallCertificates`, `EnergyClauseSixBranches`,
`EnergyClauseSixGeneral`, `EnergyClauseSixZetaCertificates`, and
`EnergyClauseSix`. All 80 new public theorems have named audits.
There are 102 new regressions: 80 exact signatures and 22 source/paper
endpoint, normalization, switch, height and actual-witness checks.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The frozen paper and all advertised outputs are unchanged.

Clauses (i)--(vi) are proved; (vii)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,270 build jobs and all 102 new regressions.
Its complete inventory covers 415 package files and 426 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,094 audited declarations (4,089 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 80
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 72 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete sixth source clause, its real consumers and
the full blueprint `imp-energy-bound4`, not the other three clauses
or the whole EPZAE-00--41 goal.

## Add-est (vii) and (viii) from corrected powering — verified history

The exact seventh and eighth printed Add-est clauses are proved on
their full closed intervals. `NewAdditiveEnergy` exports
`add_est_vii`, `add_est_vii_bound`, `add_est_vii_zero_energy`,
`add_est_viii`, `add_est_viii_bound`, and
`add_est_viii_zero_energy`.

For [42/55,79/103], the unchanged rate for A*(σ)(1−σ) is

```text
max((18−19σ)/(6(15σ−11)), 3(18−19σ)/(4(4σ−1))).
```

For [79/103,84/109], it is

```text
max((18−19σ)/(2(37σ−27)), 5(18−19σ)/(2(13σ−3))).
```

`energyClauseSeven_blueprint` and `energyClauseEight_blueprint`
also give the literal full-source conclusions of `imp-energy-bound6`
and `imp-energy-bound7`, respectively. Their (1−σ) factors occur
inside both printed denominators, with proved normalization identities.
The public epsilon--delta conclusions use actual
`zeroAdditiveEnergy (σ−δ) T`, analytic zero multiplicities and unit
tolerance; constants and the positive sigma loss precede the height.

### Actual witnesses and complete interval consumers

The full Jutila theorem is specialized to k=6 for clause (vii) and
k=5 for clause (viii). The respective sigma splits are 97/127 and
33/43. Each `energyClauseSeven_cardinality_caps` /
`energyClauseEight_cardinality_caps` theorem derives both the literal
Jutila cap at q and the companion bound ρ/q≤3−3σ at q+1 from
actual corrected cardinality witnesses. The energy witness is separate.

For τ∈[2,4], the proved cover chooses q=2 or 3 and derives τ/q∈[1,3/2].
Below the diagonal-cardinality crossover, the proof consumes the actual
q−1 energy witness and all nine Heath--Brown branches. Above it, the
actual q energy witness supplies the two proved small-height branches.
The crossover pairs are 46σ−34 and (11σ−5)/3 for clause (vii), and
38σ−28 and (18σ−8)/5 for clause (viii). The companion-cap crossover
pairs are 45σ−33 and (8σ−2)/3, and 37σ−27 and (13σ−3)/5.
The second q-energy branch realizes the corresponding printed rate
at each companion crossover; exact identities are regression-checked.

Each clause has 35 kernel-checked interval certificates: nine low-sigma
short, nine high-sigma short, eight tall, and nine short-zeta certificates.
All feed actual region consumers and uniform bounds. The independent
power ratio is bounded at 2/3 only for branch 0 and at 1/2 for the other
eight branches; the sign-sensitive branch 2 has an explicit regression.
No fifth coordinate is scaled or identified across the witnesses.
Numerical exploration is not proof evidence.

For both clauses the full short-zeta range [1,2] is derived from actual
cancellation below 3/2 and the proved twelfth moment above it. The final
theorems consume the proved endpoint-one transfer with τ₀=2.
For clause (viii), this is a documented proof refactoring: the blueprint
uses a varying τ₀, whereas Lean derives all required bounds on [2,4]
and [1,2] directly. The exact source conclusion is unchanged; no
varying-height intermediate bound or endpoint-two corollary is assumed.

### Inventory and unchanged whole-proof scope

Eighteen production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`. Each
`EnergyClauseSeven` / `EnergyClauseEight` family contains `Caps`,
`Rates`, `LowCertificates`, `HighCertificates`, `TallCertificates`,
`Branches`, `General`, `ZetaCertificates`, and the final assembly.
All 122 new public theorems have named audits. There are 172 new
regressions: 122 exact signatures and 50 endpoint, normalization,
crossover, height and actual-witness checks.

The original counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The original paper and source pins are unchanged.

Clauses (i)--(viii) are proved; (ix) remains open. EPZAE-36/37 remain
unchecked as whole items. The independent endpoint-two transfer,
remaining classical inputs, sharp Atkinson source-form bridge,
exponent-pair/density outputs and every other unfinished EPZAE-00--41
requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,288 build jobs and all 172 new regressions.
Its complete inventory covers 433 package files and 444 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,249 audited declarations (4,244 discovered target theorems and five
imported contracts) have permitted dependencies; all 122 new named audits
were checked in the complete target log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 90 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete seventh and eighth paper clauses, their real
consumers and their full blueprint conclusions. Clause (ix) and all other
unfinished EPZAE-00--41 requirements remain in the unchanged active goal.

## Double-zeta source bounds and Bourgain algebra — verified history

The corrected powering theorem and Add-est (i)--(viii) remain proved.
The printed Lemma 62 counterexample is byte-for-byte unchanged:
SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

Four new modules advance the remaining clause-(ix) route:

- `HeathBrownDoubleZetaFinite` proves the uniform finite double-zeta bound
  on actual closed-support patterns, with the one-endpoint error and
  reflected interval proved explicitly.
- `HeathBrownDoubleZeta` proves the full frozen `hb-double` conclusion
  `s ≤ max(max(ρ+1,2ρ),5ρ/4+τ/2)+1` for actual region points,
  including τ=0. Its small-height and diagonal-equality consumers are proved.
- `MixedDoubleZeta` proves the mixed Cauchy--Schwarz inequality with the
  actual kernel at **t−u**, and consumes actual patterns with common support.
- `BourgainLargeValueAlgebra` proves witness elimination and the exact
  certificate for the row `ρ ≤ 9−12σ+2τ/3`. The resulting cardinality
  bound is **conditional on the explicitly displayed Bourgain dichotomy**;
  the finite analytic selection and its limiting bridge remain OPEN.

The row certificate uses α₁=(τ+9−12σ)/6 and
α₂=max(0,4σ+4τ/3−5), a proved alternative to the table's α₂.
All five branches are checked on the complete stated closed row.
A rational regression at σ=771/1000 detects the gap in simply extrapolating
the previous Jutila/HB local peak rate; numerical sampling is not evidence
for clause (ix).

There are 25 new named audits and 35 new regressions. All four modules are
in the root imports and the `run_tao_trudgian_yang_build.bat` PowerShell
inventory. No source archive, dependency pin, public Add-est statement,
or counterexample was changed. In particular, no constraint on s′/s
has been reintroduced.

Add-est (ix), its actual Bourgain input and final general/zeta optimization,
the other public outputs, and every remaining EPZAE-00--41 acceptance test
remain OPEN. EPZAE-19, 36 and 37 are not checked off by these supporting results.

### Current verification evidence

On dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  437 package Lean files, 448 integrity-scanned files, 9,292 build jobs,
  4,277 discovered target theorems and 4,282 audited declarations.
  All 25 new named audits permit only the standard logical axioms.
  Log: `logs/tao-trudgian-yang-build-20260921-110817-ade1e44e.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: PASS, exit 0;
  all six verification stages pass, with 301 root modules, 2 explicit
  regressions, 0 unclassified files, and 14,290 discovered theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_110818.log`;
  manifest: `logs/foundation_freeze_20260921_110818.json`.

Both runs have zero Lean errors, warnings, tactic suggestions or linter failures.
There are no remaining failed verification stages. These are build/integrity
results for the installed scope, not a claim that clause (ix) or the whole goal
is complete. The reproduction manifest records hashes of the tested sources.

## Bourgain difference counts and actual zeta moments — verified history

The corrected independent cardinality/energy powering route and Add-est
(i)--(viii) are preserved. The printed Lemma 62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No fifth-coordinate scaling or third witness has been restored.

Five production modules now prove actual upstream inputs to Bourgain's
remaining analytic dichotomy:

- `BourgainDifferenceCounts`: the strict ordered-pair count
  Δ(ℓ)=#{(t,u)∈W²: |t−u−ℓ|<1}, a finite support cover, exact double
  counting, ΣΔ≤2|W|², and ΣΔ²≤2|W|³ for two-separated W.
  The cover may contain zero-count integers; these are not fabricated
  positive bins.
- `BourgainDifferenceLevels`: genuine nonempty dyadic level selection
  from positive weighted mass, with the exact log₂|W|+1 loss and
  2ʲ|Dⱼ|≤2|W|². No selector is assumed.
- `BourgainIntegerWindows`: overlap at most 2⌈H⌉+1 and the real-difference
  to integer-bin integral bridge. The latter explicitly enlarges H to H+1;
  it does not assert a same-radius replacement.
- `BourgainZetaDifferenceMoments`: actual local critical-line zeta-square
  integrals and multiplicities, their Cauchy--Schwarz/fourth-moment
  reduction, positive-mass level selection, and the actual real-pair
  consumer with the unit window enlargement.
- `BourgainFourthMoment`: the genuine symmetric fourth moment, derived
  from the proved dyadic theorem, compact initial interval and conjugation;
  it supplies the actual weighted-moment bound below.

Writing M(W,H)=Σℓ Δ(ℓ) ∫[-H,H] |ζ(1/2+i(ℓ+u))|² du, the final consumer
proves, for every η>0, uniform positive C and T₀≥1 such that

```text
M(W,H)² ≤ C H (2⌈H⌉+1) |W|³ (T+H+1)^(1+η)
```

for T≥T₀, H≥0, two-separated W⊂[0,T]. Constants precede W, T and H.
The global fourth moment is proved, not an extra theorem parameter.
The exact window loss is retained; no small-power absorption or logarithmic
large-values limit is being claimed here.

There are 31 new named audits and 45 new regressions, including strict
endpoints, empty/zero-radius cases, and a one-separated four-point set
where Δ(2)=5>|W|=4. This guards the necessary stronger separation.
All five modules are root-imported and included in the exact production
inventory behind `run_tao_trudgian_yang_build.bat`.

The retained-zeta source estimate (Bourgain (4.7)), zeta-superlevel/common-shift
selection, the full finite dichotomy and its actual-pattern logarithmic
bridge remain OPEN. The earlier `bourgain_ninth_row_of_log_dichotomy`
still has its explicit dichotomy premise. Add-est (ix), EPZAE-19/36/37
as whole items, and every other unfinished EPZAE-00--41 requirement remain
in the unchanged goal. These supporting theorems do not close those items.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: 442 package
  Lean files, 453 integrity-scanned files, 9,297 build jobs,
  4,322 discovered target theorems and 4,327 audited declarations.
  All 31 new named audits have only permitted logical dependencies,
  and all 45 new regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-115007-09779b5b.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages
  pass, 301 root modules, 2 explicit regressions, 0 excluded or
  unclassified files, 8,857 build jobs and 14,290 discovered
  nonprivate theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_115008.log`;
  manifest: `logs/foundation_freeze_20260921_115008.json`.

There are zero Lean errors, warnings, tactic suggestions, linter failures
or remaining failed verification stages. All 99 checked source,
integration and runner hashes match before and after the gates,
including the preserved counterexample. No source pin or public
Add-est statement changed. The Reproduction Manifest records the
exact evidence and hashes.

These gates establish integrity of the installed scope. The full
Bourgain dichotomy, Add-est (ix) and the unchanged whole-proof goal
are not complete.

## Bourgain critical-block Mellin localization — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Five new production modules supply a genuine retained-zeta estimate for
finite critical dyadic blocks:

- `BourgainCriticalMellin`: real-power weighting and physical dilation of
  an actual compact smooth test, exact critical-line Mellin identity, and
  its moving-pole residue. The kernel norm is scale independent; the
  residue has its explicit square-root scale factor.
- `BourgainMellinLocalization`: all polynomial Mellin moments are
  integrable; the actual zeta/Mellin tail is bounded at arbitrary order.
  The local norm estimate separates residue, local zeta integral and tail,
  with constants independent of L, t and H.
- `BourgainSmoothedPolynomial`: the fixed profile
  w(x)=`zetaIntervalCutoff 1 2 x`, equal to one on [1,2] and zero at and
  outside [1/2,5/2], produces a genuine finite-support critical polynomial.
  Its square bound consumes the Mellin theorem and interval
  Cauchy--Schwarz; its pair moment consumes the actual H-to-H+1 bridge.
- `BourgainSmoothedMoments`: proved distance-shell occupancy bounds the
  reciprocal-square overlap by four. For every positive integer q the
  complete pole sum is at most 4|W|, not an assumed diagonal estimate.
- `BourgainCriticalMajorant`: the actual finite block is zero-extended
  onto the smooth support and consumed by the native positive-kernel
  coefficient majorant. This is a full ordered-pair argument, not a
  pointwise or arbitrarily restricted-pair majorization.

The public consumer
`bourgain_critical_block_retained_zeta_moment` proves: for each integer
q >= 1 there is C_q > 0, independent of all physical parameters, such that
for L > 0, B,T,H >= 0, one-separated W in [0,T], finite
I contained in [L,2L], and |a_n| <= B n^(-1/2),

```text
sum_(t,v in W) |sum_(n in I) a_n n^(-i(t-v))|^2
 <= C_q B^2 [
      L |W| + H M(W,H+1)
      + |W|^2 (1+T)^2 / (1+H)^(2q)
    ],
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

Here Delta is the previously proved strict integer difference count, and
M is the actual finite weighted zeta-square moment. The H+1 enlargement,
coefficient factor B^2, pole term and tail are all retained. No moment,
contour shift, residue estimate, smoothness certificate or selector is
assumed. One-unit separation suffices for this consumer; the earlier
Delta <= |W| and fourth-moment count bounds still require two-unit
separation as documented.

This does **not** yet prove Bourgain (2000), equation (4.7), or the full
analytic dichotomy. The actual reflected-prefix fourth-power convolution,
dyadic assembly and Gram/reflection consumer must still feed this block
estimate. The zeta-superlevel/common-shift and local-mean lower bound,
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are not closed by
these supporting results.

All five modules are added to the root import graph and the exact
production inventory used by `run_tao_trudgian_yang_build.bat`.
The explicit audit adds 30 public theorems; 44 new regression examples
cover their exact signatures, support/plateau endpoints, the nontrivial
scale-one polynomial, the surviving diagonal and empty sets. Continue
maintaining this BAT, its PowerShell driver and the foundation
`run_lake_build.bat` whenever proof/build coverage changes. Neither
runner's warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  447 package Lean files, 458 integrity-scanned files, 9,302 build jobs,
  4,374 discovered target theorems and 4,379 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 44 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-123028-c1ae7ae1.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_122534.log`;
  manifest: `logs/foundation_freeze_20260921_122534.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 104 checked source,
integration and runner hashes match before and after these gates, including
the preserved counterexample. The Reproduction Manifest records full log
hashes and the five new/four updated build-integration file hashes.

These are integrity checks for the installed scope, not completion of
source-(4.7), the Bourgain dichotomy, Add-est (ix), or the whole-proof goal.

## Bourgain retained-zeta pattern entry — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Twelve new production modules now consume the previously proved critical
block estimate in actual source-pattern bounds:

- `BourgainWeightedMoments`, `BourgainPolynomialMoments` and
  `BourgainPrefixMoments`: exact phase/half-weight bridges, genuine
  powered coefficients, all dyadic prefix pieces and the literal n=1
  term. The native reflected prefix is **unweighted**. Its factor
  U=(2M)^k is retained; it is not silently treated as a critical prefix.
- `BourgainReflectionIntegrals`, `BourgainTraceBins`,
  `BourgainPatternEntry` and `BourgainHybridEntry`: interval Jensen,
  actual difference bins, native reflection and source Gram subfamilies,
  with the actual ceiling dual length and all reflection errors.
- `BourgainPhysicalMain` and `BourgainPhysicalPatterns`: the
  unweighted-prefix factor is cancelled against its own displacement
  scale before taking terminal length bounds. Near bins, the retained
  main term and all three reflection errors are assembled.
- `BourgainSmoothingErrors` and `BourgainSmoothedPatterns`: native
  smoothing discharges the Mellin tail and reflection errors; logarithmic,
  divisor and integration-length costs are absorbed uniformly.
- `BourgainRetainedCardinality`: the quadratic recurrence is solved
  with the actual zeta moment retained. Exact source-power and
  value-threshold identities account for every numerical factor.

For every integer k>0 and nu>0,
`bourgain_smoothed_pattern_retained` supplies theta,B,T0 independently
of the actual pattern, with 0<theta<=min(1,nu), B>0 and T0>=2.
For scale>=30, V>1, T>=T0 and N<=T, it constructs a genuine
two-separated W in the reflected ordinates, contained in [0,T], and
a positive integer Q with N/2<=Q<=2N. Write

```text
R = |W|, V0 = (V-1)/3, Z = B*T^nu,
H = heathBrownSmoothingHeight T theta,
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

It proves |P.ordinates|<=Z*R and the alternative

```text
R*V0^2 <= 2*Q^2
  OR
R^2*V0^(4k) <= Z*(2Q)^(2k) *
  [ R^2*Q^k + R*T^k + Q^k*M(W,H+1) ].
```

The actual integer-window moment, two-unit separation, H+1 enlargement
and source endpoint V-1 are explicit. No analytic moment or reflection
estimate is a theorem premise.

For k=2, `bourgain_high_value_pattern_retained` solves this alternative
under the additional **numerical high-value condition**

```text
2*[Z*(4N)^4]*(2N)^2 <= V0^8.
```

With D=Z*(4N)^4, its actual subfamily satisfies

```text
|P.ordinates| <= Z * [
  2*(2N)^2/V0^2 + 2*D*T^2/V0^8
  + sqrt(2D)*(2N)*sqrt(M(W,H+1))/V0^4
].
```

This is a proved high-value retained-moment consumer, **not the full
parameter range of printed Bourgain (2000), Lemma 4.1/(4.7)**. Its
absorption condition must be derived in the intended asymptotic range;
the unrestricted source statement needs additional control of the near
contribution. Neither obligation is concealed by the exact algebra.

The zeta-superlevel/common-shift and local-mean lower bound, actual
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are unchanged.

All twelve modules enter the default root, the target BAT's exact production
inventory, 30 explicit public-theorem audits and 43 semantic regressions.
The regressions include actual unweighted prefixes at lengths 0, 1 and 2,
the surviving literal-one pair moment, empty sets, zero radius and the
zero retained-moment specialization. Continue maintaining
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat`; no warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  459 package Lean files, 470 integrity-scanned files, 9,314 build jobs,
  4,429 discovered target theorems and 4,434 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 43 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-131005-aaa8691f.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_131248.log`;
  manifest: `logs/foundation_freeze_20260921_131248.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 116 checked source,
integration and runner hashes match before and after the final gates,
including the preserved counterexample.

The first foundation attempt,
`logs/foundation_freeze_20260921_130845.log`, exited 1: a prose line
beginning with the word "constant" matched its postulate scan. Rewording
that comment resolved the match; the proofs and scanner policy were not
changed. The complete rerun above is the current verification evidence.

These are integrity checks for the installed scope, not completion of
the full source-(4.7) range, Bourgain dichotomy, Add-est (ix), or the
whole-proof goal.

## Bourgain power windows and mass-level alternative — verified history

The authorized two-witness powering repair and Add-est (i)--(viii) remain
intact. `EnergyPoweringObstruction.lean` is unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Six new production modules advance the actual Bourgain source chain:

- `BourgainMomentWindows`: monotonicity of the genuine local zeta
  integrals and weighted difference moment; the native integer smoothing
  radius plus one fits a larger small power at a proved threshold.
- `BourgainRetainedUniform`: all constants and the square-root loss
  are absorbed into one physical epsilon loss. Its intermediate numerical
  high-value threshold remains visible.
- `BourgainRetainedPowerWindows`: exact three-term powers and their
  bounds from the same physical N,T,V and retained moment.
- `BourgainRetainedSource`: derives the numerical threshold and V-1
  endpoint loss from sigma>3/4 and the actual power windows. The abstract
  cutoff is discharged by the existing constructed smooth cutoff.
- `BourgainSmallMass`: solves the three-quarter-power recurrence,
  including zero cardinality, and derives the exact small-mass powers.
- `BourgainMassDichotomy`: consumes the actual source subfamily,
  either obtains the small-mass cardinality estimate or selects an
  actual nonempty dyadic integer difference level with all losses.

For sigma>3/4, any fixed real tau and epsilon>0,
`bourgain_retained_source_power_bound` supplies C>=1 and delta>0
before the pattern. If

```text
C <= N <= T, T <= N^(tau+delta), N^(sigma-delta) <= V,
```

it constructs two-separated W contained in the reflected source ordinates
and in [0,T]. With R0=|P.ordinates|, R=|W| and the genuine moment

```text
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
```

the conclusion is

```text
R0 <= C*N^epsilon*R,
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(3-4sigma+epsilon)*sqrt(M(W,N^epsilon))
].
```

The numerical high-value condition is no longer a premise here. The proof
chooses a positive exponent gap, dominates its actual constant, absorbs
V-1, and links T to N before bounding the smoothing radius. It retains
N<=T explicitly and permits tau=1 whenever that physical condition holds.
The exact regression at sigma=84/109 checks the strict gap
8sigma-6=18/109; no endpoint of Add-est (ix) was discarded.

The stronger actual-pattern consumer
`bourgain_retained_difference_level_dichotomy` chooses the same W
before any real alpha. Put h=N^(epsilon/8). For every alpha it proves
one of the following:

```text
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(-2alpha+tau+12-16sigma+epsilon)
]
```

or an actual integer j with D=bourgainDifferenceLevel W j such that

```text
L_R = Nat.log 2 R + 1, 0 <= j < L_R, D nonempty,
2^j <= R, 2^j*|D| <= 2*R^2,
N^(-alpha)*R^(3/2)*N^(tau/2) < M(W,h),
M(W,h) <= L_R*2^(j+1)*
           sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

The index condition is exactly
`j in Finset.range (Nat.log 2 W.card + 1)`; no logarithmic limit has
been taken. The small branch uses the actual subset-cardinality bridge
from R to R0.
The large branch derives positive mass and consumes the proved selector.
No analytic mass bound, auxiliary set or selector is postulated.

This is the **small-mass/heavy-difference-level alternative**, not the
full frozen Bourgain logarithmic dichotomy. Zeta superlevel selection,
subdivision with common parameters/shift, the local-mean lower bound and
the final mixed-moment comparison still have to be assembled. The
unrestricted low-value range of printed Lemma 4.1/(4.7), remaining physical
range bridges, the finite/logarithmic transfer, ninth-row discharge and
Add-est (ix) remain open. EPZAE-19/36/37 and the full EPZAE-00--41 contract
are not closed by this increment.

All six modules enter the root import graph and the exact production
inventory used by `run_tao_trudgian_yang_build.bat`. Twelve explicit
public-theorem audits and 23 regression examples cover the full signatures,
zero/empty windows, the native ceiling, zero-cardinality recurrence and
the exact sigma=84/109, tau=1 source-window specialization. Both the target
BAT and foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  465 package Lean files, 476 integrity-scanned files, 9,320 build jobs,
  4,441 discovered target theorems and 4,446 audited declarations.
  All 12 new explicit audits use only permitted logical dependencies;
  all 23 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-133945-11e430fe.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_133728.log`;
  manifest: `logs/foundation_freeze_20260921_133728.json`.

Both completed logs have zero Lean errors, warnings or tactic-info
diagnostics. Every foundation stage also records zero linter failures.
There are no remaining failed verification stages. All 122 checked
source, integration and runner hashes are unchanged across the final
gates, including the preserved printed-Lemma-62 counterexample.
The Reproduction Manifest records the full log and new-source hashes.

This verifies the installed theorem scope, not the full source-(4.7)
range, the complete Bourgain logarithmic dichotomy, Add-est (ix), or
the unchanged whole-proof goal.

## Bourgain actual zeta bands and shifted slices — verified history

The authorized independent cardinality/energy powering repair and
Add-est (i)--(viii) remain intact. The printed-Lemma-62 counterexample is
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness is restored.

Eight new production modules extend the genuine Bourgain large-mass chain:

- `BourgainZetaBands`: actual critical-line amplitude bands, measurable
  finite support, the proved fourth-moment measure bound and a genuine
  global linear growth majorant.
- `BourgainBandOccupancy`: literal translated integer counts, finite
  interval integrability, and both cardinality and integer-overlap bounds.
- `BourgainDyadicBands`: half-open amplitude partition and an explicit
  ceiling-logarithmic terminal count derived from actual zeta growth.
- `BourgainBandSelection` and `BourgainPositiveBand`: integration,
  finite maximization, and a positive band selected from the actual mass.
  The low-amplitude contribution is retained, then absorbed by a proved
  choice of floor; no selector or growth estimate is assumed.
- `BourgainBandShift`: the first moment method selects a real shift
  for a finite weighted family, and an actual nonempty integer slice for
  positive band mass.
- `BourgainBandCorrelation`: the normalized occupancy is defined from
  actual mass, measure and cardinality; its identity and finite bounds
  are proved.
- `BourgainPatternBand`: consumes the same W and heavy difference level
  returned by the existing actual-pattern dichotomy and assembles all
  these conclusions.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_zeta_band_dichotomy` supplies B>0, C>=1 and delta>0
before the actual pattern. Under
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`,
it chooses two-separated W in the reflected ordinates and [0,T],
with `|P.ordinates|<=C*N^epsilon*|W|`, before every real alpha.

The small branch retains the three previously proved cardinality powers.
In the large branch put R=|W| and use the returned integer j and
D=bourgainDifferenceLevel W j. The theorem retains
`j<log_2(R)+1`, D nonempty, `2^j<=R`, and `2^j*|D|<=2R^2`.
Define the actual quantities

```text
h = N^(epsilon/8), U = T+h+1,
L = sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
a = sqrt(L/(4h|D|)),
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

Then L,a>0, and some q<J gives v=a*2^q>0. The band and its mass are

```text
S = {t in [-U,U] : v <= |zeta(1/2+it)| < 2v},
I = integral_(-h)^h #{l in D : l+u in S} du,
mu = Lebesgue measure(S), K_h = 2 Nat.ceil(h)+1,
K = 2 (Nat.log 2 R+1) 2^(j+1) J (2v)^2.
```

The assembled actual-pattern theorem proves

```text
I>0, mu>0,
N^(-alpha) R^(3/2) N^(tau/2) < K I,
v^4 mu <= C U^(1+epsilon),
I <= 2h|D|, I <= K_h mu.
```

The floor has the exact identity `2h a^2 |D|=L/2`; the other half
selects the band. Spatial enlargement U is derived from the actual
difference support, including its unit integer-rounding loss. The
extra final dyadic band handles equality at powers of two.

For the actual correlation `r=I/(sqrt(mu)*sqrt(|D|))`:

```text
r>0, I=r sqrt(mu) sqrt(|D|),
r^2 <= 2h K_h,
r^2 mu <= 4h^2 |D|,
r^2 |D| <= K_h^2 mu.
```

There is a real u in (-h,h] for which
`D_u={l in D : l+u in S}` is nonempty and
`N^(-alpha) R^(3/2) N^(tau/2) < K (2h) |D_u|`.
This is a genuine shifted slice, not an abstract mass witness.
The separate weighted-family shift theorem uses one shift for the whole
supplied finite family; common band parameters across source subdivisions
have **not** yet been constructed.

The ceiling-logarithmic J and all finite losses remain explicit. No
uniform logarithmic absorption, full source subdivision, local-mean
lower estimate, final mixed-moment comparison, frozen logarithmic
dichotomy or ninth-row discharge is claimed. The unrestricted printed
Lemma 4.1/(4.7) range and remaining physical-range bridges also remain
open. Add-est (ix), EPZAE-19/36/37 and the whole EPZAE-00--41 goal
retain their existing acceptance tests.

All eight modules enter the root imports and the exact BAT inventory.
There are 29 new explicit public-theorem audits and 43 semantic
regressions, including full signatures, empty/zero windows, half-open
band boundaries, exact dyadic counts, the half-mass identity and
weighted common shifts. The target
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat` remain mandatory; no verification gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  473 package Lean files, 484 integrity-scanned files, 9,328 build jobs,
  4,476 discovered target theorems and 4,481 audited declarations.
  All 29 new explicit public audits have only permitted logical dependencies;
  all 43 new semantic regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-141745-d2685809.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_141746.log`;
  manifest: `logs/foundation_freeze_20260921_141746.json`.

Both completed logs have zero Lean errors, warnings or tactic diagnostics.
Every foundation stage also records zero linter failures. There are no
remaining failed verification stages. All 130 checked source, integration
and runner hashes are unchanged across the gates, including the preserved
counterexample. Repository scans found no prohibited proof shortcut;
the broad postulate search has only the same ten prose and two rational
structure-field matches. `git diff --check` passes; its 16 LF/CRLF notices
are Git normalization notices, not Lean diagnostics.

This verifies the installed scope. It does not complete the full Bourgain
source range/dichotomy, Add-est (ix), or the unchanged whole-proof goal.

## Bourgain shared grids and actual subdivision — verified historical checkpoint

The corrected independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. The printed-Lemma-62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The false fifth-coordinate scaling and third witness remain excluded.

Six new production modules advance the actual Bourgain source chain:

- `BourgainSharedFloor`: a physical amplitude floor independent of the
  selected difference set, local mass and component. Its doubled low-value
  cost is bounded using the actual source cardinality and heavy-level bounds.
- `BourgainFixedBand`: selection on this supplied common floor. Its
  explicit low-mass condition is discharged in the actual-pattern consumer.
- `BourgainBandLogBounds`: the exact ceiling-logarithmic band count is
  bounded by a linear logarithm, and by an arbitrary small positive power
  with fixed-parameter constants.
- `BourgainSharedGrid`: the existing actual source dichotomy now selects
  its bands on that shared grid, retaining the complete measure, occupancy,
  correlation and shifted-slice conclusions.
- `BourgainRetainedPullback`: inverse local reflection preserves actual
  cardinality, separation, the original coefficient polynomial and every
  strict ordered integer difference count. Local source bins, and retained
  subsets pulled back into distinct bins, are disjoint.
- `BourgainSubdivisionGrid`: constructs retained subfamilies in every
  actual localized pattern and assembles their disjoint original-source union
  with exact cardinality and packing cost.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_shared_grid_dichotomy` gives B>0, C>=2 and
0<delta<=1 before the pattern. It retains the physical conditions
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`.
The same W is selected before every real alpha. Its small branch is
unchanged; its large branch now uses

```text
A = |alpha|+4|tau|+epsilon+20,
a = N^(-A), h = N^(epsilon/8), U = T+h+1,
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

This a is independent of W, the difference index j, D and its actual local
mass L_D. For the returned heavy level the proof derives

```text
2 (Nat.log 2 |W|+1) 2^(j+1) [2h a^2 |D|]
  <= N^(-alpha) |W|^(3/2) N^(tau/2)
  < M(W,h)
  <= (Nat.log 2 |W|+1) 2^(j+1) L_D.
```

Thus `2(2h a^2 |D|)<L_D`, so the fixed-floor selector genuinely
applies. The floor's crude numerical margin is proved, including negative
alpha and tau; no new mass estimate is postulated.

The proved physical radius bound and actual-pattern count conclusion are

```text
U <= 3 N^(|tau|+epsilon+1),
J <= 2 + [log(4B+1) + (|tau|+epsilon+1+A) log N]/log 2.
```

For fixed B,A,u and any eta>0, the separate uniform theorem bounds J by
C_eta N^eta whenever 0<=U<=3N^u and N is sufficiently large.
Those constants may depend on A, hence on alpha; no uniform-in-alpha
small-power absorption is asserted.

The new public subdivision theorem `bourgain_subdivided_shared_grid`
uses the actual `P.localized L hL i` patterns, with unchanged N,
threshold, support and coefficients. Here L is the chosen local height;
tau controls L, **not the unrestricted original height P.T**. It assumes
`N<=L<=N^(tau+delta)` and the same scale/value conditions. It constructs
W_i for every local component, before alpha. All components therefore use
the same a,h,U=L+h+1,J, though their chosen amplitude index q may differ.

For I=range(floor(P.T/L)+1), let

```text
S_i = { (P.localized L hL i).intervalRight - w : w in W_i },
S = union_(i in I) S_i.
```

The source consumer proves S is contained in P.ordinates, S is one-separated,
the original negative-phase polynomial is large at every point of S, and

```text
|S| = sum_(i in I) |W_i|,
|P.ordinates| <= C N^epsilon |S|,
Delta_(S_i)(l) = Delta_(W_i)(l) for every integer l.
```

The count identity uses inverse reflection and swapping the ordered pair,
so the strict unit boundary and the same integer bin are preserved.
One must use these pulled-back subsets for the global source union;
normalized reflected sets from different components can overlap.

Common amplitude indices, relative difference levels and correlation levels
across the large components are still open. The shared grid and actual
subdivision do not by themselves prove source (4.43)--(4.47). The remaining
local-mean lower estimate, mixed-moment comparison, logarithmic transfer,
ninth-row discharge, unrestricted source-(4.7) range and other required
physical-range bridges remain open. Add-est (ix), EPZAE-19/36/37 and the
whole EPZAE-00--41 completion contract are unchanged.

All six modules are included in the root and the target BAT's exact
inventory, with 22 new explicit public-theorem audits and 37 semantic
regressions. Tests cover full signatures, common physical floors/counts,
unchanged localized coefficients, empty unions, inverse reflection and
strict integer-bin endpoints. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-145545-b9986edf.log`.
  All 479 package Lean files are covered, 490 Lean files scanned, and
  9334 build jobs pass. The audit checks 4501 discovered target theorems
  plus five imported boundary declarations: all 4506 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_145042.log`
  with its matching JSON manifest. All six stages pass; 301 root modules,
  two explicit regressions and no exclusions remain classified.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 22 newly explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 37 new semantic regressions
pass. Both full logs contain zero Lean errors, warnings or tactic
suggestions. Repository-wide shortcut scans found no prohibited proof term
or postulate; broad textual matches are existing prose or rational
structure-field names. The 136 recorded source/integration/runner hashes
are unchanged across verification, including the preserved counterexample.
The architecture has 160 distinct nodes and 397 resolved edges.
`git diff --check` passes; Git emits 16 existing LF/CRLF normalization
notices, not Lean diagnostics.

This verifies the installed supporting theorem scope, not the remaining
Bourgain dichotomy, Add-est (ix), or whole-proof completion.

## Bourgain common component levels and correlation product — verified historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses, unrestricted fifth
coordinates, and Add-est (i)--(viii) remain unchanged. No false scaling or
third witness is restored.

Five production modules advance the actual Bourgain component selection:

- `BourgainComponentSelection` proves weighted finite-fiber selection and
  the small/large partition estimate with its exact counting cost.
- `BourgainCommonBand` consumes `bourgain_subdivided_shared_grid`,
  selects one common actual zeta-amplitude index on the large components,
  and constructs their original-source union.
- `BourgainRelativeLevels` regrids the relative multiplicity
  `2^j/|W|`, with a shared physical floor, logarithmic count, and
  factor-four bounds on the actual ordered integer difference counts.
- `BourgainCorrelationProduct` derives a finite relative/correlation
  product lower bound from actual component mass and the fourth moment.
- `BourgainCommonLevels` consumes the common-band family, performs the
  second weighted selection, and derives that product inequality on the
  actual retained components.

The named proposition `BourgainComponentBand` records literal difference
sets, zeta-band integrals, measures, correlation and shifted-slice data.
It is a specification, not a theorem by itself. Both public subdivision
consumers construct these witnesses from the existing analytic theorem;
they do not accept that proposition as an analytic input.

The strongest consumer is `bourgain_subdivided_common_levels`.
For sigma>3/4, fixed real tau and epsilon>0, its constants B>0, C>=2 and
0<delta<=1 precede the pattern. It keeps
`C<=N<=L`, `L<=N^(tau+delta)`, and `N^(sigma-delta)<=P.V`.
The retained W_i are chosen before alpha. Here tau controls the local
height L, not the unrestricted original height P.T.

For fixed alpha let I=range(floor(P.T/L)+1), m=|I| and

```text
h=N^(epsilon/8), U=L+h+1,
a=N^(-(|alpha|+4|tau|+epsilon+20)),
J=bourgainZetaBandCount B U a,
Q=bourgainRelativeLevelCount N tau,
F=C [N^(2-2sigma+epsilon)+N^(2tau+4-8sigma+epsilon)
     +N^(-2alpha+tau+12-16sigma+epsilon)].
```

The theorem selects a common q<J, p<Q, and actual component indices A
contained in I. Every selected component has original local cardinality
strictly larger than F. Set V=a*2^q and d=N^(-(|tau|+2))*2^p.
For each selected i, D_i is the actual heavy difference level j_i of W_i,
R_i=|W_i|, and

```text
0<d<=1,
d R_i <= 2^j_i < 2 d R_i,
d R_i <= Delta_(W_i)(ell) < 4 d R_i  (ell in D_i),
d |D_i| <= 2 R_i.
```

The common relative index is not an absolute difference index.
The proved uniform count is

```text
Q <= 2+[log 5+(|tau|+2) log N]/log 2.
```

Writing r_i for the actual normalized band occupancy and
Z_i=Nat.log 2 R_i+1, the consumer also proves

```text
N^(-2alpha) N^tau < 1024 Z_i^2 J^2 C U^(1+epsilon) d r_i^2.
```

This follows by squaring the actual large-mass inequality, using
V^4 times the actual band measure <= C U^(1+epsilon), and cancelling
the positive R_i^3. No correlation lower bound is assumed.

Let S be the union of the retained sets pulled back into their original
local bins. The consumer proves S is contained in P.ordinates,
one-separated, and large for the unchanged original negative-phase
coefficient polynomial. Its cardinality is exactly sum_(i in A) R_i;
each component's strict ordered integer difference counts are preserved.
The original total satisfies

```text
|P.ordinates| <= m F + C N^epsilon J Q |S|.
```

The selected family may be empty when the small bound suffices. No
nonempty large family or unaccounted logarithmic loss is silently assumed.

Common correlation-level selection and its finite/logarithmic losses,
the full integer-slice common-shift inequality, the local-mean lower
estimate and actual mixed-moment comparison remain open. So do the
finite/logarithmic Bourgain dichotomy, its remaining physical-range
bridges and Add-est (ix). EPZAE-19/36/37 and the whole EPZAE-00--41
completion contract remain open and unchanged.

The root and exact target BAT inventory include all five modules,
with nine new explicit theorem audits and 23 semantic regressions.
Both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` remain mandatory, with unchanged coverage,
integrity and zero-warning gates.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-152459-3040905f.log`.
  All 484 package Lean files are covered, 495 Lean files scanned, and
  9339 build jobs pass. The exhaustive audit checks 4517 discovered target
  theorems and five imported boundary declarations: all 4522 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_152045.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All nine new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 23 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
the broad text search matches only existing prose and rational structure
fields. All 141 checkpoint source/integration/runner hashes are unchanged
between the pre-target-gate snapshot and post-gate check, including the
preserved counterexample. The architecture has 164 distinct nodes and
406 resolved edges. `git diff --check` passes; the 16 Git LF/CRLF
normalization notices are not Lean diagnostics.

Semantic edge check: CSEL is realized by
`bourgain_subdivided_common_band`, which consumes the actual subdivision
and weighted partition theorem. CRG is realized by
`bourgain_retained_relative_level` and
`bourgainRelativeLevelCount_log_bound`. CCP is the derived
`BourgainComponentBand.relative_correlation_lower`, not a field assumed
in the component predicate. CLEV is
`bourgain_subdivided_common_levels`, which constructs its selected
family from those actual outputs and derives the product inequality on it.

This verifies the installed supporting theorem scope, not the remaining
correlation selection, Bourgain dichotomy, Add-est (ix), or whole-proof goal.

## Bourgain common correlation and uniform selection losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. False fifth-coordinate scaling and a third
witness remain excluded.

Five new production modules complete the next finite selection step:

- `BourgainCorrelationScales`: a coarse polynomial amplitude-count
  bound and shared inverse-power correlation floor, with proved exponent
  margin and coefficient balance.
- `BourgainCorrelationWindow`: actual retained cardinality, spatial
  enlargement and mass/fourth-moment data force each component's correlation
  into that shared physical window.
- `BourgainCorrelationGrid`: a genuine finite correlation grid, its
  logarithmic count and fixed-parameter small-power bound, and actual
  component selection with two-sided occupancy bounds.
- `BourgainCommonCorrelation`: consumes the actual common-amplitude/
  relative-level family and performs the third retained-cardinality-weighted
  selection, preserving the original-source union.
- `BourgainSelectionLosses`: proves a joint arbitrary-small-power
  bound for all three actual selection counts.

The prior common-level module's introductory comment now scopes its
remaining work to downstream consumers; its theorem statement is unchanged.

For the already fixed B>0, C>=2, alpha, tau and epsilon>0, define

```text
u=|tau|+epsilon+1,
A0=|alpha|+4|tau|+epsilon+20,
E=2(|tau|+1)+2(u+A0)+u(1+epsilon),
A1=|alpha|+|tau|+E+1,
K0=4096 C (4B+2)^2 3^(1+epsilon)+1,
b=N^(-A1)/K0, h=N^(epsilon/8).
```

The floor b is independent of the local component, difference level,
local mass and band index. The proved actual-component window is
`0<b<r_i<=4h`. Its lower endpoint follows from the existing actual
correlation-product inequality, not an assumed correlation estimate.
The proof bounds its coefficient by `(K0-1)N^E` and proves

```text
(K0-1) N^E b^2 <= N^(-2alpha) N^tau.
```

The shared finite count and its bound are

```text
Kc = bourgainZetaBandCount (4K0) (h-1) (N^(-A1)),
Kc <= 2+[log(16K0+1)+(epsilon/8+A1) log N]/log 2.
```

The terminal bound is strict, including exact dyadic endpoints.
For fixed parameters and any eta>0, the count is <=D_eta N^eta
beyond a proved threshold. Alpha is an allowed dependency; no
uniform-in-alpha threshold is asserted.

The main consumer `bourgain_subdivided_common_correlation` retains
sigma>3/4, `C<=N<=L<=N^(tau+delta)`,
`N^(sigma-delta)<=P.V`, and `0<delta<=1`.
B,C,delta precede the pattern; the same W_i precede alpha.
Tau still describes the local height L, not the unrestricted original P.T.

It constructs common indices q<J, p<Q and k<Kc and actual selected bins.
All previous component data remain available. With
V=N^(-A0)2^q, d=N^(-(|tau|+2))2^p, s=b2^k,
U=L+h+1, actual difference set D_i, actual band measure mu, and
actual correlation r_i, each selected component satisfies

```text
0<s,  s<=r_i<2s,  s<=4h,
s sqrt(mu) sqrt(|D_i|) <= actual band occupancy
  < 2s sqrt(mu) sqrt(|D_i|),
N^(-2alpha) N^tau
  < 4096 (Nat.log 2 |W_i|+1)^2 J^2 C U^(1+epsilon) d s^2.
```

The factor 4096 is derived from the prior product bound and the
two-sided correlation band; it is not added as a field in the source
component predicate.

Let m=floor(P.T/L)+1 and F be the unchanged three-term small-component
bound from the preceding checkpoint. The selected original-source union S
has exact cardinality sum_i |W_i|, is one-separated, and is large for the
unchanged original coefficient polynomial. Every component's strict ordered
integer difference counts are preserved. The proved global bound is

```text
|P.ordinates| <= m F + C N^epsilon J Q Kc |S|.
```

The family may be empty when the small bound suffices. No nonempty large
family is silently assumed. The main consumer retains the finite counts;
their absorption is proved separately by
`bourgain_selection_counts_uniform_power`: for fixed B,C,alpha,tau,epsilon
and every eta>0, constants D,N0 precede the actual pattern and its
physical-window parameter, and for N>=N0, `J Q Kc<=D N^eta`. For the selected
family this applies to the actual localized pattern of height L.

The full integer-slice common-shift inequality, local-mean lower estimate,
actual mixed-moment comparison, finite/logarithmic Bourgain dichotomy and
remaining physical-range bridges are still open. Add-est (ix),
EPZAE-19/36/37 and the whole EPZAE-00--41 contract remain open.

The root and exact target BAT inventory include all five modules, with
17 new explicit theorem audits and 31 semantic regressions. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-155221-a509a790.log`.
  All 489 package Lean files are covered, 500 Lean files scanned, and
  9344 build jobs pass. The exhaustive audit checks 4543 discovered target
  theorems and five imported boundary declarations: all 4548 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_154836.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 17 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 31 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 146 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 168 distinct nodes and 417 resolved edges.
`git diff --check` passes; 16 Git LF/CRLF normalization notices are
not Lean diagnostics.

Semantic edge check: CSCL is realized by
`bourgain_component_correlation_window`, consuming the actual component
product, retained-cardinality bound and proved floor balance.
CGR is realized by `bourgain_component_correlation_grid`,
`bourgainCorrelationLevel_terminal` and
`bourgainCorrelationLevelCount_log_bound`.
CCOR is `bourgain_subdivided_common_correlation`, which consumes the
actual prior family, derives all component grid witnesses and constructs
the third weighted fiber and original-source union.
SLOSS is `bourgain_selection_counts_uniform_power`, whose conclusion
uses the actual counts and linked physical height of the supplied pattern.
These are supporting results; the full integer-slice shift, Bourgain
dichotomy, Add-est (ix), and whole-proof contract remain unfinished.

## Bourgain full integer slice and source mixed lower bound — historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses and Add-est (i)--(viii)
are unchanged. False fifth-coordinate scaling and a third witness stay excluded.

Twelve new production modules prove a full two-term common shift for the
actual selected family, a power-window local mean for the original polynomial,
and their actual source-pattern mixed lower-bound consumer:

- `BourgainIntegerSlice`, `BourgainSliceSelection`: the complete integer
  slice, its integrated cardinality and square-root bounds, and simultaneous
  weighted selection against both profiles.
- `BourgainComponentMass`, `BourgainFamilySlice`, `BourgainCommonSlice`:
  derive both weighted mass lower bounds from actual component occupancy,
  fourth moment and common levels, then consume the actual three-level family.
- `BourgainSliceGeometry`: the real image has the same cardinality, is
  one-separated, and has proved spatial bounds and shifted zeta membership.
- `BourgainLocalMean`, `BourgainPowerMean`, `BourgainLocalSquare`:
  frequency-center the original closed-support negative-phase polynomial,
  consume the native finite exponential-sum Fourier estimate, absorb its tail,
  and prove the displaced local-square estimate.
- `BourgainMixedLower`, `BourgainMixedFamily`, `BourgainCommonMixed`:
  preserve strict ordered difference counts and original-source pullbacks,
  sum over the disjoint bins, and assemble the actual mixed lower bound.

### Exact finite physical statement and semantic edges

Write h=N^(epsilon/8), U=L+h+1, Vb for the selected common zeta amplitude,
mu for the measure of its actual band, and K=2 ceil(h)+1. The full slice is

```text
Z(u) = {ell in [-ceil(U+h),ceil(U+h)] in Z : ell+u belongs to the band}.
```

For every u in [-h,h] it contains every integer whose translate lies in the
band, not just the integers from one component's difference level.
`bourgainIntegerSlice_integral_card_le` and
`bourgainIntegerSlice_integral_sqrt_card_le` prove, over [-h,h],

```text
integral |Z(u)| <= K mu,
integral sqrt(|Z(u)|) <= sqrt(2h K mu).
```

Let R_i=|W_i|, D_i be the actual heavy difference level, d the common relative
multiplicity, s the common correlation level, J the actual amplitude count,
and Zlog=3+(|tau|+1) log(N)/log(2). Define

```text
beta = N^(-alpha) N^(tau/2) / [32 Zlog J d sqrt(C U^(1+epsilon))],
a = s^2/(8hK),    b = beta/[4 sqrt(2hK)].
```

The theorem `BourgainComponentBand.weighted_mass_lower` derives its two
mass inequalities from the actual band, not from assumed desired lower bounds.
`bourgain_component_family_slice` consumes them and the complete slice
moments. `bourgain_subdivided_common_slice` constructs the actual selected
family and proves either the genuine small-component bound or a common
u in (-h,h] with nonempty Z=Z(u) and

```text
a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)
  < sum_i R_i |D_i intersect Z|.
```

Here S is exactly the disjoint union of retained sets pulled back into their
original bins; |S|=sum_i R_i. The common levels, unchanged original
coefficients, source containment, one-separation, strict difference counts,
and global packing cost m F + C N^epsilon J Q Kc |S| are retained.
No nonempty selected family is assumed; the empty case gives the small bound.

For every eta>0, `bourgain_power_window_displaced_square` provides constants
M>0 and N0>=2 before the actual pattern and points, and proves

```text
P.V^2 <= M N^eta integral_[-r,r] |F_P(x+v)|^2 dv,
r=1+2 pi N^eta,
```

when N>=N0, sigma>=0, delta<=1, N^(sigma-delta)<=P.V, and x is within one
unit of an actual large ordinate. The underlying exact modulation is
exp(i log(N)t) F_P(t); its frequencies are log(N)-log(n), of absolute value
at most one on the literal closed support [N,2N]. It uses the already
kernel-checked native `norm_gmFiniteExpSum_le_localIntegral_add_tail`,
then absorbs the actual tail using P.V>=N^(-1). No analytic local-mean
hypothesis is supplied by a caller.

This is a directly proved **power-window** route to the needed mixed lower
bound, not a proof of the printed logarithmic-window lemma (4.48).
That sharper printed statement is not marked complete.

The strongest consumer `bourgain_subdivided_mixed_lower` retains
sigma>3/4, epsilon>0, eta>0, C<=N, N0<=N,
N<=L<=N^(tau+delta), N^(sigma-delta)<=P.V and 0<delta<=1.
B,C,delta,M,N0 precede the actual pattern; W_i still precede alpha.
Tau governs the local L, not the unrestricted original P.T.
On its large branch it constructs the same nonempty full slice and proves

```text
P.V^2 d [a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)]
  < M N^eta integral_[-r,r] sum_(t in S) sum_(ell in Z)
      |F_P(t-ell+v)|^2 dv.
```

The strict-bin first-coordinate injection uses each W_i's two-separation.
The proof transports each component's ordered counts into its original bin
and sums over the disjoint source union. It does not identify the union's
total difference count with the sum of component counts.

This closes the finite physical common-shift and source mixed **lower**
steps (the roles of source (4.47) and (4.53)). It does not yet combine the
mixed upper bound with Heath--Brown, prove (4.57)--(4.63), or discharge
the ninth-row logarithmic-dichotomy premise. Add-est (ix), EPZAE-19/36/37,
and the whole EPZAE-00--41 goal remain open.

Root imports, the exact target BAT inventory, explicit audit and semantic
regressions include all twelve modules: 39 new public theorem audits and
59 new regression examples, including closed endpoints, strict excluded
difference boundaries, zero amplitude, unchanged coefficients and both
source-facing consumer types. Both `run_tao_trudgian_yang_build.bat` and
foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-164830-0fe87f33.log`.
  All 501 package Lean files are covered, 512 Lean files scanned, and
  9356 build jobs pass. The exhaustive audit checks 4601 discovered target
  theorems and five imported boundary declarations: all 4606 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_164601.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 39 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 59 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 158 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 172 distinct nodes and 428 resolved edges.

Semantic green-node check: ISL uses
`bourgainIntegerSlice_integral_card_le`,
`bourgainIntegerSlice_integral_sqrt_card_le` and
`bourgainRealSlice_separated`/`bourgainRealSlice_bounds` on the defined
complete slice. CSH is `bourgain_subdivided_common_slice`, which consumes
the actual common-correlation family and derived weighted mass bounds.
LPM is `bourgain_power_window_displaced_square`, using the proved exact
modulation, native Fourier estimate, tail absorption and interval translation.
MLB is `bourgain_subdivided_mixed_lower`, which unpacks the actual source
family and composes CSH, LPM, strict difference counts and original pullbacks.
These statements preserve the stated parameter ranges and constant order.
The full mixed upper assembly, Bourgain dichotomy, Add-est (ix) and
whole-proof contract remain open; audit counts do not close those obligations.

## Bourgain Heath–Brown comparison and linked subdivision — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est (i)--(viii)
are preserved; false fifth-coordinate scaling and a third witness stay excluded.

Ten new production modules advance the actual mixed lower bound through
Heath--Brown, remove the common multiplicity/correlation levels, and link
the subdivision to the original physical height:

- `BourgainSeparatedSelf`: the native Heath--Brown self-moment bound on
  arbitrary one-separated sets, with the original polynomial's closed support
  and explicit endpoint error. The auxiliary slice is not falsely made into
  a large-value pattern for the original polynomial.
- `BourgainMixedShift`, `BourgainMixedUpper`: exact unit-norm coefficient
  twist, integer-to-real sum bridge, integration length, and the actual
  source-set/full-slice mixed upper bound.
- `BourgainCommonComparison`: consumes the already constructed selected
  family and both actual analytic estimates.
- `BourgainLevelElimination`, `BourgainLevelFreeComparison`: use the
  genuine component product to remove correlation and multiplicity from
  the first coefficient; cancel multiplicity exactly in the second; replace
  the component three-halves sum by the retained union's cardinality,
  paying the square root of the actual bin count.
- `BourgainPhysicalUpper`, `BourgainPhysicalComparison`: prove the
  slice's enclosing height is at most 8 times the original height when
  N<=L<=T and epsilon<=8; absorb the constant-factor enlargement uniformly.
- `BourgainSubdivisionScale`, `BourgainLinkedComparison`: link
  L=T/N^chi with both original-height power bounds, prove the finite bin
  count, and instantiate the actual comparison at the ninth-row choice.

### Source-facing physical comparison

The strongest general linked consumer is
`bourgain_linked_subdivision_comparison`. It assumes sigma>3/4,
chi>=0, lambda=tau-chi>1, eta>0, theta>0 and 0<epsilon<=8.
Its positive constants B,C,M,D,N0 and
0<delta<=min(1,(lambda-1)/2) precede the actual pattern.

For N>=max(C,N0), N^(tau-delta)<=T<=N^(tau+delta),
N^(sigma-delta)<=P.V and the literal L=T/N^chi, it derives N<=L<=T,
the required local upper-height bound, and

```text
m = floor(T/L)+1 <= 2 N^chi.
```

The local band/selection constructions use **lambda**, not global tau.
The same genuine reflected W_i are chosen before alpha. For every alpha
the consumer preserves all three common levels, every actual component band,
the disjoint original-source union S, exact cardinality, one-separation,
the unchanged original polynomial and the strict ordered difference counts.

Write h=N^(epsilon/8), U=L+h+1, K=2 ceil(h)+1,
Zlog=3+(|lambda|+1) log(N)/log(2), J for the actual amplitude count,
R=|S|, and x=|Z(u)| for the nonempty complete integer slice.
Define the two level-free coefficients

```text
gamma = N^(-2alpha) N^lambda /
  [32768 h K Zlog^2 J^2 C U^(1+epsilon)],
beta = N^(-alpha) N^(lambda/2) /
  [128 Zlog J sqrt(C U^(1+epsilon)) sqrt(2hK)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The exact Lean names are `bourgainEliminatedCardCoefficient`,
`bourgainSliceSqrtCoefficient ... 1`, and `bourgainSecondBudget`.
Both lower coefficients are proved positive. Either the actual original
cardinality obeys the small-component bound m F, or S is nonempty and the
consumer constructs u in (-h,h] and the nonempty full slice satisfying

```text
P.V^2 [gamma x R + beta sqrt(x) R^(3/2)/sqrt(m)]
  < M N^eta 2(1+2 pi N^eta) D T^theta
      sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

F is the unchanged three-term small-component bound, now with local lambda.
The companion global selection inequality remains
`|P.ordinates| <= m F + C N^epsilon J Q Kc R`, with actual finite counts.
No Heath--Brown, local-mean, desired correlation, or mixed-bound hypothesis
is left for the caller to provide. Both height hypotheses and coefficient
normalization are discharged on the actual objects.

This is the full finite physical mixed comparison with the third
Heath--Brown term retained. It is not a claim that the paper's simplified
two-term display holds without its additional range assumptions.

### Ninth-row entry and exact remaining work

`bourgain_ninth_row_local_height_margin` proves that
chi=max(0,4sigma+4tau/3-5) is nonnegative and tau-chi>1 from sigma>3/4,
16sigma-11<=tau and 20sigma+tau/3<=16.
`bourgain_ninth_row_physical_comparison` actually instantiates the linked
source consumer at that choice. This closes that row's interior local-height
entry, not the row's large-values conclusion.

Next remove the finite/logarithmic losses with correctly ordered constants:
bound gamma and beta below by the required small-power expressions, use
the proved m bound, transfer the retained union back to total cardinality,
control the slice-cardinality exponent, and pass the actual comparison to
the frozen logarithmic dichotomy. Then discharge
`bourgain_ninth_row_of_log_dichotomy` and finish Add-est (ix).

The unrestricted printed-(4.7) range and other classical/source obligations
remain open. The printed logarithmic-window (4.48) is still not claimed:
the comparison uses the already proved power-window route.
EPZAE-19/36/37, Add-est (ix), and the full EPZAE-00--41 goal remain open.

The root imports, exact target BAT inventory, explicit audit and semantic
regressions include all ten modules: 31 public theorem audits and 45 regression
examples. Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, including coverage, dependency, integrity and
zero-warning gates. No frozen source or dependency pin changed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-172415-5a54834a.log`.
  All 511 package Lean files are covered, 522 Lean files scanned, and
  9366 build jobs pass. The exhaustive audit checks 4645 discovered target
  theorems and five imported boundary declarations: all 4650 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_172230.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 31 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 45 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 168 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 177 distinct nodes and 444 resolved edges.
`git diff --check` passes; the 16 Git LF/CRLF normalization notices
are not Lean diagnostics.

Semantic green-node check: HBSET is
`bourgain_separated_self_moment`, applying the native moment to the
actual reflected arbitrary set and paying the closed-support endpoint.
SHCS is `bourgain_slice_mixed_integral_cauchySchwarz`, using the
proved exact twist, support-only coefficient bound and complete integer image.
MCOMP is `bourgain_subdivided_mixed_comparison`, composing the actual
selected-family lower bound with the proved upper estimate on its source union
and full slice. LELIM is `bourgain_subdivided_level_free_comparison`;
its first coefficient is derived from the real component product, its second
uses exact multiplicity cancellation, and its power-sum loss uses the actual
disjoint-union cardinality and bin count.
PSCALE is `bourgain_linked_subdivision_comparison` and
`bourgain_ninth_row_physical_comparison`, deriving local ranges and
the original-height enclosure from the literal subdivision and shrinking
the allowed delta explicitly. No desired analytic estimate is a premise.

These are finite source-comparison results. Finite-loss absorption, the
logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain
unfinished; dependency integrity is not a claim of those endpoints.

## Bourgain uniform finite power losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged
(SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The corrected independent cardinality and energy witnesses, Heath--Brown
energy relation and Add-est (i)--(viii) remain preserved. No false
s'/s fifth-coordinate scaling or third powering witness is introduced.

Five production modules now express the actual comparison's finite losses
as explicit powers, with constants chosen before the physical pattern:

- `BourgainCoefficientIdentity` proves beta^2=gamma exactly, including
  the zero fourth-moment-constant boundary, and beta=sqrt(gamma).
- `BourgainComparisonLogLoss` bounds the literal difference logarithm
  and amplitude count jointly by an arbitrary positive power.
- `BourgainCoefficientLosses` derives the ceiling-window product,
  enlarged local-height power and both coefficient lower bounds.
- `BourgainComparisonPowerBudget` bounds the square-root bin factor
  and original-height integration factor, and proves explicit slack control.
- `BourgainLinkedPowerLoss` consumes the actual constructed family,
  retained original-source union and complete integer slice.

### Exact finite consumer and parameter order

`bourgain_linked_power_loss_comparison` fixes
sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta,
and 0<epsilon<=8 before its constants B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta). Alpha is a permitted constant dependency;
this theorem does not assert uniformity in alpha. The earlier stronger
family-before-alpha construction is unchanged.

For the actual pattern, N>=max(C,N0), L=T/N^chi,
N^(tau-delta)<=T<=N^(tau+delta), and N^(sigma-delta)<=P.V,
the theorem derives L>0 and N<=L<=T. All local grids use lambda;
the Heath--Brown budgets retain the original T.

Write R=|S|, h=N^(epsilon/8), U=L+h+1, x=|Z(u)|, and

```text
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
F = C [N^(2-2sigma+epsilon)
       + N^(2lambda+4-8sigma+epsilon)
       + N^(-2alpha+lambda+12-16sigma+epsilon)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The real selected set S is a one-separated subset of the original ordinates,
with the original polynomial large at every member. Its packing inequality is

```text
|P.ordinates| <= 2 N^chi F + C H N^(epsilon+kappa) R.
```

Either |P.ordinates|<=2 N^chi F, or S is nonempty and a genuine grid level q
and u in (-h,h] give a nonempty complete integer slice with

```text
N^(2sigma-2delta) [
  N^(-2alpha-E)/G * x R
  + N^(-alpha-E/2-chi/2)/sqrt(2G) * sqrt(x) R^(3/2)]
< K N^(2eta+(tau+delta)theta)
    sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

The coefficient bounds come from the actual denominators, not assumed
certificates. The joint J Q Kc bound is applied to the actual localized
pattern; the bin factor comes from floor(T/L)+1<=2N^chi. The source comparison
at its original delta is specialized using monotonicity to the smaller
requested tolerance, while the new loss estimates use the smaller delta.
No caller supplies an analytic bound, desired correlation, or slice witness.

### Remaining acceptance work

This proves the finite power-loss reduction, not the logarithmic dichotomy.
Choose the small parameters in the required order, absorb the remaining fixed
constants in the limiting argument, control/extract the nonempty slice's
logarithmic cardinality, and use the actual packing inequality to relate R
to the original count. Discharge `bourgain_ninth_row_of_log_dichotomy`,
then the ninth energy projection and Add-est (ix).

The unrestricted printed-(4.7) source range, printed logarithmic-window
(4.48), other open classical/density/exponent-pair work, EPZAE-19/36/37,
and the full EPZAE-00--41 goal remain open. The power-window route is retained;
no public contract, source pin or dependency pin changes.

The root import graph, exact BAT production inventory, explicit axiom audit
and semantic regressions include these five modules and all 11 public theorems.
There are 20 new regressions: 11 exact signatures and nine boundary/slack cases.
Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, with complete coverage and unchanged integrity,
dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-175120-bcf6f466.log`.
  All 516 package Lean files are covered, 527 Lean files scanned, and
  9371 build jobs pass. All 4657 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4662-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_175131.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 11 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 20 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The first foundation attempt, `foundation_freeze_20260921_175009.log`,
failed its text scan on a prose-comment line beginning "constant boundary".
The comment was clarified; no proof or scan gate was weakened. That failed log
is retained as failed historical evidence, not substituted for the current PASS.

All 173 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 178 distinct nodes and 448 resolved edges.
Repository shortcut scans find no prohibited proof term or postulate;
remaining broad text matches are existing prose and rational structure fields.

Semantic green-node check: FPOWER is exactly
`bourgain_linked_power_loss_comparison`. Its proof unpacks
`bourgain_linked_subdivision_comparison`, applies the uniform coefficient
bounds to the derived local physical scale, applies the actual selection-count
bound to `P.localized L hL 0`, and uses the genuine bin count and original T.
It retains the source small alternative and the original polynomial, and
constructs the same complete zeta slice rather than assuming one.
The arbitrarily small tolerance is derived by shrinking the source delta.
No desired analytic estimate or limiting dichotomy is a premise.

This verifies finite power-loss reduction and dependency integrity only.
The logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain open.

## Bourgain finite logarithms and slice compactness — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent corrected cardinality/energy witnesses, Heath--Brown relation,
and Add-est (i)--(viii) remain preserved. The false fifth-coordinate scaling
and third witness remain excluded.

Seven new production modules continue from the actual finite power-loss
comparison. They prove the physical slice-cardinality bound, translate both
comparison terms and the original-source packing inequality into logarithms,
and extract both real cardinality coordinates along one common subsequence.

### Actual finite logarithmic alternative

`bourgain_linked_logarithmic_comparison` consumes
`bourgain_linked_power_loss_comparison` on the original pattern, with the
same parameter order and an explicit nonempty-original-set restriction.
This restriction is needed because Mathlib gives log(0)=0; the theorem never
treats that convention as a logarithmic exponent for an empty set.

Fix sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta
and 0<epsilon<=8. Uniform B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta) precede the physical pattern. For the same
literal subdivision L=T/N^chi and original-height/amplitude hypotheses,
write

```text
rho = log_N |P.ordinates|, r = log_N |S|, x = log_N |Z(u)|,
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
Bsmall = max(chi+2-2sigma, -chi+2tau+4-8sigma,
             -2alpha+tau+12-16sigma),
HBexp(t,y) = max(2y+1, y+2, 5y/4+t/2+1).
```

Either rho<=Bsmall+epsilon+log_N(6C), or the actual nonempty retained subset
S and actual nonempty complete integer slice satisfy

```text
0 <= r <= tau+delta+log_N(2),
0 <= x <= lambda+delta+log_N(9),
rho <= log_N(6C+CH) + max(Bsmall+epsilon, epsilon+kappa+r),

max(-2alpha+2sigma+x+r-E-2delta-log_N(G),
    -alpha-chi/2+2sigma+x/2+3r/2-E/2-2delta-log_N(2G)/2)
< log_N(3K)+2eta+(tau+delta)theta
    + HBexp(tau+delta,r)/2 + HBexp(tau+delta,x)/2.
```

The source set remains one-separated and the original polynomial is large
at its members. The common grid level q and shift u remain genuine witnesses,
not separately supplied scalar cardinalities. All three Heath--Brown terms
are retained.

### Geometry, compactness and supporting limit algebra

`BourgainLogCardinality` proves the full slice has at most 2(U+h)+1
integers using its actual translated band, hence at most 9 N^(lambda+delta)
on the physical local scale. Positivity and logarithmic bounds are derived
from actual nonemptiness.

`BourgainBudgetLogarithm` proves the literal three-term budget is at most
3 N^HBexp at an actual cardinality, and proves joint continuity of HBexp and
its delta/2 height-slack bound. `BourgainComparisonLogarithm` takes logarithms
of both positive finite summands. `BourgainLogPacking` recovers exactly the
frozen first-branch maximum from the three small-component powers and keeps
the retained-to-original count loss explicit.

`bourgain_source_slice_log_subsequence` in `BourgainSliceCompactness`
derives a fixed box from actual pattern/subset/slice geometry and returns
one strictly increasing subsequence for both coordinates:
0<=r<=tau+2 and 0<=x<=lambda+5. No bounded-log-coordinate certificate is an
input. The harmless box constants do not replace the sharper finite bounds.

`BourgainComparisonLimits` proves fixed log_N multipliers tend to zero
when N tends to infinity. Its `bourgain_fixed_logarithmic_limit` passes an
explicit eventual finite logarithmic comparison and supplied coordinate
limits to the corresponding fixed-accuracy inequality. This is supporting
conditional limit algebra, not an assembled source-family dichotomy.

### Remaining source assembly

Construct the actual realizing family and select the small/large branch on
an appropriate subsequence. Apply the common compactness and limit results
to that selected family, use the original-count packing to identify the
retained exponent with the source exponent as the accuracy parameters
vanish, and remove epsilon/eta/theta/kappa/delta in their allowed order.
Then prove the frozen logarithmic dichotomy, discharge
`bourgain_ninth_row_of_log_dichotomy`, and assemble Add-est (ix).

The finite logarithmic alternative is not the zero-loss source theorem.
EPZAE-19/36/37, the ninth projection and clause (ix), all other unfinished
exponent-pair/density/public/release obligations, and the full EPZAE-00--41
goal remain open. The printed logarithmic-window (4.48) and unrestricted
printed-(4.7) range are not claimed.

All seven modules are in the root imports and exact BAT inventory, with
explicit audits for 21 public theorems and 31 new semantic regressions
(21 exact types plus ten boundary/source-form checks). Maintain
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
including full coverage, integrity, dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-182850-36f5160d.log`.
  All 523 package Lean files are covered, 534 Lean files scanned, and
  9378 build jobs pass. All 4683 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4688-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_182901.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 21 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 31 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The earlier foundation run at 182402 also passed but preceded the last source
edit; the 182901 run above supplies the final-source evidence.

All 180 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 180 distinct nodes and 455 resolved edges.
The runner inventory grew by exactly seven modules; source/dependency pins,
permitted axioms, foundation verification gates and both BAT launchers are
unchanged. No proof shortcut, postulate or warning suppression was introduced.

Semantic green-node checks:

- BLOG is `bourgain_linked_logarithmic_comparison`. It consumes the
  actual `bourgain_linked_power_loss_comparison`, derives the local scales
  from the original T and L=T/N^chi, and takes logarithms of the actual
  original/retained counts and complete integer slice. Nonemptiness,
  geometry, original-source packing, and both comparison terms are retained.
  The caller supplies no desired comparison or independent scalar witness.
- BSCOMP is `bourgain_source_slice_log_subsequence`. It derives a common
  compact box from the physical height and subset/slice hypotheses and
  returns one strictly increasing subsequence for both actual coordinates.
  It does not itself choose a realizing family or select the source branch.
- `bourgain_fixed_logarithmic_limit` is explicitly conditional supporting
  algebra: the eventual finite comparison and coordinate limits are inputs.
  It is not used to mark the full analytic source dichotomy green.

This verifies the finite logarithmic alternative, geometric compactness and
fixed-constant limit algebra only. Source branch selection, zero-loss limiting
assembly, Add-est (ix), and the unchanged whole-proof contract remain open.

## Bourgain source dichotomy and optimized region rows — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses, the Heath--Brown
relation and Add-est (i)--(viii) are preserved. No fifth-coordinate scaling
or third powering witness has been restored.

### Actual source-family construction and zero-loss limit

`exists_bourgain_region_family` chooses actual patterns from
`InCardinalityEnergyRegion` after arbitrary positive physical tolerances
and arbitrary scale thresholds. Its cardinality logarithms converge to the
source rho by the region's power sandwiches.

`exists_bourgain_diagonal_family` applies the proved finite logarithmic
alternative at accuracy `poweringAccuracy n`, choosing all analytic constants
before the patterns. One finite sum of exponential thresholds absorbs the
five varying factors G, 2G, 3K, 6C and 6C+CH. If rho>Bsmall, the source count
limit rules out the small branch on a tail. The retained source subsets,
original polynomial values and complete integer slices are actual witnesses,
not independent scalar inputs.

The resulting family has source packing

```text
rho_n <= epsilon_n + max(Bsmall+epsilon_n, 2epsilon_n+r_n)
```

and, for the same actual retained/slice cardinalities,

```text
max(-2alpha+2sigma+x_n+r_n,
    -alpha-chi/2+2sigma+x_n/2+3r_n/2)
<= (2tau-chi+12)epsilon_n
   + HBexp(tau,r_n)/2 + HBexp(tau,x_n)/2.
```

The explicit diagonal loss tends to zero. Joint geometric compactness
extracts r and x along one common subsequence. Subset monotonicity gives
r<=rho; the original-source packing and rho>Bsmall give rho<=r.
Thus r=rho, and continuity gives the exact zero-loss comparison.

The public consumer
`InCardinalityEnergyRegion.bourgain_log_dichotomy` now proves

```text
rho <= Bsmall
or exists x>=0,
  max(-2alpha+2sigma+x+rho,
      -alpha-chi/2+2sigma+x/2+3rho/2)
  <= HBexp(tau,rho)/2 + HBexp(tau,x)/2,
```

from actual region membership, sigma>3/4, chi>=0 and tau-chi>1.
It takes no source family, branch-stability assertion, coordinate-limit
certificate or analytic dichotomy as a premise. This closes the formerly
open source branch selection and zero-loss assembly in that physical range.

### Optimized region rows

Classical cardinality bounds discharge rho<=1 for tau<=3/2.
`InCardinalityEnergyRegion.bourgain_ninth_row` consumes the actual
dichotomy and the existing exact scalar certificate; its powered version
uses the corrected cardinality-preserving witness.

Three additional optimized rows follow from the same actual dichotomy.
For all rows below, sigma>3/4 and 1<=tau<=3/2; the listed additional cell
conditions are retained exactly.

| Row | Cardinality bound | Additional cell conditions |
|---|---|---|
| First affine | rho <= (16-20sigma+tau)/3 | 14sigma-10<=tau<=16sigma-11; 5tau<=4+4sigma |
| Mixed affine | rho <= 5-7sigma+3tau/4 | 4+4sigma<=5tau; 48-60sigma<=tau<=8-8sigma |
| Diagonal | rho <= 2-2sigma | tau<=14sigma-10; tau<=3sigma-1 |
| Ninth row | rho <= 9-12sigma+2tau/3 | 16sigma-11<=tau; 20sigma+tau/3<=16 |

The first-affine and diagonal height-one boundaries use the classical
estimate, not a weakened strict-margin hypothesis. The mixed cell itself
forces tau>1. Exact regressions include the common affine corner
(sigma,tau,rho-bound)=(59/76,27/19,12/19), the original 84/109 endpoint,
the height-one boundary and the actual power-two consumer.

### Remaining acceptance work

Add-est (ix) is still open. The frozen ANTEDB
`prove_zero_density_energy_7()` recipe uses tau0=8sigma-4, Bourgain and
Jutila-k=5 cardinality inputs, powers 2 through 5, the zeta moment and
Heath--Brown energy. Continue with actual corrected witnesses and exact
general/zeta energy projection over the entire interval [84/109,5/6].
Do not treat the proved cardinality row as the final energy bound.

The complete unrestricted Bourgain source range, its uniform LV-facing
assembly, any additional optimized cells required by that projection,
EPZAE-19/36/37, the other unfinished exponent-pair/density/public/release
obligations and the full EPZAE-00--41 goal remain open. Neither the printed
logarithmic-window (4.48) nor the unrestricted printed-(4.7) range is claimed.

Six new modules are root-imported and included in the exact BAT inventory.
All 15 public theorems have explicit audits and 24 new semantic regressions
(15 exact signatures and nine endpoint/object checks). The old
`NewAdditiveEnergy` module comment was corrected to say (i)--(viii), matching
its already proved theorem surface. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
with no exclusions, weakened scans, changed dependency pins or warning suppression.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-190824-8fa4580d.log`.
  All 529 package files are covered, 540 Lean files scanned and 9384
  build jobs pass. The exhaustive audit passes 4723 discovered target
  theorems plus five imported boundary declarations, 4728 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_190824.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and all declaration linters.

All 15 new public audits report only `propext`, `Classical.choice`
and `Quot.sound`. All 24 new regressions pass. Both complete final logs
contain zero Lean errors, warnings or tactic suggestions. Repository-wide
shortcut scans have no prohibited proof-term match; the broad declaration
search matches only existing prose and the two genuine rational structure
fields, also accepted by the contract-aware scanners.

All 186 checkpoint source/integration/runner hashes match the snapshot
taken before the final BAT runs. The counterexample and both BAT launchers
are unchanged. Only five existing integration/status files changed; the
remaining new Lean work is in the six named modules. No source/dependency
pin, permitted-axiom policy or verification gate was weakened.

The architecture has 183 distinct nodes and 464 resolved edges.
Semantic green-node checks:

- BDFAM is `exists_bourgain_diagonal_family`: it consumes actual region
  realizations and the finite analytic alternative, absorbs constants by
  its chosen physical scales, and derives branch selection on a tail.
- BDICH is `InCardinalityEnergyRegion.bourgain_log_dichotomy`: it invokes
  that constructor and `BourgainDiagonalFamily.source_witness`; the latter
  consumes actual geometric compactness and original-source packing to
  prove r=rho before taking the zero-loss limit.
- BROWS consists of the four stated actual-region row theorems and
  `bourgain_ninth_row_powered`. They consume the proved dichotomy,
  classical side-condition bridge, exact scalar algebra and corrected
  cardinality witness. The height-one cases are handled explicitly.

These passes verify the installed region dichotomy and specified cardinality
cells, not the full Bourgain source range, Add-est (ix), or whole-proof
completion. The energy projection and all other open goal obligations remain open.

## All nine Add-est clauses recovered by corrected powering — historical checkpoint

### Result and preserved obstruction

The authorized repair now recovers every printed Add-est clause (i)--(ix).
The original singleton counterexample in `EnergyPoweringObstruction.lean`
is unchanged (SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
Printed Lemma 62 remains false as printed: its fifth-coordinate scaling
has not been restored or assumed. The archived source and public output
statements have not been changed.

`correctedCardinalityEnergyPowering` supplies separate cardinality- and
energy-preserving witnesses. Their fifth exponents remain independently
existential. The actual Heath--Brown consumer uses the appropriate witness,
and cardinality monotonicity supplies the other coordinate's upper bound.
This is not a claim that an arbitrary four-coordinate polytope is preserved.

### Exact final-clause consumer

On the entire closed interval `84/109 <= sigma <= 5/6`, write

```text
B(sigma) = max((18-19sigma)/(9(3sigma-2)),
               4(10-9sigma)/(5(4sigma-1))).
```

The new public declarations are:

- `add_est_ix_bound`: `IsZeroDensityEnergyBound sigma (B(sigma)/(1-sigma))`.
- `add_est_ix`: the literal printed extended-real inequality
  `A*(sigma)(1-sigma) <= B(sigma)`.
- `add_est_ix_zero_energy`: for every positive epsilon, one constant and
  one positive sigma-shift bound the actual multiplicity-aware zero energy
  by `C T^(B(sigma)+epsilon)` for every sufficiently large T.
- `energyClauseNine_blueprint`: the exact divided blueprint normalization.

These theorems have only the stated sigma interval hypotheses. They do not
accept an energy estimate, cardinality theorem, source dichotomy, moment,
or optimization result as an analytic theorem premise.

The full general range `8sigma-4 <= tau <= 2(8sigma-4)` is derived by
`InCardinalityEnergyRegion.energyClauseNine_general`. Below sigma=4/5,
the exact power cover chooses q=2 or 3. Independent cardinality witnesses
at q and q+1 give rho/q<=3-3sigma. At t=tau/q<=6/5, Jutila k=5 and the
energy witness at q-1 feed all nine Heath--Brown branches. For
6/5<=t<=3/2, the actual corrected cardinality witness consumes the proved
Bourgain first-affine, mixed-affine or ninth row, while the independent
q-energy witness supplies the two energy branches. Above 3/2, all six
q-energy branches use the cardinality cap. For sigma>=4/5, the already
proved clause-(i) general rate is compared exactly with B.

The middle-height cover is exact, not sampled. Its sigma split is 17/22;
its switching lines are (81-96sigma)/5, (13-8sigma)/5, 16sigma-11,
(4+4sigma)/5, 48-60sigma, (27sigma-18)/2 and (16sigma-8)/3.
All overlaps and boundary cases are included. The proof needs no additional
high-height Bourgain row or unrestricted Bourgain theorem.

`energyClauseNine_zeta_bound` derives the complete interval
`1 <= tau <= 8sigma-4`: actual emptiness below 3/2, the proved twelfth
moment with cubic energy on [3/2,2], and the actual clause-(i) zeta
Heath--Brown consumer above 2. `energyClauseNine` then invokes the proved
endpoint-one bounded-range transfer with the source cutoff tau0=8sigma-4.
No endpoint-two source corollary is assumed.

### Coverage, source fidelity and remaining goal

Nine new modules are installed: `EnergyClauseNineRates`,
`EnergyClauseNineShortCertificates`, `EnergyClauseNineMiddleCertificates`,
`EnergyClauseNineTallCertificates`, `EnergyClauseNineBranches`,
`EnergyClauseNineRegion`, `EnergyClauseNineGeneral`,
`EnergyClauseNineZeta` and `EnergyClauseNine`.
There are 42 new closed-range branch certificates, 71 explicitly audited
public theorems including the three new `NewAdditiveEnergy` exports, and
85 new semantic regressions (71 exact signatures and 14 endpoint/object
checks). Every module is root-imported and listed in the exact BAT inventory.

The literal rate and domain were checked against frozen TeX label
`Add-est`, clause (ix), and the paper-time ANTEDB
`prove_zero_density_energy_7()` recipe with tau0=8sigma-4. Numerical
exploration was used only for discovery. Lean checks every certificate
and every actual-region consumer. The repaired proof is not a claim to
replay the archived Python's false five-coordinate powering transformation.

EPZAE-36 and EPZAE-37 now meet their mathematical acceptance tests: all
nine clause projections feed actual general/zeta consumers, and every
printed interval has an audited source-facing theorem and actual-zero
epsilon--delta consequence. EPZAE-06 remains open for deterministic
projection-recipe reproduction, rather than missing energy mathematics.
EPZAE-19's unrestricted Bourgain source range and uniform LV assembly,
EPZAE-33's separate source endpoint-two corollary, the other exponent-pair,
density, public-assembly and release obligations, and the full EPZAE-00--41
goal remain open.

Both `run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`
remain required acceptance interfaces. Maintain their exact inventory and
explicit audits whenever modules change; no exclusion, dependency-pin
change, relaxed warning rule or fifth-coordinate shortcut is permitted.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-194712-b1ebacdc.log`.
  All 538 package files are covered, 549 Lean files scanned and 9393
  build jobs pass. The exhaustive audit passes all 4809 discovered target
  theorems plus five imported boundary declarations: 4814 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_194607.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and the declaration-linter gate.

Every one of the 71 new explicit public audits was found in the final
target log and has only permitted standard logical dependencies
(`propext`, `Classical.choice`, `Quot.sound`, or subsets). All 85 new
semantic regressions pass. The complete final logs contain zero Lean
warnings, errors or tactic suggestions. The repository shortcut scans
have no prohibited proof-term match; broad declaration matches are
existing prose and the two genuine rational structure fields.

All 195 checkpoint source/integration/runner hashes match the snapshot
taken before the final target BAT run. The counterexample, both BAT
launchers, frozen sources and dependency pins are unchanged. Relative to
the preceding checkpoint, exactly five existing integration/status files
and the nine new Lean modules carry the implementation. All 186 dirty
worktree entries remain within node 63; unrelated work was not changed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 187 distinct nodes and 481 resolved edges.
The semantic green-node checks are:

- EC9C: the 42 explicit short/middle/tall branch inequalities, together
  with the rate/sign lemmas, are exact on their complete stated ranges.
  `energyClauseNine_short_branch`, the middle consumers and
  `energyClauseNine_tall_branch` apply them to the actual branch outputs.
- EC9G: `InCardinalityEnergyRegion.energyClauseNine_general` consumes
  genuine region membership, derives the power cover and cardinality caps,
  unpacks the corrected cardinality witness, and invokes the independent
  Heath--Brown energy witness. `energyClauseNine_general_bound` supplies
  the uniform epsilon-loss estimate by the proved region realization.
- EC9Z: `energyClauseNine_zeta_bound` consumes actual short-pattern
  emptiness, the proved twelfth moment and the actual zeta-region
  Heath--Brown consumer. No zeta-energy estimate is assumed.
- EC9/NAE: `energyClauseNine` consumes both full uniform ranges at
  tau0=8sigma-4. The three `add_est_ix` exports preserve the literal
  paper maximum, its full closed sigma interval, the real shifted zero
  multiset and analytic multiplicities. Alongside the already audited
  (i)--(viii) exports, this completes the nine-clause Add-est acceptance
  test, not the other public theorem families or the whole goal.

The mathematical completion of EPZAE-36/37 and the integrity-gate PASS
are separate conclusions; neither is inferred merely from audit counts.

## Closed beta duality from actual model-phase sums — historical checkpoint

### Exact mathematical result

`exponentPair_iff_beta_bound` proves frozen TeX label `beta-duality`
with its full closed range: for every candidate in the source triangle,
the actual analytic `ExponentPair k l` predicate is equivalent to
`beta(alpha) <= k + (l-k)*alpha` for every `0 <= alpha <= 1`.
This is not polygon membership or an assumed exponent-pair estimate.

The converse, `isExponentPairEstimateNonAsymptotic_of_beta_bound`,
takes a finite subcover of the compact alpha interval. Minimum phase
tolerance, maximum derivative order and maximum threshold supply one
uniform set of constants for every physical pair `1 <= N <= T`.
The proof links alpha to `log_T N` and proves the exact real-power
identity with the original epsilon losses.

For the forward endpoint, the actual approximate-model condition gives
`c_sigma <= -F'' <= sigma+1` on the interior, with
`c_sigma = sigma*2^(-sigma-1)/2 > 0`.
`betaModelSample_secondDifference_bounds` transports this curvature
to the physical samples `-2*pi*T*F((A+n)/N)`.
`norm_exponentialSumAt_le_secondDerivative` consumes that result,
the native Guth--Maynard finite second-difference estimate, the proved
complex-conjugation/radians bridge, and all three boundary terms. It yields

```text
||sum_{a <= n <= b} e(T F(n/N))||
  <= K_sigma (sqrt(T) + N/sqrt(T))
```

for `T,N >= 1`, `T <= N^2`, the original dyadic endpoints, and
the stated approximate-model tolerance. The estimate is not a premise.
The non-asymptotic ANTEDB interface then gives
`exponentSumGrowthExponent_one_le_half`.
Together with the existing forward theorem on alpha<1, this proves
`exponentSumGrowthExponent_le_exponentPairLine_closed`.
`exponentSumGrowthExponent_zero` also proves beta(0)=0.

### Semantic status and remaining obligations

EPZAE-09's convex closure and exact closed-interval two-way duality are
proved. EPZAE-09 remains OPEN: the source reflection identity
`beta(1-alpha)=1/2-alpha+beta(alpha)` and the lower endpoint bound
`1/2 <= beta(1)` are not claimed here. The finite second-derivative
estimate is not the source dual-phase B transformation, and does not
complete EPZAE-10's B-process, the A/C/D processes, the derivative inputs,
the beta table, or any of the four new exponent-pair outputs.

Seven modules are installed: `BetaUniformity`, `BetaSecondDerivative`,
`BetaDiscreteCurvature`, `BetaBProcessMajorant`, `BetaFiniteSum`,
`BetaModelSumBound` and `BetaClosedDuality`.
Their 21 public theorems have explicit dependency audits and exact-type
regressions; six additional checks cover the closed endpoints, the uniform
physical estimate and an actual closed-interval model sum at T=N.
All seven modules are root-imported and listed in the exact principal BAT
inventory.

The permanent singleton counterexample to printed Lemma 62 is unchanged.
The corrected independent rho/k and rho*/k witnesses, Heath--Brown
consumers, and all nine proved Add-est clauses remain intact.
No fifth-coordinate scaling or third witness has been restored.
EPZAE-36/37 remain DONE; the whole EPZAE-00--41 objective and its other
open acceptance tests remain unchanged.

`run_tao_trudgian_yang_build.bat` remains the target's principal
acceptance interface, alongside foundation `run_lake_build.bat`.
Maintain their exact module inventory, explicit audits, warning gate and
source-integrity checks as work continues. This checkpoint is concrete
progress toward the original whole-proof goal, not a replacement goal.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-202605-c2073498.log`.
  All 545 package files are covered, 556 Lean files scanned and 9400
  build jobs pass. The exhaustive audit passes 4840 discovered target
  theorems plus five imported boundary declarations: 4845 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_202606.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

All 21 new explicit public audits were found in the final target log;
each has only `propext`, `Classical.choice` and `Quot.sound`.
All 27 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 204 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. The 195-file preceding snapshot has
only the four expected integration/runner changes; coverage also adds
seven new Lean modules and the two existing module headers corrected
to describe the now-proved equivalences. The permanent counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, frozen archives and dependency pins are unchanged.
All 195 dirty worktree entries remain within node 63. No unrelated
user changes were reverted, staged, committed or pushed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 193 distinct nodes and 496 resolved edges.
Its new green-node checks are:

- DUC: `ExponentPair.convexCombination` is the previously proved
  analytic convex-closure theorem, not just triangle closure.
- DUU: `isExponentPairEstimateNonAsymptotic_of_beta_bound` consumes
  actual ANTEDB beta bounds at every alpha and derives uniform physical
  constants through a finite subcover; N and T are linked by log_T N.
- DUS: `norm_exponentialSumAt_le_secondDerivative` consumes the
  actual approximate-model phase, derived curvature, physical discrete
  differences, conjugation identity and three boundary terms.
- DUE: `exponentSumGrowthExponent_zero` proves beta(0)=0, and
  `exponentSumGrowthExponent_one_le_half` consumes the complete
  finite estimate through the genuine non-asymptotic beta definition.
- DUF: `exponentPair_iff_beta_bound` assembles both directions for
  the exact source triangle and every alpha in the closed unit interval.
  It does not assume an exponent-pair estimate in the converse or a
  beta reflection theorem in the endpoint proof.

DUR and aggregate EPZAE-09 remain open for the exact reflection identity
and beta(1)>=1/2. The named source `beta-duality` lemma is proved,
but this does not complete its broader Checklist item, the remaining
public-output families or the whole goal. Mathematical/source
completeness and dependency-integrity PASS are separate conclusions.

## Exact beta endpoints and classical second-derivative pair — historical checkpoint

### Exact mathematical results

`exponentSumGrowthExponent_endpoints` now proves the complete frozen
`beta-end` statement: beta(0)=0 and beta(1)=1/2.
`half_le_exponentSumGrowthExponent_one` supplies the missing lower bound
from the actual logarithmic model phase, without a mean-square estimate
as an assumption.

For every natural m, set N=T=16(m+1)^2 and use the closed integer interval
[N,N+m]. For each 0<=j<=m, the proved elementary logarithm inequalities give

```text
|N log((N+j)/N)-j| <= j^2/N <= 1/16.
```

Cosine periodicity removes the integer j in the real part of the original
oscillatory factor. The remaining angle has absolute value at most one,
so each term has real part at least 1/2.
`norm_logPhase_resonant_sum_lower` therefore proves, for this actual sum,

```text
||sum_{N <= n <= N+m} e(N log(n/N))|| >= sqrt(N)/8.
```

The scale is unbounded, both dyadic endpoints are derived, and N=T gives
the exact power-asymptotic exponent one. The audited ANTEDB logarithmic
lower-bound consumer yields beta(1)>=1/2. Together with the prior
second-derivative upper bound, this proves equality. This is an alternate
proof of the exact endpoint claim; it does not claim to formalize the
paper's separate L2 proof of beta(alpha)>=alpha/2 for every alpha.

`isExponentPairEstimateNonAsymptotic_half_half` also proves the genuine
uniform estimate for the classical pair (1/2,1/2).
For T<=N^2 it consumes the actual model-phase second-derivative estimate;
N<=T bounds N/sqrt(T) by sqrt(T). For T>N^2, the original finite sum is
bounded by 3sqrt(T) using its cardinality. The phase tolerance, derivative
order and constant depend only on the source parameters, and every
epsilon loss is retained.
`exponentPair_half_half` converts this to the original asymptotic
predicate. Closed duality then proves
`exponentSumGrowthExponent_le_half` and the combined bound
`exponentSumGrowthExponent_le_min_self_half` on 0<=alpha<=1.

### Coverage and remaining whole-proof obligations

Four new modules are installed: `BetaLogCoherence`, `BetaResonantSum`,
`BetaEndpoints` and `ClassicalSecondDerivativePair`.
Their 18 public theorems have explicit audits and exact-signature
regressions, plus six additional actual-sum, analytic-predicate and
endpoint checks. The root imports and the exact PowerShell inventory
behind `run_tao_trudgian_yang_build.bat` cover every module.

EPZAE-09 now has proved convex closure, full closed-interval two-way
duality, and both exact beta endpoints. Its sole remaining acceptance
obligation is the reflection identity on the whole unit interval.
The two endpoint reflection regressions do not establish the interior
identity. The classical seed is not the full B transformation; all
unproved A/B/C/D process, derivative, beta-table, advertised new-pair,
density, public-assembly and release obligations retain their status.
The whole EPZAE-00--41 goal remains active and unchanged.

The original Lemma 62 counterexample is preserved byte-for-byte.
Corrected independent rho/k and rho*/k powering, the Heath--Brown
consumers, and all nine Add-est clauses are unchanged; EPZAE-36/37
remain DONE. No scaled fifth coordinate or third witness is assumed.

Keep both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` as mandatory acceptance gates. Continue updating
the exact module inventory, root imports, explicit audits and semantic
regressions whenever the proof graph changes; never bypass their
warning or proof-integrity checks.

### Current-checkout verification and semantic audit

Both required commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-204634-0b462a03.log`.
  All 549 package files are covered, 560 Lean files scanned and 9404
  build jobs pass. The exhaustive audit passes 4870 discovered target
  theorems plus five imported boundary declarations: 4875 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_204635.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

Each of the 18 new explicit public audits was found in the final target
log with only `propext`, `Classical.choice` and `Quot.sound`.
All 24 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 208 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. Relative to the preceding 204-file
checkpoint, only the four integration/runner files changed, and the four
new production modules extend the hash coverage. The counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, dependency pins, frozen sources and all existing
energy-proof modules are unchanged. All 199 dirty worktree entries
remain within node 63; no unrelated changes were reverted, staged,
committed or pushed. `git diff --check` passes; Git's CRLF-conversion
notices are not Lean diagnostics.

The architecture has 195 distinct nodes and 503 resolved edges.
Its changed green-node checks are:

- DUL: `norm_logPhase_resonant_sum_lower` derives the lower bound
  for the literal ANTEDB sum at the actual natural scale and endpoints.
  The logarithmic remainder, integer periodicity, real-part estimate,
  term count and square-root normalization are proved.
- DUE: `half_le_exponentSumGrowthExponent_one` supplies an unbounded
  logarithmic model family, proves its dyadic endpoints and N=T relation,
  and invokes the genuine beta lower-bound consumer.
  `exponentSumGrowthExponent_endpoints` combines it with the already
  proved zero endpoint and endpoint-one upper bound.
- CSP: `isExponentPairEstimateNonAsymptotic_half_half` derives one
  uniform model-phase estimate on the whole 1<=N<=T domain by the two
  complementary scale cases. `exponentPair_half_half` returns the
  actual analytic predicate, and the beta corollaries consume closed
  duality. No exponential-sum estimate is assumed as a terminal premise.

The existing closed-duality proof needs only the upper endpoint bound;
it does not rely on the new logarithmic lower-bound construction.
DUR and aggregate EPZAE-09 remain open solely for the full reflection
identity. The classical seed does not close EPZAE-10's general processes.
The other open Checklist items and the original whole-proof goal remain
open. These semantic conclusions are independent of the audit count.

## Actual inverse and Legendre phases — historical checkpoint

EPZAE-09/10 now has an actual inverse-slope and Legendre-phase entry.
The four modules consume the original approximate-model phase and derive
strict monotonicity, smooth inversion on the open slope image, reciprocal
curvature, a first-order reciprocal-exponent model error bound, and physical
stationary points with their original N,T,r variables linked.

For cσ=σ*2^(-σ-1)/2, g=(F')^{-1} on J=F'((1,2)), and
G(v)=v*g(v)-F(g(v)), the checked conclusions include
G'=g, G''=1/F''(g(v)), 1/(σ+1)<=-G''<=1/cσ, and
|G'(v)-v^(-1/σ)|<=δ/cσ on J intersect (2^(-σ),1).
The trimmed reference interval is proved to lie in J with explicit
δ margins. The original phase T*F(x/N)-r*x has its unique interior
stationary point at x=N*g(r*N/T), the value -T*G(r*N/T), and the
proved scaled curvature bounds. Its Fourier sign is linked by conjugation.

The next mathematical obligations are DHC (uniform higher-order model
errors and canonical-domain normalization) and DBT (the actual transformed
sum, amplitude handling, endpoint conventions and uniform error).
Both are owned by EPZAE-09/10 and remain OPEN. DUR and EPZAE-09 remain
OPEN for full beta reflection; the general B process is not yet proved.

The exact theorem consumers and green-node audit are recorded in the
latest section of `Tao-Trudgian-Yang Goal Prompt.md`.
The permanent counterexample, corrected independent rho/k and rho*/k
witnesses, Heath--Brown consumers and all nine Add-est clauses are unchanged.
The full EPZAE-00--41 goal and all other open outputs remain unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions. Target log:
`logs/tao-trudgian-yang-build-20260921-211419-4caca476.log`;
foundation log: `Riemann Zeta/logs/foundation_freeze_20260921_211419.log`.
The target covers 553 package files and audits 4929 declarations.
All 37 new public audits and 42 new regression examples pass.
Both BATs and the counterexample are unchanged. Exact hashes and
foundation stage evidence are in the latest Reproduction Manifest section.

## Uniform all-order Legendre model control — historical checkpoint

The all-order compact phase-control component of EPZAE-09/10 is now proved.
The eight new modules derive the actual inverse/Legendre derivative
recurrence for every natural order, construct the exact logarithmic/power
reference phase, bound its derivatives by Pochhammer coefficients, and
propagate the original phase errors through the inverse coordinates.

The main consumer is `modelPhaseLegendreDual_compact_anchored_uniformity`.
For fixed sigma>0, 2^(-sigma)<a<=b<1, Q and epsilon>0, it gives one
positive input tolerance. Every qualifying original phase then has
[a,b] inside its actual slope image, all dual model errors through Q
are at most epsilon, and the anchored phase-value discrepancy is at most
epsilon*|v-w| for every v,w in [a,b]. The input derivative order depends
only on Q. The proof does not assume common slope-image membership,
higher-order inverse estimates or bounds on additive constants.

DHE, DHR, DHU and DHA are green for these exact conclusions. DHC remains
OPEN for smooth extension and normalization to [1,2]; DBT and full beta
reflection remain OPEN. The next phase-side step is to construct a
smooth compactly supported correction from the anchored error, prove
its all-order bounds, and rescale the retained phase to the canonical
interval using multiplicative rescaling; a general affine translation changes
the monomial model. Retained windows of ratio below two can be normalized
individually, with a finite cover still required for broader windows.
The current compact interval is not a replacement definition
for the source model, nor is sigma restricted to exceed one.

See the latest Goal Prompt section for exact formulas and green-node
semantic checks. The counterexample, corrected powering, Heath--Brown
consumers and all nine Add-est clauses are unchanged. The full
EPZAE-00--41 objective and other open outputs remain unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-215130-00a61f53.log)
and [final foundation log](../../logs/foundation_freeze_20260921_215409.log).
The target covers 561 package files and audits 5026 declarations.
All 44 new public audits and 52 new regression examples pass.
All 220 checkpoint source/integration/runner hashes are stable across
both final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Canonical Legendre extension and finite model families — historical checkpoint

Canonical extension is now proved on the source's full closed [1,2]
interval. Exact retained Legendre values, all-order errors, finite
coverage of arbitrary compact reference-slope intervals, and the actual
ANTEDB model-family predicate are assembled. The scales and cutoffs are
fixed before F, Q and epsilon; one delta controls all charts.
See the latest Goal Prompt for the exact formulas and quantifier order.

DCF, DHC, DCC and DMF are green for their named analytic consumers.
EPZAE-09/10 and full reflection remain open: DBT still needs the actual
Poisson/stationary sum transformation, its dual N,T normalization,
amplitude handling, endpoint/boundary-band estimates and uniform errors.
The next step is a source-facing transformed-sum theorem consuming the
actual physical stationary-point and canonical-model outputs. Existing
specialized logarithmic reflection and Atkinson stationary estimates
are references for reusable components, not proofs for arbitrary model F.

The counterexample, independent two-witness repair and all nine Add-est
clauses are preserved. The full EPZAE-00--41 goal remains unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-222922-4233a5f3.log)
and [final foundation log](../../logs/foundation_freeze_20260921_222922.log).
The target covers 569 package files and audits 5058 declarations.
All 27 new public audits and 35 new regression examples pass.
All 228 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Exact Poisson source entry and physical dual sums — historical checkpoint

The original finite source sum now enters an absolutely convergent
Poisson series with at most two endpoint terms. A constructed cutoff
agrees exactly with strict-interior lattice points; nonempty strict
interior intervals give equality. Physical dual scales, exact
stationary exponents, character conjugation and the literal canonical
dual sum are connected. DXS, DXW, DXF, DXE and DXT are green for these
specific consumers, documented in the latest Goal Prompt.

Continue DBT with uniform general-model stationary integral estimates,
curvature-amplitude and partial-summation control, lattice-margin cutoff
budgets, nonstationary tails and moving dual-boundary bands. The proved
source endpoint loss does not discharge these analytic errors.
Full beta reflection, general B-process and EPZAE-09/10 remain open.
The counterexample and complete repaired Add-est chain are unchanged;
the full EPZAE-00--41 objective remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-231301-8d992207.log)
and [final foundation log](../../logs/foundation_freeze_20260921_231301.log).
The target covers 575 package files and audits 5124 declarations.
All 32 new public audits and 40 new regression examples pass.
All 234 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Stationary amplitudes, source beta consumers and quadratic coordinates — historical checkpoint

DCA, DMA, DVA, DSB, DQD and DQJ are now green for their narrowly
specified actual-object consumers. The original F yields the curvature
amplitude, positive third derivative, sampled finite variation and a
main-block bound from canonical unweighted beta estimates. Taylor's
theorem gives the signed quadratic coordinate and its derivative at
the stationary point. No desired weighted bound, model condition or
Taylor-ratio limit is supplied as a hypothesis.

Continue DQI with smooth regularity across the critical point, an
actual local inverse and uniform higher derivative estimates. Feed
these into DBT's transformed Poisson weights and stationary integral
errors. The curvature amplitude alone does not account for the
original lattice-dependent smoothing weight. Cutoff margin budgets,
nonstationary tails and moving dual-boundary bands also remain.
A fixed chart's source-beta consumer is not yet the full physical
alpha-to-1-alpha transport or uniform beta reflection.

The whole EPZAE-00--41 goal remains active; no aggregate acceptance
condition or public output changed. The counterexample and complete
corrected two-witness -> Heath--Brown -> optimization -> Add-est chain
are preserved.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-000055-22681e8e.log)
and [final foundation log](../../logs/foundation_freeze_20260922_000107.log).
The target covers 583 package files and audits 5203 declarations.
All 46 new public audits and 54 new regression examples pass.
All 242 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Smooth quadratic inverse and original-mode remainder — historical checkpoint

The actual quadratic coordinate now has a smooth inverse on its actual
open image, including the critical point. Both first derivatives have
explicit bounds depending only on sigma. Differentiated Taylor averages
and the exact FTC identity establish the coordinate's smoothness.
An actual positive-Jacobian substitution transports complex integrals
and integrability. The original source cutoff is retained in the
transformed amplitude and exact physical Fourier modes.

The source consumer constructs the same original cutoff before T,
preserves exact lattice values and endpoint loss <=2, and gives
stationary-mode quadratic integrability and a uniform amplitude-size
bound. The physical remainder identity keeps chi(g(v)) and e(-1/8);
the error norm is exactly N*norm(R). No uniform remainder upper bound
or new Fresnel evaluation is claimed.

DTA, DQS, DMI, DJB, DQV, DMW, DQP and DQR are green for the narrow
consumers listed in the latest Goal Prompt. Continue DQI with uniform
higher inverse/weight derivative estimates and smooth zero-extension
off the moving image. Then discharge DBT's uniform stationary remainder,
lattice-margin budgets, nonstationary tails and moving boundary bands.
Physical power-window/epsilon transport and full reflection remain open.
Pointwise all-order smoothness and uniform first-derivative bounds do
not discharge those higher-order uniform estimates.

EPZAE-09/10 and the whole EPZAE-00--41 objective remain active under
unchanged acceptance tests. The preserved counterexample, independent
rho/k and rho*/k witnesses, Heath--Brown consumers, exact optimization
and all nine Add-est clauses are unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-010958-9aae1d59.log)
and [final foundation log](../../logs/foundation_freeze_20260922_010947.log).
The target covers 594 package files and audits 5272 declarations.
All 54 new public audits and 63 new regression examples pass.
All 253 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Uniform smooth weights and stationary remainder bounds — historical checkpoint

DQI's named analytic branch is now proved for each fixed original
cutoff: actual smooth zero-extension, compact support and whole-line
integrability; uniform all-order coordinate and inverse derivatives;
and global weight derivatives with explicit original-cutoff jet budgets.

The next analytic step has also been proved. Exact Taylor decomposition
and odd cancellation reduce the weighted quadratic error to a genuine
integration-by-parts estimate. The checked generic Fresnel value and
tail complete an explicit O(1/T) remainder bound. Applied to the actual
Morse weight, it gives an O(N/T) physical stationary-mode error, retaining
chi(g(r*N/T)) and e(-1/8). The source consumer constructs the same lattice
cutoff before sigma/F/T, preserves Poisson summability and endpoint
loss <=2, and proves the error for every stationary integer frequency.

The constants are uniform in F,v,T,N when chi is fixed. When chi is
chosen from N,a,b, its derivative budgets may vary with those parameters.
Continue DBT with quantitative lattice-margin/transition control,
nonstationary modes/tails, weighted-main-block assembly and moving
dual boundaries. Then complete physical power-window/epsilon transport,
full beta reflection and the general B process. EPZAE-09/10 remain open.

DZW, DJC, DJI, DJW, DQI, DRE and DSE are green only for the exact
consumers recorded in the latest Goal Prompt. No aggregate acceptance
test is weakened. The counterexample, independent two-witness repair,
Heath--Brown energy relation, optimization and all nine Add-est clauses
remain unchanged; the full EPZAE-00--41 goal remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-021704-cf554732.log)
and [final foundation log](../../logs/foundation_freeze_20260922_021704.log).
The target covers 610 package files and audits 5402 declarations.
All 75 new public audits and 85 new regression examples pass.
All 269 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Controlled cutoff families and weighted Fourier bounds — historical checkpoint

The original cutoff family is now explicit and controlled before all
lattice parameters. Sharp order-n transformed-weight jets cost eta^(-n),
not a large undifferentiated polynomial power. The source loss is
4*N*eta+2 and the current stationary mode error is C*N/(T*eta^3).
Width-independent cutoff variation supplies the actual weighted main
block and the original-model nonstationary 4/(pi*d) estimate.

The next DBT work must address the quantitative SUM, not just another
per-mode existence statement:

1. Prove a uniform far-tail estimate for the actual buffered Fourier
   modes. The present 1/d bound is not summable. Higher integration by
   parts with the proved original cutoff jets is a possible route;
   all dependence on T,N,eta and the tail threshold must be explicit.
2. Prove the complete mode partition, including near-endpoint frequencies
   and moving dual-boundary bands. Retain the physical T/N relation.
3. Balance the actual source boundary discrepancy and summed stationary
   remainders as eta varies with the physical scales. The displayed
   first remainder and trivial source error need not suffice by themselves.
   Higher-order quadratic expansions with localized cutoff derivatives,
   or cancellation in the source boundary bands, are research routes,
   not installed estimates.
4. Assemble the weighted main block with the quantitative error budget,
   then prove physical alpha-to-1-alpha power-window/epsilon transport,
   full beta reflection and the general B process.

Do not infer a quantitative tail from absolute Poisson summability,
or uniform summed control merely from constants chosen before the lattice.
Do not remove the original cutoff value at the critical point.
The separate canonical slope-chart cutoff normalizes the dual phase;
it is not an assertion that the original source cutoff equals one.

The six new green nodes are limited to the exact consumers in the latest
Goal Prompt. DBT, DUR and aggregate EPZAE-09/10 remain open under unchanged
acceptance tests. The full goal, preserved counterexample and completed
corrected Add-est chain remain in force.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-085137-4fb8b007.log)
and [final foundation log](../../logs/foundation_freeze_20260922_085138.log).
The target covers 625 package files and audits 5516 declarations.
All 50 new explicit public audits and 66 new regression examples pass.
All 284 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Quantitative Fourier tails and the actual core expansion — historical checkpoint

The outside-core analytic branch is now quantitatively assembled.
The same original source has a controlled infinite tail, logarithmic
exterior integer blocks, and an exact physical-envelope core reduction.
The actual stationary subset has cardinality <=3*T/N+3 and a proved
summed error D*eta^(-3)*(1+N/T), independently of the tail radius.
The source expansion retains the remaining core modes literally.

The next proof work must address the inside of that core:

1. Bound the actual inner-core nonstationary modes and moving endpoint
   bands. The exterior harmonic theorem applies beyond floor/ceiling
   envelope endpoints; it does not estimate the complementary modes
   retained inside the core.
2. Group the actual stationary set into suitable canonical dual charts
   and consume the previously proved cutoff-weighted beta main theorem,
   preserving all physical scale and endpoint relations.
3. Obtain a sufficiently strong combined stationary/source error budget.
   The current trivial source loss 4*N*eta+2 and summed stationary loss
   D*eta^(-3)*(1+N/T) do not themselves close the required exponent bounds.
   Localized derivative control, higher-order stationary expansions and
   source-boundary cancellation are possible research routes, not results
   asserted by this checkpoint.
4. Complete physical alpha-to-1-alpha power-window/epsilon transport,
   full beta reflection and the general B process.

The exact radius can be large without enlarging the stationary count;
its exterior cost is logarithmic. Prove the needed scale comparisons
rather than claiming that a ceiling expression is automatically absorbed.
The tail tolerance in the new consumers is a numerical error budget,
distinct from the source beta predicate's exponent-loss epsilon.

All remaining original outputs and release requirements stay in scope.
No aggregate acceptance test changed. The counterexample and complete
corrected Add-est chain remain preserved.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-094603-f91c6946.log)
and [final foundation log](../../logs/foundation_freeze_20260922_094604.log).
The target covers 635 package files and audits 5587 declarations.
All 29 new explicit public audits and 41 new regression examples pass.
All 294 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Width-independent curvature and the bounded inner core — historical checkpoint

The original Fourier modes now satisfy C_sigma*N/sqrt(T), uniformly in
every real frequency and original cutoff width. Genuine derivatives
within [1,2] at the endpoints give the exact slope image. If
L=floor((T/N)*s_F(2)) and U=ceil((T/N)*s_F(1)), the actual stationary
core is precisely the open integer interval (L,U). Its complement is
[A,L] disjoint-union [U,B], not an assumed or approximated selection.

The two nearest modes use curvature; all others use derived actual
endpoint gaps and harmonic sums. The full complement is bounded by

```text
2*C_sigma*N/sqrt(T)+(8/pi)*(1+log(3*T/N+3)).
```

The new source consumer contains only the original cutoff-weighted
stationary main terms over (L,U). Its paid errors include original
smoothing, far-tail/exterior reduction, the stationary remainder, and
the displayed complete nonstationary-core bound.

The previous literal unestimated inner-core nonstationary residual is
now discharged by an original-object consumer. Its endpoint frequencies
are handled with a newly proved real oscillatory-integral second-derivative
bound, not by assuming a positive distance from the stationary range.
The source's stationary main sum is now a literal open integer interval,
which is the input to the still-unfinished canonical-chart assembly.

DBT/full beta reflection remain OPEN. The original source loss
4*N*eta+2 and stationary loss D*eta^(-3)*(1+N/T) still need a sharp
physical-scale balance. Actual stationary-frequency assembly through
the canonical dual charts, moving/reference endpoint conventions,
and alpha-to-1-alpha epsilon/power-window transport remain required.
No aggregate EPZAE checkbox or source theorem is marked complete here.

The new uniform curvature estimate can control near-stationary transition
bands while strengthening the stationary error. It does not itself bound
the sharp summed STATIONARY transition remainder. The fixed interior
canonical cover must not be treated as a proved cover of every moving
endpoint frequency.

The permanent printed-Lemma-62 counterexample, independent rho/k and
rho*/k witnesses with unrelated fifth coordinates, Heath--Brown energy
relation, exact optimization and all nine Add-est clauses are unchanged.
No false s'/s scaling or third witness is restored. The full
EPZAE-00--41 objective remains active and unfinished.

### Verified build evidence

On 22 September 2026, after the final Lean and integration edits:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  [complete target log](logs/tao-trudgian-yang-build-20260922-103135-cc078125.log). Coverage is 655 scanned Lean files,
  644 production package files and 9499 build jobs. The audit checks
  5649 discovered target theorems plus five imported declarations, 5654 total.
- `cmd /c run_lake_build.bat --no-pause` from the foundation root:
  PASS, exit 0; [complete foundation log](../../logs/foundation_freeze_20260922_103132.log) and
  [machine-readable manifest](../../logs/foundation_freeze_20260922_103132.json). All six stages pass;
  301 root modules plus two regressions, 8857 jobs, 7636 explicit
  declarations and 14290 discovered theorems retain their verified status.

Both complete physical logs contain zero Lean warnings, errors or tactic
suggestions. All 32 new explicit audits occur once, with permitted logical
axioms only. The final 9499-job focused regression build is warning-free;
all 42 new examples pass. The target also verifies all 20 pinned source
files, 12 frozen ANTEDB files and deterministic certificate regeneration.
No coverage, integrity, dependency, warning or output gate was weakened.
Runner PASS verifies the installed scope, not full beta reflection or
the unfinished whole-proof goal.

## Sharp stationary source expansion and interior logarithmic sums — previous checkpoint

The ORIGINAL source now has a sharp interior C_sigma*N/(T*d) error,
a logarithmic sum over the actual plateau integers, a proved transition
count, and support-exterior harmonic bounds. The assembled source theorem
chooses eta=T^(-1/2), giving nonlogarithmic error
(4+6*E)*N/sqrt(T)+3+2*E*(sigma+1), with every remaining logarithm and
the polynomial far-tail radius explicit. The actual short-interval source
branch is also proved. No eta^(-3) stationary loss is needed in this route.

Public consumers:
`modelPhaseBufferedFourierMode_interior_uniform`,
`modelPhaseBufferedInteriorBlock_error`,
`modelPhaseBufferedTransition_error`,
`modelPhaseBufferedSharpCore_error`,
`modelPhase_buffered_source_inverse_sqrt_expansion`, and
`norm_exponentialSumAt_le_buffered_short`.

Uniform logarithmic budgets, the actual moving canonical dual-chart
assembly, alpha-to-1-alpha power-window transport, full beta reflection,
and the general B process remain OPEN under EPZAE-09/10. No aggregate
checkbox changes. The full EPZAE-00--41 objective remains unfinished.
See the latest Goal Prompt for exact hypotheses, constants, formulas
and the six green-node semantic checks.

All 12 new modules enter the default imports and exact runner inventory;
44 public axioms audits and 49 regressions accompany them.
The counterexample and corrected powering/Heath--Brown/optimization/
nine-clause Add-est chain are preserved. Both build BATs remain mandatory.

### Verification

Both mandatory BAT runners passed on 22 September 2026 with exit code 0,
zero Lean warnings/errors/tactic suggestions, and passing integrity and
dependency gates. The target covers 656 production-package files,
scans 667 Lean files, and audits 5778 imported/target declarations.
All 44 new explicit audits and 49 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-113320-9230abb9.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_113331.log).
All 315 checkpoint source/integration/runner hashes agree before and
after the BATs. The graph has 258 nodes and 713 resolved, nonduplicate
edges; all 42 aggregate checklist checkboxes are unchanged.
The full goal remains unfinished.

## Uniform source power error and full moving-slope geometry — previous checkpoint

The original source now satisfies the uniform comparison
C_sigma,epsilon*(N/sqrt(T)+T^epsilon), with constants chosen before all
physical data. The actual retained plateau integers are used in the long
branch; the genuine source cardinality pays for the entire short branch.
Every retained frequency has a derived actual critical point and an
explicit positive endpoint margin.

The full actual slope image, under delta<=min(2^(-sigma)/2,1), lies in
[2^(-sigma)/2,2]. Inverse-point stability and every original derivative
comparison at the explicit reciprocal reference point now hold there,
including outside the strict reference interval. This does not assume
smoothness of the original phase outside [1,2].

Public consumers: `modelPhase_source_sharp_comparison`,
`modelPhaseSharpStationarySet_critical_geometry`, and
`modelPhaseInverse_iteratedDeriv_expanded_reference_error`.
See the latest Goal Prompt for exact signatures, bounds and green-node
checks. Higher inverse/Legendre errors on the expanded window, exact
moving canonical charts, physical power-window transport, full beta
reflection and the general B process remain OPEN under EPZAE-09/10.
All 42 aggregate checkboxes are unchanged.

Six new modules, 23 public audits and 27 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/nine-clause Add-est chain are unchanged.
Both build BATs remain mandatory and must track production coverage.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 662 package files, scans 673
Lean files and audits 5817 discovered target theorems plus 5 imported
anchors (5822 declarations). All 23 new explicit audits occur once and
use only permitted standard logical axioms; all 27 regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-120938-14509d95.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_120949.log).
All 321 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 262 nodes and 722 resolved,
nonduplicate edges; all 42 aggregate checkboxes are unchanged.
The counterexample and repaired energy chain remain unchanged.

## Moving canonical Taylor extensions and retained-frequency coverage — previous checkpoint

The actual Legendre error now has a globally smooth moving-endpoint
Taylor extension, exact on its retained plateau, with uniform finite
derivative bounds independent of the shrinking buffer width. Full-image
inverse/reference jet estimates and a five-region proof supply the bounds;
no exterior regularity of the original phase is assumed.

`modelPhase_source_canonicalTaylorPhase` chooses its model tolerance
before the source data, derives h=min(c_sigma,1)/(4*sqrt(T)) and the anchor
F'(3/2), proves the full closed-[1,2] canonical model condition, and proves
exact phase identities for EVERY retained stationary integer.
It does not assert that all integers belong to one multiplicative chart.

The finite positive-slope chart partition, whole stationary main-sum beta
bound, physical power-window transport, beta reflection and general
B process remain OPEN under EPZAE-09/10. All 42 aggregate checkboxes are
unchanged. See the latest Goal Prompt for the exact formulas, finite input
orders, constant dependencies and four green-node semantic checks.

Eighteen modules, 53 public audits and 60 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain are preserved.
Both build BATs remain mandatory and must track production coverage.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 680 package files, scans 691
Lean files and audits 5904 discovered target theorems plus 5 imported
anchors (5909 declarations). All 53 new explicit audits occur once and
use only permitted standard logical axioms; all 60 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-130811-0ad529b7.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_130808.log).
All 339 checkpoint source/integration/runner hashes match before and after
the BATs. Eighteen source texts and four integration texts also match
their normalized snapshots. The graph has 266 nodes and 732 edges, with
no duplicate nodes or unresolved endpoints; all 42 aggregate checkboxes
are unchanged. The counterexample and repaired energy chain remain unchanged.

## Full source chart assembly and the analytic B-process — previous checkpoint

The exact finite positive-slope grid now partitions EVERY original
retained stationary integer into contiguous natural-number chart blocks.
The moving Taylor phases, actual amplitude variation and upstream beta
bounds are assembled, with physical dual windows derived from N,T.
`sourceExponentialSum_reflection_estimate` proves the complete original
sum bound, including C*(N/sqrt(T)+T^epsilon) source error.

The resulting nonasymptotic reflection bound has exponent
max(0,beta+1/2-alpha). Its max is removed only when the reflected exponent
is proved nonnegative. The full beta-reflection identity remains OPEN.

`ExponentPair.bProcess` now proves the paper's analytic transformation
(k,l)->(l-1/2,k+1/2); its target affine line is nonnegative by the triangle
conditions. It does not assume the still-open exact reflection identity.
The next reflection obligation is a genuine beta lower bound sufficient
to remove the zero envelope. A and C processes remain open, so EPZAE-10
is not crossed out. All 42 aggregate checkbox states are unchanged.

Eleven modules, 35 public audits and 41 regressions are integrated.
The printed counterexample, corrected independent powering witnesses,
Heath--Brown energy relation, exact optimization and all nine repaired
Add-est clauses are unchanged. BOTH build BATs remain mandatory and
their imports, inventory and audits must track production changes.
See the current Goal Prompt for quantifiers and all five green-node tests.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 691 package files, scans 702
Lean files and audits 5960 discovered target theorems plus 5 imported
anchors (5965 declarations). All 35 new explicit audits occur once and
use only permitted standard logical axioms; all 41 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-135040-f8df686c.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_135036.log).
All 350 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match
their normalized snapshots. The graph has 270 nodes and 740 edges, with
no duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain remain unchanged. These checks verify this recorded scope;
they do not assert whole-goal completion.

## Exact beta reflection from coherent source sums — previous checkpoint

`exponentSumGrowthExponent_reflection` now proves the exact printed
identity beta(1-alpha)=1/2-alpha+beta(alpha) for every 0<=alpha<=1,
including endpoints. Convex closure, closed two-way duality and the
endpoint values were already proved; all EPZAE-09 mathematical
acceptance clauses are now supplied.

The new lower-bound proof is independent of reflection and the B-process.
It constructs actual phases log(u)+c*(u-1) with integral linear
oscillation at integer N, controls every finite model jet, and sums
a genuine closed coherent block. Beyond every threshold it produces
T^alpha=N and norm(original sum)>=T^(alpha-1/2)/8, proving
beta(alpha)>=alpha-1/2. This removes the zero envelope from the
previous complete original-source estimate; the two reflected
inequalities then give equality. No stronger alpha/2 bound is claimed.

Six modules, 18 public audits and 24 regressions are integrated.
EPZAE-10 remains OPEN: its general B-process is proved, A and C are not.
Continue with those analytic processes and the remaining whole-proof
obligations; this checkpoint does not complete the full goal.

The printed counterexample, corrected independent powering witnesses,
Heath--Brown relation, exact energy optimization and all nine repaired
Add-est clauses remain unchanged. BOTH build BATs remain mandatory,
and production imports, inventory and audits must track source changes.
See the current Goal Prompt for quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 697 package files, scans 708
Lean files and audits 5990 discovered target theorems plus 5 imported
anchors (5995 declarations). All 18 new explicit audits occur once and
use only permitted standard logical axioms; all 24 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-141433-3e901ee8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_141443.log).
All 356 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 274 nodes and 748 edges, with no
duplicate nodes or edges and no unresolved endpoints. There are still
42 aggregate checkboxes: only EPZAE-09 changes to complete; all others
retain their status. The counterexample and completed repaired energy
chain are unchanged. These checks verify this recorded scope, not
whole-goal completion.

## Domain-preserving A-process models and source differencing — previous checkpoint

The A-process now has a domain-preserving shifted-model constructor,
exact original-source correlation identities, and a summed-correlation
Weyl inequality on the literal source exponential sum.

The constructed phase uses affine compression inside [1,2] and has
model parameter sigma+1, with every requested finite derivative and
both endpoints controlled by one tolerance chosen before the source.
Its physical parameters are exactly N'=N-r and T'=sigma*T*r/N;
the reindexed integers and conjugation are proved, including empty
overlaps. The analytic exponent-pair consumer derives its model and
endpoint conditions but explicitly retains C<=T' and N'<=T'.

`source_exponentialSum_weyl` constructs the actual padded source
sequence and keeps 2*H times the SUM of nonzero correlations. It has
no assumed analytic estimate. The small-dual-parameter branch and
integer shift optimization remain OPEN; A is not yet proved.
EPZAE-09 and the B-process remain complete. C remains open.
All 42 aggregate checkbox states are unchanged.

Eleven modules, 32 public audits and 39 regressions are integrated.
The printed counterexample and the corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain remain unchanged. BOTH build BATs
remain mandatory and must track production imports, inventory and audits.
See the current Goal Prompt for exact quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 708 package files, scans 719
Lean files and audits 6069 discovered target theorems plus 5 imported
anchors (6074 declarations). All 32 new explicit audits occur once and
use only permitted standard logical axioms; all 39 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-150004-71e72f6e.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_150014.log).
All 367 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match their
normalized snapshots. The graph has 280 nodes and 760 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain are unchanged. These checks verify this recorded scope,
not the still-open A-process or whole-goal completion.

## General analytic A-process from original source sums — previous checkpoint

The classical A-process is now proved for the paper's actual analytic
exponent-pair predicate:

    ExponentPair k l
      ==> ExponentPair (k/(2*k+2)) (l/(2*k+2)+1/2).

The public consumer is `ExponentPair.aProcess`. Its proof derives the
closed shifted model, source reindexing and conjugation, all positive
dual-height estimates, summed correlations, the original-source Weyl
bound, a genuine natural-number shift and the full epsilon budget.
It does not assume a transformed-phase estimate, a dual-height window,
an optimization certificate, or the output exponent-pair estimate.

The formerly open small-height branch is proved by the full closed-source
`norm_exponentialSumAt_le_firstDerivative`; curvature handles transition
heights, and `ExponentPair.allPositiveHeight_bound` combines every positive
height with the actual input pair. `sourceShiftCorrelation_normalized_bound`
links the result back to N,T,r, including the N^2/(T*r) term.
`sum_sourceShiftCorrelation_le` retains its harmonic sum.
`source_exponentialSum_differencing_bound` consumes the literal source sum.

`integer_shift_optimization` uses an actual floor-comparable natural H;
when that scale is too small, the original sum's cardinality supplies
the separate branch. `aProcessOptimizationScale_balance` and
`aProcessOptimizationScale_cost` link the optimum exactly to N,T.
The logarithmic loss is absorbed by `aProcess_power_budget`.
`source_exponentialSum_aProcess_bound` and
`isExponentPairEstimateNonAsymptotic_aProcess` assemble every source
interval, empty interval and bounded-N case with constants chosen first.

Fifteen production modules, 33 explicit public-theorem audits and 40
regressions are integrated. The extra fixtures include actual A/A/B
compositions yielding (1/6,2/3), (1/14,11/14), and (2/7,4/7), the H=0/H=1
harmonic endpoints, and two optimization-scale checks.

EPZAE-09 and both A/B processes are complete; C remains OPEN, so EPZAE-10
remains unchecked. D, Heath--Brown derivative inputs, certified beta
tables, the four advertised pairs and the remaining density/public
release obligations remain in the whole-proof goal. All 42 aggregate
checkbox states are unchanged.

The printed counterexample, corrected independent rho/k and rho*/k
witnesses, unrestricted fifth coordinates, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
preserved. BOTH build BATs remain mandatory; keep their production
imports, PowerShell inventory, audits and regression coverage synchronized.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 723 package files, scans 734
Lean files and audits 6118 discovered target theorems plus 5 imported
anchors (6123 declarations). All 33 new explicit audits occur once and
use only permitted standard logical axioms; all 40 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-155044-98a95e32.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_155054.log).
All 382 checkpoint source/integration/runner hashes match before and after
the BATs. Fifteen source texts and four integration texts also match their
normalized snapshots. The graph has 281 nodes and 762 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. This verifies the exact analytic A-process,
not C or whole-goal completion. The counterexample and the completed
repaired energy chain remain unchanged.

## Native Heath–Brown derivative input and exact source beta bound — previous checkpoint

The source `heath-brown-2017` conclusion is proved by
`exponentSumGrowthExponent_le_heathBrown` for every natural k >= 3
and every real alpha > 0, with the exact displayed three-branch formula.
Its public signature has no derivative theorem or beta bound parameter.
The native input is `GafniTao.heathBrownKthDerivativeTheorem_native`.

The nine-module bridge derives signed model-jet bounds, the physical
scale lambda = c*T/N^k, smoothness on the actual closed interval, exact
translation and conjugation of the tail sum, and restoration of the
first endpoint. It includes singleton and empty intervals. Constants,
model accuracy and derivative order precede all actual phases, heights,
scales and source endpoints. The source window and epsilon budget give
the non-asymptotic beta predicate, then the exact ANTEDB growth exponent.

The pinned dependency contains 460 unchanged mathematical source modules
with documented import-path adaptations and two proved PNT prefixes.
It inherits the canonical foundation and its existing pins, without a
second or shadow foundation. Its ledger verifies 469 files and its root
reaches all 463 Lean modules. The audit also checks every nonprivate
theorem defined in those pinned modules, including the global PNT names.
The first compatibility build that exposed unrelated admitted Wiener
preliminaries is not accepted evidence; the proved prefixes avoid that
monolithic import without editing the canonical external checkout.

All ten new production modules, 42 named public audits, four explicit native/PNT
boundary audits and 51 semantic regressions are integrated. The fixtures
include the actual beta bounds beta(1/2) <= 5/12 and beta(1/3) <= 11/36,
plus exact formula, source-table endpoints and closed-singleton checks.

`HeathBrownBetaTable` proves the first two source beta-table rows from
this analytic bound, including alpha zero and both joining endpoints.
The second affine segment is proved on the larger closed interval
[1/4,2/5], then restricted to the printed endpoint 890/3277. These are
proved analytic rows, not a claim that the full beta table is complete.

EPZAE-12 is complete. EPZAE-09 and A/B remain complete; C and D remain
open, so EPZAE-10 and EPZAE-11 stay unchecked. Certified beta-table
assembly, the four advertised exponent pairs, density and release
obligations remain in the unchanged whole-proof contract. Only the
EPZAE-12 checkbox changes among the 42 aggregate items.

The permanent printed Lemma 62 counterexample and completed corrected
cardinality/energy powering, Heath--Brown energy relation, exact energy
optimization and all nine Add-est clauses are unchanged. The two powering
witnesses still have independent, unrestricted fifth coordinates.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
source verifiers, root imports, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, import,
dependency, audit or runner changes. A passing build does not complete
the remaining whole-proof outputs.

Scoped `.gitattributes` rules preserve the exact bytes of pinned Sources,
ANTEDB/native dependency files, the generated certificate and the permanent
counterexample across Git checkouts. The runner requires this policy file.
No repository Git configuration was changed. A read-only comparison of
509 protected files against HEAD found 507 byte-identical; the only two
differences are the documented native README correction and its ledger.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), each
with exit code 0. Their complete physical logs contain no Lean warnings,
errors, tactic suggestions or linter failures. The target covers 733
package files and scans 1,207 Lean files; its default build checks 10,065
jobs. The audit checks 6,191 discovered target theorems, 6,240 pinned
source theorems and 5 imported anchors: 12,436 declarations in total.
All 42 new named public audits and all four native/PNT boundary audits
occur exactly once and use only permitted standard logical axioms.
All 51 new semantic regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-174454-55b1abae.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_174825.log).
The foundation's six stages pass with zero diagnostics: 301 root modules,
two retained regressions, 8,857 build jobs, 7,636 explicit public declarations
and 14,290 discovered theorem dependencies.

All 1,228 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Ten source modules and five integration/verifier files match
their normalized snapshots. The complete [source checkpoint record](logs/tao-trudgian-yang-heath-brown-20260922-174454-55b1abae.json)
records these hashes and the exact new public signatures. The synchronized
graph has 286 nodes and 772 edges, with no duplicate or unresolved links.
Only EPZAE-12 changes among the 42 aggregate checkbox states. The permanent
counterexample and completed repaired energy branch are unchanged.
This verifies the recorded scope, not whole-goal completion.

## Robert–Sargos fourth-power near-count — previous checkpoint

`card_sargosFourthNearSolutions_le_log` proves, for every natural N >= 1,

    card {q in (N,2N]^4 :
      |q0²+q1²-q2²-q3²| <= N,
      |q0⁴+q1⁴-q2⁴-q3⁴| <= N³}
      <= 4096 N² (1+log N).

The finite set contains actual integer quadruples. No counting bound,
moment estimate or exponent-pair conclusion is a theorem parameter.
The geometric calculation derives |q0*q1-q2*q3| <= 5N and a bounded
sum displacement, then injects the quadruples into four integer linear
coordinates. The two difference coordinates satisfy |u*v| <= 11N.
The signed hyperbola count is proved via an injective sign/absolute-value
encoding, actual natural-number fibers, division bounds and the harmonic
sum. Zero fibers and all signs are included.

Four production modules contain 17 public theorems. All have explicit
audits and exact-signature regressions; nine additional fixtures check
N=0/1/2 counts, zero fibers, both signs and coordinate encoding.
This proves the counting assertion in Robert–Sargos section 5
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)),
with an explicit constant and a stronger N >= 1 domain.
It does not yet prove the fourth-moment integral, the sixth-moment
bootstrap or the analytic C-process. Those remain under EPZAE-10.
D, remaining beta rows/pairs, density and public-release obligations
also remain open. All 42 aggregate checkbox states are unchanged.

The counterexample, independent corrected powering witnesses and
completed Heath--Brown energy/optimization/all-nine-Add-est chain
are unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic
beta-table rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Both it and the foundation `run_lake_build.bat` remain mandatory after
proof/integration/runner changes. Retain the scoped byte-preservation
rules for the pinned inputs, generated certificate and counterexample.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 737 package files, scans
1,211 Lean files and completes 10,069 default-build jobs. Its audit checks
6,232 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,477 declarations. The 17 new explicit public audits occur once
with only permitted standard logical axioms; all 26 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-181839-3e1844f8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_182203.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,232 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Four source texts and four integration texts match normalized
snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-count-20260922-181839-3e1844f8.json)
contains the hashes, exact theorem signatures and both evaluation results.
The synchronized graph has 290 nodes and 779 edges, with no duplicates,
unresolved endpoints or unclassified nodes. All 42 aggregate checkbox
states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos rectangular windows and fixed-sum fourth moment — previous checkpoint

`sargosQuartic_fourth_moment` proves, for every natural N >= 1,
every fixed complex coefficient sequence with |z_n| <= 1 on (N,2N],
and every real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      |sum_{N<n<=2N} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|^4
      <= 131072 Delta/N (1+log N).

The sum, both physical windows and the four-variable count are literal.
No counting bound, moment estimate, kernel identity or exponent-pair
conclusion is assumed. The fixed coefficients may be arbitrary on the
source interval but do not depend on the integration parameters.

Fourteen new production modules prove whole-line sinc-square
integrability, its real-frequency tent Fourier transform, shifted-window
normalization, exact two-dimensional finite Gram integration, cutoff to
actual near pairs, and the source ordered-pair square. The rectangular
mean-square factor is exactly 16*delta*lambda. The source fourth moment
then consumes the proved 4096 N^2(1+log N) quadruple count, with
lambda=2/N^3. Both translated centers and non-integral frequencies are
included. No pinned native source was modified.

All 68 new public boundaries have explicit axiom audits and exact-signature
regressions. Fourteen additional fixtures cover tent/kernel normalization,
cutoff endpoints, a non-integral shifted frequency, N=1/2 source intervals
and sums, zero coefficients, and a concrete fourth-moment specialization.

This is the fixed-sum part of the Robert–Sargos section 4--5 analytic
transfer ([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
It does not yet prove the maximum over prefixes in source Lemma 2,
the slowly varying phase extension, the sixth-moment bootstrap, or the
analytic C-process. EPZAE-10 stays open. D, the remaining beta rows,
the four advertised pairs, density and release obligations remain open.
All 42 aggregate checkbox states are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy witnesses, Heath--Brown energy relation, exact energy
optimization and all nine repaired Add-est clauses are unchanged.
EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Retain the scoped byte-preservation rules
for pinned inputs, the generated certificate and the counterexample.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 751 package files, scans
1,225 Lean files and completes 10,083 default-build jobs. Its audit checks
6,330 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,575 declarations. All 68 new explicit public audits occur once
with permitted standard logical axioms only; all 82 new regressions pass.
The intermediate fixture warning and conversion error were fixed before
these accepted full runs; they are not acceptance evidence.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-191919-9f77a11b.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_192240.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,246 recorded proof/configuration/tooling hashes are unchanged across
both serialized BATs. Fourteen source texts and four integration texts
match their normalized snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-moment-20260922-191919-9f77a11b.json)
contains the hashes, all exact new public signatures and both evaluation
results. The synchronized graph has 293 nodes and 784 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos maximal-prefix fourth moment — previous checkpoint

`sargosQuartic_maximal_fourth_moment` proves, for every natural N >= 1,
fixed coefficients |z_n| <= 1 on (N,2N], and real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^4
      <= 10616832 Delta/N (1+log N)^5.

H is an integer, every source prefix is present, and the maximum is
attained. The extra H=0 prefix is the proved zero sum. This bounds the
pointwise maximum before integration, not merely each fixed-prefix
integral. Empty and zero-coefficient cases are retained and tested;
the estimate itself requires N >= 1.

Thirteen production modules prove exact finite Fourier inversion on
ZMod N, the geometric kernel and unit-circle gap, and a prefix-independent
nonnegative coefficient majorant with total mass at most 3(1+log N).
Two finite Cauchy--Schwarz inequalities give the fourth-power bound.
A proved residue bijection identifies the literal integer interval.
Every completed mode is the original sum with unit-modulus coefficient
twists independent of alpha and gamma. Maximum continuity, rectangle
integrability and finite integral interchanges are proved. The final
estimate consumes the earlier fixed-sum theorem and its literal
four-variable count, without assuming any count or moment estimate.

All 61 new public boundaries have explicit audits and exact-signature
regressions. Fifteen further fixtures cover zero-frequency kernels,
N=1/2/3 majorant masses, residue endpoints, proper/full/empty prefixes,
zero coefficients and a concrete maximal-moment specialization.

This establishes the weighted maximal fourth-moment assertion of
Robert–Sargos section 5 for natural N, with an explicit constant and
1+log N normalization
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
The parameter-dependent slow-phase extension, higher-moment window
transfer, sixth-moment bootstrap and analytic C-process remain open.
EPZAE-10 stays unchecked. D, remaining beta rows/pairs, density and
release obligations remain open. All 42 aggregate checkbox states
are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy powering witnesses, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows
are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Keep byte-preservation rules for the
pinned inputs, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0 with no Lean errors, warnings, tactic
suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [complete target log](logs/tao-trudgian-yang-build-20260922-220844-6863d940.log);
  764 production modules, 1238 scanned Lean files, 10096 build jobs,
  6425 target plus 6240 pinned theorems and five imported boundaries
  audited (12670 total). Each of the 61 new public audits appears once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_221514.log)
  and [manifest](../../logs/foundation_freeze_20260922_221514.json);
  all six stages pass, 8857 build jobs, 301 root modules and two
  retained regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-maximal-20260922-220844-6863d940.json) records
1259 physical source/configuration/tooling hashes, unchanged across
both runs, plus 17 normalized module/integration hashes. The 469-file
native pin and its 463-module closure pass. No earlier proof file was
changed: only the root, audit, regressions and runner inventory were
extended. The synchronized graph has 295 nodes and 787 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged (22 checked). The counterexample SHA-256
remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos parameter-dependent slow phase — previous checkpoint

The literal quartic prefixes now admit the actual phase
alpha*n^2+gamma*n^4+phi(alpha,gamma,n), with fixed source coefficients.
For N >= 1, K >= 0 and Delta >= 1/N, assume only the genuine local
derivative data on x in [N,2N] and on the integration rectangle:

    |d phi(alpha,gamma,x)/dx| <= K/N.

`sargosSlowQuarticMaximum_le` derives the pointwise bound by
(1+2*pi*K) times the unperturbed prefix maximum. The proof uses the
global character Lipschitz bound, exact integer-interval reindexing,
and finite Abel summation. Its adjacent variation is at most 2*pi*K;
no moment estimate or conclusion-equivalent variation bound is assumed.

`sargosSlowQuartic_upper_fourth_moment` then proves

    upper integral over [0,Delta] x [-N^-3,N^-3]
      (max_{0<=H<=N} |sum_{N<n<=N+H}
        z_n exp(2*pi*i*(alpha*n^2+gamma*n^4+phi(alpha,gamma,n)))|)^4
      <= (1+2*pi*K)^4 * 10616832 Delta/N (1+log N)^5.

There is no measurability hypothesis on the phase family here.
`sargosUpperIntegral` is the infimum of nonnegative integrals of
almost-everywhere measurable majorants. Its monotonicity and equality
with the ordinary nonnegative integral on measurable integrands are
proved. The result therefore does not exploit the default value of an
undefined Bochner integral.

For an almost-everywhere strongly measurable actual fourth-power
integrand, `integrable_sargosSlowQuarticFourth` proves integrability
from the existing majorant, and `sargosSlowQuartic_fourth_moment`
proves the ordinary iterated-integral estimate via Fubini. Continuity
of the actual maximum follows from continuity of each sampled phase.
The linear-phase consumers derive the derivative data for
phi(alpha,gamma,x)=u(alpha,gamma)*x/N; the upper-integral consumer
allows an arbitrary bounded, possibly nonmeasurable u.

Seven production modules contain 29 explicitly audited public theorems.
There are 29 exact-signature regressions and nine additional fixtures,
including a sin(alpha)-dependent phase, a bounded family without a
measurability assumption, Dirac upper integration, zero phase,
zero coefficients, the empty prefix and N=0 definitions.

This realizes the slow-phase removal used in Robert–Sargos section 4,
and composes it with the proved section 5 fourth moment
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S4)).
The printed variation sentence has an extra 1/N: a derivative of size
K/N over an interval of length N gives variation of size K. The proof
uses the correct explicit constant. The arbitrary higher-moment and
two-window comparison in Lemma 1, the sixth-moment argument and the
analytic C-process remain open. EPZAE-10 remains unchecked.

The permanent printed Lemma 62 counterexample and the completed
corrected powering -> Heath--Brown energy -> exact optimization ->
all nine repaired Add-est clauses are unchanged. A/B, EPZAE-09,
EPZAE-12 and the first two analytic beta rows are preserved.
All 42 aggregate checkbox states are unchanged.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, explicit audits, regressions and source verifiers
synchronized. Run it and the foundation `run_lake_build.bat` after
proof, integration, dependency or runner changes; preserve the pinned
bytes, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-223544-52ff7f68.log); 771 production modules,
  1245 scanned Lean files, 10103 build jobs; 6474 target and 6240 pinned
  theorems plus five imported boundaries audited (12719 total).
  All 29 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_223848.log) and
  [manifest](../../logs/foundation_freeze_20260922_223848.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-slowphase-20260922-223544-52ff7f68.json) records
1266 physical source/configuration/tooling hashes, unchanged across
both runs, and 11 normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, every earlier proof file is unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 297 nodes and 790 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos small-alpha sixth moment — previous checkpoint

`sargosQuartic_small_sixth_moment` proves, for every natural N >= 1,

    integral_{alpha=0}^{1/sqrt(N)} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^6
      <= 44845498368 (1+log N)^5.

This is the literal unweighted sum and its actual attained prefix
maximum, not a bound for arbitrary bounded coefficients. Every
integration and interval comparison has a proved integrability argument.
There is no sixth-moment, counting or cancellation hypothesis.

The quartic second difference is computed exactly. Its fourth-degree
coefficient is at most 110 N^2 on the actual sample range. With
|gamma| <= N^-3 and alpha >= 128/N, this gives positive curvature
between alpha and 3 alpha before conversion to radians.
The existing local discrete second-derivative theorem is applied to
the exact prefix and gives |S| <= 64 N sqrt(alpha), for alpha <= 1.
The conversion from the additive character to radians is proved.

A two-window split suffices. On [0,128/N], the trivial |S|^2 <= N^2
multiplies the proved maximal fourth moment. On [128/N,1/sqrt(N)],
the curvature bound gives |S|^2 <= 4096 N^2/sqrt(N), and the fourth
moment is bounded on the larger [0,1/sqrt(N)] window. The exact scale
identity N*(1/sqrt(N))^2=1 removes N. This yields log^5 directly,
without the extra logarithm from counting dyadic windows.

`sargosQuartic_small_sixth_moment_log_six` gives the (1+log N)^6
version. `sargosQuartic_small_sixth_moment_source` proves the literal
logarithm convention for N >= 2, with absolute constant

    44845498368 (1+1/log 2)^6

multiplying (log N)^6. Thus the exact source small-alpha assertion
is a proved consumer, including the logarithmic normalization bridge
([Robert–Sargos, section 5, Lemma 3](https://arxiv.org/html/2307.03554v1#S5)).
The cutoff 128/N is deliberately verified; the printed 16/N does not
uniformly guarantee positive quartic curvature. Changing this internal
cutoff changes only the absolute constant, not the public source result.

Six production modules contain 22 public theorem boundaries, each with
an explicit audit and exact-signature regression. Nine additional
fixtures test the sign issue, exact quartic difference, verified cutoff,
empty intervals, N=0 definitions, a literal full prefix, and the N=1/2
moment and source-normalization specializations.

The full higher-moment/window comparison, global sixth-moment bootstrap,
quartic B/Legendre transfer and analytic C-process remain open.
EPZAE-10 stays unchecked; this is the section 5 input, not the full
sixth-moment theorem or C-process. All 42 aggregate checkbox states
remain unchanged.

The maximal fourth moment and parameter-dependent slow-phase upper
and ordinary integral theorems are preserved. The permanent printed
Lemma 62 counterexample and completed corrected powering ->
Heath--Brown energy -> exact optimization -> all nine repaired Add-est
clauses remain unchanged, as do A/B, EPZAE-09, EPZAE-12 and the first
two analytic beta rows.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell inventory,
root imports, explicit audits, semantic regressions and source
verifiers synchronized. Run it and the foundation
`run_lake_build.bat` after proof, integration, dependency or runner
changes. Preserve pinned bytes and the permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-230214-7730af3c.log); 777 production modules,
  1251 scanned Lean files, 10109 build jobs; 6516 target and 6240 pinned
  theorems plus five imported boundaries audited (12761 total).
  All 22 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_230522.log) and
  [manifest](../../logs/foundation_freeze_20260922_230522.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-sixth-20260922-230214-7730af3c.json) records
1272 physical source/configuration/tooling hashes, unchanged across
both runs, and ten normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, all earlier proof files are unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 299 nodes and 795 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos full window comparison — previous checkpoint

The full higher-moment window comparison in Robert–Sargos Lemma 1 is now
kernel-checked for every natural N >= 2 and p >= 1. The public consumers are
`sargos_lemma_one_upper` and `sargos_lemma_one`; the latter derives
integrability from measurability and the proved majorant. No count,
cancellation estimate, window comparison, or moment bound is assumed.

Write B for the literal number of ordered pairs of p-tuples of integers
in (N,2N] satisfying the source quadratic and quartic tolerances
1/delta and 1/lambda. Let J be the unweighted fixed-sum 2p moment on
[-Delta/2,Delta/2] x [-mu/2,mu/2]. With derivative bound K/N on the actual
source interval and parameter rectangle, set

```text
C(p,K) = 16 [3 (1 + 2 pi K) (1 + 1/log 2)]^(2p).
U <= C(p,K) delta lambda (log N)^(2p) B,
B <= 64/(Delta mu) J,
0 < Delta <= delta, 0 < mu <= lambda.
```

Here U is the genuine upper integral of the actual slow-phase prefix
maximum; arbitrary, even nonmeasurable parameter dependence is allowed.
For an AEStronglyMeasurable integrand the ordinary iterated integral is
proved to agree, and the source-normalized inequality
U / [(log N)^(2p) delta lambda] <= C(p,K) B is exposed.
The result even permits delta > 1. The finite maximum includes the empty
prefix, whose norm is zero; the estimate therefore covers all source
nonempty prefixes as well. The coefficient family is fixed in the two
parameters and has norm at most one on the actual source interval.

The dependency chain is substantive:

- The p-th power is expanded exactly over `Fin p -> (N,2N]`.
- The physical tolerance identities retain both N^2 and N^4.
- The upper sinc-kernel window bound yields 16 delta lambda times the count.
- A dual tent Gram identity bounds that count by the central integral.
  Its compact support and weight at most one are proved, and every counted
  pair contributes at least Delta mu/64; all remaining weights are nonnegative.
- Finite weighted Jensen and actual Fourier completion work for every
  positive integer power. The common prefix kernel has mass at most
  3(1+log N); each completed mode has fixed unit-modulus-twisted coefficients.
- Actual Abel removal supplies the factor (1+2 pi K)^(2p), and a proved
  log-normalization inequality recovers the literal source log.

The 13 modules are `SargosWeightedPowers`, `SargosMomentTuples`,
`SargosMomentCount`, `SargosDualTentKernel`, `SargosDualTentGram`,
`SargosDualTentWindow`, `SargosMomentCentral`, `SargosPowerRegularity`,
`SargosPowerCompletion`, `SargosMaximalWindow`, `SargosSlowPowerWindow`,
`SargosLemmaOne`, and `SargosLemmaOneMeasurable`.
All 57 public theorems are explicitly audited. The 66 new regressions
comprise 57 exact signatures and nine additional fixtures, including
N=1 count scaling, delta > 1, sixth/tenth moments, both tent-support
directions, a smooth sine phase, and an arbitrary bounded linear-phase family.

Source: [Robert–Sargos, section 4, Lemma 1](https://arxiv.org/html/2307.03554v1#S4).
The explicit derivative loss uses the correct O(K) variation over an
interval of length N, not the printed O(1/N) variation sentence.

This closes the higher-moment window-comparison subbranch of EPZAE-10.
The global sixth-moment bootstrap, real dual-scale interval handling,
quartic B/Legendre and sextic slow-error calculation, and C-process are
still open. The previous small-alpha sixth moment remains available
with its verified log^5 estimate and exact source log^6 corollary.
No aggregate task is newly marked complete.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 790 production modules, 1264 scanned Lean files,
  10122 Lake jobs, 6607 target + 6240 pinned + 5 boundary declarations
  audited (12852 total). All 57 public declarations appear exactly once
  in the explicit audit and use only permitted logical axioms.
  [Full extension log](logs/tao-trudgian-yang-build-20260922-234413-dcbd04c1.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, with 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260922_234712.log) and
  [manifest](../../logs/foundation_freeze_20260922_234712.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. The production inventory, root imports, explicit audit and
  semantic regressions were updated together.
- All 1285 source/config/tooling files were byte-identical across the
  BAT pair; the 17 normalized source/integration hashes are recorded in
  the [checkpoint JSON](logs/tao-trudgian-yang-sargos-windows-20260922-234413-dcbd04c1.json).
  Of the previous 1272 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the 13 new modules were added.

The evaluated foundation HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`
with a dirty worktree. An owner Progress Update advanced the previous
HEAD during ongoing work; no agent commit or push was performed.
All 509 protected tracked files are unchanged against this HEAD.
The permanent counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 301 nodes and 801 edges, with no missing endpoints,
duplicates or unclassified nodes. All 42 aggregate checkbox states are
unchanged (22 checked). The repaired energy branch and all nine Add-est
clauses remain intact; the whole-proof goal is still open.

## Robert–Sargos sixth-moment base and strip reduction — previous checkpoint

The actual base integral `sargosSixthBaseMoment N` is defined by the
unweighted fixed sum on alpha in [0,1] and gamma in [-N^-3,N^-3].
Its kernel-checked bounds are

```text
1/64 <= I(N) <= 2 N^3                     (natural N >= 1).
```

The lower bound is derived from the literal diagonal tuple injection:
there are N^p source p-tuples, and each pair (t,t) satisfies both
nonnegative tolerances. The dual-tent count-to-central integral theorem
is then consumed. Exact complex conjugation under
(alpha,gamma) -> (-alpha,-gamma), actual integral reflection and
rectangle inclusion relate the central integral to I(N). No positive
lower bound, diagonal count or base-moment estimate is a parameter.

The same sign/window bridge consumes the previously proved small-alpha
maximal estimate and yields the fixed-sum central sixth moment on
[-1/sqrt N,1/sqrt N] x [-N^-3,N^-3] bounded by

```text
89690996736 (1+log N)^5.
```

For N >= 2, the literal source log^6 corollary has absolute constant
89690996736 (1+1/log 2)^6.

The completed Lemma 1 now has a further actual consumer:
`sargosQuartic_maximal_sixth_strip_reduction` bounds the weighted prefix
maximum on any translated unit-width alpha strip and any positive
height width lambda by

```text
128 C(3,0) (1 + lambda N^3) (log N)^6 I(N).
```

The ordinary and upper-integral slow-phase consumers replace C(3,0)
by C(3,K), for the proved derivative bound K/N. C is the explicit
constant from the preceding full-window checkpoint. The upper-integral
version allows arbitrary nonmeasurable parameter dependence; the
ordinary version derives integrability from measurability. The width
choice min(lambda,2/N^3), its positivity, physical count monotonicity,
central window inclusion and factor 1+lambda N^3 are all proved.

The six new modules are `SargosDiagonalMoment`, `SargosSymmetricWindow`,
`SargosCentralSixthMoment`, `SargosSixthBaseMoment`,
`SargosSixthStripCount`, and `SargosSixthStripTransfer`. Their 24 public
theorems are explicitly audited. The 34 new regressions comprise all
24 exact signatures and ten additional fixtures, including empty-tuple
counting, N=1 bounds, a concrete translated strip, the scale boundary,
a smooth sine phase and arbitrary bounded nonmeasurable linear phases.

These are the actual initial beta=3 estimate, nonvanishing base bound
and height-strip reduction used around
[Robert–Sargos, section 7](https://arxiv.org/html/2307.03554v1#S7).
They do not establish I(N) << N^epsilon. The exponent-improving recurrence,
quartic B/Legendre expansion, real dual-scale interval conversion and
C-process remain open. No aggregate checklist status changes.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 796 production modules, 1270 scanned Lean files,
  10128 Lake jobs, and 6640 target + 6240 pinned + 5 boundary declarations
  audited (12885 total). All 24 public theorems appear exactly once in the
  explicit audit with only permitted logical axioms.
  [Extension log](logs/tao-trudgian-yang-build-20260923-001009-8680cd0c.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260923_001404.log) and
  [manifest](../../logs/foundation_freeze_20260923_001404.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. Root imports, runner inventory, audit and regressions are
  synchronized. All 1291 source/config/tooling files were byte-identical
  across the BAT pair; ten normalized source/integration hashes and all
  physical hashes appear in the [checkpoint JSON](logs/tao-trudgian-yang-sargos-base-20260923-001009-8680cd0c.json).
  Of the preceding 1285 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the six new modules were added.

HEAD remains `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78` with a dirty worktree.
No agent commit or push was performed. All 509 protected tracked files
remain unchanged against that HEAD. The permanent counterexample retains
SHA-256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 303 nodes and 805 edges, without duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The repaired energy branch and all nine Add-est clauses
remain intact; the whole-proof goal is still open.

## Robert–Sargos actual quartic Legendre expansion — previous checkpoint

The actual source phase g(x)=alpha*x^2+gamma*x^4 now has a kernel-checked
inverse slope on [N,2N]. Under N>0, alpha>0 and
|gamma| <= alpha/(96*N^2), its curvature lies between 3*alpha/2 and
5*alpha/2. The chosen inverse is proved to invert the real polynomial;
it is smooth on the open slope image. The signed phase
g*(y)=g(w(y))-y*w(y) has derivative -w(y).

For this actual phase, the residual v is defined by the exact identity

```text
g*(y) = -y^2/(4*alpha) + gamma*y^4/(16*alpha^4)
        - gamma^2*y^6/(16*alpha^7) + v(y).
|v(y)|  <= 10240*|gamma|^3*N^8/alpha^2.
|v'(y)| <= 16384*|gamma|^3*N^7/alpha^3.
```

Both bounds are proved by exact rational polynomial identities, not
assumed asymptotic expansions. With x=w(y), u=2*gamma*x^2/alpha,
the residual polynomials have absolute bounds 5 and 16 for |u|<=1/12.
The derivative is that of the same residual used in the phase identity.

For N>=9216, alpha>=1/sqrt(N), and |gamma|<=N^-3, the scale
hypotheses are derived, giving |v|<=10240 and |v'|<=16384/(alpha*N).
The actual slope image equals the open interval between the endpoint
slopes and is convex. Consequently the residual has the corresponding
Lipschitz bound on that image. For alpha in [Delta,2*Delta], the image
is contained in (2*Delta*N-4,8*Delta*N+32).

This is the quartic specialization of
[Robert–Sargos (6.7), with the large-scale threshold and dual interval in section 7](https://arxiv.org/html/2307.03554v1#S6).
It does not prove the generic perturbation Lemma 4 or the oscillatory
B-transform. The source display (6.2) omits a square root in the
stationary amplitude; (7.5) has the required inverse square root.
The remaining transform must use that correct amplitude, with a
proved full error bound. This discrepancy does not change any frozen
Tao–Trudgian–Yang public output.

The seven modules are `SargosQuarticPhase`, `SargosQuarticInverse`,
`SargosQuarticLegendreAlgebra`, `SargosQuarticLegendreRemainder`,
`SargosQuarticLegendreBounds`, `SargosQuarticLegendreScale`,
and `SargosQuarticDualRange`. Their 44 public theorems are explicitly
audited. The 59 regressions comprise all exact signatures and 15 fixtures,
including both signs of a nonzero quartic coefficient, the Legendre
sign, inverse endpoints, the exact quadratic residual, both polynomial
boundaries, N=9216, and a physical dyadic dual interval.

Still open: the actual oscillatory B-transform, curvature-amplitude
and residual removal from its integer sum, real dual-scale/integer-block
conversion, the parameter Jacobian and covering, the bounded N range,
the exponent-improving sixth-moment recurrence, and the C-process.
The previous base-moment and all-height strip bounds remain available.
No aggregate checklist status changes; the permanent printed-Lemma-62
counterexample, corrected powering, and all nine Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 803 production files, 1,277 scanned Lean
  files and 10,135 build jobs. The audit covers 6,731 target theorems,
  6,240 pinned-source theorems and five boundary anchors (12,976 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-004528-1a1e7f39.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_004918.log)
  and [manifest](../../logs/foundation_freeze_20260923_004918.json).
- All 1,298 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-legendre-20260923-004528-1a1e7f39.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 305 nodes and 809 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos quartic stationary coordinate and Poisson entry — previous checkpoint

The normalized quartic phase F(u)=u^2+epsilon*u^4 now has an explicit
positive quadratic coordinate about the actual stationary point:

```text
L(epsilon,r,u) = 1 + epsilon*(u^2 + 2*u*r + 3*r^2),
z(epsilon,r,u) = (u-r)*sqrt(2*L(epsilon,r,u)).
F(u)-F(r)-F'(r)*(u-r) = z(epsilon,r,u)^2/2.
```

For |epsilon|<=1/96 and r,u in [0,3], the proved coefficient bounds are
7/16<=L<=25/16. The exact coordinate derivative is

```text
(2+4*epsilon*(u^2+u*r+r^2))/sqrt(2*L),
```

and lies in [7/16,25/4]. The coordinate is smooth wherever L>0 and
strictly increasing on the closed extended interval. Its actual chosen
inverse is proved smooth on the open image, with derivative in
[4/25,16/7]. The inverse maps zero to r, and its derivative there is
1/sqrt(2+12*epsilon*r^2).

The physical consumer uses epsilon=gamma*N^2/alpha, T=alpha*N^2,
and r=w(y)/N, where w is the already proved inverse quartic slope.
All range and coefficient hypotheses are derived from the source
curvature assumptions. It proves the exact original-variable identity

```text
g(x)-y*x = g*(y) + (T/2)*z(epsilon,r,x/N)^2.
```

The physical stationary Jacobian is also proved exactly:
(N/sqrt(T))*(inverse-coordinate)'(0)=1/sqrt(g''(w(y))).
Thus the required square-root curvature amplitude is derived from
the actual coordinate, not supplied as an input.

A separate actual-source entry constructs a smooth compact cutoff
chi with 0<=chi<=1 from the literal source lattice. For every natural
N>=1, one cutoff works for all real alpha,gamma. The theorem
`sargosQuartic_source_poisson` proves absolute summability of the
original Fourier integrals

```text
Integral chi(x/N)*e(alpha*x^2+gamma*x^4-m*x) dx
```

over all integer m, and bounds the difference between their full
Poisson series and the unweighted source sum on (N,2N] by 2.
The endpoint count, cutoff values, real/complex character convention,
Schwartz decay and Poisson equality are all derived. No
approximate-model-phase or oscillatory-transform hypothesis is used.

The four modules are `SargosQuarticMorse`,
`SargosQuarticMorseInverse`, `SargosQuarticMorsePhysical`, and
`SargosQuarticPoisson`. Their 40 public theorems are explicitly audited.
The 52 regressions comprise every exact signature and 12 fixtures,
covering both signs at the coefficient bounds, the actual inverse
and critical derivative, physical scaling/amplitude, and N=1 source
and endpoint behavior.

This supplies the actual-coordinate and Poisson-entry obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
It does not yet estimate the individual Fourier modes or prove the
B-transform. The exact lattice cutoff carries no claimed uniform derivative
budget; the quantitative step must choose controlled cutoffs and pay their
source-endpoint loss. Remaining: uniform higher inverse/weight derivatives,
actual integral substitution and cutoff transport, complete
stationary/nonstationary mode errors and lattice summation, the
curvature-amplitude/residual Abel steps, dual block conversion,
parameter Jacobian/covering, bounded N range, the sixth-moment
recurrence, and the C-process. No aggregate checklist status changes.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 807 production files, 1,281 scanned Lean
  files and 10,139 build jobs. The audit covers 6,818 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,063 total).
  All 40 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-011542-75b94f86.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_011847.log)
  and [manifest](../../logs/foundation_freeze_20260923_011847.json).
- All 1,302 physical proof/configuration/tooling hashes are identical
  before and after both runners. The four modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-20260923-011542-75b94f86.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 307 nodes and 816 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos uniform quartic jets and cutoff transport — previous checkpoint

The actual positive quadratic coordinate and its inverse now have
all-order derivative bounds uniform in |epsilon|<=1/96 and r in [0,3].
The coordinate bounds hold on u in (0,3); inverse bounds hold on the
actual moving open image. Constants depend only on the derivative
order, not on epsilon, r or the individual phase.

The polynomial A=2*(1+epsilon*(u^2+2*u*r+3*r^2)) has exact derivatives
A'=4*epsilon*(u+r), A''=4*epsilon and A^(j)=0 for j>=3.
Every atom in the coordinate's proved finite derivative expression
has absolute value at most 3. Explicit finite expression magnitudes
give the coordinate bounds; explicit finite sums of those bounds give
the inverse bounds. The formulas are proved against the actual
coordinate/inverse, not a model-phase surrogate.

The positive inverse Jacobian now transports both the complex
Bochner integral and integrability between (0,3) and the actual
coordinate image. The transported source cutoff is exactly

```text
W(z) = chi(inverse(z))*inverse'(z) on the actual open image,
W(z) = 0 outside that image.
W(0) = chi(r)/sqrt(2+12*epsilon*r^2).
```

For smooth chi with closed support contained in (0,3), W is globally
smooth and compactly supported, including across the moving image
boundary. Its closed support lies in the actual coordinate image of
the closed support of chi, and uniformly in [-6,6]. Every derivative
is integrable and supported in that same compact image. The whole-line
identity holds for arbitrary complex g:

```text
Integral chi(u)*g(u) du = Integral W(z)*g(inverse(z)) dz.
```

Global all-order weight estimates retain an explicit finite cutoff
jet budget M. Their constants depend only on M and the output order,
not on the phase parameters. No derivative budget uniform in a
varying cutoff family is inferred from compactness.

Eleven modules are installed: `SargosQuarticMorseCurvature`,
`SargosQuarticMorseJets`, `SargosQuarticMorseJetBounds`,
`SargosQuarticMorseInverseJets`, `SargosQuarticMorseInverseJetBounds`,
`SargosQuarticMorseChangeVariables`, `SargosQuarticMorseAmplitude`,
`SargosQuarticMorseSupport`, `SargosQuarticMorseGlobalIntegral`,
`SargosQuarticMorseWeightJets`, and `SargosQuarticMorseWeightBounds`.
All 50 public theorems have exact-signature regressions and explicit
axiom audits; 12 additional fixtures cover signed boundary coefficients,
high-order vanishing, arbitrary derivative orders, cutoff retention,
moving-image exterior behavior and global cutoff budgets.

These results discharge further actual-coordinate analytic obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
They do not yet prove a Fourier-mode remainder or the B-transform.
Remaining are the physical positive-quadratic Fourier identity and
Fresnel remainder, controlled cutoff family and source loss, complete
stationary/nonstationary mode errors and lattice sums, curvature and
Legendre-residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 818 production files, 1,292 scanned Lean
  files and 10,150 build jobs. The audit covers 6,891 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,136 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-014238-0efee296.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_014551.log)
  and [manifest](../../logs/foundation_freeze_20260923_014551.json).
- All 1,313 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-jets-20260923-014238-0efee296.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 309 nodes and 822 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos physical stationary estimates and controlled source entry — previous checkpoint

The actual physical quartic Fourier integral is now proved equal to
its positive-quadratic representation. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open quartic slope image,
put epsilon=gamma*N^2/alpha, T=alpha*N^2 and r=w(y)/N. Then

```text
Integral chi(x/N)*e(g(x)-y*x) dx
  = N*e(g*(y))*Integral W(z)*e((T/2)*z^2) dz,
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

The original cutoff has closed support in (1,2), and W is its actual
smooth transported weight from the preceding checkpoint. The physical
factor N, actual stationary point, signed Legendre phase, positive
Fresnel sign and square-root curvature amplitude are all proved.
The leading coefficient is chi(r)*main(y); the cutoff is not dropped.

Exact complex conjugation transfers the already proved negative
quadratic Fresnel remainder to positive curvature. With the finite
original-cutoff derivative budget M visible, the theorem
`sargosQuarticFourierMode_stationary_bound` bounds the difference
from chi(r)*main(y) by C(M)/(alpha*N). Its constants do not depend
on N, alpha, gamma or y.

A separate varying-cutoff theorem chooses constants before both
endpoints, the width eta, and the quartic parameters. Its actual
transformed nth derivative costs at most C_n*eta^(-n), for 0<eta<=1.
This yields

```text
|physical mode - chi(r)*main(y)| <= C*eta^(-3)/(alpha*N).
```

The exponent -3 is explicitly retained. This estimate alone is not
the sharp summed B-transform error; a local plateau argument and
complete mode/lattice analysis are still required.

The source-facing controlled cutoff is now constructed explicitly:
chi(u)=bufferedCutoff((N+1)/N,2,eta)(u), for natural N>=1 and eta>0.
`sargosQuartic_buffered_poisson` proves absolute summability of the
original physical Fourier modes and

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4) - Sum_(m in Z) mode(m)|
  <= 4*N*eta+2.
```

Its endpoint count, literal source interval, source phase and
normalizations are derived. No model-phase approximation, Poisson
error certificate, or stationary-phase estimate is an input.

Seven modules are installed: `SargosQuarticMorseFourier`,
`SargosPositiveQuadraticRemainder`, `SargosQuarticMorseRemainder`,
`SargosQuarticStationaryEstimate`, `SargosQuarticBufferedJets`,
`SargosQuarticBufferedStationary`, and `SargosQuarticBufferedPoisson`.
All 17 public theorems have exact-signature regressions and explicit
axiom audits. Twelve additional fixtures test the Fresnel sign,
physical normalization and amplitude, arbitrary derivative order,
explicit width powers, and N=1,2 source support/endpoint behavior.

These are supporting steps toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
The sharp interior, near-edge, exterior and infinite-tail estimates,
their integer sums, curvature/residual Abel steps, integer dual-block
conversion, parameter Jacobian/covering, bounded N, sixth-moment
recurrence and C-process remain open. No aggregate checklist status
changes. The permanent counterexample, corrected powering and all
nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 825 production files, 1,299 scanned Lean
  files and 10,157 build jobs. The audit covers 6,930 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,175 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-020618-a3f2de7d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_020944.log)
  and [manifest](../../logs/foundation_freeze_20260923_020944.json).
- All 1,320 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-stationary-20260923-020618-a3f2de7d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 312 nodes and 833 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos sharp quartic interior stationary error — previous checkpoint

The actual positive-curvature quartic Fourier mode now has a sharp
interior error with no inverse cutoff-width loss. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open slope image, write
r=w(y)/N for its actual normalized stationary point. For the controlled
cutoff chi=bufferedCutoff(l,b,eta), assume 1<=l, b<=2, eta>0, d>0,
l+2*eta+d<=r and r+d<=b-2*eta. Then

```text
|mode(y) - e(g*(y)+1/8)/sqrt(g''(w(y)))| <= C/(alpha*N*d).
```

The constant is chosen before l, b, eta, d and all physical parameters.
The cutoff coefficient is one because the actual stationary point
lies inside its proved plateau; it is not discarded by assumption.
The source mode, inverse, signed Legendre phase, positive Fresnel sign,
physical N factor and square-root amplitude are the original objects.

The proof derives an actual quadratic-coordinate window |z|<=H.
Uniform coordinate distances and slope gaps locate its inverse images.
On that window the transported cutoff's derivatives are actual inverse
derivatives, so their constants do not grow as eta tends to zero.
The local positive-quadratic remainder is bounded by C_local/(T*H).

An exact positive-Jacobian change of variables identifies the central
original-integral piece. The two omitted original-integral tails
are bounded together by 128/(7*pi*T*H), using actual slope gaps and
the proved width-independent cutoff variation. Choosing H=d/4 and
T=alpha*N^2 gives the displayed physical estimate. All hypotheses
for the window, tails, plateau and normalization are derived.

Nine modules are installed: `SargosQuarticMorseGeometry`,
`SargosQuarticMorseWindow`, `SargosPositiveQuadraticLocal`,
`SargosQuarticLocalRemainder`, `SargosQuarticCenteredPhase`,
`SargosQuarticWindowIntegral`, `SargosQuarticLocalNonstationary`,
`SargosQuarticWindowTails`, and `SargosQuarticInteriorStationary`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Twelve further fixtures check both perturbation endpoints,
the quadratic specialization and derivative, actual inverse windows,
genuine integrability, positive central transport, varying widths,
and the quarter-distance physical bound.

This completes the sharp interior component, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Near-edge, exterior and infinite-tail bounds and their integer sums
remain open, followed by curvature/residual Abel steps, integer dual
blocks, parameter Jacobian/covering, bounded N, the sixth-moment
recurrence and C-process. Aggregate checklist states do not change.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 834 production files, 1,308 scanned Lean
  files and 10,166 build jobs. The audit covers 6,960 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,205 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-023612-86705e16.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_023922.log)
  and [manifest](../../logs/foundation_freeze_20260923_023922.json).
- All 1,329 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-interior-20260923-023612-86705e16.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 314 nodes and 840 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos sharp quartic support-frequency core — previous checkpoint

The original quartic Fourier modes now have uniform estimates at
every real frequency, including frequencies without a stationary
point and those at moving support endpoints. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and the actual controlled cutoff
chi=bufferedCutoff(l,b,eta), with 1<=l, b<=2 and eta>0,

```text
|mode(y)| <= 4*(2/pi+2)/sqrt(alpha).
```

This follows from the actual quartic curvature and the proved cutoff
variation, by exact complex conjugation of the negative-curvature
integral theorem. No model-phase approximation is assumed. The actual
stationary main term has norm at most 1/sqrt(alpha).

Outside the support's actual slope interval, the original physical
mode has a reciprocal-gap bound 4/(pi*gap), where gap is the distance
from y to g'(N*(l+eta)) or g'(N*(b-eta)). The physical normalization
and the cutoff-empty case are proved. These are pointwise exterior
bounds; their integer sums are not yet included.

For the interior, the actual quartic curvature upper bound converts
frequency gaps to distances of the real inverse stationary point.
The preceding C/(alpha*N*d) estimate therefore becomes C'/gap.
Summing the two reciprocal edge distances gives a logarithmic error
over the literal integer interval; no stationary-image or per-mode
estimate is left as an input.

Support endpoints are rounded outwards, plateau endpoints inwards:

```text
L = floor g'(N*(l+eta)),     U = ceil g'(N*(b-eta)),
A = ceil  g'(N*(l+2*eta)),   B = floor g'(N*(b-2*eta)).
```

If l+4*eta<b, the transition complement Icc(L,U) minus Ioo(A,B)
has at most 5*alpha*N*eta+6 elements. Exactly resonant and nearest
endpoint frequencies are included. The public consumer
`sargosQuarticBufferedSupportCore_error` proves

```text
|Sum_(L<=y<=U) mode(y) - Sum_(A<y<B) main(y)|
 <= C*(1+log((B-A-1).toNat)) + (5*alpha*N*eta+6)*D/sqrt(alpha),
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

C>=1 and D>0 are chosen before all cutoff and physical parameters.
The source Fourier modes and actual signed stationary main terms are
used throughout. Empty integer interior blocks are handled explicitly.

Six modules are installed: `SargosQuarticFourierCurvature`,
`SargosQuarticExteriorModes`, `SargosQuarticInteriorFrequency`,
`SargosQuarticInteriorSum`, `SargosQuarticTransitionBands`, and
`SargosQuarticSharpCore`. All 18 public theorems have exact-signature
regressions and explicit axiom audits. Twelve further fixtures cover
all-frequency quadratic and extreme perturbation bounds, empty
cutoffs, physical stationary amplitude, both exterior gaps, exact
rounding at N=8, and the actual eleven-frequency interior block.

This is the sharp finite support-frequency core, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Exterior integer sums, quantitative infinite-tail bounds and full
source assembly remain open, followed by curvature/residual Abel
steps, integer dual blocks, parameter Jacobian/covering, bounded N,
the sixth-moment recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 840 production files, 1,314 scanned Lean
  files and 10,172 build jobs. The audit covers 7,000 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,245 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-025806-560f1b5d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_030120.log)
  and [manifest](../../logs/foundation_freeze_20260923_030120.json).
- All 1,335 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-support-core-20260923-025806-560f1b5d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 317 nodes and 849 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos complete explicit-parameter quartic source expansion — previous checkpoint

The literal quartic source sum is now connected to its actual signed
stationary main terms through every Fourier-mode class. Exterior
integer sums, quantitative two-sided infinite tails and source
assembly are proved. The cutoff width, truncation radius and
logarithmic lengths remain explicit; the final stationary-scale
error simplification is not yet claimed.

The original normalized quartic kernel has uniform second-derivative
bound C*eta^(-2)*(1+|T|)^2. Its actual phase has first two derivative
bounds proved from |epsilon|<=1/96 on [1,2]. Exact normalization links
T=alpha*N^2, epsilon=gamma*N^2/alpha and Fourier frequency y*N to the
original physical mode. Consequently,

```text
|mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*y^2), y != 0,
|Sum_(|y|>R) mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*R).
```

The omitted series is the actual two-sided integer tail. Both signs,
absolute convergence, zero-frequency exclusion and the physical N
factor are proved. A separate source consumer chooses an explicit
positive radius achieving any requested tail tolerance.

The left and right support-exterior blocks each have norm sums bounded
by (4/pi)*harmonic(length); both together have logarithmic loss.
They are exactly reindexed, with no omitted or duplicated nearest
exterior integer. Combining them with the preceding sharp support
core gives the complete finite Fourier-window expansion.

For the literal source Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4), take
natural N>=1, alpha>0, |gamma|<=alpha/(96*N^2), 0<eta<=1,
l=(N+1)/N, and l+4*eta<2. Let L,U be the outward-rounded support
slopes and A,B the inward-rounded plateau slopes. Then
`sargosQuartic_source_stationary_expansion` proves

```text
|source - Sum_(A<y<B) e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= 4*N*eta+2
  + C*eta^(-2)*(1+alpha*N^2)^2/(N*R)
  + D*(1+log((B-A-1).toNat))
  + (5*alpha*N*eta+6)*E/sqrt(alpha)
  + (4/pi)*(2+log((L+R).toNat)+log((R-U).toNat)).
```

Here R is a positive natural number whose symmetric interval contains
[L,U], and C>=1, D>=1, E>0 are chosen before all source parameters.
The precision consumer constructs
R=ceil(C*eta^(-2)*(1+alpha*N^2)^2/(N*tolerance))+|L|+|U|+1,
proves the required interval containment, and replaces the actual
tail term by tolerance. No Poisson, stationary or tail estimate is
left as an assumption.

Six modules are installed: `SargosQuarticExteriorSum`,
`SargosQuarticKernelJets`, `SargosQuarticFourierDecay`,
`SargosQuarticFourierTail`, `SargosQuarticFourierWindow`, and
`SargosQuarticSourceExpansion`. All 17 public theorems have exact
signature regressions and explicit axiom audits. Twelve further
fixtures check extreme perturbations, the actual kernel and carrier,
physical decay/tail constants, a concrete truncation tolerance,
empty exterior blocks, rounded finite windows, and the literal N=8
source's nine-frequency stationary block.

This assembles the explicit-parameter source chain toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the linked stationary-scale cutoff choice, polynomial
radius/logarithmic budgets and the final uniform B-transform error;
then curvature/residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 846 production files, 1,320 scanned Lean
  files and 10,178 build jobs. The audit covers 7,026 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,271 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-032157-6b77f0c9.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_032511.log)
  and [manifest](../../logs/foundation_freeze_20260923_032511.json).
- All 1,341 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-expansion-20260923-032157-6b77f0c9.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 320 nodes and 860 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos large-source quartic B-transform — previous checkpoint

The literal quartic source now has a uniform B-transform into its full
closed stationary integer range. The actual cutoff choice, every
frequency logarithm, both infinite tails and the omitted endpoint
terms are consumed by one public theorem. This closes the large-source
oscillatory-transform step, not the sixth-moment recurrence.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_B_transform` proves, with one constant M>=1
chosen before N, alpha and gamma,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)
 - Sum_(g'(N)<=y<=g'(2N), y integer)
     e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= M*(1/sqrt(alpha)+1+log(2+alpha*N)).
```

Here g(x)=alpha*x^2+gamma*x^4, w is its actual inverse slope on
[N,2N], and g*(y)=g(w(y))-y*w(y). Both integer endpoint resonances
are included with full weight; their possible boundary contributions
are covered by the proved error. The positive square-root amplitude
is retained, consistently with (7.5). The earlier documented
missing square root in displayed (6.2) is not imported as an identity.

The stationary cutoff is eta=1/sqrt(alpha*N^2)=1/(N*sqrt(alpha)).
Its positivity, eta<=1 and nonempty source plateau are derived from
the original source range. Smoothing contributes 4/sqrt(alpha);
the transition term simplifies with no surviving inverse-width loss.
Every actual rounded slope has absolute integer size at most
6*alpha*N^2+1. The prescribed positive radius is at most
(C+16)*(alpha*N^2+1)^3; all three logarithmic lengths are bounded
using (C+24)*(alpha*N^2+1)^3, including zero-length cases.

The intermediate uniform consumer retains the actual buffered main
range. A separate closed-range bridge proves inverse-slope and
amplitude bounds at the endpoints, plateau containment, and the
count of omitted terms:
```text
omitted cardinality <= 5*alpha/2+10*alpha*N*eta+4.
```
At the stationary width and alpha<=1 their total norm is at most
17*(1/sqrt(alpha)+1). The final consumer restores the full closed
stationary sum and derives its logarithmic error from linked source
scales; no cutoff, stationary estimate or endpoint certificate is
assumed.

Nine modules are installed: `SargosQuarticStationaryWidth`,
`SargosQuarticRoundedBounds`, `SargosQuarticRadiusBudget`,
`SargosQuarticLogBudget`, `SargosQuarticUniformSource`,
`SargosQuarticClosedRange`, `SargosQuarticEndpointBands`,
`SargosQuarticEndpointError`, and `SargosQuarticBTransform`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen further fixtures check the stationary width,
degenerate inverse-square identity, threshold plateau, smoothing,
transition algebra, prescribed radius, full closed range, both
resonant endpoints, exterior exclusion, boundary amplitude, omitted
cardinality and the assembled source estimate.

This realizes the large-integer-source B-transform needed toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the power-scale error corollary, actual curvature and
residual Abel steps, integer dual blocks and real-scale conventions,
parameter Jacobian/covering, bounded N, the sixth-moment recurrence
and C-process. It does not assert the general C4 version of (6.2).
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 855 production files, 1,329 scanned Lean
  files and 10,187 build jobs. The audit covers 7,076 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,321 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-035345-754b20b2.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_035655.log)
  and [manifest](../../logs/foundation_freeze_20260923_035655.json).
- All 1,350 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-b-transform-20260923-035345-754b20b2.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 322 nodes and 866 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos source power error and both Abel steps — previous checkpoint

The literal quartic source is now bounded by the actual degree-six
polynomial prefix maximum. The quarter-power error and both Abel
steps are proved, including the full closed stationary range and
its resonant endpoints. Neither amplitude variation nor residual
variation is an assumed analytic input.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_le_polynomialPrefixMaximum` proves

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(alpha^(-1/2)*Pmax(N,alpha,gamma)+N^(1/4)).
```

The single constant C>=1 is chosen before N, alpha and gamma.
Pmax is the attained maximum over every prefix, including the empty
prefix, of the actual integer interval
[ceil(g'(N)), floor(g'(2N))], with phase

```text
p(y) = -y^2/(4*alpha)+gamma*y^4/(16*alpha^4)
       -gamma^2*y^6/(16*alpha^7).
```

The prefix definition uses the exact integer interval length and
works also for an empty interval. It is not a separately supplied
exponential-sum majorant. The source consumer links every parameter
to the original phase g(x)=alpha*x^2+gamma*x^4.

The preceding full B-transform now has error at most C*N^(1/4).
The proof derives alpha^(-1/2)<=N^(1/4) and
log(N+1)<=1+4*N^(1/4), then consumes the actual logarithmic error.

The actual amplitude 1/sqrt(g''(w(y))) is positive, bounded by
alpha^(-1/2), and monotone or antitone according to the sign of
gamma on the closed slope range. Its sampled finite variation is
at most alpha^(-1/2). Exact integer reindexing and Abel summation
bound the full stationary sum by twice this scale times the genuine
unweighted Legendre-prefix maximum. The unit phase e(1/8) is removed
by an exact identity and norm equality.

The literal Legendre residual v(y)=g*(y)-p(y) uses the existing
source derivative bound 16384/(alpha*N). Its character has interior
Lipschitz constant 32768*pi/(alpha*N), while the actual slope interval
has length at most 5*alpha*N/2. Interior sampled variation is therefore
at most 81920*pi. On the full closed range, the first and last possible
boundary jumps each cost at most 2 by unit modulus. This yields the
uniform finite-variation budget 5+81920*pi, without extending the
derivative theorem to an unproved endpoint domain. The residual Abel
consumer retains every endpoint and supplies the polynomial maximum
used by the final source theorem.

Eight modules are installed: `SargosQuarticPowerError`,
`SargosQuarticAmplitude`, `SargosQuarticAmplitudeVariation`,
`SargosIntegerPrefix`, `SargosQuarticAmplitudeAbel`,
`SargosQuarticResidualVariation`, `SargosQuarticResidualBoundary`,
and `SargosQuarticResidualAbel`. All 29 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures cover quarter powers, threshold source errors,
constant curvature, both monotonicity signs, inverse endpoints,
sampled amplitude variation, negative and empty integer prefixes,
the literal dual polynomial, closed residual boundary variation,
and the final source-to-polynomial bound.

This completes the power-scale and actual-weight/residual steps toward
[Robert–Sargos (7.5)–(7.8)](https://arxiv.org/html/2307.03554v1#S7).
Still open: dyadic integer block conversion and real-scale conventions,
the sign-conjugation bridge to the source parameter change, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No integral transfer or recurrence is claimed here. No aggregate
checklist status changes. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 863 production files, 1,337 scanned Lean
  files and 10,195 build jobs. The audit covers 7,128 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,373 total).
  All 29 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-042459-0f7675ca.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_042813.log)
  and [manifest](../../logs/foundation_freeze_20260923_042813.json).
- All 1,358 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-abel-20260923-042459-0f7675ca.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 324 nodes and 872 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos rounded dyadic blocks and exact conjugation — previous checkpoint

The actual closed stationary-prefix interval now reduces to two integer
dyadic blocks. Exact conjugation converts their phases to positive
quadratic phases while retaining the sextic correction.

For natural N>=9216, N^(-1/2)<=Delta<=1/2,
alpha in [Delta,2*Delta] and |gamma|<=N^(-3), let
m=floor(2*Delta*N). The source-facing theorem
`sargosQuartic_source_le_two_slow_blocks` proves, with one C>=1
chosen before every source parameter,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(Delta^(-1/2)*(Smax(m)+Smax(2*m))+N^(1/4)),
Smax(h) = max_(0<=L<=h)
 |Sum_(h<n<=h+L) e(x*n^2+y*n^4+phi(n))|,
x=1/(4*alpha), y=-gamma/(16*alpha^4),
phi(t)=gamma^2*t^6/(16*alpha^7).
```

These are the actual slow quartic maxima, not assumed majorants.
The scale is linked to the source: m>=192 and
Delta*N<=m<=2*Delta*N<m+1. The integer stationary endpoints satisfy
ceil(g'(N))>=m-4 and floor(g'(2N))<=4*m+35.
At most 40 unit-modulus terms lie outside (m,4*m].
Each retained interval is the difference of two prefixes in
(m,2*m] or (2*m,4*m]. This yields the two genuine maxima
and a bounded loss absorbed in the existing quarter-power error.

The polynomial sign reversal, character conjugation, prefix conjugation
and maximum equality are exact. In particular, the correction
gamma^2*t^6/(16*alpha^7) is retained. The natural scale m is not
silently identified with the paper's real scale 2*Delta*N.

Six production modules are installed: `SargosIntegerBlock`,
`SargosIntegerTwoBlocks`, `SargosIntegerDyadicTrim`,
`SargosQuarticRoundedScale`, `SargosQuarticPrefixBlocks`,
and `SargosQuarticDualConjugation`. All 19 public theorems have
exact-signature regressions and explicit axiom audits. Thirteen
additional fixtures cover negative and empty intervals, the exact
40-term trimming bound, integral and nonintegral rounded scales,
both extreme perturbation signs, the actual sextic polynomial,
and the source bound at N=9216.

This is a pointwise source reduction toward
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Parameter change, Jacobian, rectangle covering, integrated transfer,
the real-scale convention, bounded N, recurrence and C-process remain
open. No integral estimate or recurrence is claimed. All 42 aggregate
checkbox states are unchanged. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 869 production files, 1,343 scanned Lean
  files and 10,201 build jobs. The audit covers 7,188 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,433 total).
  All 19 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-045149-2aa62e03.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_045504.log)
  and [manifest](../../logs/foundation_freeze_20260923_045504.json).
- All 1,364 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-dyadic-conjugation-20260923-045149-2aa62e03.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 326 nodes and 874 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos actual parameter change and sextic rectangle moment — previous checkpoint

The actual source parameter substitution and the moment bound on each
admissible parameter rectangle are now proved. No Jacobian formula,
inverse map, phase-variation bound or rectangle moment is assumed.

The map
`(alpha,gamma) -> (1/(4*alpha),-gamma/(16*alpha^4))`
is its own inverse when alpha is nonzero. Its exact scalar derivatives
give the inverse Jacobian weight 1/(64*x^6). Two genuine set-integral
substitutions prove the triangular change of variables, including
the variable vertical range [-16*H*x^4,16*H*x^4]. For Delta>0 and H>=0,
this yields the fixed-rectangle bound

```text
Integral_(Delta<=alpha<=2Delta, |gamma|<=H) F(map(alpha,gamma))
 <= 4096*Delta^6 *
    Integral_(1/(8Delta)<=x<=1/(4Delta), |y|<=H/(16Delta^4)) F(x,y).
```

This statement is for nonnegative extended-real iterated integrals,
and does not require an integrand-measurability hypothesis.
`sargosQuarticDual_sixth_parameter_transfer` consumes it for the
actual source-linked slow maxima. The exact sextic identity changes
gamma^2*t^6/(16*alpha^7) into 4*y^2*t^6/x.

On a unit-width rectangle [c,c+1] by [d,d+2/M^3], with
M>=2, 0<Delta<=1/2, c>=1/(8*Delta) and
|d|<=5/(Delta*M^3), the frozen coefficients are exactly
e(4*d^2*n^6/c), of modulus one. Their residual phase is
4*(y^2/x-d^2/c)*t^6. The proved coefficient bound is
2496/M^6 and the derivative bound is 1916928/M.
The actual prefix and maximum are unchanged by this freezing.

The completed Lemma 1 consumer then proves

```text
Integral_rectangle Smax(M,x,y,4*y^2*t^6/x)^6
 <= 384*Cwindow(3,1916928)*(log M)^6*I(M).
```

Both a genuine upper-integral theorem and the ordinary nonnegative
iterated-integral theorem are installed. Measurability of the actual
sextic maximum is proved, not assumed. These are estimates for each
admissible rectangle; the finite covering has not yet been assembled.

Eight modules are installed: `SargosQuarticParameterMap`,
`SargosQuarticParameterDomain`, `SargosQuarticParameterChange`,
`SargosQuarticParameterTransfer`, `SargosQuarticSexticFreeze`,
`SargosQuarticSexticBounds`, `SargosQuarticSexticRectangle`,
and `SargosQuarticMomentTransfer`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures check reciprocal images, source-scale parameters,
the sextic identity, the extremal Jacobian bound, frozen unit modulus,
rectangle boundaries and the actual source-moment transfer.

This advances the source reduction in
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Still open: finite rectangular covering and its count, assembled
large-source sixth-moment bound, rounded/real-scale conventions,
bounded N, recurrence and C-process. The original quartic pointwise
bound uses the linked integer scales m=floor(2*Delta*N) and 2*m;
this checkpoint does not silently replace them by real scales.
All aggregate checklist states, the permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 877 production files, 1,351 scanned Lean
  files and 10,209 build jobs. The audit covers 7,254 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,499 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-051922-22d50561.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_052320.log)
  and [manifest](../../logs/foundation_freeze_20260923_052320.json).
- All 1,372 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-parameter-rectangle-20260923-051922-22d50561.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 328 nodes and 878 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos large-source sixth moment at rounded scales — previous checkpoint

The literal source sixth moment now satisfies the large-source
two-scale reduction. The public theorem
`sargosQuartic_large_source_sixth_moment` chooses one C>=1 before
all N and Delta, and proves for natural N>=9216 and
N^(-1/2)<=Delta<=1/4, with m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)),
R(N,Delta) =
 Integral_(Delta<=alpha<=2Delta, |gamma|<=N^(-3))
 |Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|^6.
```

R and I are the actual Bochner integrals of the literal quartic sums.
No majorant, Jacobian, covering, slow-phase estimate or moment
inequality is supplied as an analytic premise.

The closed transformed rectangle has a finite grid cover retaining
all endpoints. Its horizontal count is at most 2/Delta and its
vertical count at most 5/Delta. Every corner satisfies the already
proved sextic rectangle theorem. A finite-cover integration inequality
allows overlapping boundaries; no disjointness or boundary omission
is assumed. Summing the actual rectangle moments and applying the
proved source parameter change gives, at either admissible integer
scale M,

```text
Integral_source DualMax(M)^6
 <= 15728640*Cwindow(3,1916928)*Delta^4*(log M)^6*I(M).
```

The source-facing sixth-power consumer uses both real dual maxima
and the original pointwise source bound. It bounds the sixth power
of the quarter-power error by N^3, whose integral over the source
rectangle is exactly 2*Delta. Measurability of the actual dual maxima
and the bridge from the original Bochner integral to nonnegative
iterated integrals are proved. The linked scales satisfy
m>=2, 2*m>=2, m<=N and 2*m<=N, so both logarithms transfer to log N.
The actual lower bound I(m)>=1/64 absorbs the error, without an
extra logarithmic loss.

Eleven modules are installed: `SargosIntervalGrid`,
`SargosFiniteCoverIntegral`, `SargosQuarticCoverGeometry`,
`SargosQuarticCoverMoment`, `SargosQuarticDualMoment`,
`SargosQuarticSixthPower`, `SargosQuarticMomentIntegration`,
`SargosRectangleLinearIntegral`, `SargosQuarticSourceMoment`,
`SargosQuarticMomentScale`, and `SargosQuarticLargeSourceMoment`.
All 24 public theorems have exact-signature regressions and explicit
axiom audits. Fifteen additional fixtures cover zero/nonintegral
grid lengths, closed right endpoints, negative grid origins, actual
source grid counts at both scales, boundary corners, sixth powers,
the integrated source error, and the final threshold, nonintegral
rounding and Delta=1/4 source estimates.

This is the natural-N, rounded-scale, large-source form of the
reduction in [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
It does not identify m with the real number 2*Delta*N.
Still open: the bounded source range, the source's real-scale
convention, global recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 888 production files, 1,362 scanned Lean
  files and 10,220 build jobs. The audit covers 7338 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13583 total).
  All 24 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-054924-c8e7f79f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_055711.log)
  and [manifest](../../logs/foundation_freeze_20260923_055711.json).
- All 1,383 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-large-source-moment-20260923-054924-c8e7f79f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 330 nodes and 883 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos bounded reduction and finite-scale bootstrap — previous checkpoint

The rounded two-scale reduction now covers every natural N>=16.
The theorem `sargosQuartic_sixth_moment_reduction` chooses one C>=1
before N and Delta, and proves, for N^(-1/2)<=Delta<=1/4 and
m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)).
```

The previously omitted range 16<=N<=9216 is discharged using the
actual source rectangle inclusion, I(N)<=2*N^3, I(m)>=1/64,
m>=8 and Delta>=1/96. No additional analytic premise is introduced.

The recurrence now has an actual finite-scale consumer.
For the literal full-sum moment, the near-count upper/lower bounds
and symmetry prove localization without a maximal-completion loss:

```text
I(N) <= (1024/A)*InitialMoment(N,A),       0<A<=1/2.
```

A finite dyadic split retains every interval endpoint. Its linked
scales delta_i start at N^(-1/2), satisfy delta_i<=A, cover [0,A]
together with the small-alpha interval, and obey sum(delta_i)<=2*A.
If A is below the first scale, direct integral monotonicity applies.
The integration theorem consumes the actual R(N,delta_i), not a
separately supplied surrogate integral.

`sargosSixthBaseMoment_power_bootstrap` chooses C>=1 before
beta and B. For beta,B>=0, a genuine upstream bound
I(M)<=B*M^beta for every natural M>=1 implies, for N>=16 and
0<A<=1/4,

```text
I(N) <= C*((1+log N)^5/A + B*(log N)^6*(4*A*N)^beta).
```

Both rounded moment scales are explicitly bounded by 4*A*N in this
consumer. The upstream power bound is an explicit, narrower input:
it is used at those smaller linked moments. It is not a premise
equivalent to the bootstrap conclusion.
`sargosSixthBaseMoment_cubic_bootstrap` discharges that input using
the proved trivial estimate. Separately,
`sargosSixthBaseMoment_sqrt_bound` consumes the actual small-alpha
estimate and localization to prove for natural N>=4

```text
I(N) <= (1024*44845498368)*sqrt(N)*(1+log N)^5.
```

Seven modules are installed: `SargosQuarticBoundedScale`,
`SargosQuarticBoundedMoment`, `SargosSixthLocalization`,
`SargosDyadicIntegral`, `SargosSixthDyadicBudget`,
`SargosSixthPowerBootstrap`, and `SargosSixthBootstrapInputs`.
All 18 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen additional fixtures cover threshold scales,
the bounded-range constant, empty/nonempty dyadic sums, the source
scale budget, negative/zero integration cases, localization,
small-alpha and square-root estimates, and actual source consumers.

This advances [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
The finite-scale bootstrap is proved; the epsilon-quantified exponent
improvement and its iteration are not yet proved. The exact real-scale
convention and C-process also remain open. The integer m is not
identified with 2*Delta*N. Aggregate checklist states, the permanent
counterexample, corrected powering and all nine Add-est clauses
remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 895 production files, 1,369 scanned Lean
  files and 10,227 build jobs. The audit covers 7374 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13619 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-061935-4e284490.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_062253.log)
  and [manifest](../../logs/foundation_freeze_20260923_062253.json).
- All 1,390 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-bounded-bootstrap-20260923-061935-4e284490.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 335 nodes and 894 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos natural-scale maximal sixth moment — previous checkpoint

The global recurrence and its iteration are now proved for the actual
natural-scale quartic moment. The public source-facing consumer
`sargosQuartic_maximal_sixth_moment` proves:

```text
For every epsilon>0 there is C>=1, chosen before N,z,lambda,c,d,
such that for every natural N>=2, |z(n)|<=1 on N<n<=2N,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(0<=H<=N)|Sum_(N<n<=N+H) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The maximum, coefficients, integer prefixes and Bochner integrals
are the actual previously defined objects. No moment estimate,
recurrence, exponent iteration or epsilon-loss bound is assumed
in this final theorem.

The finite-scale bootstrap is optimized at
A=(1/4)*N^(-beta/(1+beta)). Its admissibility is proved uniformly,
including beta=0. Exact real-power identities give the improved
exponent beta/(1+beta). The global logarithm estimate

```text
(1+log x)^6 <= (1+6/epsilon)^6*x^epsilon,    x>=1, epsilon>0
```

discharges the loss without an eventual-threshold assumption.
`SargosSixthMomentExponent beta` records the actual
epsilon-quantified estimate, with the constant chosen before N.
`sargosSixthMomentExponent_step` proves the genuine implication
from beta to beta/(1+beta), and explicitly handles all small N.

The proved trivial exponent 3 initiates the sequence
beta_n=3/(1+3*n). Its exact recurrence and arbitrarily small values
yield `sargosSixthBaseMoment_subpolynomial`:
for every epsilon>0, I(N)<=C*N^epsilon for every natural N>=1.
The final weighted maximal theorem consumes this bound and the
completed source-height strip transfer, then absorbs its logarithm.
The stronger square-root initial estimate remains available.

Six modules are installed: `SargosSixthExponentAlgebra`,
`SargosSixthLogAbsorption`, `SargosSixthOptimizedBootstrap`,
`SargosSixthMomentExponents`, `SargosSixthMomentIteration`,
and `SargosSixthMomentTheorem`. All 15 public theorems have
exact-signature regressions and explicit axiom audits.
Fourteen additional fixtures check zero-exponent parameters,
exact successive exponents, logarithmic absorption at x=1,
iteration outputs, subpolynomial bounds and the actual weighted
maximal integral at the smallest permitted natural block N=2.

This is the natural-block form of the sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not yet replace natural block endpoints by arbitrary real
scales. That real-scale bridge, the exact real-scale Lemma 5
convention, and the C-process remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 901 production files, 1,375 scanned Lean
  files and 10,233 build jobs. The audit covers 7402 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13647 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-063351-3ad01f0f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_063758.log)
  and [manifest](../../logs/foundation_freeze_20260923_063758.json).
- All 1,396 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-natural-sixth-theorem-20260923-063351-3ad01f0f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 338 nodes and 897 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos real-scale maximal sixth moment — previous checkpoint

The source-facing theorem `sargos_source_maximal_sixth_moment`
now proves the weighted maximal sixth-moment estimate at arbitrary
real scales, with the actual maximum over real endpoints:

```text
For every epsilon>0 there is C>=1, chosen before M,z,lambda,c,d,
such that for every real M>=2, |z(n)|<=1 on M<n<=2M,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(M<X<=2M)|Sum_(M<n<=X) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*M^(3+epsilon)+M^epsilon).
```

The endpoint maximum is the supremum of the literal integer sums
over the real interval M<X<=2M. Its equality to a finite prefix
maximum and its attainment are proved, not assumed.
The coefficient condition is stated on the physical interval
M<n<=2M. The double integral is the actual Bochner integral.
No moment estimate or endpoint bridge is a hypothesis of the
final theorem.

With m=floor(M), the real block has m or m+1 terms. The literal
prefix comparison gives Max_real<=Max_natural+1, including the
possible extra upper-endpoint term. The sixth-power bound
Max_real^6<=32*(Max_natural^6+1) is integrated over the actual
rectangle; the constant contribution is exactly lambda.
Continuity and the needed product, inner and outer integrability
are proved. Monotonicity of real powers transfers the completed
natural-scale theorem from m to M and absorbs the extra lambda.
The final uniform constant is 32*(C_natural+1).

Seven modules are installed: `SargosRealQuarticBlock`,
`SargosRealQuarticPrefix`, `SargosRealQuarticRegularity`,
`SargosRealQuarticMomentTransfer`, `SargosRealSixthMomentTheorem`,
`SargosRealQuarticEndpoints`, and `SargosSourceSixthMoment`.
All 22 public theorems have exact-signature regressions and
explicit axiom audits. Fourteen additional fixtures check
integer and noninteger scales, the strict left and closed right
endpoints, both possible block lengths, zero prefixes, attained
real maxima, translated rectangles, zero-height integration and
the source theorem at M=5/2.

This realizes the source maximal sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not claim the separate exact real-scale Lemma 5 convention,
nor Sargos's C-process. Those remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 908 production files, 1,382 scanned Lean
  files and 10,240 build jobs. The audit covers 7445 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13690 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-070029-00a8fc3c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_070350.log)
  and [manifest](../../logs/foundation_freeze_20260923_070350.json).
- All 1,403 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-sixth-theorem-20260923-070029-00a8fc3c.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 341 nodes and 901 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos initial-interval moments and uniform sextuple count — previous checkpoint

`sargos_initial_sextuple_count` proves the actual source count:

```text
For every epsilon>0 there is C>=1, chosen before N and c,
such that for every natural N>=1 and every real c,

 #{(n,n') in {1,...,N}^3 x {1,...,N}^3 :
     sum_i n_i^2 = sum_i n'_i^2,
     c <= sum_i n_i^4-sum_i n'_i^4 <= c+N^3}
 <= C*N^(3+epsilon).
```

Triples are literal functions from Fin 3 to the integer interval
1<=n<=N. Their square and fourth-power sums are integer sums;
ordered pairs retain all multiplicities. Both window endpoints
are closed. The theorem's constant is uniform in the real shift c.
This realizes [Sargos 2003, Lemma 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82873).

The stronger theorem `sargosInitialSextupleWindow_card_bound`
allows every positive width B and proves
card<=C*(N^3+B)*N^epsilon, uniformly in N,B,c.
No count estimate is assumed.

The initial-interval moment is also proved. The actual dyadic
decomposition separates {1,2} and the blocks (2^i,2^(i+1)].
A finite sixth-power inequality is integrated with all needed
integrability established. Literal zero-padding transfers an
arbitrary N to a power-of-two P with N<=P<=2N. The dyadic count's
sixth power is absorbed by a proved logarithmic/epsilon bound.
`sargosInitialQuartic_sixth_moment` gives, uniformly in bounded
coefficients and translated windows,

```text
Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
 |Sum_(1<=n<=N) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The shift-uniform count does not assume a translation principle.
The shifted tent-kernel Gram identity is proved with its actual
character factor. Taking the norm of the integral bounds it by
the same central unshifted moment. The actual tuple-power
expansion and source-window inclusion then give the count.

Ten modules are installed: `SargosInitialInterval`,
`SargosInitialRegularity`, `SargosInitialMomentTransfer`,
`SargosInitialDyadicMoment`, `SargosInitialTruncation`,
`SargosInitialSixthMoment`, `SargosShiftedTentGram`,
`SargosShiftedNearCount`, `SargosInitialMomentTuples`,
and `SargosInitialSextupleCount`. All 33 public theorems have
exact-signature regressions and explicit axiom audits.
Eighteen additional fixtures cover empty and non-dyadic intervals,
zero-padding at and beyond the endpoint, dyadic decomposition,
zero-height integration, exact tuple multiplicities, empty and
closed-endpoint shifted windows, arbitrary real shifts, and
the actual N=1 and N=3 moment/count consumers.

The real-scale maximal moment remains complete. Sargos's
symmetric differencing inequality, Taylor-remainder assembly,
A-bar-four inequality and C-process remain open. The separate
exact real-scale Robert–Sargos Lemma 5 convention also remains
open. No aggregate checklist item changes status. Preserve
the permanent counterexample, corrected powering and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 918 production files, 1,392 scanned Lean
  files and 10,250 build jobs. The audit covers 7506 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13751 total).
  All 33 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-072955-0a22d012.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_073326.log)
  and [manifest](../../logs/foundation_freeze_20260923_073326.json).
- All 1,413 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-initial-sextuple-20260923-072955-0a22d012.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 344 nodes and 906 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos finite symmetric differencing — previous checkpoint

`sargos_finite_sextuple_differencing` now proves the actual finite
polynomial estimate. For arbitrary complex coefficients a and natural
1<=H<=M, let Phi be a on the integer interval 0<=m<M and zero elsewhere.
Set S=sum Phi(m), E=sum |Phi(m)|^2 and

```text
Q = sum_(t,t' in {1,...,H}^3, s2(t)=s2(t'))
      |sum_(0<=m<M)
         product_i Phi(m+t_i)Phi(m-t_i)
         * conjugate(product_i Phi(m+t'_i)Phi(m-t'_i))|.

|S|^12 <= 1492992*(M/H)^6*E^6
           + 382205952*(M^11/H^4)*Q.
```

All tuples are literal ordered triples, their square frequencies are
integer sums, and Q retains every square-diagonal sextuple and its
multiplicity. The theorem assumes no differencing estimate, Gram identity,
moment bound or analytic certificate.

The proof starts with actual even shifts, finite Cauchy and exact
parity fibers. The square is nonconjugated at this stage. Negative
offsets pair with positive offsets, leaving the actual diagonal term.
Zero-padding support and center translation are proved. A finite maximum
selects an actual parity fiber. Cubing expands into literal triples;
Holder and the exact frequency Gram identity give the sixth-power bound.
Conjugation appears between the two triples in that Gram identity.
Finally, the parity indicators are removed by a proved termwise majorant,
so the public endpoint has no parity witness or restriction.

This is the polynomial finite input corresponding to
[Sargos 2003, Section 3.2](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The paper's one-based interval convention has not yet been bridged in
this consumer. The exact printed Lemma 1 maximum is not claimed: the
proved parity-fiber variant supplies the downstream finite inequality
directly. The source index bridge, Taylor-remainder assembly, derivative
bounds, phase/support identification, witness selection, A-bar-four
inequality and C-process remain open. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Eleven modules are installed: `SargosSymmetricAveraging`,
`SargosSymmetricFibers`, `SargosSymmetricPositive`,
`SargosSymmetricSupport`, `SargosSymmetricDifferencing`,
`SargosFiniteFrequencyGram`, `SargosGroupedSecondMoment`,
`SargosSymmetricTriples`, `SargosSymmetricSixth`,
`SargosSymmetricTwelfth` and `SargosSextupleMajorant`.
All 42 public theorems have exact-signature regressions and explicit
axiom audits. Eighteen additional fixtures cover support endpoints,
empty intervals, odd/even parity fibers, genuinely nonconjugated
squaring, Gram conjugation, empty tuple types, diagonal multiplicities
and the actual H=1 and (M,H)=(3,2) consumers.

The completed shift-uniform sextuple count and real-scale maximal
sixth moment are preserved. No aggregate checklist item changes
status. Preserve the permanent counterexample, corrected powering
and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 929 production files, 1,403 scanned Lean
  files and 10,261 build jobs. The audit covers 7596 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13841 total).
  All 42 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-080954-241e9fff.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_081351.log)
  and [manifest](../../logs/foundation_freeze_20260923_081351.json).
- All 1,424 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-symmetric-differencing-20260923-080954-241e9fff.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 346 nodes and 909 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos source Taylor and interior reduction — previous checkpoint

`sargos_character_interior_differencing` proves a source-indexed
estimate for the actual character sum. For every epsilon>0 there is
C>=1, chosen before natural H>=1, M>=H and the real phase f, such that

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qinterior
    + C*M^11*H^epsilon.
```

Qinterior is the actual sum over all ordered pairs of triples in
{1,...,H}^3 with equal integer square sums. Each term is the norm
of the character sum over the open integer interval
(radius+1, M-radius), where radius is the maximum of all six
offsets. Its phase is exactly

```text
(s4(t)-s4(t'))/12 * f^(4)(m) + u(t,t',m),
u(t,t',m) = sum_i v(t_i,m) - sum_i v(t'_i,m).
```

The one-based source bridge is proved: sums, zero-padding, triples
and full sextuple correlations are translated exactly from the
previous zero-based finite theorem. No source-index convention
remains assumed in this consumer.

The actual symmetric residual v is defined from f(m+n)+f(m-n)
minus its constant, quadratic and quartic terms. Its degree-five
Taylor cancellation and genuine integral representation are proved:

```text
v(n,m) = (1/120) * integral_0^n
           [f^(6)(m+t)+f^(6)(m-t)]*(n-t)^5 dt.
```

Under local smoothness of the original phase on the actual segment,
the proved bound is |v(n,m)|<=B*n^6/360 when |f^(6)|<=B there.
Iterated derivatives commute with this constructed remainder.
The literal six-term residual satisfies
|u^(j)(m)|<=B*H^6/60 when the original (j+6)-th derivative is bounded
by B on the sextuple's actual maximum-offset segment. The local
radius theorem is obtained by an exact retyping of the same
coordinates; it does not enlarge the required phase domain.
A source-interior consumer uses only smoothness and original
derivative bounds inside (1,M).

The actual padded products have precisely the closed support
[radius+1,M-radius]. Their character phase, including conjugation
between the two triples and cancellation of the quadratic term,
is proved. Removing its endpoints costs at most two unit terms,
including empty, reversed and singleton intervals. The full
square-diagonal cardinality bound is proved from the earlier
width-general sextuple count, giving O_epsilon(H^(4+epsilon)).
This controls the aggregate boundary error in the displayed
interior estimate. No boundary smoothness or global remainder
extension is assumed.

These are the source-indexed polynomial differencing input and
local Taylor/phase steps for
[Sargos 2003, Sections 3.2–3.3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The global remainder extension, quartic-window witness/prefix
selection, A-bar-four theorem and C-process remain open.
The Taylor lemmas use local C-infinity hypotheses, as available
for the intended model phases; the paper's separate finite-C^k
formulation is not claimed complete. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Thirteen modules are installed: `SargosSourceDifferencing`,
`SargosSymmetricTaylor`, `SargosSymmetricTaylorJets`,
`SargosTaylorIntegral`, `SargosSymmetricTaylorIntegral`,
`SargosSextupleRemainder`, `SargosSextuplePhase`,
`SargosTupleSupport`, `SargosSourceSextuplePhase`,
`SargosSextupleRadiusJets`, `SargosSquareDiagonalCount`,
`SargosSextupleEndpoints` and `SargosInteriorDifferencing`.
All 50 public theorems have exact-signature regressions and
explicit axiom audits. Twenty additional fixtures check source
endpoints and translation, zero/constant/quartic/sextic Taylor
cases, the zero-height integral, derivative order zero, diagonal
phase cancellation, actual singleton/empty supporting intervals,
coincident/reversed endpoints, the H=1 count, and the actual
(M,H)=(3,2) interior consumer.

The earlier sixth moments, shifted sextuple count and finite
symmetric differencing are preserved. No aggregate checklist
item changes status. Preserve the permanent counterexample,
corrected powering and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 942 production files, 1,416 scanned Lean
  files and 10,274 build jobs. The audit covers 7702 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13947 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-084446-824cd661.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_084836.log)
  and [manifest](../../logs/foundation_freeze_20260923_084836.json).
- All 1,437 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-taylor-20260923-084446-824cd661.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 350 nodes and 914 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos smooth remainder extension — previous checkpoint

`sargos_smooth_extended_reduction` constructs the smooth remainder
family used in the actual source-indexed finite reduction. For each
finite order Q and epsilon>0, one C>=1 is chosen before H, M, the
phase f and the original-derivative bound B. For 1<=H<=M, B>=0,
local C-infinity regularity on (1,M), and

```text
|f^(j+6)(y)| <= B/M^j   (y in (1,M), 0<=j<=Q+1),
```

the constructed physical extension U_q satisfies, for every actual
ordered sextuple q,

```text
U_q is globally C-infinity;
U_q(m) = u_q(m) at every integer radius+1 < m < M-radius;
|U_q^(j)(x)| <= C*B*H^6/(60*M^j)  (0<=x<=M, 0<=j<=Q).
```

Here u_q is the actual six-term symmetric Taylor remainder, not a
freely supplied function. The construction normalizes it as
u_q(M*x), proves the local affine derivative identity, and derives
its jets from the original phase. With l=(radius+1)/M,
r=(M-radius)/M and h=1/(8M), the actual nonempty integer support
proves l+4h<r. Every retained integer m has m/M in the agreement
plateau [l+2h,r-2h]. Both Taylor anchors lie within distance one
of the observation interval [0,1]. The existing Taylor-pasted
construction therefore gives genuine global smoothness and
uniform finite-order bounds, even as the buffer shrinks.
The zero branch is tied to an empty actual integer support.

Exact phase and sum identities replace u_q by U_q inside every
retained character sum, with all ordered sextuple multiplicities
unchanged. The assembled theorem also proves

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qextended
    + C*M^11*H^epsilon.
```

Qextended is defined using the actual interior character sums
with phase (s4(t)-s4(t'))*f^(4)(m)/12+U_q(m).
The common C controls both the extension and the boundary error.
The original phase bounds are explicit narrower analytic inputs;
no global remainder certificate, extension existence, agreement
condition or final sum estimate is assumed.

This closes the C-infinity, finite-order uniform-constant extension
consumer. It does **not** close the printed finite-C^k,
constant-one remainder statement or the A-bar-four witness theorem
in [Sargos 2003, Section 3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The construction uses original jets through Q+7. The physical
model-phase input still needs its consumer, followed by signed
quartic-window counting, witness/prefix selection, optimization
and the C-process. The separate exact real-scale Robert–Sargos
Lemma 5 convention also remains open.

Eight modules are installed: `SargosLocalAffineJets`,
`SargosRemainderLocalSmooth`, `SargosNormalizedRemainder`,
`SargosRemainderGeometry`, `SargosRemainderExtension`,
`SargosPhysicalRemainderExtension`, `SargosExtendedSextuplePhase`
and `SargosSmoothExtendedReduction`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Sixteen
additional fixtures check zero/negative affine scaling, the
M=0/1 buffer conventions, empty and singleton integer interiors,
exact agreement, zeroth derivatives, a genuinely nonzero sextic
remainder (-15120), zero original-phase bounds and an empty
actual correlation.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 950 production files, 1,424 scanned Lean
  files and 10,282 build jobs. The audit covers 7755 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14000 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-091416-0a8b1879.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_091748.log)
  and [manifest](../../logs/foundation_freeze_20260923_091748.json).
- All 1,445 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-remainder-extension-20260923-091416-0a8b1879.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 353 nodes and 920 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos actual transformed model — previous checkpoint

The actual approximate model phase now supplies the remainder
extension's original-derivative hypotheses. The finite budget
D(sigma,Q)=1+sum_(p<Q+7) modelPhaseJetCoefficient(sigma,p)
depends only on the fixed model parameter and requested order.
For a source phase T*F((A+x)/N), N<=A and A+M<=2N imply M<=N.
Closed-interval model data through order Q+6, with delta<=1,
therefore gives

```text
|f^(j+6)(x)| <= (D(sigma,Q)*|T|/N^6)/M^j
  (1<x<M, 0<=j<=Q+1).
```

Local regularity is derived inside the physical interval; no
exterior smoothness of F is assumed. The theorem
`sargos_model_smooth_reduction` consumes this real-scale source
phase in the constructed extension and finite sum reduction.

The transformed-model branch is proved for the natural full
dyadic block, f(x)=T*F(1+x/M), M>=1. Put
D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0 and
T1=tau*T*D4/M^4. The normalized fourth derivative is defined
using **within-derivatives on the closed interval [1,2]**.
Its smoothness, derivative composition, falling-factorial identity
and exact model-error scaling are proved at both endpoints,
giving parameter sigma+4 and error delta/D4.

The actual globally smooth extension U_q is rescaled as
U_q(M*(u-1))/T1 and added to this fourth-derivative model.
`sargosTransformedModel_approximate` proves that, for each
sigma>0 and finite P, one C>=1 chosen before all physical data
gives the closed-interval model error

```text
(delta + C*H^6/(tau*M^2))/D4.
```

The source model order is P+7, the extension order is P+1,
and tau,T are positive. The correction estimate consumes the
constructed remainder's actual jets. No transformed-model
predicate or global remainder bound is assumed.

Exact physical entry is proved, not just an exponent inequality:

```text
T1*G(1+x/M) = tau*f^(4)(x)+U_q(x)  (0<x<M).
```

The source sextuple phase and its character sum are identified
with this expression at every actual interior integer.
`sargos_positive_sextuple_model` sets tau to the actual positive
quartic difference divided by 12 and returns both the approximate
model and the exact source-sum identity. A further proved
inequality gives H^6/(tau*M^2)<=eta from tau>=H^3 and
H^3/M^2<=eta.

This is the actual-model input for
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Signed quartic-window counting, the general subinterval/real-scale
transformed-model bridge, witness/prefix selection, optimization
and the C-process remain open. The natural full-block transformed
consumer is not claimed to cover arbitrary real-scale subintervals.
The printed finite-C^k constant-one A-bar-four formulation and
separate exact real-scale Robert–Sargos Lemma 5 convention
also remain open.

Eight modules are installed: `SargosModelRemainderJets`,
`SargosModelSmoothReduction`, `SargosWithinDerivativeCalculus`,
`SargosFourthDerivativeModel`, `SargosPhaseCorrection`,
`SargosTransformedModel`, `SargosTransformedSource` and
`SargosPositiveSextupleModel`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Eighteen
additional fixtures cover the fourth coefficient at sigma=0,1,2,
both closed endpoints, the exact reference primitive, derivative
order zero, zero/constant/quadratic corrections, physical time
normalization, zero frequency, a genuine square-diagonal sextuple
with quartic difference 144, the large-frequency threshold and
an actual transformed reference-model consumer.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 958 production files, 1,432 scanned Lean
  files and 10,290 build jobs. The audit covers 7821 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14066 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-094310-2a298bd0.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_095000.log)
  and [manifest](../../logs/foundation_freeze_20260923_095000.json).
- All 1,453 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-transformed-model-20260923-094310-2a298bd0.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 356 nodes and 926 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos real-scale source consumer — previous checkpoint

The transformed model now covers arbitrary admissible real scales
N>=1 and natural source windows [a,a+M] inside [N,2N].
There is no assumption that M is comparable to N. The original
physical phase is f(x)=T*F((a+x)/N), and its actual derivative
bounds retain N in every denominator.

The six-term Taylor remainder is normalized by N, extended with
the existing Taylor-pasting construction, and pulled back to a
globally smooth U_q. It agrees at every actual interior integer.
The proved jets hold on the two-sided physical observation
interval [-N,N], which is essential because N*u-a can be negative
even when u belongs to the canonical closed interval [1,2].
For each fixed model parameter and finite order, one constant
is chosen before all source scales, phases and sextuples.

With D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0,
the actual transformed time and model are

```text
T1 = tau*T*D4/N^4,
G(u) = F^(4)_within(u)/D4 + U_q(N*u-a)/T1,
model error <= (delta + C*H^6/(tau*N^2))/D4.
```

All derivatives and model bounds on [1,2] include both closed
endpoints. The original source order is P+7, and the constructed
extension uses order P+1. No regularity of F outside its source
interval is assumed.

Both signs of the actual quartic difference are handled by
swapping the two ordered triples when necessary. This preserves
the radius and exact integer support, negates the actual source
phase, and conjugates its character sum. Its norm is therefore
unchanged. The oriented frequency is exactly the absolute
integer quartic difference, and tau=abs(difference)/12.
Orientation is not used to collapse the counting set: all ordered
sextuple multiplicities remain available to subsequent estimates.

The source-entry bridges are now explicit kernel-checked identities.
The original closed natural interval sum is its one-based integer
source sum plus one endpoint character, with norm loss exactly 1.
For each nonempty actual inner support, translation by a gives
the exact natural closed interval with endpoints
a+R+2 and a+M-R-1. Its dyadic scale conditions are derived from
N<=a and a+M<=2N. Empty supports are treated as the actual empty
sum, not substituted for nonempty source objects.

The public consumer `sargos_large_frequency_exponentPair_bound`
uses an existing genuine exponent pair (k,l), sigma>0 and epsilon>0.
It chooses delta>0, source order P>=1, eta>0 and C>=1 before
all physical inputs. For the original phase model, 1<=H<=M,
N>=1, N<=a, a+M<=2N, T>0 and

```text
tau = abs(actual quartic difference)/12 >= H^3,
H^3/N^2 <= eta,
```

it proves the actual interior source-sum norm is at most

```text
C*((T1/N)^(k+epsilon)*N^(l+epsilon) + N/T1).
```

The proof derives the transformed model error, both-sign identity,
natural interval and scale conditions, then invokes the existing
all-positive-height exponent-pair theorem. None of those bridges,
nor the desired transformed-sum bound, is an assumed certificate.
This is a consumer of an upstream exponent pair, not yet a proof
of the new C-transformed exponent pair.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Remaining EPZAE-10 work is actual signed-window aggregation,
including the reciprocal-frequency term, finite C-process
assembly and optimization. The printed A-bar-four witness/prefix
selection, finite-C^k constant-one formulation and separate exact
real-scale Robert–Sargos Lemma 5 convention remain open.

Thirteen production modules are installed: `SargosScaledRemainder`,
`SargosScaledRemainderGeometry`, `SargosScaledRemainderExtension`,
`SargosScaledPhysicalRemainder`, `SargosScaledModelRemainder`,
`SargosAffinePhaseCorrection`, `SargosScaledTransformedModel`,
`SargosScaledTransformedSource`, `SargosSourceModelEntry`,
`SargosSextupleOrientation`, `SargosOrientedModelSource`,
`SargosInnerModelEntry` and `SargosLargeFrequencyModelBound`.
All 46 public theorems have exact-signature regressions and explicit
axiom audits. Twenty-two further fixtures cover non-integer scales,
negative physical arguments, correction derivatives, time scaling,
zero frequency, source singleton/endpoint behavior, an actual
positive and negative quartic difference, square-diagonal membership,
conjugation, empty and singleton inner supports, the genuine empty
extension branch and large-frequency error thresholds.

No aggregate checklist item changes status. The permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 971 production files, 1,445 scanned Lean
  files and 10,303 build jobs. The audit covers 7938 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14183 total).
  All 46 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-101936-e5b0e215.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_102331.log)
  and [manifest](../../logs/foundation_freeze_20260923_102331.json).
- All 1,466 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-scale-source-20260923-101936-e5b0e215.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 360 nodes and 935 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos finite closed-source inequality — previous checkpoint

The actual signed-frequency aggregation and finite C-process
inequality are proved. All ordered sextuple multiplicities are
retained; orienting a phase never replaces the counting set by
its image.

The small-frequency set has absolute quartic difference at most
12*H^3. It lies in the actual signed window [-12*H^3,12*H^3],
so the proved shifted-window theorem gives cardinality at most
C_epsilon*H^(3+epsilon). Its actual inner character sum has norm
at most M, derived from the literal integer support.

For large frequencies, the absolute difference is at most 3*H^4.
Every such sextuple is covered by an actual window

```text
j*H^3 <= abs(difference) <= (j+1)*H^3,
1 <= j <= 3*H.
```

The index is the natural floor of abs(difference)/H^3.
Each absolute window is contained in two actual signed windows.
The proved finite cover inequality permits overlapping endpoints
only through nonnegative overcounting; no disjointness or omitted
multiplicity is assumed. Each window's reciprocal contribution is
controlled by its actual count and 12/(j*H^3).
The harmonic-sum estimate and an explicit logarithmic-loss bound
therefore give

```text
sum_(large ordered sextuples) 12/abs(difference)
  <= C_epsilon * H^epsilon.
```

This avoids the extra factor H produced by using only the full
diagonal count and the lower frequency threshold.

The actual all-positive-height exponent-pair consumer is summed
over this set. The quartic frequency is explicitly linked to both
terms: tau<=H^4 controls the main term, while the exact identity
N/T1=(N^5/(D4*T))*(12/abs(difference)) supplies the secondary term.
The small and large sets form a proved disjoint partition of the
original square-diagonal set.

The public theorem `sargos_finite_closed_model_process` consumes
an actual exponent pair (k,l), sigma>0 and epsilon>0. It chooses
delta>0, P>=1, eta>0 and C>=1 before all physical inputs.
For the original model F, real N>=1, T>0, N<=a, a+M<=2N,
1<=H<=M and H^3/N^2<=eta, it proves

```text
norm(exponentialSumAt F T N a (a+M))^12
 <= C * H^epsilon *
    [ N^12/H
      + N^11*(D4*T*H^4/N^5)^(k+epsilon)*N^(l+epsilon)
      + N^16/(D4*T*H^4) ],
D4 = sigma*(sigma+1)*(sigma+2)*(sigma+3).
```

This is the exact original closed natural sum, not a generic
majorant or a separately assumed transformed estimate.
The proof consumes the actual full correlation bound and
twelfth-power differencing theorem, derives M<=N, and absorbs
the single endpoint character with a proved twelfth-power bound.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The finite inequality is not yet the C-transformed exponent pair.
Actual integer-H selection, short-window and low-height branches,
epsilon bookkeeping and final exponent-pair assembly remain open.
The printed A-bar-four witness/prefix selection, finite-C^k
constant-one formulation and separate exact real-scale
Robert–Sargos Lemma 5 convention remain distinct open obligations.

Ten production modules are installed: `SargosFrequencyWindows`,
`SargosFrequencyWindowCover`, `SargosReciprocalFrequency`,
`SargosSmallFrequencyContribution`, `SargosFrequencyScaleBounds`,
`SargosLargeFrequencyContribution`, `SargosModelCorrelationBound`,
`SargosFiniteProcessAlgebra`, `SargosFiniteModelProcess` and
`SargosFiniteClosedProcess`.
All 26 public theorems have exact-signature regressions and explicit
axiom audits. Twenty additional fixtures cover zero/positive/negative
frequencies, actual large square-diagonal sextuples with quartic
difference plus or minus 2,108,304, their distinct ordered identities,
the correct width-H^3 bin and excluded adjacent bin, exact tau,
empty source support, zero weights and finite-scale arithmetic.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 981 production files, 1,455 scanned Lean
  files and 10,313 build jobs. The audit covers 7992 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14237 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-105350-e615b783.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_105812.log)
  and [manifest](../../logs/foundation_freeze_20260923_105812.json).
- All 1,476 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-finite-closed-process-20260923-105350-e615b783.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 363 nodes and 941 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Exact analytic C-process — previous checkpoint

EPZAE-10 is complete: the genuine analytic exponent-pair predicate is
preserved by all three exact A/B/C formulas. The new public theorem is

```text
ExponentPair.cProcess :
  ExponentPair k l ->
  ExponentPair (k/(12*(1+4*k)))
               ((11*(1+4*k)+l)/(12*(1+4*k))).
```

Its only mathematical input is the original exponent pair. It does not
assume a transformed estimate, optimized majorant or desired output pair.
The source formula is the C-process in the frozen paper's
`exp-process` lemma, citing
[Sargos 2003, Theorem 5](https://www.impan.pl/shop/publication/transaction/download/product/82873).

The proof now links every optimization variable to the original physical
parameters. With

```text
t0 = (5+15*k+5*l)/(2+3*k),
R = (T/N)^(-k/(1+4*k)) * N^((1+4*k-l)/(1+4*k)),
(Kc,Lc) = C(k,l),
```

Lean proves the exact balance identity and
`N^12/R = ((T/N)^Kc*N^Lc)^12`. In the high-height range
`N^t0 <= T`, the actual optimum satisfies
`R <= N^(2/3-1/100)` and `N^(13/3) <= T*R^3`.
A derived initial threshold makes the finite-process smallness and
secondary-term conditions hold. When `2 <= R <= M`, the proof selects
the actual natural integer `H = floor(R)`, proves `R/2 <= H <= R`,
and consumes `sargos_finite_closed_model_process` with every condition
discharged. The main and secondary terms, rounding loss and all epsilon
powers are bounded by the target twelfth power.

When `M < R` or `R < 2`, the literal closed source sum is controlled
by its actual `M+1` terms. For low heights `N <= T <= N^t0`,
three applications of the proved A-process to the genuine classical
pair `(1/2,1/2)` yield `(1/30,26/30)`; an exact threshold identity
compares its bound to the C-process target. Small N is absorbed into
a uniform constant, and reversed or singleton natural intervals are
handled with their actual source semantics.

`isExponentPairEstimateNonAsymptotic_cProcess` assembles all branches.
For every epsilon>0 and sigma>0, it chooses delta>0, derivative order
P>=1 and C>=1 before the phase, real scales and natural endpoints.
The existing non-asymptotic equivalence then gives
`ExponentPair.cProcess`. Neither a comparable-length source interval
nor a lower bound on k is imposed; k=0 remains included.

The printed A-bar-four witness/prefix-selection statement, its
constant-one finite-C^k formulation, and the separate exact real-scale
Robert–Sargos Lemma 5 convention are **not claimed as proved**.
They were previously listed as possible intermediate routes. The
implemented route instead uses the proved summed finite inequality and
the natural-rounded moment reduction. These unused stronger or
different-convention intermediates are not additional requirements of
EPZAE-10's unchanged acceptance test: the exact analytic C transformation
itself is now proved.

Fourteen production modules carry this final assembly:
`SargosCProcessParameters`, `SargosClassicalLowHeight`,
`SargosCProcessScale`, `SargosCProcessHighScale`,
`SargosCProcessLowComparison`, `SargosCProcessThresholds`,
`SargosCProcessIntegerChoice`, `SargosCProcessMainBalance`,
`SargosCProcessTrivialBranches`, `SargosCProcessMainError`,
`SargosCProcessBoundBudget`, `SargosCProcessTargetBudget`,
`SargosCProcessHighSource` and `ExponentPairCProcess`.
All 44 public theorems have exact-signature regressions and explicit
axiom audits. Another 22 fixtures check actual analytic output pairs
`(1/72,67/72)` and `(1/408,50/51)`, triangle boundaries, exact height
thresholds, zero-k scales, nonintegral rounding, empty/singleton source
intervals, zero epsilon and the low-height comparison.

Only EPZAE-10 changes aggregate status. EPZAE-11's D-process, remaining
beta-table rows, four advertised new pairs, zeta-growth/density bridges
and whole-project release remain open. These two auxiliary C-images
are not the four advertised `new-exp-pair` outputs.

Preserve the permanent counterexample, corrected two-witness powering,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 995 production files, 1,469 scanned Lean
  files and 10,327 build jobs. The audit covers 8,051 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,296 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-112323-d2b42d66.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_112654.log)
  and [manifest](../../logs/foundation_freeze_20260923_112654.json).
- All 1,490 physical proof/configuration/tooling hashes are identical
  before and after both runners. The fourteen modules and four
  integration files also have recorded normalized hashes. Full evidence
  is in the [checkpoint JSON](logs/tao-trudgian-yang-exact-c-process-20260923-112323-d2b42d66.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 365 nodes and 945 edges, with no duplicate/missing endpoints
or unclassified nodes. Of 42 aggregate checkbox states, only EPZAE-10
changes to checked (23 checked). Every other state is preserved.
The whole-proof goal remains open.

## Native Heath-Brown exponent-pair family — previous checkpoint

The complete native Heath–Brown family is now proved for every integer
k>=3, with the exact source formula:

```text
exponentPair_heathBrown :
  3 <= k ->
  ExponentPair (2/((k-1)^2*(k+2)))
               (1-(3*k-2)/(k*(k-1)*(k+2))).
```

The input is the natural derivative order, not an assumed exponent pair,
derivative theorem or optimization certificate. The proof consumes the
already kernel-checked native kth-derivative theorem through
`isExponentSumBoundNonAsymptotic_heathBrown`.
The source is Heath–Brown,
[A new k-th derivative estimate for exponential sums via Vinogradov's mean value](https://arxiv.org/abs/1601.04493),
Theorem 2 and its proof, as frozen locally at v3. The arbitrary source
epsilon is already represented in the actual beta/exponent-pair
definitions; no fixed positive epsilon is left in the public pair.

For alpha in (0,1/2], set tau=1/alpha. The proof constructs an actual
natural j>=3 satisfying

```text
((j-1)^2+1)/j <= tau <= (j^2+1)/(j+1).
```

The construction uses the least natural index with a sufficient upper
endpoint and proves the lower endpoint from minimality. It does not
assume a cover or an order-selection oracle. Exact adjacent identities
and decreasing secant slopes prove that the selected local secant lies
below every fixed family secant. All three actual derivative-error
exponents are bounded on the selected interval. The reciprocal-scale
identity links these exponents to the native beta bound.

At alpha=0, the proved beta endpoint supplies the result. The new
`exponentPair_of_beta_bound_half` uses the already-proved exact
reflection identity and the candidate slope condition l-k>=1/2 to
supply the other half of the closed unit interval. The family satisfies
the entire exponent-pair triangle, including all boundary requirements.
The existing closed duality theorem then gives the actual analytic
exponent pair.

The separate D-transform work is deliberately narrower:
`SargosDProcessGeometry` proves denominator positivity, triangle and
slope, exact zero/half endpoint gaps, and the secondary-line comparison.
`sargosDProcess_pair_of_beta_bound` is **conditional** on its explicitly
displayed source beta estimate. It derives an exponent pair using
half-interval duality when 5*k-3*l+2>=0 and k+3*l>=2.
It is not a proof of the analytic D-process, nor of the Bourgain input
pair. In particular, the source's maximum cannot be dropped without
checking the comparison conditions. The original D-process theorem
remains EPZAE-11 OPEN. Its cited primary paper,
[Sargos 1995, Theorem 7.1](https://doi.org/10.1112/plms/s3-70.2.285),
has not yet been obtained in full; publisher pages restrict access,
and the available database statement does not supply its analytic proof.

Seven production modules are installed: `BetaHalfDuality`,
`SargosDProcessGeometry`, `HeathBrownPairParameters`,
`HeathBrownPairSecants`, `HeathBrownPairTriangle`,
`HeathBrownPairLocalBound` and `HeathBrownExponentPairs`.
All 41 public theorems have explicit axiom audits and exact-signature
regressions. Another 24 fixtures exercise actual family pairs for
k=3,4,5,6,10; genuine A/B/C images; D's exact rational formula and
negative endpoint gaps; joined interval endpoints; both directions of
global secant comparison; the actual order-selection theorem; and beta
at zero and one half. These fixtures do not assert the missing
D-process estimate.

EPZAE-10 remains complete with exact A/B/C transformations. No aggregate
checkbox changes in this checkpoint. The remaining beta rows, four
advertised new pairs, zeta-growth/density outputs and final reproduction
remain open. The new family is an analytic input, not a claim that
`new-exp-pair` has been completed.

The permanent powering counterexample, corrected two-witness theorem,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,002 production files, 1,476 scanned Lean
  files and 10,334 build jobs. The audit covers 8,108 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,353 total).
  All 41 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-114934-4d93bc9c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_115307.log)
  and [manifest](../../logs/foundation_freeze_20260923_115307.json).
- All 1,497 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-heath-brown-family-20260923-114934-4d93bc9c.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 369 nodes and 955 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(23 checked). The whole-proof goal remains open.

## Large-value powering and subdivision — previous checkpoint

The source cardinality powering inequality is now proved by
`largeValueExponent_powering` for every natural k, including zero:

```text
1/2 <= sigma <= 1, tau >= 0
  -> LV(sigma,k*tau) <= k*LV(sigma,tau).
```

It consumes the actual cardinality witness of the corrected Lemma 62.
Neither fifth coordinate is constrained or scaled. The preserved singleton
pattern proves nonnegativity and the exact height-zero endpoint. A failed
uniform cardinality bound now yields genuine source patterns at unbounded
scales; their common compactness subsequence gives an actual energy-region
point with cardinality exponent above the failed candidate.
`isLargeValueBound_iff_region_cardinality` proves the full converse to the
existing region consumer. Infimum closure then supplies the exact
epsilon-loss boundary, not merely a strictly larger exponent.

`largeValueExponent_subdivision` proves both printed Huxley subdivision
inequalities for 0 <= tau <= tau'. Height enlargement preserves the actual
coefficients and ordinates. Subdivision sums actual localized patterns and
bounds the literal floor-bin count, with constants and radii selected
before the input pattern. Equal heights and height zero are included.
`isLargeValueBound_of_bounded_power_range` transfers a uniform bound from
the closed factor-two interval to every larger height.

`huxley_largeValueBound` and `largeValueExponent_le_huxley` now provide
the standalone uniform source bound
`LV(sigma,tau) <= max(2-2*sigma,4+tau-6*sigma)` on the full stated domain.
Their proof consumes `InCardinalityEnergyRegion.huxley_cardinality` through
the new actual-region converse. The powered Huxley estimate consumes the
corrected powering theorem. The mean-square exponent API and its short-height
and sigma=1 endpoint consequences consume the already-proved finite estimate.

Seven production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`LargeValueBoundClosure`, `LargeValueNonnegative`,
`LargeValueRegionWitness`, `LargeValuePowering`,
`LargeValueSubdivisionBounds`, `LargeValueElementaryBounds` and
`LargeValueHuxleyBound`. All 22 public theorem signatures have regressions;
16 further fixtures cover zero height/power, equal-height subdivision,
actual unchanged coefficients/ordinates, concrete mean-square/Huxley bounds
and an improved bound from the powered Huxley consumer.

EPZAE-18 remains OPEN: the random-sign/block lower bound and the resulting
exact sigma=1/2 identity still need their actual-pattern construction.
The standalone Huxley sub-obligation of EPZAE-19 is complete; the other
listed classical inputs remain open. No aggregate checkbox is changed.
The analytic D-process, remaining beta rows, four advertised new pairs,
zeta-growth/density outputs and whole-proof release obligations remain open.

The original Lemma 62 counterexample, corrected two-witness theorem,
Heath–Brown energy relation, exact optimization and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,009 production files, 1,483 scanned Lean
  files and 10,341 build jobs. The audit covers 8,145 target theorems,
  6,240 pinned-source theorems and five anchors (14,390 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-121240-f22694a3.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_121607.log) and
  [manifest](../../logs/foundation_freeze_20260923_121607.json).
- All 1,504 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-large-value-powering-20260923-121240-f22694a3.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 373 nodes and 967 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

## Exact square-root large-value exponent — previous checkpoint

`largeValueExponent_half` now proves the exact source endpoint
`LV(1/2,tau) = tau` for every tau>=0. It constructs genuine normalized
Dirichlet polynomials and one-separated ordinate sets; neither the desired
large-value bound nor an extremal-pattern family is an assumption.

The finite sign samples are a literal recursively enumerated list.
Multiplicities are retained even when different sign choices produce the
same value. Their second moment is exactly the sum of squared block
weights times the number of samples. Their fourth moment is at most
three times the squared variance times that number. Finite Cauchy–Schwarz
gives the explicit one-twelfth lower-tail count. Double counting selects
one common sample with many large evaluations, rather than a different
coefficient sequence at every ordinate.

The input coefficient vectors are actual singleton indicators on the
closed dyadic integer interval. The proof establishes their pointwise
normalization and the actual additive evaluation map, so the selected
sample supplies one coefficient function with norm at most one at every
integer. Unit modulus of the true negative-sign Dirichlet phases gives
the exact variance. The lattice consists of natural integers between zero
and floor(T); its one-separation, interval membership and cardinality are
proved explicitly.

`exists_half_largeValuePattern` constructs, for every integer N>=2 and
every real T>0, a full source pattern with scale N, physical height T,
threshold sqrt((N+1)/2), and T<=12*card(W).
Taking N=n+2 and T=N^tau gives actual unbounded-scale patterns.
Constant-factor logarithmic sandwiches prove the value exponent 1/2 and
cardinality exponent tau. The already-proved common compactness subsequence
then yields `exists_half_largeValueEnergyRegion`, with its cardinality
coordinate exactly tau. Every uniform candidate is at least tau, and the
existing separation upper bound supplies the reverse inequality.

Twelve production modules are root-imported, explicitly audited and
included in the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`:
`FiniteSignSamples`, `FiniteSignMoments`, `FiniteMomentSelection`,
`FiniteSignLargeValues`, `FiniteSignCoefficients`,
`FiniteIncidenceSelection`, `FiniteSignEvaluationMoments`,
`FiniteSignSelection`, `FiniteRandomCoefficients`,
`LargeValueRandomLattice`, `LargeValueRandomPattern` and
`LargeValueHalfExponent`.
All 28 public theorem signatures have regressions. Sixteen additional
fixtures cover empty and repeated sign samples, concrete moment estimates,
coefficient normalization, lattice endpoint counts, the nonnegative-height
guard, a genuine N=2/T=1/2 pattern, and the exact exponent/region statements
at zero, fractional and large heights.

EPZAE-18 remains OPEN only for the remaining general lower-bound
construction: for 1/2<sigma<=1 prove
`min(2-2*sigma,tau) <= LV(sigma,tau)`.
The sigma=1 and tau=0 endpoints already follow from nonnegativity; the
remaining substantive step is the coherent finite-block construction for
1/2<sigma<1. Full subdivision, corrected cardinality powering, zero-height
and upper-bound APIs stay proved. No aggregate checkbox changes here.

The analytic D-process, remaining beta rows, advertised new pairs,
remaining classical/zeta/density interfaces and final release obligations
remain open. The original counterexample and all nine repaired Add-est
clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,021 production files, 1,495 scanned Lean
  files and 10,353 build jobs. The audit covers 8,193 target theorems,
  6,240 pinned-source theorems and five anchors (14,438 total).
  All 28 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-123925-4025ec63.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_124307.log) and
  [manifest](../../logs/foundation_freeze_20260923_124307.json).
- All 1,516 physical proof/configuration/tooling hashes are identical
  before and after both runners. The twelve modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-random-sign-half-exponent-20260923-123925-4025ec63.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 376 nodes and 973 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

## Complete elementary large-value calculus — previous checkpoint

EPZAE-18 is now complete. Its original acceptance test is unchanged:
subdivision, lower/L2 bounds, obvious bounds and raising to a power all
have actual uniform source-pattern proofs with coefficient normalization.
The full source labels are `hux-sub`, `lv-lower`, `l2-mvt` and
`power-lemma`.

The remaining general lower bound is now proved by
`largeValueExponent_lower`:

```text
1/2 <= sigma <= 1, tau >= 0
  -> min(2-2*sigma,tau) <= LV(sigma,tau).
```

This includes all closed endpoints and is stronger in domain than the
printed lower-bound clause for sigma>1/2. The separate sharp endpoint
`largeValueExponent_half` remains LV(1/2,tau)=tau for every tau>=0.
No Montgomery equality is asserted beyond the proved ranges.

The new proof uses q=floor(N/L) actual disjoint natural blocks
[N+j*L,N+(j+1)*L), all contained in the closed source support [N,2N].
Each block has exactly L indices, and q*L>=N/2.
The coefficient vectors are their actual indicators, with pointwise sum of
norms at most one. The unused remainder and the right endpoint may carry
zero coefficients; the source support and its closed convention are unchanged.

`dirichletPhase_block_variation` proves the actual negative-sign phase bound
from the exact complex exponential identity and log(n/a)<=n/a-1.
For 0<=t<=N/(2L), `largeValueBlock_sum_lower` gives norm(block sum)>=L/2.
Thus the literal block-family variance is at least N*L/8.
The finite common-sign selection theorem consumes this variance and proves
one normalized coefficient sequence, shared by all selected ordinates.

`exists_block_largeValuePattern` constructs a full source pattern for
every N>=2, 1<=L<=N and T>0, with

```text
V = sqrt(N*L/16);
min(T,N/(2L)) <= 12*card(W).
```

The choice L=floor(N^(2*sigma-1)) is justified by exact real/natural
inequalities, including its positive lower bound. It gives
N^sigma/8<=V<=N^sigma and
N^min(tau,2-2*sigma)<=24*card(W) when T=N^tau.
These constants are uniform and derived before choosing the physical
pattern. Along N=n+2 the time/value logarithmic exponents converge to
tau/sigma. An actual common energy-region subsequence supplies a cardinality
coordinate rho>=min(2-2*sigma,tau). The existing uniform-bound consumer
forces every candidate B to be at least this lower bound, and the exact
least-exponent definition supplies the public statement.

The source-completion map is:

| EPZAE-18 clause | Public consumer |
| --- | --- |
| Both subdivision inequalities | `largeValueExponent_subdivision` |
| General lower bound | `largeValueExponent_lower` |
| Sharp sigma=1/2 endpoint | `largeValueExponent_half` |
| L2 mean-square upper bound | `largeValueExponent_le_meanSquare` |
| Obvious upper bound | `largeValueExponent_le_tau` |
| Every natural power, including zero | `largeValueExponent_powering` |

Powering still consumes the corrected cardinality witness, including its
actual convolution, divisor normalization and dyadic selection chain.
It does not use a scaled fifth coordinate. Subdivision still uses actual
localized patterns and its literal floor-bin count.

`LargeValueElementaryCalculus` additionally assembles the exact known
equality ranges: tau<=2-2*sigma, the mean-square range tau<=1, and the
Huxley range tau<=4*sigma-2. `largeValueExponent_one` proves
LV(1,tau)=0 for every tau>=0 by the proved bounded-range powering consumer.

Ten production modules are root-imported and included in the PowerShell
inventory behind `run_tao_trudgian_yang_build.bat`:
`DirichletBlockPhase`, `FiniteBlockCoefficients`,
`LargeValueBlockGeometry`, `LargeValueBlockCoherence`,
`LargeValueBlockVariance`, `LargeValueBlockPattern`,
`LargeValueBlockExponents`, `LargeValueLowerPatterns`,
`LargeValueLowerBound` and `LargeValueElementaryCalculus`.
All 25 public theorem signatures have explicit audits and regressions.
Twenty additional fixtures exercise zero-length empty blocks, closed
support, uncovered remainders, exact floor endpoints, phase coherence at
the height boundary, actual region witnesses, lower-bound and equality
crossovers, sigma=1 at arbitrary height, and the distinct sharp
sigma=1/2 behavior.

EPZAE-18 is the only newly checked aggregate item.
EPZAE-19 remains OPEN for its other classical inputs; the architecture
now separates that obligation from the completed elementary calculus.
The analytic D-process, remaining beta rows, advertised new pairs,
remaining zeta/density interfaces and final release obligations stay open.
The permanent counterexample and all nine repaired Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,031 production files, 1,505 scanned Lean
  files and 10,363 build jobs. The audit covers 8,245 target theorems,
  6,240 pinned-source theorems and five anchors (14,490 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-130446-48e1dea6.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_131219.log) and
  [manifest](../../logs/foundation_freeze_20260923_131219.json).
- All 1,526 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-elementary-large-values-20260923-130446-48e1dea6.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 381 nodes and 986 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. Only EPZAE-18 changes among the 42 aggregate
checkboxes (24 checked). The whole-proof goal remains open.

## Actual Type-I cardinality transfer — previous checkpoint

The cardinality side of `zero-from-large` now has a complete uniform
Type-I source consumer. This is a proved transfer from explicit upstream
`IsZetaLargeValueBound` hypotheses, not an unconditional zero-density
theorem. EPZAE-24 remains OPEN.

`cardinality_eq_sum_color_fibers` counts every fiber of the original finite
index type. `cardinality_le_color_count_mul` sums the corresponding bounds.
Equal ordinate values are never collapsed here. The two exact pattern
conversion theorems use proved one-separation to show that the finite
ordinate image has exactly the original index cardinality. Thus analytic
multiplicity is retained in the zero-copy domain until separation justifies
passing to an image.

`LargeValueUniformity` proves general and zeta compact-range uniformity.
A genuine finite open subcover chooses one constant and one positive
threshold window before the pattern. It includes finite-scale excursions
past both interval endpoints and lowers the actual threshold without
changing any coefficient or ordinate. The resulting bound is
`card(W) <= C*T^B*N^epsilon`.

The Type-I expanded slab [T/2,4T] is covered by three actual positive zeta
slabs. No ordinate translation or coefficient twist is used. Every color
fiber is counted, giving the literal factor 3. Actual Fourier deweighting
then supplies a bounded shifted ordinate for each original index.
The proved unit-bin occupancy estimate and parity/rank coloring separate
every shifted fiber.

The complete cardinality loss is

```text
K(d) = 3 * card(ZMod 2 x Fin(ceil(2d+2)+1))
     <= 24*(1+d).
```

It is linear in the displacement. If 0<=theta<eta and
d<=2*pi*T^theta, then eventually K(d)<=T^eta.
No energy upper bound, square/cube conversion or selection of only four
energy classes substitutes for counting all original indices.

`classicalTypeI_uniform_source_cardinality_bound` consumes the actual
sharp cutoff polynomial. Its positive threshold forces N<=6T;
the Fourier order, normalized threshold and all loss absorption are proved.
The zeta hypotheses select delta before the slightly shifted source line s
and threshold exponent D. The resulting bound is
`card(index type) <= C*T^(B+epsilon)`.

`classicalTypeI_uniform_source_class_cardinality_bound` applies this to a
literal Type-I branch/scale fiber of the shifted zero multiset. Its natural
scale is `2^r*floor(T^a)`, with the floor loss proved. Largeness and
one-separation follow from the genuine branch label and refined color.
No detached source-polynomial family or final class-count estimate is
assumed.

Nine production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`CardinalityPartition`, `ClassicalPatternCardinality`,
`LargeValueUniformity`, `ClassicalTypeICardinalityTransfer`,
`ClassicalTypeIFourierCardinality`, `ClassicalTypeICardinalityLoss`,
`ClassicalTypeICardinalityUniformity`, `ClassicalTypeISourceCardinality`
and `ClassicalTypeISourceClasses`.
All 15 public theorem signatures have regressions. Eighteen additional
fixtures cover empty/constant color fibers, analytic-copy multiplicity,
coincident-ordinate exclusion, all positive-slab boundaries, exact rounded
coloring costs and strict subpower absorption.

The source-cardinality theorem uses zeta hypotheses on [1,1/a] (or
[1,2/a] after the natural floor loss). It does not silently replace the
paper's final tau>=2 contract. Remaining: actual Type-II cardinality,
multiplicity-preserving slab/global assembly, the exact endpoint-two
reflection bridge and the sup/limsup density statement and corollaries.
No aggregate checkbox changes at this checkpoint.

EPZAE-18, the corrected cardinality/energy powering, the independent rho/k
and rho-star/k witnesses, the Heath--Brown energy relation, all nine repaired
Add-est clauses and the permanent singleton counterexample remain proved
and unchanged. Other classical, exponent-pair, zeta/density and release
obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,040 production files, 1,514 scanned Lean
  files and 10,372 build jobs. The audit covers 8,269 target theorems,
  6,240 pinned-source theorems and five anchors (14,514 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-132951-4bd2396c.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_133317.log) and
  [manifest](../../logs/foundation_freeze_20260923_133317.json).
- All 1,535 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-type-i-cardinality-20260923-132951-4bd2396c.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 386 nodes and 997 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## Actual endpoint-one cardinality-to-density transfer — previous checkpoint

`isZeroDensityBound_of_uniform_largeValue_bounds` now proves the complete
intermediate cardinality transfer:

```text
1/2 < sigma < 1, B >= 0, tau0 > 0;
LV_zeta bound B*tau for every tau >= 1;
LV bound B*tau for every tau >= tau0
  -> IsZeroDensityBound sigma (B/(1-sigma)).
```

The conclusion uses the actual multiplicity-weighted symmetric zero
rectangle and the original epsilon--delta quantifier order. The large-value
predicates are explicit, genuinely upstream inputs, not assumed zero-count
or detector-family estimates. The source statement's stronger lower zeta
endpoint 2 remains an independent obligation. EPZAE-24 is still OPEN.

`ClassicalTypeIICardinalityPatterns` packages the actual sharp mollifier,
with its divisor majorant and exact normalized threshold. It proves that the
pattern ordinate count equals the complete original zero-copy class count.
The native factory discharges the coefficient majorant. The uniform
Type-II consumer chooses its threshold window before the source real-part
line and consumes the literal dyadic cutoffs, scale label, expanded height
and one-separation.

`ClassicalSlabCardinalityClasses` extracts the genuine shifted source
branch/scale for every zero. It refines this by all parity/rank colors.
The zero count is exactly the sum of the cardinalities of these fibers;
no selected four-class energy witness replaces this partition.
The outer cardinality cost obeys `K*T^(3*theta)`, with the actual local
analytic-multiplicity cap and both logarithmic dyadic counts accounted for.

`classicalSlabZeroCount_bound_of_uniform_largeValue_bounds` assembles the
Type-I and Type-II cardinality consumers. The source cutoff exponents,
real-part shift, Fourier displacement and threshold losses are selected in
the required dependency order. Empty branch labels have empty fibers.
The conclusion is an actual positive-slab estimate for
`zeroCountRect (sigma-delta) 1 T (2*T)`.

`ZeroCardinalityRestrictions` injects indexed subfamilies into containing
weighted zero sets without discarding copy numbers. Negative ordinates are
transported through the proved zero-copy conjugation equivalence, including
equality of analytic vanishing orders. The symmetric assembly counts every
signed dyadic color, retains the terminal partially occupied slab, and
absorbs the actual finite low-height zero count. The logarithmic number of
colors is bounded by any positive height power.

The final predicate follows by splitting the arbitrary epsilon loss between
the positive-slab estimate and symmetric assembly, then choosing one global
constant and a positive real-part shift. No root of an energy estimate, zero
count oracle or unproved polynomial family is used.

Eight production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalTypeIICardinalityPatterns`, `ClassicalTypeIICardinalityTransfer`,
`ClassicalSlabCardinalityClasses`, `ClassicalSlabCardinalityLoss`,
`ClassicalSlabCardinalityTransfer`, `ZeroCardinalityRestrictions`,
`ZeroCardinalityAssembly` and `ZeroCardinalityTransfer`.
All 14 public theorem signatures have regressions. Sixteen additional
fixtures check analytic-copy counts, empty weighted sets, both signed slab
boundaries and excluded exterior points, strict subpower losses, and actual
unconditional density consequences obtained by supplying the proved obvious
large-value bounds.

Remaining within EPZAE-24: the exact sup/limsup exponent formulation,
the source's zeta endpoint-two reflection reduction, and all source
corollaries. The current endpoint-one predicate is not a substitute for
that unchanged aggregate acceptance contract. No aggregate checkbox changes.

The permanent counterexample, corrected independent cardinality/energy
powering witnesses, Heath--Brown energy relation, all nine repaired Add-est
clauses and complete EPZAE-18 elementary calculus remain intact.
Other classical, exponent-pair, zeta/density and release obligations stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,048 production files, 1,522 scanned Lean
  files and 10,380 build jobs. The audit covers 8,286 target theorems,
  6,240 pinned-source theorems and five anchors (14,531 total).
  All 14 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-134332-f1498f0d.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_134658.log) and
  [manifest](../../logs/foundation_freeze_20260923_134658.json).
- All 1,543 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-endpoint-one-density-20260923-134332-f1498f0d.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 392 nodes and 1,011 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## Endpoint-one density envelopes and sharp zeta nonexistence — previous checkpoint

The actual endpoint-one cardinality-to-density predicate now has its
supremum/limsup formulation and a bounded-range corollary using corrected
cardinality powering. The printed source's stronger zeta endpoint two
remains OPEN, so EPZAE-24 is not checked off.

For 1/2 < sigma < 1, the proved intermediate inequality is

```text
A(sigma)*(1-sigma)
  <= max(sup_{tau >= 1} LV_zeta(sigma,tau)/tau,
         limsup_{tau -> infinity} LV(sigma,tau)/tau).
```

`ZeroCardinalityExponentTransfer` consumes the actual Type-I/II
multiplicity-weighted zero-count transfer. The general-LV singleton lower
bound makes the envelope nonnegative. Each real number above it supplies
all zeta hypotheses and eventually all general hypotheses. EReal division,
infinite values and the strict real-part domain are handled explicitly.

The infimum-to-uniform zeta bound is reused from the existing
`ZetaLargeValueDiscreteness` module. `ZetaLargeValueBoundClosure` is only
a compatibility import, not a new proof. A duplicate draft definition and
duplicate audit entries were removed before this verification checkpoint.
The original canonical declarations retain their explicit audit.
Minus infinity is allowed; no false nonnegativity of zeta exponents is used.

`ZeroCardinalityBoundedRanges` reduces the necessary inputs to

```text
LV_zeta(sigma,tau) <= B*tau for 1 <= tau < tau0;
LV(sigma,tau)      <= B*tau for tau0 <= tau <= 2*tau0;
B >= 0 and tau0 > 0
  -> IsZeroDensityBound sigma (B/(1-sigma))
  -> A(sigma) <= B/(1-sigma).
```

The long general range uses the corrected cardinality-powering witness.
At and beyond tau0, the general bound also bounds zeta patterns.
The short interval is half-open; the general interval includes both
endpoints. For tau0 < 1 the short interval is empty. The disproved
s-prime/s scaling and the independent energy witness are not used here.

`ZetaSecondDerivativePatterns` proves the full sharp-interval range

```text
1/2 < sigma <= 1, 1 <= tau < 2*sigma
  -> every sufficiently large admissible zeta pattern has no ordinates
  -> LV_zeta(sigma,tau) = minus infinity.
```

It consumes the literal-polynomial bound
`2 + 200*sqrt(t) + 12*pi*N/t`. One positive parameter window retains
both strict gaps tau < 2*sigma and tau < 2; the threshold absorbs the
factor two in [T,2T]. Arbitrary real cardinality/energy bounds and
pointwise strict power saving on every sharp integer interval follow.
Earlier restricted-range results and their consumers are unchanged.

The three new analytic modules and the compatibility import are
root-imported and included in the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`. Nine new public theorem signatures
and two reused closure signatures have exact regressions. Twenty further
fixtures cover minus-infinity closure, interval boundaries, empty ranges,
endpoint nonnegativity, strict exclusions and numerical density
consequences from the native Huxley theorem. These include
`IsZeroDensityBound (3/4) (8/3)` and `A(4/5) <= 5/2`;
they are consequences, not new best-known estimates.

Remaining within EPZAE-24: actual source reflection reducing the zeta input
endpoint from one to two, and the exact source corollaries. The proved
endpoint-one results are labeled intermediates, not replacements for that
unchanged acceptance contract. No aggregate checkbox changes.

The permanent counterexample, corrected independent cardinality/energy
powering witnesses, Heath--Brown energy relation, all nine repaired Add-est
clauses and complete EPZAE-18 elementary calculus remain intact.
Other classical, exponent-pair, zeta/density and release obligations stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,052 production files, 1,526 scanned Lean
  files and 10,384 build jobs. The audit covers 8,297 target theorems,
  6,240 pinned-source theorems and five anchors (14,542 total).
  All nine new public theorems and both reused closure theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260923-141622-b8317f2e.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_142024.log) and
  [manifest](../../logs/foundation_freeze_20260923_142024.json).
- All 1,547 physical proof/configuration/tooling hashes are identical before
  and after both runners. The four module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-endpoint-one-envelope-20260923-141622-b8317f2e.json).

Owner HEAD at this checkpoint is `a8bdea22a024a84924a0c4accd6af656af969700`.
The owner advanced HEAD during development; no agent commit or push was
performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 395 nodes and 1,018 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## Positive reflected source and Fourier entry — previous checkpoint

The actual interior Type-I source now produces a separated reflected family
at genuine positive ordinates, with literal coefficients, physical scales,
thresholds and cardinality loss. Its output is then explicitly consumed by
bounded coefficient-one Fourier extraction. This is proved analytic entry
work; the endpoint-two density transfer remains OPEN.

`extract_positive_ordinate_reflected_block` treats both retained Poisson
signs. For the negative sign it uses the actual isometry v -> 3*T-v.
The finite image has exactly the same cardinality and remains one-separated.
Both signs yield positive ordinates in [T/2,5T/2] and the exact loss

```text
card(W) <= 2 * (2 * (2*ceil(H)+1)) * clog(2,M) * card(U).
```

The conclusion has the literal real normalized reflected coefficients.
It does not merely supply, independently for each point, a norm-equivalent
positive ordinate without separation information.

`eventually_interior_source_positive_reflected_data` invokes the native
actual smooth-source Poisson reflection, kernel and tail bounds. It retains
the source dyadic scale Q, natural dual cutoff M, detector threshold and
normalized reflected threshold L. The selected scale is exactly 2^j < M.
The physical logarithmic scale lies between 1/(1/2+d) and the proved fixed
upper bound. Both the full source-dependent lower bound for L and
`T^g/Cref <= L` are exported, with g > 0. No detached exponent or
assumed cardinality estimate is substituted.

The coefficient identities prove, on the actual positive natural support,

```text
normalizedReflected(sigma,M,n)
  = M^(-sigma) * classicalFixedLine(M,-sigma,n).
```

The exact polynomial and norm identities retain this factor. In particular,
M^sigma times the reflected norm equals the fixed-line norm when M > 0.
The cutoff, its right endpoint and the excluded n=0 term are handled
explicitly. Nonnegative sigma is not silently dropped from the native
unit-coefficient bound.

`exists_classicalReflected_explicitBoundedOrdinate_family` applies the
proved arbitrary-order Fourier extraction at real parameter -sigma.
For reflected threshold L it uses sourceV=M^sigma*L in both the radius
and the coefficient-one threshold

```text
sourceV / (4*N^sigma*classicalTypeIFourierL1(-sigma)).
```

The Fourier step retains its input index type: the selected reflected
family. Its full perturbation-energy inequality is also exported; neither
powering nor the disproved s-prime/s scaling is used here. This does not
transfer energy from the entire original source W through the earlier
cardinality-only subset selection. That all-index energy bridge remains open.

`eventually_interior_source_positive_reflected_fourier_data` unpacks the
actual reflection factory and invokes this Fourier theorem on that same
selected block and family, for every derivative order k > 1. Thus the
factory-to-Fourier edge is a kernel-checked composition, not an inferred
relationship between compatible-looking standalone statements.

Five production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedCardinality`, `ClassicalReflectedSourceData`,
`ClassicalReflectedCoefficients`, `ClassicalReflectedFourier` and
`ClassicalReflectedSourceFourier`.
Eight exact public signatures and twelve further fixtures check literal
coefficient values, cutoff boundaries, the negative-sigma guard, exact
normalization, sign reversal, interval preservation and image cardinality.

Remaining: absorb the actual Fourier radius and threshold losses; re-separate
the shifted family; apply compact-range zeta bounds near tau=2; and connect
all source branches back to the multiplicity-weighted zero-copy partition.
The final endpoint-two cardinality/energy transfers and source corollaries
are not claimed. EPZAE-21/24/33 and all aggregate checkbox states are unchanged.

The endpoint-one density results, full second-derivative zeta nonexistence,
EPZAE-18, corrected cardinality/energy powering, Heath--Brown energy relation,
all nine repaired Add-est clauses and permanent counterexample remain intact.
Other classical, exponent-pair and release obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,057 production files, 1,531 scanned Lean
  files and 10,389 build jobs. The audit covers 8,309 target theorems,
  6,240 pinned-source theorems and five anchors (14,554 total).
  All eight new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260923-214023-ae130de3.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_214539.log) and
  [manifest](../../logs/foundation_freeze_20260923_214539.json).
- All 1,552 physical proof/configuration/tooling hashes are identical before
  and after both runners. The five module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-positive-reflection-20260923-214023-ae130de3.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
The owner advanced HEAD during development; no agent commit or push was
performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 399 nodes and 1,027 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## All-index reflected source and uniform Fourier radius — previous checkpoint

The actual interior Type-I source now passes through reflection and
coefficient-one Fourier extraction on its original finite index type.
Every index, including coincident ordinates and multiplicity copies, is
retained. This closes the all-index displacement bridge missing from the
previous selected-subset construction; it does not yet prove the final
endpoint-two cardinality or energy transfer.

Reality of the literal normalized reflected coefficients gives exact norm
symmetry for the full wide polynomial. `exists_positive_reflected_shift`
therefore merges both native Poisson sign alternatives before any dyadic
choice. `exists_reflected_bounded_dyadic_family` chooses a bounded shift
and an actual dyadic label for every original index. It proves

```text
E_1(W) <= (4*ceil(1+4*H)+6) * E_1(W').
```

No large-cardinality subset is used to stand in for the original energy.
The source consumer uses a finite image only to obtain the native
pointwise analytic reflection and pulls the result back to every index.
It exports shifts at most T^d, positive ordinates in [T/2,5T/2],
the literal reflected coefficients and the full source-energy inequality.

`eventually_interior_source_indexed_reflected_data` also exports the
actual common threshold L, its exact source-dependent lower bound,
T^g/Cref <= L with g>0, and for each retained N=2^label:
1<N<M and logarithmic scale between 1/(1/2+d) and the fixed upper bound.
A singleton norm estimate is used only pointwise to bound L by N;
the original indexed family remains intact in the energy conclusion.

For sigma>=0, N<=M and L>=1, the factor M^sigma cancels from the
Fourier-radius base estimate. The theorem
`exists_order_eventually_classicalReflectedFourierRadius_le_rpow`
chooses one derivative order k>1 before T,M,N,L, and bounds the actual
radius by T^theta for every theta>0.

`eventually_interior_source_indexed_fourier_data` consumes the actual
indexed reflection output, derives L>=1 and N<=T, and applies
coefficient-one extraction at each actual dyadic length with that same k.
It retains the original index type and labels, the literal cutoff
Ioc(N,min(2*N,M)), the exact normalized threshold

```text
M^sigma * L / (4*N^sigma*classicalTypeIFourierL1(-sigma)),
```

and the uniform radius estimate. Its combined displacement is
D=T^d+2*pi*T^theta; its energy conclusion is for the entire original source:

```text
E_1(W) <= (4*ceil(1+4*D)+6) * E_1(W_final).
```

Six production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedRadius`, `ClassicalReflectedIndexed`,
`ClassicalReflectedIndexedSource`, `ClassicalReflectedIndexedGeometry`,
`ClassicalReflectedIndexedFourier` and
`ClassicalReflectedIndexedSourceFourier`.
Nine exact-signature regressions and twelve further fixtures cover both
signs, coincident-index energy versus set-image cardinality, empty input,
combined displacement, dyadic endpoints, the near-two scale and an
instantiated uniform-radius theorem.

Remaining: convert the exported threshold to the required N-power bound;
separate every shifted color without losing multiplicity; apply uniform
zeta bounds near tau=2; and assemble the lower-scale, near-endpoint and
terminal source branches with the actual zero-copy partition.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The endpoint-one transfers, corrected cardinality/energy powering,
Heath--Brown relation, all nine repaired Add-est clauses and the permanent
counterexample are preserved. Other whole-proof obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,063 production files, 1,537 scanned Lean
  files and 10,395 build jobs. The audit covers 8,329 target theorems,
  6,240 pinned-source theorems and five anchors (14,574 total).
  All nine new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-003630-1cb927cd.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_004011.log) and
  [manifest](../../logs/foundation_freeze_20260924_004011.json).
- All 1,558 physical proof/configuration/tooling hashes are identical before
  and after both runners. The six module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-all-index-reflection-20260924-003630-1cb927cd.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 403 nodes and 1,036 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## Fixed-line interior reflected source bounds — previous checkpoint

The fixed-line interior smooth Type-I branch now has uniform
C*T^(B+epsilon) bounds for both its cardinality and its full indexed
additive energy. These are deductions from the intended compact zeta
large-value or zeta-energy hypotheses on [2,U], where
U=2/((sigma-1/2)/2), with 1/2<sigma<1 and B>=0.
The actual source branch has 1<tau<2, Q=2^r*Y, r>=2,
Y+1<=Q/2, 2*Q<=A, and A=floor(sharpZetaCutoff(T)).
Other branches and the global endpoint-two transfer remain OPEN.

The two source-facing consumers are:

- `classicalReflected_uniform_interior_source_cardinality_bound`;
- `classicalReflected_uniform_interior_source_energy_bound`.

For every epsilon>0 they choose a positive perturbation exponent d and
C>=1 before u, the physical scales and the indexed family. For each
0<=u<=d one height threshold then works for every actual source family.
The conclusion is respectively card(ι)<=C*T^(B+epsilon) or
E_1(W)<=C*T^(B+epsilon). All original indices are retained, and the
hypothesis is the literal smooth source-polynomial largeness condition,
not a supplied replacement family or assumed cardinality/energy estimate.

The threshold normalization keeps the full source-dependent exponent.
Its comparison with the actual upper length scale loses at most u+3*d.
The favorable M^sigma/N^sigma factor is proved to be at least one for
N<=M and sigma>=0. A uniform absorption theorem uses the exact identity
T=N^(log_N T), the upper logarithmic scale U and the explicit small-loss
condition U*(u+3*d)<=delta/2. The actual source consumer derives the
coefficient-one lower threshold N^(sigma-delta) from these facts.

Four literal positive height intervals cover [T/4,4*T], with lower
heights T/4,T/2,T,2*T. Their logarithmic heights are within the chosen
window of [2,U]. The compact zeta constants are chosen before the
physical scales and families. No height translation or coefficient twist
is used. All four cardinality fibers are counted; the energy deduction
uses the proved four-fiber energy inequality, not a cardinality-selected
subset. The corresponding explicit height costs are 4 and 2304.

The bounded perturbation of the original separated family supplies its
actual unit-bin multiplicity bound. The coloring is refined by the actual
dyadic label. Every occupied color has the required scale and threshold;
empty fibers and empty index/label types are handled explicitly.
Both resulting bounds are for the entire original indexed source family.

The physical consumer derives the large-length, near-two and positive
window conditions from the source factory. Its explicit logarithmic and
ceiling losses are then bounded: the cardinality loss is at most
Kcard*T^(2*d), and the energy loss at most Kenergy*T^(9*d).
The actual dual cutoff is proved to lie below the sharp source cutoff.
Choosing d within the threshold, scale-window and epsilon budgets
therefore yields the two stated source bounds with no residual radius,
normalization, coloring or logarithmic-loss hypothesis.

Eleven new production modules are root-imported, explicitly audited and
covered by the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedThreshold`, `ClassicalReflectedThresholdAbsorption`,
`ClassicalReflectedNormalizedSource`, `ClassicalReflectedHeightWindows`,
`ClassicalReflectedCompactTransfer`, `ClassicalReflectedColorGeometry`,
`ClassicalReflectedColorTransfer`, `ClassicalReflectedPhysicalWindows`,
`ClassicalReflectedSourceTransfer`, `ClassicalReflectedLoss` and
`ClassicalReflectedSourceBounds`.
Twenty-two exact public signatures and twenty additional fixtures check
closed height boundaries, literal color assignments, exponent-margin
endpoints, exact finite losses, empty cutoffs and uniform physical scale
conditions. Standard logical axioms are permitted; no project axiom or
admitted proof is introduced.

Remaining: match the detector's actual source-line and threshold
conventions to this fixed-line branch; handle the lower-scale,
near-endpoint and terminal source cases; and assemble every source and
zero-copy color with actual analytic multiplicities. The exact endpoint-two
cardinality/energy transfers and final corollaries are not claimed.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.

The endpoint-one transfers, corrected two-witness powering, Heath--Brown
relation, all nine repaired Add-est clauses and the permanent singleton
counterexample remain intact. The full EPZAE-00--41 goal is still open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,074 production files, 1,548 scanned Lean
  files and 10,406 build jobs. The audit covers 8,374 target theorems,
  6,240 pinned-source theorems and five anchors (14,619 total).
  All 22 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-014058-1fb323df.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_014526.log) and
  [manifest](../../logs/foundation_freeze_20260924_014526.json).
- All 1,569 physical proof/configuration/tooling hashes are identical before
  and after both runners. The eleven module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-interior-source-20260924-014058-1fb323df.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 409 nodes and 1,051 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.


## Global detector entry and shifted-line interior bounds — previous checkpoint

Seven production modules add thirteen audited public theorems and twenty
semantic regressions (thirteen exact signatures and seven boundary/empty
or multiplicity fixtures).

The actual Type-I detector's full long-tail assertion now supplies global
smooth labels on every original multiplicity-copy index. These are the
global `Y,A` blocks, not the local two-block smoothing of one sharp
polynomial. The exact cardinality partition and four-fiber energy
inequality are retained; no cardinality-selected subfamily replaces the
energy source.

`classicalReflected_uniform_shifted_line_source_cardinality_bound` and
`classicalReflected_uniform_shifted_line_source_energy_bound` choose one
line window, displacement exponent and constant before the source line
and threshold loss. They use genuine upstream zeta large-value bounds on
`[2, 8/(sigma-1/2)]`. The two
`classicalTypeI_global_interior_source_*_bounds` theorems consume the
actual detector classes and bound every legal interior fiber with
`1 < tau < 2` by `C*T^(B+epsilon)`.

Terminal blocks are impossible pointwise, hence their entire index types
are empty. `eventually_classicalTypeI_global_source_classification`
additionally proves that every occupied global label is either one of the
two bottom blocks or an interior block with actual physical `tau > 1`.
The source-line parameter order is non-circular: the common window and
loss budget precede the later Type-II-dependent choice of shifted line.

Still open: estimates for the bottom blocks and direct interior
`tau >= 2`, their joint loss budget and full multiplicity-copy slab
assembly, and the printed endpoint-two density/energy corollaries.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The endpoint-one results, corrected two-witness powering, Heath--Brown
relation, all nine repaired Add-est clauses and singleton counterexample
are preserved. The whole-proof goal remains open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,081 production files, 1,555 scanned Lean
  files and 10,413 build jobs. The audit covers 8,405 target theorems,
  6,240 pinned-source theorems and five anchors (14,650 total).
  All 13 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-021500-212125e6.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_021842.log) and
  [manifest](../../logs/foundation_freeze_20260924_021842.json).
- All 1,576 physical proof/configuration/tooling hashes are identical before
  and after both runners. The seven module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-global-source-20260924-021500-212125e6.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 414 nodes and 1,067 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.


## Direct interior source bounds and detector consumers — previous checkpoint

Thirteen production modules add thirty public theorems and forty-six
semantic regressions (thirty exact signatures and sixteen boundary
fixtures). The new source branch is conditional only on the displayed
upstream coefficient-one zeta large-value/cardinality or energy bounds.

The actual global interior block is restricted to its literal annulus
`(Q/2,2Q]`, with `Q=2^r*floor(T^a)`. Fourier inversion uses one fixed
Schwartz profile and gives exactly the two coefficient-one dyadic lengths
`Q/2` and `Q`. The arbitrary-order tail, bounded ordinate shift and
full-index energy perturbation are proved without selecting a
cardinality-only subfamily. One derivative order precedes the source line;
profile constants affect only the eventual height threshold.

The physical floor cutoff proves `N >= T^a` for both lengths. If the
original source has `tau >= 2`, both actual logarithmic scales lie in
`[2,1/a]`. The global smooth-label loss, Fourier mass, source threshold,
height windows and every separation color are discharged and their
finite losses absorbed.

`classicalDirect_uniform_shifted_line_source_cardinality_bound` and
`classicalDirect_uniform_shifted_line_source_energy_bound` give
`C*T^(B+epsilon)` with a common line window, displacement exponent and
constant chosen before the source line and threshold loss. The two
`classicalTypeI_global_direct_source_*_bounds` theorems consume the
actual detector's global-label fibers, retaining the exact original
cardinality partition and four-fiber energy decomposition.

Both interior ranges now have actual detector consumers: reflected
`1 < tau < 2` and direct `tau >= 2`. Still open are the two bottom
source blocks and the common-parameter, single-labeling full slab
assembly with Type II and analytic multiplicities, followed by the
printed endpoint-two density/energy corollaries. Separate existential
label choices from the two branch consumers must not be spliced together.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The repaired powering, Heath--Brown relation, nine Add-est clauses and
permanent singleton counterexample remain intact.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,094 production files, 1,568 scanned Lean
  files and 10,426 build jobs. The audit covers 8,466 target theorems,
  6,240 pinned-source theorems and five anchors (14,711 total).
  All 30 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-025840-866df8ea.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_030835.log) and
  [manifest](../../logs/foundation_freeze_20260924_030835.json).
- All 1,589 physical proof/configuration/tooling hashes are identical before
  and after both runners. The thirteen module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-direct-source-20260924-025840-866df8ea.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 419 nodes and 1,080 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.


## Endpoint-two density and energy transfers — previous checkpoint

Thirteen production modules add forty public theorems and sixty-two
semantic regressions (forty exact signatures and twenty-two boundary
fixtures). EPZAE-24 and EPZAE-33 now reach their source conclusions.

The two bottom global blocks use the actual normalized source coefficients
on every original index. Their literal support and floor cutoff prove
`T^(a/2) <= N <= T^(2a)`, and both logarithmic counts are absorbed.
The general large-value estimates, reflected interior estimates and direct
interior estimates share constants chosen before the shifted source line.

One global labeling is then selected once from the actual Type-I detector.
The same fibers feed every branch; exact cardinalities and all four
energy-color classes retain every analytic multiplicity copy. The common
cutoff and Type-I window precede the Type-II tolerance, and the source
line is chosen only after both. All outer losses are absorbed.

The audited source-facing outputs are:

- `zeroDensityExponent_le_sup_limsup_endpoint_two`: printed
  `zero-from-large`, with zeta supremum over `tau >= 2`.
- `zeroDensityExponent_le_endpointTwo_bounded_suprema`: exact
  `zero-large-cor-0`, with zeta `[2,tau0)` and general
  `[tau0,2*tau0]`.
- `zeroDensityExponent_le_two_thirds_suprema`,
  `zeroDensityExponent_le_three_div_of_largeValue_bounds`, and
  `zeroDensityExponent_le_three_div_of_montgomery_range`: the other
  three printed density corollaries. Powers two and three cover the
  two-thirds interval; the Montgomery variant uses proved subdivision.
  Its small-cutoff case uses the independently proved Ingham bridge.
- `zeroDensityEnergyExponent_le_endpointTwo_bounded_suprema`: exact
  `zeroe-large-cor-0`. The original endpoint-one `zeroe-from-large`
  remains intact; an additional endpoint-two energy sup/limsup theorem
  is proved as a strengthening, not mislabeled as the printed lemma.

The short zeta supremum is literally `bottom = -infinity` when
`tau0 <= 2`, including equality. Compact-range powering consumes the
independent corrected cardinality or energy witness. No relation between
the fifth coordinates is reintroduced.

The singleton counterexample, corrected two-witness powering,
Heath--Brown relation and all nine Add-est clauses are preserved.
The whole-proof goal remains open: the D-process analytic input,
remaining beta/exponent-pair and zeta-growth work, improved density
outputs and final release assembly are separate obligations.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,107 production files, 1,581 scanned Lean
  files and 10,439 build jobs. The audit covers 8,541 target theorems,
  6,240 pinned-source theorems and five anchors (14,786 total).
  All 40 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-034939-53b58c9d.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_035654.log) and
  [manifest](../../logs/foundation_freeze_20260924_035654.json).
- All 1,602 physical proof/configuration/tooling hashes are identical before
  and after both runners. The thirteen modules and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-endpoint-two-20260924-034939-53b58c9d.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 428 nodes and 1,108 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
26 are checked; only EPZAE-24 and EPZAE-33 changed at this checkpoint.
The whole-proof goal remains open.


## Improved Bourgain density — previous checkpoint

Four production modules add twenty-four public theorems and forty semantic
regressions (twenty-four exact signatures and sixteen boundary fixtures).

EPZAE-27 reaches the unchanged source output:
`zeroDensityExponent_le_bourgain_improved` proves
`A(sigma) <= max(2/(9*sigma-6),9/(8*(2*sigma-1)))`
for the full closed interval `17/22 <= sigma <= 4/5`.
The `_lower` and `_upper` public theorems prove the two closed subranges,
including their common endpoint `38/49`.
`bourgain_improved_isZeroDensityBound` also gives the uniform shifted,
multiplicity-weighted zero-count estimate itself.

The proof uses the original cutoff
`min(9*(3*sigma-2)/2,8*(2*sigma-1)/3)` and the paper's two auxiliary
parameter choices. Exact certificates bound all five Bourgain terms and
derive nonnegative auxiliary parameters, cardinality side conditions and
the physical margin `tau-chi>1`. The existing actual-region consumer and
the failure-of-uniformity equivalence then yield the genuine uniform LV
bound. The proved twelfth moment supplies the zeta range, and the completed
endpoint-two source transfer concludes the density estimate.

One documented proof change is necessary: use the already-proved Jutila
theorem with `k=4`, rather than the printed argument's insufficient
`k=3` comparison. At `sigma=38/49, tau=6/5`, both displayed k=3/Bourgain
estimates exceed the desired `11/20`; a kernel-checked regression records
this gap. The k=4 bound closes it, and exact overlap certificates cover the
entire interval. This is not a counterexample to the advertised density
theorem, whose statement is unchanged.

The standalone unrestricted Bourgain LV input (EPZAE-19) remains open;
this proof derives every condition for the sufficient existing source range.
The permanent Lemma-62 singleton counterexample, corrected independent
powering witnesses, Heath--Brown relation, all nine Add-est clauses, and
completed EPZAE-24/33 transfer contracts are preserved.

Kernel integrity and source completeness are separate verdicts: both pass
for EPZAE-27. The D-process, remaining beta/new-pair/zeta-growth work, other
advertised density outputs, reproduction and whole-proof release remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,111 production files, 1,585 scanned Lean
  files and 10,443 build jobs. The audit covers 8,582 target theorems,
  6,240 pinned-source theorems and five anchors (14,827 total).
  All 24 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-041416-2d614f2b.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_041829.log) and
  [manifest](../../logs/foundation_freeze_20260924_041829.json).
- All 1,606 physical proof/configuration/tooling hashes are identical before
  and after both runners. The four modules and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-bourgain-density-20260924-041416-2d614f2b.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 432 nodes and 1,119 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
27 are checked; only EPZAE-27 changed from the preceding checkpoint.
The whole-proof goal remains open.


## Exponent-pair zeta growth — previous checkpoint

Seven production modules add twenty-six public theorems and forty-two
semantic regressions (twenty-six exact signatures and sixteen fixtures).

The exact source lemma `exp-pair-mu` is proved by
`ExponentPair.isZetaGrowthBound` and
`ExponentPair.zetaGrowthExponent_le`:
an actual analytic exponent pair `(k,l)` gives `mu(l-k) <= k`.
The growth predicate has every epsilon quantifier and a uniform threshold,
uses the actual Riemann zeta function and both signs of the ordinate.
Its extended-real infimum is proved equivalent to these epsilon-loss
upper bounds; no finiteness or conjectural lower bound is assumed.

The consumer derives the logarithmic model phase with its exact
`t/(2*pi)` normalization, conjugates the phase sign, applies finite Abel
summation to the actual weighted Dirichlet sums, and cancels the dyadic
scale at `sigma=l-k`. The sharp cutoff is partitioned exactly, including
its last partial block. Its logarithmic count is absorbed by epsilon loss.
The genuine sharp Poisson/Euler truncation is used at arbitrary strip
points, with no zeta-zero hypothesis. Its three remainder terms total at
most 150. This covers both strip endpoints and negative ordinates.

Actual pair consumers in the regression suite prove the classical
`mu(0)<=1/2`, `mu(1)<=0`, `mu(1/2)<=1/6` and `mu(5/7)<=1/14`
bounds. The `mu(7/10)<=3/40` fixture deliberately retains the unproved
specific pair as an explicit premise; it is not an unconditional result.
EPZAE-15 remains open until that named corollary is proved.

The permanent Lemma-62 singleton counterexample, corrected independent
powering witnesses, Heath--Brown energy relation, all nine Add-est clauses,
and completed EPZAE-24/27/33 contracts are unchanged. Preserve the
Bourgain-density k=3 proof-gap regression and its proved k=4 replacement.

Kernel integrity and source completeness are separate verdicts: the
generic exponent-pair-to-mu source lemma is complete, but EPZAE-15 and
the whole-proof release are not. The remaining D-process, beta/new-pair
outputs, other advertised density outputs and reproduction stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,118 production files, 1,592 scanned Lean
  files and 10,450 build jobs. The audit covers 8,628 target theorems,
  6,240 pinned-source theorems and five anchors (14,873 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-060220-bc031597.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_060604.log) and
  [manifest](../../logs/foundation_freeze_20260924_060604.json).
- All 1,613 physical proof/configuration/tooling hashes are identical before
  and after both runners. The seven modules and four integration files
  also match after normalizing line endings.

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 439 nodes and 1,131 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
27 are checked; no aggregate completion status changed in this checkpoint.
The whole-proof goal remains open.

## Low-height obstruction and corrected pair transfer — previous checkpoint

The printed unrestricted `add-bound(i)` is false. This is a second, separate
source obstruction; the permanent printed-Lemma-62 powering counterexample
and its authorized repair remain unchanged.

For every integer n >= 2, the new genuine coefficient-one interval patterns
have N=n^4, T=n/4, V=n^3/2 and W={n/4}. Their actual Dirichlet sums have norm
at least V. The unbounded family proves
`zetaLargeValueExponent (3/4) (1/4) ≠ ⊥`.
The already proved classical pair gives mu(1/2)<=1/6, so
1/2+(1/4)mu(1/2)<=13/24<3/4. Thus the printed implication cannot hold
for all positive tau. The public theorem
`zetaGrowth_unrestricted_largeValue_transfer_counterexample`
assembles the actual family and growth bound; this is not a numerical
sample or an assumed asymptotic witness.

A corrected pair-based theorem is independently kernel-checked:
for an actual `ExponentPair k l`, tau>=0,
sigma>k*tau+l-k and sigma>1-tau imply LV_zeta(sigma,tau)=-infinity.
`ExponentPair.zetaLargeValueExponent_eq_bot` retains the genuine
2*pi*N/t residual in the all-height logarithmic-sum estimate, proves a
common positive margin, and consumes the actual coefficient-one interval
of each zeta pattern. The second strict condition is automatic when
tau>=1 and sigma>=1/2. The classical (1/6,2/3) pair therefore gives
nonexistence when tau>=1 and sigma>tau/6+1/2.

Source crosswalk: frozen TeX `add-bound(i)` at lines 770–789 and
`lvz-340` at lines 864–866; the latter's unrestricted height domain
must not be inferred from the corrected theorem. The current
[ANTEDB zeta large-values chapter](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html)
also juxtaposes unrestricted transfer statements with a low-height
coherent-pattern lower bound. The local proof, not the blueprint's prose,
is the proof evidence.

Five new production modules:
`ZetaCoherentPattern`, `ZetaLowHeightFamily`,
`ZetaLowHeightObstruction`, `ZetaPairNonexistenceMargin` and
`ZetaPairNonexistence`. Their 15 public theorems have explicit audits;
the regression adds 15 exact-interface checks and 14 fixtures, including
actual n=2/n=4 patterns, the obstruction, both strict margins and
high-height applications. The root imports and principal runner inventory
include all five modules.

EPZAE-21 remains OPEN. The generic arbitrary-mu corrected transfer,
remaining source zeta interfaces and full advertised outputs are not
claimed. Source-contract correction authorization is pending; the false
printed statement is not silently replaced. This does not obstruct work
on independently proved corrected results or other proof branches.
EPZAE-15 still needs the specific old-pair/growth input. EPZAE-24/27/33,
all nine repaired Add-est clauses, their multiplicity conventions and
their public outputs are preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,123 production files, 1,597 scanned Lean
  files and 10,455 build jobs. Audit: 8,676 target,
  6,240 pinned-source and five anchor theorems (14,921 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  using only permitted logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-063123-ea95cd5a.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_063511.log) and
  [manifest](../../logs/foundation_freeze_20260924_063511.json).
- All 1,618 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates; all nine new/changed module and
  integration files also match after line-ending normalization.
  All 509 protected tracked files remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 443 nodes and 1,139 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. A clean dependency audit
does not close the remaining source-semantic obligations.

## Sharp low-height zeta exponent — previous checkpoint

The low-height obstruction is now sharpened to the exact value:
for sigma>=0 and 0<=tau<1,
LV_zeta(sigma,tau)=tau when sigma+tau<=1, and equals -infinity
when sigma+tau>1. The public consumer is
`zetaLargeValueExponent_lowHeight`.
The boundary is included in the nonempty branch:
in particular, LV_zeta(3/4,1/4)=1/4, not merely a value different
from -infinity. Both earlier counterexamples remain unchanged.

The proof constructs coefficient-one intervals of length
floor(N^sigma), samples the actual Dirichlet sum on a translated
one-separated lattice in [T,2T], and uses T=N^tau/8 and
V=floor(N^sigma)/2. The family has at least T ordinates and
N^sigma/4<=V<=N^sigma/2. Logarithmic limits and the genuine
uniform-bound definition give the lower exponent. The opposite
branch uses the actual first-derivative estimate O(N/t), retaining
closed interval endpoints, phase normalization and strict margins.
No exponent-pair, growth or moment estimate is assumed.

Four production modules:
`ZetaCoherentLattice`, `ZetaCoherentScale`,
`ZetaLowHeightExact`, `ZetaLowHeightVanishing`.
There are eight new public theorems, eight exact-interface regression
checks and 18 fixtures. These include equality at sigma+tau=1,
tau=0, values approaching tau=1, the genuine finite lattice patterns,
and contradictions to both unrestricted `lvz-340` and a falsely
nonstrict vanishing boundary. All four modules are imported by the
root, inventoried by the BAT runner and explicitly audited.

This proves the low-height formula corresponding to
[ANTEDB Lemma 8.10](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html),
and independently pinpoints the failure of frozen-source
`add-bound(i)` and `lvz-340` below height N. It does not prove the
generic arbitrary-mu corrected transfer, the remaining reflection
interface, or the missing old exponent pair. EPZAE-15/19/21 and the
whole-proof release remain OPEN; no aggregate checklist item closes.
Source-contract correction authorization remains pending, while
independent valid proof branches continue.

The corrected pair transfer from the preceding checkpoint still
requires sigma>k*tau+l-k and sigma>1-tau; the latter is automatic
for tau>=1 and sigma>=1/2. The permanent printed-Lemma-62
counterexample, authorized two-witness powering repair, Heath–Brown
energy relation, optimization and all nine Add-est clauses are preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,127 production files, 1,601 scanned Lean
  files and 10,459 build jobs. Audit: 8,696 target,
  6,240 pinned-source and five anchor theorems (14,941 total).
  All eight new public theorems occur exactly once in the explicit audit,
  using only permitted logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-064709-bc64d0ee.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_065116.log) and
  [manifest](../../logs/foundation_freeze_20260924_065116.json).
- All 1,622 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates; all eight new/changed module and
  integration files also match after line-ending normalization.
  All 509 protected tracked files remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 446 nodes and 1,145 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. A clean dependency audit
does not close the remaining source-semantic obligations.

## Exact Heath–Brown large values — previous checkpoint

The printed `hb-opt` result is now proved on the full source strip
`1/2 ≤ σ ≤ 1, τ ≥ 0`:

`LV(σ,τ) ≤ max(2−2σ, 10+τ−13σ)`.

`heathBrown_largeValueBound` supplies the uniform epsilon–delta
statement. `largeValueExponent_le_heathBrown` and
`zetaLargeValueExponent_le_heathBrown` expose its general and
coefficient-one exponent consequences. This is an independent Lean
derivation of the exact displayed source result, not an assumed import
of the unavailable 1979 page.

Thirteen new production modules contain 31 public theorems, one private
helper theorem and the actual integral definition `zetaGlobalConvolution`.
The proof keeps the original coefficient-one interval, finite ordinate
sets, one-separation, and all Perron residues and tails:

- Actual interval probes give the short-height estimate and the
  sixth-order Perron convolution estimate.
- The proved zeta twelfth moment extends to `[0,3T]). Weighted Hölder
  and the separated kernel bound control the common-window convolution.
- Sharp Gram duality is split at `N^(7/5)). The near row retains its
  diagonal and harmonic term; the far row uses both signed difference
  sets and their actual twelfth moment.
- The resulting finite dichotomy gives
  `LV ≤ max(2−2σ,18+2τ−24σ)` for `σ ≥ 7/8, τ ≥ 3/2`.
  Subdivision at `τ₀=11σ−8` gives the exact `hb-opt` maximum.
  One-separation and Jutila `k=2` cover the lower strip.

The principal BAT inventory, root imports, explicit axiom audit, and
semantic regression suite include all 13 modules. The 44 added checks
comprise all 31 exact public signatures and 13 endpoint, branch,
normalization and preserved-counterexample fixtures.

EPZAE-19 remains OPEN for the unrestricted Bourgain theorem and its
remaining source-facing assembly. EPZAE-26 is not closed: the specific
old exponent pair and the full improved-density consumer are separate
obligations. The exact low-height zeta formula, both source
counterexamples, corrected two-witness powering and all nine Add-est
clauses remain intact. No supporting source statement was silently
changed. Recovery-record maintenance remains permanently optional and
skipped.

Source-facing Lean statement: [HeathBrownLargeValues.lean](Extension/TaoTrudgianYang2025/HeathBrownLargeValues.lean).
The frozen source remains [Tao_Trudgian_Yang_v2.tex](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex), label `hb-opt`.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,140 production files, 1,614 scanned Lean
  files and 10,472 build jobs. Audit: 8,739 target, 6,240 pinned-source
  and five anchor theorems (14,984 total). All 31 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-073452-c7fdbca1.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_073845.log) and
  [manifest](../../logs/foundation_freeze_20260924_073845.json).
- All 1,635 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates. All 509 protected tracked files
  remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 450 nodes and 1,156 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. The failed preliminary
endpoint-regression run is superseded by the successful logs linked
above; no failed run is release evidence.

## Full Bourgain source theorem — previous checkpoint

Both printed parts of `bourgain-lvt` are now proved on their complete
source range. `bourgain_large_values` uses the actual
`ρ=(largeValueExponent σ τ).toReal`, nonnegative `α₁,α₂`,
`1/2<σ<1` and `τ>0`. Its second part retains exactly the printed
cap `ρ≤min(1,4−2τ)`. The supporting dichotomy and uniform-bound APIs
also include the closed sigma and height endpoints.

The earlier physical restrictions were discharged, not made into
new theorem assumptions. If `τ−α₂≤1`, mean square gives the small
branch. If `σ≤3/4`, either mean square again gives that branch or
the explicit witness `s=4σ+ρ` satisfies the auxiliary inequality.
The proved physical Bourgain argument covers every remaining case.

`exists_energyRegion_at_largeValueExponent` realizes the exact
infimum exponent using actual patterns on unbounded scales. Failure of
each slightly smaller bound, simultaneous compactness of the three
logarithmic coordinates, and the genuine uniform upper bound identify
the cardinality limit. Thus the final theorem has no assumed region
membership, dichotomy, moment bound, or realization hypothesis.

EPZAE-19 is now DONE: Huxley, all positive-integer Jutila bounds,
Heath–Brown `hb-opt`, the genuine twelfth moment and the unrestricted
Bourgain source theorem are all supplied.

The same continuation proves `hb-density2` unconditionally for
`7/10<σ≤19/22`, and separately at `σ=1`.
`ExponentPair.heathBrown_density_of_old_pair` gives the exact full
`7/10<σ≤1` consumer when supplied the actual analytic pair
`(3/40,31/40)`; that pair is still unproved. EPZAE-26 remains OPEN.
The corrected high-height pair-to-zeta theorem is used; the false
unrestricted growth-transfer statement is not used or silently replaced.

Four new modules contain 12 public theorems and one five-term
exponent definition. All are registered in the root package and
principal BAT; 24 regressions cover all 12 exact signatures plus
12 endpoint, branch, attainment, density and counterexample fixtures.
The original powering counterexample, the later low-height obstruction,
the sharp low-height formula and all nine repaired Add-est clauses
remain unchanged. Recovery-record maintenance is skipped.

Source-facing modules:
[BourgainLargeValues.lean](Extension/TaoTrudgianYang2025/BourgainLargeValues.lean),
[LargeValueExponentAttainment.lean](Extension/TaoTrudgianYang2025/LargeValueExponentAttainment.lean),
[HeathBrownDensityRange.lean](Extension/TaoTrudgianYang2025/HeathBrownDensityRange.lean).

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,144 production files, 1,618 scanned Lean
  files and 10,476 build jobs. Audit: 8,757 target, 6,240 pinned-source
  and five anchor theorems (15,002 total). All 12 new public declarations
  occur exactly once in the explicit audit, using only permitted logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-074939-b6807e10.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_075340.log) and
  [manifest](../../logs/foundation_freeze_20260924_075340.json).
- All 1,639 physical proof/configuration/tooling hashes are unchanged
  across the successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 454 nodes and 1,168 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion is now 28 of 42 checklist items; EPZAE-19 is the sole newly
checked item. The whole-proof goal remains active and incomplete.

## General real zeta moment transfer — previous checkpoint

Printed `add-bound(ii)` is proved with its full closed-strip parameters:
`1/2≤c≤1`, `1/2≤σ≤1`, every real `A≥1`, every real `M`, and
`τ≥2`. The actual dyadic moment
`∫[H,2H] |ζ(c+it)|^A ≤ Cη H^(M+η)` implies the uniform bound
`IsZetaLargeValueBound σ τ (τM−A(σ−c))` and the corresponding
inequality for the actual extended-real infimum `LV_ζ`.
The moment input is exactly the source hypothesis, not an assumed
Perron estimate, large-value conclusion, or energy-region witness.

For `c<1`, the exact arbitrary-line Mellin identity retains the
moving pole. Uniform cutoff bounds control both its residue and the
far integral `O_c(N^(c+3)/T²)`. The physical source windows derive
the Perron entry, with the approximation tolerance explicitly
depending on `1−c`. Weighted Hölder is proved for real orders,
including `A=1`; separation gives only logarithmic loss.
Three actual dyadic intervals normalize the source window, and the
two-sided height window handles either sign of `M+η`.

The endpoint `c=1` uses a separate proved argument. Euler–Maclaurin
with fixed cutoff `ceil(H²)`, the literal constant term, and the
integrated oscillatory prefix give
`∫[H,2H] |ζ(1+it)| ≥ H/2` eventually. Real-order Hölder then forces
`M≥1` from the source moment itself. The elementary ordinate count
closes the endpoint. No contour integrability through the pole and
no extra hypothesis `M≥1` are assumed.

Twelve new modules contain 49 public theorems and seven definitions.
All modules are in the default root and principal BAT inventory.
The 63 new regressions comprise 49 exact signatures and 14 fixtures:
fractional orders, the order-one and pole-line endpoints, negative
height exponents, the genuine twelfth-moment specialization, the
literal unwrapped source statement, and both counterexamples.

Source-facing declarations are
`zetaRealMoment_largeValueBound_closed_strip` and
`zetaLargeValueExponent_le_of_realMoment_closed_strip` in
[ZetaRealMomentEndpoint.lean](Extension/TaoTrudgianYang2025/ZetaRealMomentEndpoint.lean).
The endpoint lower bound is in
[ZetaOneLineLowerMean.lean](Extension/TaoTrudgianYang2025/ZetaOneLineLowerMean.lean);
the arbitrary-line transfer is in
[ZetaRealMomentLargeValues.lean](Extension/TaoTrudgianYang2025/ZetaRealMomentLargeValues.lean).
The unchanged [frozen source](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex)
is label `add-bound(ii)`, not the false unrestricted part (i).

EPZAE-21 remains OPEN for the general growth/nonexistence and exact
reflection-supremum obligations. EPZAE-19 remains complete; the
specific old pair and full EPZAE-26 density range remain open.
The original printed-powering counterexample, the low-height growth
counterexample, the sharp low-height formula, corrected two-witness
powering and all nine Add-est clauses are preserved. No false
supporting statement is silently replaced. Recovery records are
untouched and their maintenance is permanently skipped.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,156 production files, 1,630 scanned
  Lean files and 10,488 build jobs. Audit: 8,847 target, 6,240 pinned
  and five anchor theorems (15,092 total). All 49 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-083213-8b579737.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_083711.log) and
  [manifest](../../logs/foundation_freeze_20260924_083711.json).
- All 1,651 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 459 nodes and 1,179 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 28 of 42; no whole checklist item is newly
crossed out. The whole-proof goal remains active and incomplete.

## General high-height zeta growth transfer — previous checkpoint

General growth, not just an exponent-pair specialization, now gives
zeta-pattern nonexistence throughout `τ≥2`. For
`1/2≤c,σ≤1`, the proved source-style condition is
`c+τ·μ(c)<σ`, with `μ(c)` the actual extended-real infimum.
`zetaHighHeight_exponent_eq_bot_of_mu` concludes
`LV_ζ(σ,τ)=−∞` without assuming that the infimum is finite or attained.

The proof integrates the actual pointwise growth bound to supply every
real-order dyadic moment, with exponent `1+A·m`. Either sign of
`m` is allowed. Choosing a sufficiently large real `A≥1` in the
completed moment transfer makes the cardinality exponent negative.
The proved discreteness theorem then excludes every ordinate in one
uniform physical parameter window. A separate consumer gives strict
power saving for every literal sharp integer interval in `[N,2N]`.
The actual pole-line first moment also proves that any growth
candidate at `c=1` is nonnegative.

Two modules contain ten new public theorems, all root-imported,
registered in the principal BAT inventory and explicitly audited.
Eighteen regressions cover all ten exact signatures plus eight
actual-Weyl, infimum, fractional-moment, Lindelof-conditional,
negative-exponent, pole-line and preserved-counterexample fixtures.
See [ZetaGrowthRealMoments.lean](Extension/TaoTrudgianYang2025/ZetaGrowthRealMoments.lean)
and [ZetaGrowthHighHeight.lean](Extension/TaoTrudgianYang2025/ZetaGrowthHighHeight.lean).

This does not assert or silently repair the false unrestricted
`add-bound(i)`. The height restriction is explicit. Corrected
intermediate-height growth transfer and the exact reflection supremum
remain open under EPZAE-21. Full `add-bound(ii)`, EPZAE-19, both
counterexamples, corrected two-witness powering and all nine Add-est
clauses remain intact. Aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,158 production files, 1,632 scanned
  Lean files and 10,490 build jobs. Audit: 8,864 target, 6,240 pinned
  and five anchor theorems (15,109 total). All ten new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-084907-ccf72179.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_085748.log) and
  [manifest](../../logs/foundation_freeze_20260924_085748.json).
- All 1,653 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 461 nodes and 1,184 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Corrected general zeta growth transfer — previous checkpoint

The independent corrected growth theorem is proved across all height
cases. On `1/2≤c,σ≤1`,
`zetaCorrected_exponent_eq_bot_of_mu` consumes the actual EReal
inequality `c+τ·μ(c)<σ` together with the explicit necessary
low-height condition `σ>1−τ`, and concludes `LV_ζ(σ,τ)=−∞`.
It assumes neither a finite nor an attained growth infimum.
The same theorem chain supplies one uniform empty-pattern window
and strict power saving for every literal sharp interval in `[N,2N]`.

The proof now covers `1<τ<2` as well as higher heights. Actual
cutoff order `j+3` gives the far error
`D(j,c) N^(c+j+2)/T^(j+1)`. For each `τ>1`, a fixed integer
order makes this bounded on the physical height window. The retained
pole error is also bounded and both are absorbed against the actual
large value. Consequently the real-order moment transfer is strengthened
to every `τ>1`, all real `A≥1`, arbitrary real `M`, and the
full closed line/sigma strip, using only the source moment hypothesis.

At `τ=1`, the actual classical pair gives nonexistence for `σ>1/2`.
The native Dirichlet mean-square identity, with its diagonal retained,
proves that no genuine closed-strip growth candidate is negative.
This also proves `μ(c)≥0` for the actual EReal infimum, so the strict
growth gap reaches that height-one boundary. Below height one, the
already proved sharp low-height formula supplies the corrected result.

Seven new modules contain 27 public theorems and one definition.
They are root-imported, included in the principal BAT inventory and
explicitly audited. The 41 added regressions comprise all 27 exact
signatures and 14 fixtures, including translated intervals, actual Weyl
growth at `τ=3/2`, the pole endpoint, a Lindelof-conditional consumer,
the essential strict residual boundary and both counterexamples.
See [corrected transfer](Extension/TaoTrudgianYang2025/ZetaGrowthCorrectedTransfer.lean),
[above-one moment transfer](Extension/TaoTrudgianYang2025/ZetaRealMomentAboveOne.lean)
and [growth nonnegativity](Extension/TaoTrudgianYang2025/ZetaGrowthNonnegative.lean).

This does not rename or replace the false unrestricted printed
`add-bound(i)`. Its counterexample remains permanent, as does the
printed Lemma 62 counterexample. Corrected two-witness powering and
all nine Add-est clauses are preserved. EPZAE-21 remains OPEN for the
exact reflection supremum and unresolved source-contract correction;
aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,165 production files, 1,639 scanned
  Lean files and 10,497 build jobs. Audit: 8,924 target, 6,240 pinned
  and five anchor theorems (15,169 total). All 27 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-091728-00db0d90.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_092155.log) and
  [manifest](../../logs/foundation_freeze_20260924_092155.json).
- All 1,660 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 468 nodes and 1,201 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Sharp logarithmic reflection source — previous checkpoint

The reflection source entry now starts from an actual zeta pattern.
For every positive epsilon one constant is fixed before the pattern.
If its physical height satisfies `T≥2π`, the source interval is
retained and every actual ordinate `t` has a literal positive
natural-number interval `J_t` contained in
`(t/(4πN), t/(2πN))`. With `λ=t/(2π)`, the proved estimate is

`V ≤ sqrt(λ) |Σ[n∈J_t] n^(-1) n^(-it)| + Cε (N/sqrt(λ)+λ^ε).`

`zetaPattern_sharp_log_reflection_entry` supplies the actual
interval property, exact dual-scale bounds and this full-error
estimate together. No functional-equation, reflection estimate,
moving-interval large-value bound or coefficient-one conclusion
is assumed. Both source endpoints and the empty/short branch are paid
by the existing sharp B-process comparison.

The new proof specializes the genuine logarithmic phase: inverse
slope `1/v`, curvature `v²`, physical amplitude `sqrt(λ)/q`
and an explicit common phase of norm one. It identifies every
retained stationary term and reindexes the actual positive consecutive
integer frequencies without changing the reciprocal weights.

Five new modules contain 23 public theorems and two definitions.
All are root-imported, included in the principal BAT inventory and
explicitly audited. The 31 regressions comprise all 23 exact signatures
and eight concrete rational-stationary, empty-interval and preserved
counterexample fixtures. See
[actual pattern entry](Extension/TaoTrudgianYang2025/ZetaSharpReflectionEntry.lean),
[sharp source comparison](Extension/TaoTrudgianYang2025/ZetaSharpLogReflection.lean)
and [literal dual interval](Extension/TaoTrudgianYang2025/ZetaLogDualInterval.lean).

This is the source entry, not the full reflection supremum.
The moving reciprocal-weighted intervals must still be completed to
one common coefficient-one convolution, with uniform kernel/tail
bounds, separated extraction and the exact supremum consumer.
The independent corrected general growth transfer and above-one
real-moment transfer remain proved. Both permanent counterexamples,
corrected two-witness powering and all nine Add-est clauses remain
intact. EPZAE-21 remains OPEN; aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,170 production files, 1,644 scanned
  Lean files and 10,502 build jobs. Audit: 8,968 target, 6,240 pinned
  and five anchor theorems (15,213 total). All 23 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-094315-eff1f4b8.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_094943.log) and
  [manifest](../../logs/foundation_freeze_20260924_094943.json).
- All 1,665 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 473 nodes and 1,209 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Uniform common reflection convolution — previous checkpoint

The moving reciprocal-weighted reflection sum is now completed exactly
to one common coefficient-one polynomial. Set
`M=T/(4πN)` and
`S=Icc (floor(M)+1) (ceil(T/(πN)))`.
This actual positive integer interval is fixed before the ordinate.
Mellin inversion on `Re(s)=-1` cancels the reciprocal coefficients,
with integrability and every finite sum/integral interchange proved.

Define the actual localized convolution

`B(S,T,t) = ∫[T/2-t,3T-t] |Σ[n∈S] n^(-i(t+u))|/(1+|u|) du.`

For every positive epsilon one source constant is fixed before the
pattern. Whenever `T≥2π` and `M≥1`,
`zetaPattern_uniform_localized_reflection` proves, for every actual
ordinate and every natural derivative parameter `j`, with `λ=t/(2π)`,

`V ≤ sqrt(λ) [4 D1 B(S,T,t)/M + K_j/(4πN)^(j+1)] + Cε [N/sqrt(λ)+λ^ε].`

Here `D1=zetaCutoffDerivativeMass 1` and
`K_j=12·5^j·2^(j+1)·zetaCutoffDerivativeMass(j+2)/(j+1)`.
These are fixed transition constants, not hypotheses about a desired
large-value bound. All moving endpoints have disappeared from the
estimate. The empty dual interval is handled explicitly.

The first derivative controls the negative-line Mellin kernel at every
frequency, including zero. Higher derivatives provide arbitrary-order
tails away from zero. The common interval has cardinality at most
`6M`; actual endpoint geometry supplies uniform bounds. The near
window keeps every shifted ordinate in `[T/2,3T]`, and the discarded
integral is fully paid by the displayed tail.

Nine modules contain 33 public theorems and three definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 45 regressions contain all 33 exact signatures and 12
fixtures: zero frequency, literal common intervals, empty intervals,
a computed reciprocal sum, kernel constants and both counterexamples.
See [uniform actual-pattern entry](Extension/TaoTrudgianYang2025/ZetaReflectionUniformEntry.lean),
[exact finite completion](Extension/TaoTrudgianYang2025/ZetaReciprocalCompletion.lean)
and [localized convolution](Extension/TaoTrudgianYang2025/ZetaReflectionLocalizedCompletion.lean).

The exact reflection supremum is still OPEN. The next steps are
physical-window error absorption, separated extraction from this
common convolution, fixed-factor interval/height normalization and
the exact EReal supremum consumer. The corrected general growth
transfer, full real-moment transfer, corrected two-witness powering,
all nine Add-est clauses and both permanent counterexamples remain
intact. EPZAE-21 stays OPEN; aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,179 production files, 1,653 scanned
  Lean files and 10,511 build jobs. Audit: 9,047 target, 6,240 pinned
  and five anchor theorems (15,292 total). All 33 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-101527-45061ad5.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_101937.log) and
  [manifest](../../logs/foundation_freeze_20260924_101937.json).
- All 1,674 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 478 nodes and 1,215 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Error-free reflection convolution entry — previous checkpoint

All sharp-source and Mellin-tail errors are now absorbed uniformly on
the actual physical exponent window. For every fixed `τ>1`,
`exists_zetaReflectionConvolution_uniform_entry` chooses a positive
radius and a threshold before the pattern. For every `σ≥1/2`,
an actual pattern with `N^(τ−δ)≤T≤N^(τ+δ)` and
`N^(σ−δ)≤V` satisfies, at every actual ordinate,

`V·sqrt(T)/N ≤ K·B(S,T,t).`

The constant `K=1+32π·zetaCutoffDerivativeMass 1` is fixed and
positive. The common coefficient-one interval and the actual localized
convolution are unchanged from the preceding proof. No reflection,
convolution or large-value estimate is assumed.

The proof chooses a fixed derivative order and
`δ=min(1/8,(τ−1)/16)`. Physical powers imply both required
source conditions `T≥2π` and `T/(4πN)≥1`. The three retained
errors have a common strict power gap, and one threshold bounds
their sum by `V/2`. The final theorem needs no upper value bound
and no restriction `σ≤1`, which is useful for reflected coordinates.

Finite dyadic selection is also proved separately. A positive finite
mass above the low floor selects an actual nonempty value band with
the required amplitude-times-cardinality lower bound. Translating the
selected subset by one common shift preserves both cardinality and
one-separation exactly. This finite result does not yet choose the
analytic common shift from the convolution.

Five modules contain 17 public theorems and two definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 29 regressions contain all 17 exact signatures and 12
fixtures: actual height and remainder bounds, the `τ=3/2, σ=1/2`
consumer, concrete value bands, common-shift separation, positive
selected mass and both counterexamples.
See [uniform error-free entry](Extension/TaoTrudgianYang2025/ZetaReflectionConvolutionEntry.lean),
[physical threshold](Extension/TaoTrudgianYang2025/ZetaReflectionErrorThreshold.lean)
and [finite value bands](Extension/TaoTrudgianYang2025/ZetaReflectionValueBands.lean).

Next: select one common shift using the weighted integral mean, apply
the finite amplitude selection to actual shifted values, construct
the normalized target zeta pattern and prove the exact EReal reflection
supremum. The affine value loss must be retained; the informal
pointwise reflection identity is not a replacement for the source
supremum statement. EPZAE-21 remains OPEN; completion remains 28/42.
Both counterexamples, corrected powering and all nine Add-est clauses
remain intact.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,184 production files, 1,658 scanned
  Lean files and 10,516 build jobs. Audit: 9,081 target, 6,240 pinned
  and five anchor theorems (15,326 total). All 17 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-103643-8f5e545b.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_104037.log) and
  [manifest](../../logs/foundation_freeze_20260924_104037.json).
- All 1,679 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 482 nodes and 1,220 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Actual common-shift reflected family — previous checkpoint

The analytic common shift and actual separated value-family extraction
are proved. `exists_zetaReflection_value_family` starts from an
actual nonempty zeta pattern in the uniform physical window, for every
`τ>1` and `σ≥1/2`. It supplies one common shift
`u∈[-2T,2T]` and a literal nonempty subset of the translated
original ordinates. The selected set is exactly one-separated and
lies in `[T/2,3T]`.

Let `K=zetaReflectionConvolutionConstant`,
`L=zetaMomentLogLoss T`, `S=zetaReflectionCommonInterval T N`,
`a=V sqrt(T)/(8 K N L)`, and
`J=clog_2(ceil(|S|/a))+1`. The actual selected values satisfy
`q≤|Σ[n∈S] n^(-iv)|<2q`, with `q=a·2^j` and `j<J`, and

`q·|U| ≥ |W| V sqrt(T)/(8 K N L J).`

Every frequency coefficient is literally one. The proof retains the
amplitude-cardinality loss needed by the source's affine supremum;
it does not assert cardinality conservation at one fixed threshold.

An exact identity first turns the finite sum of localized convolutions
into one weighted common-shift integral, including the actual shifted
height indicators. Its support is `[-2T,2T]`; its positive kernel has
logarithmic mass. A weighted mean selects one shift, and the previously
proved finite dyadic lemma selects a nonempty band. The final theorem
discharges the convolution input using the actual error-free source
entry. No desired LV bound, reflection estimate or selected-pattern
existence is assumed.

Five modules contain 16 public theorems and three definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 28 regressions contain all 16 exact signatures and 12
fixtures: empty inputs, actual positive and excluded shifted heights,
literal band counts, the exact common integral, positive floors and
both counterexamples.
See [actual-pattern extraction](Extension/TaoTrudgianYang2025/ZetaReflectionSourceFamily.lean),
[common-shift mean](Extension/TaoTrudgianYang2025/ZetaReflectionShiftMean.lean)
and [actual selected value family](Extension/TaoTrudgianYang2025/ZetaReflectionValueFamily.lean).

The selected family is not yet packaged as a normalized zeta pattern:
its fixed common frequency annulus and positive height range still
need finite dyadic subdivision and scale normalization. Those steps,
the logarithmic loss bounds and the exact EReal supremum equality
remain OPEN. The informal pointwise reflection identity is not the
target. EPZAE-21 stays OPEN; aggregate completion remains 28/42.
Both counterexamples, corrected powering and all nine Add-est clauses
remain intact.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,189 production files, 1,663 scanned
  Lean files and 10,521 build jobs. Audit: 9,115 target, 6,240 pinned
  and five anchor theorems (15,360 total). All 16 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-105438-e7ef1b7e.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_110150.log) and
  [manifest](../../logs/foundation_freeze_20260924_110150.json).
- All 1,684 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 485 nodes and 1,223 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Genuine normalized reflected pattern — previous checkpoint

The reflection extraction now ends in a genuine
`ZetaLargeValuePattern`, not merely a selected ordinate family.
For every `τ>1`, one positive radius and scale threshold are chosen
before the actual source pattern and every `σ≥1/2`.
The theorem derives the large dual-scale condition from the physical
window; it does not assume a reflected pattern or an LV estimate.

Writing `M=T/(4πN)`, the literal common frequency interval is
partitioned into three disjoint blocks with scales
`floor(M), 2 floor(M), 4 floor(M)`. Each active block is an
integer interval inside its exact dyadic support. Three positive
height windows cover `[T/2,3T]`. Finite cover selection retains
at least one ninth of the extracted ordinates and divides the value
threshold by three. Exact one-separation is inherited.

The resulting actual target pattern `Q` satisfies
`M/2≤Q.N≤4M`, `T/2≤Q.T≤2T`, and
`Q.V=a·2^j/3`, where
`a=V sqrt(T)/(8 K N L)`, `K=zetaReflectionConvolutionConstant`,
`L=zetaMomentLogLoss T`, and `j<J=reflectionBandCount S a`.
Its nonempty ordinate set is a literal subset of one common translate
of the original set, and

`Q.V·|Q.W| ≥ |W| V sqrt(T)/(216 K N L J).`

The actual coefficients are the indicator of the selected integer
interval; the target has its exact required height interval
`[Q.T,2 Q.T]`. The finite construction and the final uniform theorem
both retain explicit frequency and height block witnesses.

Six modules contain 20 public theorems and two definitions. All are
root-imported, listed in the maintained principal BAT inventory and
explicitly audited. The 32 regressions include all 20 exact signatures,
literal nonempty and empty blocks, boundary heights, rounded scales,
and both permanent counterexamples.
See [actual-source normalized entry](Extension/TaoTrudgianYang2025/ZetaReflectionPatternEntry.lean),
[genuine pattern construction](Extension/TaoTrudgianYang2025/ZetaReflectionNormalizedFamily.lean),
and [literal frequency partition](Extension/TaoTrudgianYang2025/ZetaReflectionFrequencyBlocks.lean).

Remaining: absorb the logarithmic and band-count losses, normalize
the physical exponent coordinates, and prove the printed affine EReal
supremum equality, including bottom cases. The heuristic pointwise
reflection identity is not the target. EPZAE-21 remains OPEN and
aggregate completion stays 28/42. Both counterexamples, corrected
powering and all nine Add-est clauses remain preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,195 production files, 1,669 scanned
  Lean files and 10,527 build jobs. Audit: 9,155 target, 6,240 pinned
  and five anchor theorems (15,400 total). All 20 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-111539-73fd7038.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_111955.log) and
  [manifest](../../logs/foundation_freeze_20260924_111955.json).
- All 1,690 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `e56b7a81701e01cbafcb6bd77d6c7b74bd507098`. The owner advanced
  HEAD during verification; all checked physical source hashes stayed
  identical, and the protected files also match the preceding HEAD.
  No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 487 nodes and 1,225 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Uniform subpower reflected pattern — previous checkpoint

All explicit logarithmic reflection losses are now absorbed.
For every `τ>1` and `ε>0`,
`exists_zetaReflection_power_loss_pattern` chooses a positive radius
and scale threshold before the actual source pattern and every
`σ≥1/2`. It constructs a genuine nonempty target zeta pattern `Q`
with the same fixed-factor frequency and height bounds as before:

`T/(8πN)≤Q.N≤T/(πN)`, `T/2≤Q.T≤2T`.

Its ordinates are a literal subset of one common translate of the
source ordinates, and its actual interval coefficients and exact
one-separation are retained. Both estimates hold:

`Q.V ≥ V sqrt(T)/(N·N^ε)`;

`Q.V·|Q.W| ≥ |W| V sqrt(T)/(N·N^ε)`.

The rounded band count is not discarded. The actual common interval
and value floor give `|S|/a≤336 K T²` once the derived physical
conditions hold. A ceiling-logarithm estimate bounds the literal
`J=clog_2(ceil(|S|/a))+1` by a fixed multiple of `log T`.
The complete factor `216 K L J` is subpower in height, then in
source scale. One uniform window derives the required dual-scale,
height and `V≥1` conditions. The final theorem assumes no
reflection, loss estimate or target-pattern existence.

Five modules contain eight public theorems and one definition. All
are root-imported, listed in the maintained principal BAT inventory,
and explicitly audited. The 16 regressions contain every exact
signature, zero/one and rounded band counts, a concrete small
positive loss exponent, and both permanent counterexamples.
See [actual subpower extraction](Extension/TaoTrudgianYang2025/ZetaReflectionPowerLossPattern.lean),
[uniform source window](Extension/TaoTrudgianYang2025/ZetaReflectionSourceLossWindow.lean),
and [actual logarithmic height loss](Extension/TaoTrudgianYang2025/ZetaReflectionHeightLoss.lean).

Remaining: construct the unbounded reflected counterexample family
with thresholds chosen before each source pattern; prove the
transformed exponent limits and compact amplitude subsequence;
then establish the printed affine EReal supremum equality, including
bottom cases. EPZAE-21 stays OPEN and completion remains 28/42.
Both counterexamples, corrected powering and all nine Add-est clauses
remain preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,200 production files, 1,674 scanned
  Lean files and 10,532 build jobs. Audit: 9,165 target, 6,240 pinned
  and five anchor theorems (15,410 total). All eight new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-113129-35dc65d3.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_113554.log) and
  [manifest](../../logs/foundation_freeze_20260924_113554.json).
- All 1,695 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `e56b7a81701e01cbafcb6bd77d6c7b74bd507098`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 489 nodes and 1,227 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Reflected coordinate limits and amplitude subsequence — historical checkpoint

The actual normalized reflection now has its physical-coordinate
limits and a compact amplitude subsequence. For actual source
sequences with `N→∞`, `log_N T→τ>1`, the proved finite
normalization gives

`log_N Q.N→τ−1`, `Q.N→∞`, and
`log_(Q.N) Q.T→τ/(τ−1)`.

Failure of a proposed uniform source bound constructs genuine source
and target sequences. The positive error for each index first fixes
its reflection radius and threshold; only then is that source
pattern selected. The original height and value exponents converge
to the required parameters, and the exact product lower bound is
retained. No preselected sequence is assumed to cross changing
thresholds uniformly.

For `log_N V→σ`, the value-floor exponent tends to
`a=σ+τ/2−1`. The actual target polynomial and nonempty ordinate
set give `Q.V≤2 Q.N`. Compactness supplies one strict subsequence
with `log_N Q.V→v` and `a≤v≤τ−1`.

Actual uniform zeta bounds are also consumed along nonempty pattern
sequences. They give eventual logarithmic cardinality bounds with
arbitrary positive slack. Such an actual sequence proves its zeta
exponent nonnegative; this is not a blanket nonnegativity assertion
and does not erase EReal bottom cases.

Four modules contain 13 public theorems and no new definitions.
All are root-imported, listed in the maintained principal BAT
inventory and explicitly audited. The 21 regressions contain all
13 exact signatures, concrete scale and height limits, actual
nonempty-family consequences, and both permanent counterexamples.
See [ordered counterexample families](Extension/TaoTrudgianYang2025/ZetaReflectionCounterexampleFamilies.lean),
[compact amplitude extraction](Extension/TaoTrudgianYang2025/ZetaReflectionAmplitudeLimits.lean),
[physical-coordinate limits](Extension/TaoTrudgianYang2025/ZetaReflectionScaleLimits.lean),
and [sequential zeta bounds](Extension/TaoTrudgianYang2025/ZetaLargeValueSequentialBounds.lean).

Remaining: use the actual amplitude-cardinality inequality to prove
the affine exponent comparison; then assemble the printed EReal
supremum equality using reflection symmetry and all bottom cases.
No cardinality-limit assumption or heuristic pointwise reflection
identity has been substituted. EPZAE-21 remains OPEN; completion
stays 28/42. Both counterexamples and all repaired Add-est clauses
remain preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,204 production files, 1,678 scanned
  Lean files and 10,536 build jobs. Audit: 9,193 target, 6,240 pinned
  and five anchor theorems (15,438 total). All 13 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-114941-ad2a1344.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_115356.log) and
  [manifest](../../logs/foundation_freeze_20260924_115356.json).
- All 1,699 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 492 nodes and 1,230 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

## Exact reflection supremum identity — historical checkpoint

Printed `add-bound(iii)` is now proved exactly by
`zetaLargeValueExponent_reflection_supremum`, for every
`σ≥1/2` and `τ>1` (including the paper's `σ≤1` range):

`sup_[σ≤s≤1] (LV_zeta(1/2+(s−1/2)/(τ−1), τ/(τ−1)) + (s−σ)/(τ−1))
 = (1/(τ−1)) sup_[σ≤s≤1] (LV_zeta(s,τ)+s−σ).`

This is the literal EReal supremum identity, not the informal
pointwise heuristic `lvz-reflect`. The proof consumes the actual
normalized reflected patterns and their compact amplitude subsequence.
The product lower bound yields `r+a≤v+κb` for each uniform target
bound `b`; no convergence of logarithmic cardinality is assumed.
Taking the true infimum gives the affine exponent witness, and
failure of a source bound yields the genuine reflection envelope.

Positive finite affine maps commute with arbitrary EReal suprema.
The exact coordinate involution gives both inequalities. In the
reverse direction, transformed indices above one contribute bottom:
the actual reflection envelope is empty above half the height exponent,
so the corresponding actual zeta exponent is negative infinity.
Empty index intervals, top and bottom cases are retained.

Seven modules contain 22 public theorems and four definitions.
All are root-imported, included in the maintained BAT inventory,
and explicitly audited. The 35 regressions include all 22 exact
signatures, endpoint and time-involution specializations, empty
suprema, the out-of-range bottom branch, arbitrary EReal affine
suprema, and both permanent counterexamples.
See [actual mass comparison](Extension/TaoTrudgianYang2025/ZetaReflectionMassLimits.lean),
[exponent witness](Extension/TaoTrudgianYang2025/ZetaReflectionExponentWitness.lean),
[pointwise envelope](Extension/TaoTrudgianYang2025/ZetaReflectionMassEnvelope.lean),
and [exact printed identity](Extension/TaoTrudgianYang2025/ZetaReflectionSupremumIdentity.lean).

EPZAE-21 remains OPEN. The separately disproved unrestricted
`add-bound(i)` contract has not been authorized for replacement. The corrected growth theorem with `σ>1−τ` is already
independently proved; neither the false original nor its counterexample
has been altered. Reflection and the printed moment clause are complete. The sharper
Atkinson local source-form branch remains OPEN in the architecture;
this checkpoint does not claim that stronger auxiliary theorem.
Completion stays 28/42. The original Lemma 62 counterexample,
corrected two-witness powering, and all nine Add-est clauses are preserved.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,211 production files, 1,685 scanned
  Lean files and 10,543 build jobs. Audit: 9,273 target, 6,240 pinned
  and five anchor theorems (15,518 total). All 22 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-121743-3113cfb4.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_122157.log) and
  [manifest](../../logs/foundation_freeze_20260924_122157.json).
- All 1,706 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `8400c71c9888107c4b5137feabdac099ceb487d91864d9a8f76cc11b83cf7d5b`;
  foundation `ff9f8760af372c543e514b7f2d52aa0b6222289163b136a6625a6773b8ec085a`;
  foundation manifest `3ae45d1bd0983c03f94c47714e8cfd3fdb1f5a8fcdac0a997735f333de3e3cb4`.
  Earlier fixture-only failed runs are retained; the successful gates
  above include the repaired exact numeral-coercion regression.


The synchronized architecture has 495 nodes and 1,233 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance remains permanently skipped; no such file
was changed.

## Exponent-pair large values and long-cutoff density — historical checkpoint

Seven new modules prove 18 public theorems from the actual analytic
exponent-pair predicate and actual large-value patterns.

The sharp Gram-row estimate retains the low-frequency reciprocal term
and the diagonal. One-separation bounds the reciprocal sum by a harmonic
number, and uniform logarithmic absorption proves the Montgomery range
`1+l-k+k*tau < 2*sigma`. Subdivision closes the cutoff and gives
`LV(sigma,tau) <= 2-2*sigma + max(0,tau-(2*sigma-1-l+k)/k)`
for `k>0, sigma<=1, tau>=0`, including nonpositive cutoffs.

For `t=(2*(1+k)*sigma-1-l)/k>0`, the A-transformed actual pair
excludes zeta patterns below `t`. The existing zero-transfer consumer
and the proved Gram range yield `A(sigma)<=4/t` when
`1/2<sigma<1` and `t>=12*sigma-8`.
The separate `k=0` theorem proves `A(sigma)<=0` for
`sigma>(l+1)/2`; it never divides by zero.
The complementary short-cutoff branch of printed `bourgain-zd`
remains OPEN. EPZAE-28 is not closed by this partial-range theorem.

The exact old-pair deduction is also proved: Watt's actual analytic
pair `(89/560,369/560)`, followed by A/B/A and exact rational convex
combinations, gives `(3/40,31/40)`, then
`mu(7/10)<=3/40` and the full improved Heath--Brown density formula.
These four consumers explicitly require Watt's still-unproved analytic
pair. They are conditional deductions, not proofs of that input;
EPZAE-15 and EPZAE-26 remain OPEN.

All seven modules are root-imported, present in the BAT inventory,
and explicitly audited. The 28 regressions include all 18 exact
signatures, strict and closed cutoffs, the nonpositive-cutoff case,
the zero-coordinate branch, actual A/A-pair density specializations
including equality at the long-cutoff boundary, the conditional Watt
consumer, and both permanent counterexamples.
See [sharp Gram bound](Extension/TaoTrudgianYang2025/ExponentPairGramBound.lean),
[closed and subdivided range](Extension/TaoTrudgianYang2025/ExponentPairLargeValues.lean),
[long-cutoff density](Extension/TaoTrudgianYang2025/BourgainPairLongCutoff.lean),
[zero-coordinate density](Extension/TaoTrudgianYang2025/BourgainPairZeroCoordinate.lean),
and [conditional old-pair deduction](Extension/TaoTrudgianYang2025/OldExponentPairDeduction.lean).

Completion remains 28/42. The exact printed reflection identity is
complete; EPZAE-21 still has the false unrestricted growth contract
and sharper Atkinson source-form branch open. The original Lemma 62
counterexample, corrected cardinality/energy powering and all nine
Add-est clauses remain unchanged.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,218 production files, 1,692 scanned
  Lean files and 10,550 build jobs. Audit: 9,298 target, 6,240 pinned
  and five anchor theorems (15,543 total). All 18 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-124842-502cd817.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_125310.log) and
  [manifest](../../logs/foundation_freeze_20260924_125310.json).
- All 1,713 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `cf098f4b225f0e5e3117b261d005a9a1684b79a1abbf05b82de8d32ee3233cb4`;
  foundation `651a2332ac2c1119711a0d2bb1ce4df2c4a714a3380dfdba76f2b6f914de245b`;
  foundation manifest `27e5e3e83e8396dfe4774f28e2a2db81d63ee6068a2659456414827e466ff8f4`.
  The earlier fixture-only failed run is retained; the successful
  gates include the explicit cutoff parameter, numeral coercion and
  tactic-sequencing repairs.


The synchronized architecture has 501 nodes and 1,252 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Atkinson exponent-pair entry and Gram rows — historical checkpoint

Eight new modules prove 25 public theorems and define three physical
normalization functions. They connect the actual Atkinson phase difference
to the analytic exponent-pair predicate; no phase estimate is supplied
as an extra hypothesis.

The rationalized normalized derivative is jointly smooth even as the
two heights approach each other. Its finite jets converge uniformly to
the inverse-square-root model on both closed index endpoints.
The exact radians-to-unitary-phase identity then applies the proved
all-positive-frequency exponent-pair theorem, retaining its reciprocal
low-frequency term.

The resulting maximal-prefix bound holds in either height order.
Summation over actual separated heights preserves the exact diagonal
and bounds reciprocal gaps by a harmonic number. The packet consumer
uses the actual alternating divisor coefficients and independently
chosen prefixes at each height.

The actual pair `(2/9,11/18)` is derived by proved A/B processes.
Its rational counting coordinates are `15/4`, `24` and `11/72`.
These coordinate identities are not a zeta counting or moment theorem.
The dyadic physical-cutoff optimization, actual zeta-value consumer,
restricted sixth moment and complementary short-cutoff density branch
remain OPEN. EPZAE-28 is not closed by this checkpoint.

All eight modules are root-imported, included in the principal BAT
production inventory and explicitly audited. The 38 regressions cover
all 25 exact signatures, the zero-parameter/equal-height limiting model,
both closed index endpoints, empty prefixes and packets, diagonal and
height-order symmetry, and both permanent counterexamples.
See [normalization](Extension/TaoTrudgianYang2025/AtkinsonGapNormalization.lean),
[uniform finite jets](Extension/TaoTrudgianYang2025/AtkinsonGapModelJets.lean),
[analytic model entry](Extension/TaoTrudgianYang2025/AtkinsonGapModelEntry.lean),
[actual exponent-pair application](Extension/TaoTrudgianYang2025/AtkinsonGapExponentPair.lean),
[prefix bound](Extension/TaoTrudgianYang2025/AtkinsonPairPrefixGram.lean),
[separated Gram rows](Extension/TaoTrudgianYang2025/AtkinsonPairGramRows.lean)
and [restricted-sixth pair](Extension/TaoTrudgianYang2025/IvicSixthPair.lean).

Completion remains 28/42. The long-cutoff and zero-coordinate density
branches and exact reflection supremum remain proved. Watt's analytic
input, the false unrestricted growth contract and the sharper Atkinson
source-form/smaller-width branch remain open. The printed Lemma 62
counterexample, corrected two-witness powering, Heath--Brown energy
relation and all nine Add-est clauses remain unchanged.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,226 production files, 1,700 scanned
  Lean files and 10,558 build jobs. Audit: 9,343 target, 6,240 pinned
  and five anchor theorems (15,588 total). All 25 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-132159-5dc8a3d9.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_132641.log) and
  [manifest](../../logs/foundation_freeze_20260924_132641.json).
- All 1,721 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `358390883a6ac0bbb0cac8bc6973ad397d395b1ffc860e4aaac7295384728833`;
  foundation `820a558b3e65a4615a3f655d3fd9f7203b554c864ff54eee29913456edd3327d`;
  foundation manifest `c154fae7c4270948b6509e0014c1bdeeb50fd8a1b0b588422c910dfa92d873e4`.
  The earlier fixture-only failed run is retained; the successful
  regression signatures explicitly select the native Guth--Maynard
  separation predicate.


The synchronized architecture has 506 nodes and 1,265 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Physical exponent-pair packets and local-mean counting — historical checkpoint

Eight new modules prove 27 public theorems and define three explicit
power-budget/absorption functions. The actual Atkinson dyadic Gram budget
now has a uniform physical exponent-pair bound; no phase or divisor-energy
estimate is left as an analytic premise.

The nominal power algebra keeps all three terms. At the literal cutoff
`N=ceil(72*H*(log(2H)/G)^2)`, the diagonal and reciprocal-gap terms have
scale `R*H/G`, while the pair term has scale
`R^2*L^k*H^(l-k)*G^(1+k-2*l)`.
The proof establishes uniform model entry for every retained dyadic block,
handles ceiling and block-count losses, and absorbs logarithms into any
positive power of H. Restricting the internal diameter to `min(L,H)`
extends the resulting theorem to every positive localization length.

The resulting bounds are consumed by the actual stationary leading sum
and both local-mean-excess packets. The original source-width hypotheses,
including the above-fourth-root condition where required, are retained.
For the proved pair `(2/9,11/18)`, the off-diagonal width exponent is zero.
The explicit absorption length
`L=(Y^2/(4*A*H^(7/18)))^(9/2)`
and the actual finite floor-bin cover give
`R <= 2*A*H/(G*Y^2) + 1024*A^(11/2)*H^(15/4)/(G*Y^11)`.
After uniform loss absorption, the unconditional local-mean consumer
proves `R <= D*H^nu*(H/(G*Y^2)+H^(15/4)/(G*Y^11))`
for actual separated heights with actual integral excess at least Y.

All eight modules are root-imported, included in the principal BAT
production inventory and explicitly audited. The 38 regressions include
all 27 exact signatures, empty packets and zero-cardinality/zero-cutoff
budgets, zero and positive absorption thresholds, the closed terminal
height bin, and both permanent counterexamples.
See [nominal power algebra](Extension/TaoTrudgianYang2025/AtkinsonPairPowerAlgebra.lean),
[actual dyadic consumer](Extension/TaoTrudgianYang2025/AtkinsonPairDyadicBudget.lean),
[uniform physical cutoff](Extension/TaoTrudgianYang2025/AtkinsonPairCutoff.lean),
[actual packet consumers](Extension/TaoTrudgianYang2025/AtkinsonPairPackets.lean),
[explicit absorption](Extension/TaoTrudgianYang2025/IvicSixthAbsorption.lean)
and [actual local-mean counting](Extension/TaoTrudgianYang2025/IvicSixthLocalCounting.lean).

This is not yet a pointwise-zeta counting theorem or a restricted sixth
moment. Their occupancy-preserving and measure/integral consumers, and
the complementary short-cutoff density branch, remain OPEN.
Completion stays 28/42. Watt's analytic input, the false unrestricted
growth contract and the separate sharper Atkinson source-form/smaller-width
branch remain open. Both counterexamples, corrected two-witness powering,
the Heath--Brown energy relation and all nine Add-est clauses are preserved.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,234 production files, 1,708 scanned
  Lean files and 10,566 build jobs. Audit: 9,393 target, 6,240 pinned
  and five anchor theorems (15,638 total). All 27 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-134816-5da582f6.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_135229.log) and
  [manifest](../../logs/foundation_freeze_20260924_135229.json).
- All 1,729 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `5effde1c28621163b8828ed4134331e945390f1d2aaa32ce8cfbb4d65910bbdb`;
  foundation `092732d1edf9c5fae20c59a700e9bd3d5be7558f98622b7ac48b7cc269bd1dbc`;
  foundation manifest `26040a1b910e904b43271f646ec48a0755afc6ed4df906144edb86840b842dde`.
  The earlier fixture-only failed run is retained; the successful
  regression explicitly normalizes the numerical absorption threshold.


The synchronized architecture has 509 nodes and 1,273 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Actual peak counts and restricted sixth moment — historical checkpoint

Six new modules prove 14 public theorems, with no new definitions.
They consume the proved local-mean count to count the original actual
unit-separated zeta peaks. Both separated parity classes of cluster
centers are used, and every occupancy superlevel is summed; no factor
of the physical width is lost by counting centers alone.

The constructed width `G=V^2/(K*log(3H)^2)` derives all source-width
conditions and absorbs the actual local-source error. After logarithmic
absorption, for every positive epsilon and sufficiently large H,
actual peaks in `[H,2H]` with `V>=H^(1/8+epsilon)` satisfy
`R <= H^epsilon*(H/V^6+H^(15/4)/V^24)`.
There is no extra upper-amplitude premise: the proved actual pointwise
growth bound supplies the required source range, with the empty case
handled separately.

Above `V>=H^(11/72+epsilon)`, the sixth-power weighted count and full
Lebesgue superlevel measure are proved. The maximal unit-ball cover
includes the entire actual superlevel set, not merely sampled points.
The layer-cake argument then proves the actual restricted sixth moment:

`integral_{H<=t<=2H, |zeta(1/2+it)|>=H^(11/72+epsilon)}`
`    |zeta(1/2+it)|^6 dt <= H^(1+epsilon)`

for every positive epsilon and all sufficiently large H. Closed
thresholds, empty sets and integrability of the actual sixth power are
retained. This does not assert an unrestricted sixth-moment theorem.

All six modules are root-imported, included in the principal BAT
production inventory and explicitly audited. The 24 regressions include
all 14 exact signatures, the rational threshold cancellation, occupancy
two, a numerical epsilon specialization of the actual integral theorem,
measurable/integrable and empty-set cases, and both permanent counterexamples.
See [occupancy-preserving peak counts](Extension/TaoTrudgianYang2025/IvicSixthPointClusters.lean),
[constructed width](Extension/TaoTrudgianYang2025/IvicSixthPointWidth.lean),
[uniform actual peak range](Extension/TaoTrudgianYang2025/IvicSixthPointRanges.lean),
[weighted peaks and full measure](Extension/TaoTrudgianYang2025/IvicSixthWeightedPeaks.lean),
[layer-cake consumer](Extension/TaoTrudgianYang2025/IvicSixthTailIntegral.lean)
and [restricted sixth moment](Extension/TaoTrudgianYang2025/IvicSixthRestrictedMoment.lean).

The restricted moment-to-zeta-large-values transfer and complementary
short-cutoff density branch remain OPEN; EPZAE-28 is not yet complete.
Completion stays 28/42. Watt's analytic input, the false unrestricted
growth contract and the separate sharper Atkinson source-form/smaller-width
branch remain open. Both counterexamples, corrected two-witness powering,
the Heath--Brown energy relation and all nine Add-est clauses are preserved.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,240 production files, 1,714 scanned
  Lean files and 10,572 build jobs. Audit: 9,422 target, 6,240 pinned
  and five anchor theorems (15,667 total). All 14 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-140209-0f92ef51.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_140717.log) and
  [manifest](../../logs/foundation_freeze_20260924_140717.json).
- All 1,735 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `cc83810c6c267af41d710d2b3e1b8c51e7f23a5f0da4e678091751d017107ef5`;
  foundation `775fb657e82eefe436e6acea8f69eda22ff59ecdf66a1b492a4f7b2cabd0fe63`;
  foundation manifest `8f941cea166159b3a95a660092ce5a52e91586aa27c525ea813bbbe13f744f1d`.

The synchronized architecture has 513 nodes and 1,278 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Restricted sixth-moment zeta transfer — historical checkpoint

Five new modules prove 18 public theorems and introduce one genuine
continuous positive-part truncation of the actual critical-line zeta norm.
The truncated sixth integral is bounded by the proved actual restricted
sixth moment. Three dyadic intervals cover the literal Perron source
window `[T/2,3T]); both the logarithmic kernel loss and the common
physical threshold are retained and absorbed uniformly.

The actual Perron entry and separated sixth-power convolution estimate
now prove

`LV_zeta(sigma,tau) <= tau-6*(sigma-1/2)`

for `sigma>=1/2`, `tau>1` and
`(11/72)*tau<sigma-1/2`. The proof derives the amplitude gap with
explicit positive epsilon/delta witnesses, then bounds the original
coefficient-one pattern cardinality. The EReal least exponent consumes
the actual asymptotic bound. No full sixth-moment hypothesis is added,
and neither the strict amplitude restriction nor the Perron height
condition is removed.

All five modules are root-imported, included in the principal BAT
production inventory and explicitly audited. The 28 regressions include
all 18 exact signatures, vanishing and zero-threshold truncations,
the actual specialization `sigma=9/10, tau=5/2, rho=1/10`,
strict boundary and low-height guards, empty sums and both permanent
counterexamples. See [continuous truncation](Extension/TaoTrudgianYang2025/IvicSixthExcess.lean),
[literal source window](Extension/TaoTrudgianYang2025/IvicSixthExcessSource.lean),
[separated convolution](Extension/TaoTrudgianYang2025/IvicSixthExcessConvolution.lean),
[physical amplitude gap](Extension/TaoTrudgianYang2025/IvicSixthAmplitude.lean)
and [actual zeta large-value transfer](Extension/TaoTrudgianYang2025/IvicSixthLargeValues.lean).

The complementary Bourgain short branch requires a separate
general-coefficient Gram consumer of the restricted sixth moment.
Its intended bound is `LV(sigma,tau)<=max(2-2*sigma,tau+9-12*sigma)`
under `(11/72)*tau<2*sigma-3/2`. This is still OPEN, not supplied
by the coefficient-one Perron theorem just proved. At the endpoint
`tau=3*t/4`, the restriction becomes `11*t<192*sigma-144`;
with `k*t=2*(1+k)*sigma-1-l`, it gives the printed restriction
`(170*k-22)*sigma>144*k-11*l-11`. This algebra identifies the
needed source route; it does not prove the missing analytic estimate.

Completion stays 28/42. Watt's analytic input, the false unrestricted
growth contract and the separate sharper Atkinson source-form/smaller-width
branch remain open. Both counterexamples, corrected two-witness powering,
the Heath--Brown energy relation and all nine Add-est clauses are preserved.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,245 production files, 1,719 scanned
  Lean files and 10,577 build jobs. Audit: 9,448 target, 6,240 pinned
  and five anchor theorems (15,693 total). All 18 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-142547-845e85c3.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_143028.log) and
  [manifest](../../logs/foundation_freeze_20260924_143028.json).
- All 1,740 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `ad786825166546028ca26e0e0d6bfb87256c2c7db4b32a7382fbba1ecae7e0c2`;
  foundation `1111902a2ccc1953dfbfce6b3bffc82a0a4239d8db3c944cf3b8e2a25a230d51`;
  foundation manifest `bace24d4d246506d001a6135497807634104229bcf57830a49506ec7e4e58358`.

  The initial regression-only warning run is retained; two unnecessary
  tactic combinators were removed before both clean gates passed.

The synchronized architecture has 515 nodes and 1,282 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Bourgain pair-to-density theorem completed — historical checkpoint

Eleven new modules prove 34 public theorems and introduce four genuine
analytic/kernel definitions. EPZAE-28 is complete; completion is 29/42.
The complete public result is
[ExponentPair.bourgain_zero_density](Extension/TaoTrudgianYang2025/BourgainPairDensity.lean),
with every printed hypothesis and both alternative side conditions.
The zero first coordinate and sigma=1 endpoint are included.

The actual restricted sixth moment first gives a symmetric global
continuous excess moment, with a terminal-height-independent compact
initial integral. A fixed smooth Gram weight is exactly one on the
source pattern's closed dyadic support. Phase-aligned finite duality
produces a genuine Gram row; Mellin localization preserves its pole,
local zeta integral and arbitrarily decaying tail. The real-centered
window overlap is proved without rounding, with exact cost `2*H+1`.

The actual small-value and tail terms are absorbed before finite
sixth-power Holder. The remaining alternative has scales
`R*V^2<=D*N^2` or `R*V^12<=D*N^9*T^(1+7*eta)`.
The smoothing radius and decay order are constructed. Explicit
epsilon/delta witnesses derive the physical amplitude gap and prove

`LV(sigma,tau)<=max(2-2*sigma,tau+9-12*sigma)`

for positive tau with `(11/72)*tau<2*sigma-3/2`. This is an actual
general-coefficient theorem, not a zeta-pattern proxy or a full
sixth-moment assumption. Its strict threshold and the exact affine
budget close Bourgain's complementary short branch. The earlier
long-cutoff and zero-coordinate proofs are consumed unchanged.

See [symmetric excess moment](Extension/TaoTrudgianYang2025/IvicSixthGlobalExcess.lean),
[smooth Gram kernel](Extension/TaoTrudgianYang2025/IvicSixthSmoothGram.lean),
[actual Mellin entry](Extension/TaoTrudgianYang2025/IvicSixthTraceMellin.lean),
[real-window overlap](Extension/TaoTrudgianYang2025/IvicSixthWindowOverlap.lean),
[actual row split](Extension/TaoTrudgianYang2025/IvicSixthGramRow.lean),
[finite cardinality](Extension/TaoTrudgianYang2025/IvicSixthGramCardinality.lean),
[physical moment consumer](Extension/TaoTrudgianYang2025/IvicSixthPhysicalPatterns.lean),
[chosen smoothing](Extension/TaoTrudgianYang2025/IvicSixthSmoothing.lean),
[general large-value exponent](Extension/TaoTrudgianYang2025/IvicSixthGeneralLargeValues.lean)
and [short-branch algebra](Extension/TaoTrudgianYang2025/BourgainPairShortAlgebra.lean).

All modules are root-imported, inventoried by the principal BAT and
explicitly audited. The 48 regressions include all 34 exact signatures,
the actual short-branch specialization `A(9/10)<=20/13` using
the analytically derived pair `(1/6,2/3)`, actual general LV at
`sigma=9/10,tau=39/20`, exact strict-boundary guards, sigma=1,
empty/zero-window and reflection cases, and both permanent counterexamples.

The optimized eight-piece envelope remains OPEN. Its first displayed
pair is on two excluded boundaries of the strict source theorem and
requires a genuine closure argument; all eight pairs still need their
analytic provenance discharged. Watt's input, the false unrestricted
growth contract and the separate sharper Atkinson source-form/smaller-width
branch remain open. Corrected two-witness powering, the Heath--Brown
energy relation and all nine Add-est clauses remain intact.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,256 production files, 1,730 scanned
  Lean files and 10,588 build jobs. Audit: 9,505 target, 6,240 pinned
  and five anchor theorems (15,750 total). All 34 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-145418-b7175bb1.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_145832.log) and
  [manifest](../../logs/foundation_freeze_20260924_145832.json).
- All 1,751 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `9c28f54f4c105bc0a6330d79f9a598be3ab31fe1a78a73208ff9df7af147e044`;
  foundation `2683daa6262c27e855ace953f1d587a7df2bb6c88e402dee6ff14b277d34296d`;
  foundation manifest `c061c713d6bb0b5e2baf0a308309af02d67643f9c8b45370349f4f929029800e`.

The synchronized architecture has 519 nodes and 1,289 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Bourgain boundary closure and exact eight-piece transfer — historical checkpoint

Two new modules prove 12 public theorems and define the literal
eight-piece function. Completion remains 29/42: EPZAE-28 is complete,
but EPZAE-29 is not marked complete while analytic pair inputs remain open.

[The closed-boundary theorem](Extension/TaoTrudgianYang2025/BourgainPairDensityClosure.lean)
uses the genuinely proved classical pair `(1/14,11/14)` and actual
analytic convex combinations. The mixing parameters tend to zero,
the denominator remains eventually positive, every perturbed pair
satisfies the strict Bourgain hypotheses, and the real rational bounds
converge inside `EReal`. The result includes both `k=11/85` and
`15*l+20*k=13`; no strict source hypothesis was silently weakened.
The first rational formula `11/(12*(4*sigma-3))` is proved with
its analytic exponent-pair input explicit.

[Eight analytic consumers and assembly](Extension/TaoTrudgianYang2025/BourgainOptimizedTransfer.lean)
connect every generated rational piece to the actual density exponent.
All source lower endpoints satisfy the required analytic admissibility
inequalities. `optimizedBourgainBound` selects the literal eight pieces;
each internal endpoint belongs to its left-hand piece. The theorem
`optimizedBourgain_bound_of_pairs` consumes eight actual `ExponentPair`
inputs. It is explicitly conditional, not an unconditional proof of
the published optimized density theorem. The earlier seven crossover
identities and exact interval-cover certificate are reused unchanged.

All 12 new public declarations are explicitly audited and have
exact-signature regressions. The 24 new regressions also cover all seven
internal endpoint owners, the genuine specialization `A(19/20)<=8/7`,
both excluded strict-boundary guards and both permanent counterexamples.

The pinned paper-time `bourgain_ep_to_zd()` driver manually installs
its target pairs using placeholder proof strings and empty dependencies.
Those entries are useful discovery data, not Lean proof provenance.
The pinned literature identifies stronger exponent-pair and beta inputs,
including Sargos's D-process, Bourgain's 2017 pair and Huxley's beta
tables. Analytic proofs of the required inputs remain open. A finite
A/B/C/Heath--Brown search did not find these eight pairs; that finite
search is not a nonexistence theorem and is not used by Lean.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
The separate false unrestricted growth contract and sharper Atkinson
source-form/smaller-width branch are not claimed resolved.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,258 production files, 1,732 scanned
  Lean files and 10,590 build jobs. Audit: 9,531 target, 6,240 pinned
  and five anchor theorems (15,776 total). All 12 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-151533-a216239a.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_152013.log) and
  [manifest](../../logs/foundation_freeze_20260924_152013.json).
- All 1,753 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `507ff6b861f4c15aba5ce8faac79e60226c235358d4e8ea4f52f979a5e406a6f`;
  foundation `2e08778832d73afc199f5308fd22ff1bc58b26ccc00e58fb41896504f63cee6f`;
  foundation manifest `a734a0e648d10c167c917b6f558b040c6b75cbcc11b140bc82c697f4dc175ec5`.

The synchronized architecture has 521 nodes and 1,296 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Robert–Sargos 2002 arithmetic and signed conic count — historical checkpoint

Twelve new modules prove 31 public theorems and define four actual phase
polynomials. Completion remains 29/42. This is progress on the independent
EPZAE-15/26 old-pair route, not a proof of the fourth-derivative theorem,
the old exponent pair, or the full improved Heath--Brown density bound.

[The source geometry](Extension/TaoTrudgianYang2025/RobertSargosFourthGeometry.lean)
reduces the literal two-coordinate system to the displacement equation
and conic polynomial. It retains the actual Taylor terms
`-r*h^2-r^2*h`: the source-to-counting tolerance is
`E+12*R*H^2`, not an equality that drops those terms.
The [same-sign displacement bound](Extension/TaoTrudgianYang2025/RobertSargosDisplacement.lean)
and [square-root ratio strip](Extension/TaoTrudgianYang2025/RobertSargosRatioGeometry.lean)
follow from the actual linear equation, near-quadratic inequality and
dyadic support, with explicit constants.

[Primitive congruence spacing](Extension/TaoTrudgianYang2025/PrimitiveCongruenceSpacing.lean)
uses integer Bezout identities, determinant divisibility and uniqueness
of reduced fractions. The finite count is derived from that spacing.
The [primitive-triple theorem](Extension/TaoTrudgianYang2025/PrimitiveTripleCount.lean)
then decomposes by the actual `gcd(u,v)`, proves that it divides the
modulus, normalizes each fiber and sums over divisors. It proves the
finite-set form of Robert--Sargos (2002), Lemma 5, with explicit bound

`card S <= tau(c)+4*V^2*(beta-alpha)*sigma(c)/c^2`,

where `tau(c)` is the number of positive divisors and `sigma(c)` is
their sum. These are actual divisor sums, not supplied counting inputs.
The theorem allows zero numerator/third coordinate and uses closed
ratio intervals, a proved strengthening of the source's nonzero/strict
parameter conventions. Denominators remain positive and the modulus
is nonzero. [The signed-modulus version](Extension/TaoTrudgianYang2025/PrimitiveTripleSignedCount.lean)
derives both signs without changing the solution count.

[The actual conic consumer](Extension/TaoTrudgianYang2025/RobertSargosSameSignCount.lean)
proves the full fixed-`r,h1,h2` branch, including both signs of
`r`, both common signs of `q1,q2`, and the source's gcd ordering.
For the actual primitive triples its explicit bound is

`2*tau(abs r)+64*delta*Q^2*sigma(abs r)/(H*abs r)`.

Negative triples are reflected by an injective map; cardinalities,
primitivity, the linear equation and the quadratic tolerance are all
transported in Lean. This theorem actually consumes the ratio geometry
and primitive count, rather than merely restating their interfaces.

All 31 public theorems are explicitly audited. The 38 regressions cover
their exact signatures, retained Taylor correction, the need for gcd
normalization, a non-pairwise-coprime primitive triple, negative modulus,
the two-sign conic consumer and both permanent counterexamples.
All 12 modules are root-imported and included in the BAT production inventory.

The total six-variable primitive count, all parameter cases, seven-variable
gcd reduction and the finite-sum/double-large-sieve assembly of the fourth
derivative test remain OPEN. The 2002 counting system is distinct from
the already proved Robert--Sargos 2003 near-count used by the C-process.
No 2003 theorem is relabeled as the missing 2002 theorem.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and the genuine boundary closure remain proved; EPZAE-29 still
needs analytic pair provenance. The separate false unrestricted growth
contract and sharper Atkinson source-form/smaller-width branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,270 production files, 1,744 scanned
  Lean files and 10,602 build jobs. Audit: 9,594 target, 6,240 pinned
  and five anchor theorems (15,839 total). All 31 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-160226-564ac3d0.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_160640.log) and
  [manifest](../../logs/foundation_freeze_20260924_160640.json).
- All 1,765 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `485053b1e9e625865d71782622367124ed24b3d2f9f5970cfe69f6cc7adc5545`;
  foundation `fdda554c4e7071dab384a4ebc8a64334aee3cd16ca308a9ce9e2d66f50be7cc9`;
  foundation manifest `03f5e62b07cdeabffa08a06c0c693a8d1c7c5dcf81c78a0b5917bb402925fd78`.
- An earlier extension run correctly failed two concrete divisor-cardinality
  fixtures. They were repaired using kernel reduction, and the complete
  rerun above passed; the earlier failed log is not completion evidence.


The synchronized architecture has 526 nodes and 1,307 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Robert–Sargos complementary counts and source projections — historical checkpoint

Thirteen new modules prove 27 public theorems, introduce the actual
six-coordinate point and primitive-system types, and define its two
coordinate projections. Completion remains 29/42. The total counting
theorem and fourth-derivative test are still OPEN.

[Complementary geometry](Extension/TaoTrudgianYang2025/RobertSargosCoefficientGeometry.lean)
and [the affine band](Extension/TaoTrudgianYang2025/RobertSargosAffineBand.lean)
are derived from the literal source line and reduced quadratic.
The retained identity is
`h2*q2*(q1+2*d-q2)=E+r*d*(q1+d)`.
On the source supports with `delta<=1`, the actual displacement bound
gives `abs d<=9*Q`, the linear ratio error is at most `9*R/H`,
and `abs(2*d+q1-q2)<=delta*Q+99*R*Q/H`.
No residual term is dropped.

[Safe orientation](Extension/TaoTrudgianYang2025/RobertSargosConicOrientation.lean)
proves that one conic pivot is valid for same-sign frequencies. Swapping
the frequency/coefficient coordinates and negating `d` negates the
reduced polynomial only after the actual line equation is used.
The [full two-pivot conic count](Extension/TaoTrudgianYang2025/RobertSargosFixedDisplacementConic.lean)
and [linear-strip count](Extension/TaoTrudgianYang2025/RobertSargosFixedDisplacementLinear.lean)
count actual primitive coefficient triples. With `n=abs d>0`, their
explicit bounds are respectively

`tau(n)+8*H^2*delta*sigma(n)/n^2` and
`tau(n)+72*H*R*sigma(n)/n^2`.

Both coordinate/gcd conventions, the sign of the modulus and actual
solution cardinalities are transported in Lean.
[Actual divisor growth](Extension/TaoTrudgianYang2025/PrimitiveDivisorGrowth.lean)
uses the foundation's proved pointwise divisor theorem.
[The displacement consumers](Extension/TaoTrudgianYang2025/RobertSargosFixedDisplacementLoss.lean)
give `C_epsilon*n^epsilon*(1+8*H^2*delta/n)` and
`C_epsilon*n^epsilon*(1+72*H*R/n)`.
[The original fixed-coefficient consumer](Extension/TaoTrudgianYang2025/RobertSargosFixedCoefficientLoss.lean)
gives `C_epsilon*H^epsilon*(1+delta*Q^2/H)`.
In all three theorems the constant depends only on epsilon; no divisor
or counting estimate is a premise.

[Integer interval and affine-band counts](Extension/TaoTrudgianYang2025/IntegerAffineBandCount.lean)
keep the closed-endpoint allowance and count actual finite fibers.
For `D,Q>=1`, `abs d<=2D`, `abs q1<=2Q` and affine width `B>=0`,
the triple count is at most `25*D*Q*(2*B+1)`.
[The primitive source system](Extension/TaoTrudgianYang2025/RobertSargosPrimitiveSystem.lean)
contains the actual six integer coordinates, both primitive gcds, nonzero
`r,d`, same-sign frequencies, support, line and near-quadratic conditions.
Closed boxes overcount the source's half-open boxes.
[Its projection theorem](Extension/TaoTrudgianYang2025/RobertSargosPrimitiveProjection.lean)
applies the affine-band count to the real source frequency image.
The two coordinate keys jointly determine the original point.

All 13 modules are root-imported and in the BAT production inventory.
All 27 public theorems have explicit axiom audits and exact-signature
regressions. The 36 new regressions additionally check both actual pivot
orientations, reject each nonprimitive gcd, guard an invalid pivot and
the false swap identity without the line equation, retain interval
endpoints, and preserve both permanent counterexamples.

What remains is mathematical summation: actual source fibers, all
parameter regimes, dyadic displacement ranges, zero displacement and
the seven-variable gcd reduction. The finite-difference, Taylor,
double-large-sieve and parameter assembly of the fourth-derivative
test remain open. Neither the old analytic pair nor the EPZAE-15/26
end theorem is claimed proved by these supporting counts.
The distinct Robert--Sargos 2003 C-process count is not substituted.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and the genuine boundary closure remain proved; EPZAE-29 still
needs analytic pair provenance. The separate false unrestricted growth
contract and sharper Atkinson source-form/smaller-width branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,283 production files, 1,757 scanned
  Lean files and 10,615 build jobs. Audit: 9,681 target, 6,240 pinned
  and five anchor theorems (15,926 total). All 27 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-163227-e809caa4.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_163645.log) and
  [manifest](../../logs/foundation_freeze_20260924_163645.json).
- All 1,778 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `44bdbc731d29fb495c3bb2ed19017a347845fa57182decb8f622f3bc6189809b`;
  foundation `4b44dbfd66cf151a28f930e13c03bbc5197a8f58ab1c30e07c88d792e905129b`;
  foundation manifest `72ec7ae1aff8ddaa5a497b7da4b877dd11c0d71400e87960a0ea7a69022eddec`.


The synchronized architecture has 529 nodes and 1,317 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Robert–Sargos full primitive counting theorem — historical checkpoint

Twenty-two new modules prove 41 public theorems and define three actual
coordinate maps. The complete primitive six-variable count is now proved,
not merely its individual fibers or projected image. Completion remains
29/42: the seven-variable source count and fourth-derivative test are OPEN.

[The public assembly](Extension/TaoTrudgianYang2025/RobertSargosPrimitiveCount.lean),
`exists_robertSargos_primitive_count`, states that for every `epsilon>0`
there is `C_epsilon>0`, depending only on epsilon, such that every finite
set `S` of actual `RobertSargosPrimitiveSystem R H Q delta` points satisfies

`card S <= C_epsilon*(R*H*Q)^(1+epsilon)*(1+delta*Q)`

when `R,H,Q>=1`, `delta>=0` and `R<=H/2`.
The source structure retains both primitive gcds, nonzero r and d,
same-sign frequencies, the literal linear and near-quadratic equations,
and all six support conditions. Closed boxes overcount the paper's
half-open supports; delta zero is also allowed. No counting estimate,
divisor bound or exponent pair is assumed by this public theorem.

[Coefficient fibers](Extension/TaoTrudgianYang2025/RobertSargosCoefficientFibers.lean)
and [their summation](Extension/TaoTrudgianYang2025/RobertSargosWideFrequencyBound.lean)
prove the complete target in `H<=Q`. The actual coefficient image has
at most `12*R*H^2` keys, and each full solution fiber is counted.

[Frequency reconstruction](Extension/TaoTrudgianYang2025/RobertSargosFrequencyCoordinates.lean)
proves exact cardinality preservation on fixed-key fibers.
[The source-fiber consumers](Extension/TaoTrudgianYang2025/RobertSargosFrequencyFibers.lean)
derive every input of the previously proved conic and linear bounds
from the actual source points.
[Fixed-displacement affine-band counts](Extension/TaoTrudgianYang2025/IntegerFixedDisplacementCount.lean)
give at most `(4*Q+1)*(2*B+1)` frequency pairs.
[Signed weighted summation](Extension/TaoTrudgianYang2025/RobertSargosFrequencyWeightSums.lean)
retains the harmonic sum and absorbs it using epsilon/2; each positive
absolute displacement has at most two signs.
This is a direct finite-sum replacement for dyadic summation, not a
missing dyadic hypothesis. It covers the complete range
`1<=abs d<=floor(9*Q)` for `delta<=1`.

[The complementary counts](Extension/TaoTrudgianYang2025/RobertSargosComplementaryCount.lean)
have the form `C_epsilon*Q^epsilon*Q*(1+B)*(Q+A)`, with
`B=delta*Q+99*R*Q/H` and respectively
`A=8*H^2*delta` or `A=72*H*R`.
[The parameter comparisons and assembly](Extension/TaoTrudgianYang2025/RobertSargosSmallToleranceCount.lean)
prove the target in both `Q<=H` regimes, split at `delta=R/H`,
and thus for every frequency regime with `0<=delta<=1`.

[The large-tolerance branch](Extension/TaoTrudgianYang2025/RobertSargosLargeToleranceCount.lean)
uses the actual equation `h2*q2=h1*q1+r*d`.
[Positive factor-pair injection](Extension/TaoTrudgianYang2025/IntegerProductCount.lean)
bounds each actual source fiber by divisors of its nonzero product,
whose absolute value is at most `4*H*Q`.
The four-coordinate key image has at most `570*delta*R*H*Q^2` points
when `delta>=1`. The foundation's proved divisor bound supplies the
uniform epsilon loss. This completes the remaining tolerance range.

All 22 modules are root-imported and in the BAT production inventory.
All 41 public theorems have explicit axiom audits and exact-signature
regressions. The 51 new regressions also test distinct valid source
points with the same frequency key, positive and negative factor
products, both displacement signs, zero tolerance, and both permanent
counterexamples. A projected image is never substituted for the
original six-coordinate solution cardinality.

The zero-displacement branch, two-gcd normalization, exceptional large
coordinate-gcd range and seven-variable count remain OPEN. The
finite-difference, shift, Taylor, double-large-sieve and parameter
assembly of the fourth-derivative test remain OPEN. Neither the old
analytic pair nor the EPZAE-15/26 end theorem is claimed proved by
this primitive counting theorem. The distinct 2003 C-process count
is not substituted for the 2002 source system.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and the genuine boundary closure remain proved; EPZAE-29 still
needs analytic pair provenance. The separate false unrestricted growth
contract and sharper Atkinson source-form/smaller-width branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,305 production files, 1,779 scanned
  Lean files and 10,637 build jobs. Audit: 9,727 target, 6,240 pinned
  and five anchor theorems (15,972 total). All 41 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-171900-f82731cc.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_172333.log) and
  [manifest](../../logs/foundation_freeze_20260924_172333.json).
- All 1,800 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `cedfeb1a429bd2c6d4cc21e7692af130372b8e59e9246cb50f472b31b454c82e`;
  foundation `8d799c52dc55bf3d0a8271e82eae41da0b5389d0687d7f089e64f1be4318eb9a`;
  foundation manifest `47c92c0f2ea58c3d25272ccc5523f3048e5f8925e0694840d4f063a43f7b0c4a`.


The synchronized architecture has 533 nodes and 1,324 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.


## Robert–Sargos seven-variable source theorem — historical checkpoint

Twenty new modules prove 47 public theorems, define nine actual
coordinate/gcd maps and introduce three source types. The full
seven-variable counting theorem is now proved. Completion remains
29/42: the fourth-derivative exponential-sum theorem and the resulting
analytic exponent pair remain OPEN.

[The literal source consumer](Extension/TaoTrudgianYang2025/RobertSargosSourceCount.lean),
`exists_robertSargos_source_count`, proves the finite-set form of
Robert--Sargos (2002), Theorem 2. For every `epsilon>0` there is
`C_epsilon>0`, depending only on epsilon, such that

`card S <= C_epsilon*(R*N*H*Q)^(1+epsilon)*(1+delta*Q)`.

Its hypotheses are the actual seven integer coordinates, the paper's
strict r bound, half-open frequency and coefficient supports, closed
n supports, same-sign frequencies, literal line equation and
near-quadratic inequality. Scales satisfy `R,H,Q,N>=1`,
`R<=H/2` and `delta>0`. The
[closed-support assembly](Extension/TaoTrudgianYang2025/RobertSargosSevenCount.lean)
also allows delta zero. The source-to-closed-box bridge is proved in
Lean; endpoint conventions are not merely described in prose.

[Triple-gcd arithmetic](Extension/TaoTrudgianYang2025/IntegerTripleNormalization.lean)
proves divisibility, positivity, scaling and primitivity after exact
integer division. [The actual coordinate maps](Extension/TaoTrudgianYang2025/RobertSargosNormalizationCoordinates.lean)
restore every original point and are injective on each fixed gcd fiber.
[Source normalization](Extension/TaoTrudgianYang2025/RobertSargosNormalizedSystem.lean)
transports every sign, support, line and tolerance condition. The line
scales by `j*k` and the reduced quadratic by `j*k^2`; delta stays fixed.

[Integer frequency support](Extension/TaoTrudgianYang2025/RobertSargosNormalizedFrequency.lean)
permits the scale `Q'=max(1,Q/k)`. This covers `k>Q` as well as
`k<=Q`: normalized nonzero integer frequencies have absolute value
at least one. The larger scale only enlarges the permitted tolerance.
For the actual possible gcds, `j<=R`, `k<=2*Q` and
`Q'<=2*Q/k`. Thus no exceptional large-gcd range is dropped.

[The actual gcd-fiber consumer](Extension/TaoTrudgianYang2025/RobertSargosGcdFiberCount.lean)
applies the previously proved primitive theorem to the normalized
source image, preserving its cardinality.
[Uniform weighted fibers](Extension/TaoTrudgianYang2025/RobertSargosWeightedGcdFibers.lean)
are bounded by `C_epsilon*(R*H*Q)^(1+epsilon)*(1+delta*Q)/(j*k)`.
[Exact double harmonic summation](Extension/TaoTrudgianYang2025/RobertSargosGcdSums.lean)
and an epsilon split yield the
[full nonprimitive six-variable count](Extension/TaoTrudgianYang2025/RobertSargosReducedCount.lean).
This is a faithful alternative to the printed separate large-gcd
treatment, not a claim that its intermediate Lemma 6 inequality was
reproduced verbatim.

[The seven-variable source system](Extension/TaoTrudgianYang2025/RobertSargosSevenSystem.lean)
uses `d=n1-n2` and the exact quadratic cancellation.
[The multiplicity bridge](Extension/TaoTrudgianYang2025/RobertSargosSevenMultiplicity.lean)
reconstructs the original point from its reduced point and n2, giving
at most N original points per reduced fiber.
The nonzero-displacement branch therefore consumes the complete
six-variable count. The
[zero-displacement branch](Extension/TaoTrudgianYang2025/RobertSargosSevenZeroCount.lean)
instead uses the exact product `h2*q2=h1*q1`, nonzero factor-pair
divisor bounds and the actual four-coordinate source projection.
[The public assembly](Extension/TaoTrudgianYang2025/RobertSargosSevenCount.lean)
splits and sums the two disjoint branches with uniform constants.

All 20 modules are root-imported and in the BAT production inventory.
All 47 public theorems have explicit axiom audits and exact-signature
regressions. The 63 new regressions additionally test signed gcds,
actual quotient restoration, a source point with `k>Q`, both frequency
signs, zero displacement at delta zero, the half-open source bridge,
and distinct seven-coordinate points sharing one displacement key.
Both permanent counterexamples are retained.

The counting input of the independent EPZAE-15/26 Robert--Sargos 2002
route is now complete. The fourth-derivative finite-sum argument,
A-times-A differencing, shifts, partial summation, Taylor-error
consumption, double-large-sieve and parameter assembly remain OPEN.
No analytic exponent pair, growth end theorem or full EPZAE-26
density formula is claimed by the counting result.
The distinct 2003 C-process count is not substituted.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and the genuine boundary closure remain proved; EPZAE-29 still
needs analytic pair provenance. The separate false unrestricted growth
contract and sharper Atkinson source-form/smaller-width branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,325 production files, 1,799 scanned
  Lean files and 10,657 build jobs. Audit: 9,831 target, 6,240 pinned
  and five anchor theorems (16,076 total). All 47 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-175738-e35b7802.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_180657.log) and
  [manifest](../../logs/foundation_freeze_20260924_180657.json).
- All 1,820 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `ac26e8aedc1ed47935f4eacd20c77affaa292c6c19e58c4dc6c7ae4e30c4e267`;
  foundation `9435be034898c4d78180b88bceadc96b1c29d82490f0dc973d33287df0cea35d`;
  foundation manifest `c1db6b070e260d0bcbd8f35beda89c76c2d5ef62d169e97e8ca9f9e78dcc89fe`.


The synchronized architecture has 536 nodes and 1,331 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos finite A-times-A and C4 phase bridge — historical checkpoint

Twelve new production modules prove 33 public theorems, define seven
actual maps/functions and introduce the actual Taylor-coordinate system.
The new finite and local analytic inputs are proved; the full
fourth-derivative theorem remains OPEN. Completion stays 29/42.

[The Taylor-coordinate system](Extension/TaoTrudgianYang2025/RobertSargosTaylorSystem.lean)
uses the literal `h*q-r*n` equality and the complete polynomial
`h*q^2+2*h*q*n-r*n^2-r*h^2-r^2*h`. A proved involution reverses
r, preserving cardinality. The source-to-counting map charges both
lower-degree terms to `E+12*R*H^2`.
[The actual count consumer](Extension/TaoTrudgianYang2025/RobertSargosTaylorCount.lean)
then proves, uniformly for every epsilon,

`card S <= C_epsilon*(R*N*H*Q)^(1+epsilon)*
  (1+(E+12*R*H^2)/(H*Q))`.

The scales satisfy `R,H,Q,N>=1`, `E>=0` and `R<=H/2`.
The constant precedes every scale, tolerance and finite source set.
When `R*H^2<=E`, the final factor is at most
`1+13*E/(H*Q)`. The actual seven-variable theorem is consumed;
no Taylor-coincidence count is assumed.

[Finite-smoothness Taylor estimates](Extension/TaoTrudgianYang2025/FiniteSmoothTaylor.lean)
use only the required finite derivative order on the actual segment.
[The cubic phase identity](Extension/TaoTrudgianYang2025/RobertSargosCubicPhase.lean)
expands the genuine mixed symmetric difference. It retains the exact
constant term `-r^3*f'''(m)/3` and all four genuine remainder evaluations.
[All four remainder derivatives](Extension/TaoTrudgianYang2025/RobertSargosCubicJets.lean)
are bounded using local C4 regularity and a fourth-derivative bound;
infinite smoothness is not assumed. The fourth derivative is proved
equal to the original fourth derivative.
[Unit-phase extraction](Extension/TaoTrudgianYang2025/RobertSargosMixedCharacter.lean)
removes only the terms constant in q,h,n from the norm of the actual sum.
The mixed remainder remains inside the exponential; removing it by
multiple partial summation is still OPEN.

[Actual rectangular averaging](Extension/TaoTrudgianYang2025/RobertSargosPlaneAveraging.lean)
starts from an arbitrary complex array and its two-coordinate zero padding.
[Exact correlation reindexing](Extension/TaoTrudgianYang2025/RobertSargosPlaneCorrelation.lean)
transports every boundary term into the signed correlations
`Re(conj(a(m+q,h))*a(m,h+r))`. The real part agrees with the
conjugate orientation in the source.
[Signed shift multiplicities](Extension/TaoTrudgianYang2025/ShiftDifferenceWeights.lean)
count exactly `N-natAbs(d)` pairs for every integer d, including
zero and differences outside the interval.
[Product weights](Extension/TaoTrudgianYang2025/DoubleShiftWeights.lean)
and [the exact weighted Gram identity](Extension/TaoTrudgianYang2025/RobertSargosPlaneWeights.lean)
recover both factors `(1-|q|/Q)*(1-|r|/R)`.
Only the full weighted sum is shown nonnegative; individual correlations
are not assumed positive.

[The finite A-times-A theorem](Extension/TaoTrudgianYang2025/RobertSargosATimesA.lean)
proves the exact coefficient `(M+Q)*(H+R)/(Q*R)`, and hence
`4*M*H/(Q*R)` when `0<Q<=M` and `0<R<=H`, multiplying that
actual weighted correlation sum. There is no supplied correlation
majorant. This theorem uses the zero-based finite rectangle.
The paper's particular symmetric-phase array, translated supports,
zero-shift removal and boundary errors still need an explicit consumer;
the entire source Step 2 is not declared complete merely from this lemma.

All 12 modules are root-imported and in the BAT production inventory.
All 33 public theorems have explicit axiom audits and exact-signature
regressions. The 51 regressions additionally check the sign-reversal
consumer with unequal h coordinates, zero tolerance, the retained
Taylor correction and cubic constant sign, boundary zero padding,
positive/negative/zero/outside shift counts, a genuine signed
correlation, a concrete A-times-A specialization, and both permanent
counterexamples.

Still OPEN: initial conjugated A-process and source array entry,
dyadic selection, zero-shift estimates, shift/boundary errors, mixed
exponential derivatives and multiple partial summation, double-large-sieve,
sample spacing, scale assembly, the analytic pair and old-pair convex
deduction. The complete seven-variable Theorem 2 is not reopened.
The distinct nonconjugated 2003 C-process is not substituted.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and genuine boundary closure remain proved; EPZAE-29 still
needs analytic pair provenance. The separate false unrestricted
growth contract and sharper Atkinson branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,337 production files, 1,811 scanned
  Lean files and 10,669 build jobs. Audit: 9,919 target, 6,240 pinned
  and five anchor theorems (16,164 total). All 33 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-184000-aa3f7738.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_184448.log) and
  [manifest](../../logs/foundation_freeze_20260924_184448.json).
- All 1,832 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `9af4650ba9737e9a7095cdf81e4b7cc21d009c8196a0f75ffba92221555df7d0`;
  foundation `60248e9f7d35d5923ca1a994221c0c3137dd4114f0855501313b4e021d866dc9`;
  foundation manifest `7c3c4774b5e79d5853b2d9ac16eeb553ceebb8f44e193ad105564d33a8d78e12`.


The synchronized architecture has 539 nodes and 1,337 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos source A-times-A and boundary control — historical checkpoint

Nine new production modules prove 32 public theorems and define six actual
source objects. The source entry and endpoint replacement are proved;
the fourth-derivative theorem and analytic exponent pair remain OPEN.
Completion stays 29/42.

[The literal source entry](Extension/TaoTrudgianYang2025/RobertSargosSourceATimesA.lean)
translates the zero-based finite inequality into an arbitrary complex array
supported on the one-based rectangle. It proves the padded-array, sum and
correlation translations and consumes the existing A-times-A inequality.

[The actual symmetric array](Extension/TaoTrudgianYang2025/RobertSargosSymmetricArray.lean)
is `e(f(m+h)-f(m-h))` on `H<=h<2H`, `h+1<=m<=M-h`,
and zero elsewhere. Its coefficient norm, source support and exact source
sum are proved. [The correlation support](Extension/TaoTrudgianYang2025/RobertSargosCorrelationSupport.lean)
retains both h and h+r. Explicitly,

`max(H,H-r)<=h<=min(2H-1,2H-1-r)`,

`max(h+1-q,h+r+1)<=m<=min(M-h-q,M-h-r)`.

[The exact finite correlation sum](Extension/TaoTrudgianYang2025/RobertSargosCorrelationSum.lean)
and [source A-times-A consumer](Extension/TaoTrudgianYang2025/RobertSargosSymmetricATimesA.lean)
derive the actual phase-sum estimate with coefficient `8*M*H/(Q*R)`,
for `0<Q<=M`, `0<R<=2H`, and both signed triangular weights.
No correlation estimate or source-support identity is supplied as a hypothesis.

[Signed integer endpoint control](Extension/TaoTrudgianYang2025/IntegerIntervalBoundary.lean)
proves that replacing `[a+r,b-r]` by `[a,b]`, under any common finite
mask, changes a sum of unit-bounded coefficients by at most `2*abs(r)`.
It includes negative shifts and empty intervals.
[The actual source consumer](Extension/TaoTrudgianYang2025/RobertSargosCorrelationBoundary.lean)
therefore bounds the change in the h,m correlation by `2*H*abs(r)`.
The replacement changes only the m interval; the h overlap and the
actual mixed phase still depend on r.

[Exact triangular mass and first-moment bounds](Extension/TaoTrudgianYang2025/TriangularShiftBounds.lean)
and [the weighted endpoint assembly](Extension/TaoTrudgianYang2025/RobertSargosWeightedBoundary.lean)
give `robertSargos_trimmed_a_times_a`: the weighted simplified-endpoint
correlation, with coefficient `8*M*H/(Q*R)`, plus the explicit error
`16*M*H^2*R`. The r-dependent interval is not silently identified with
its r=0 version. For example, with M=20,h=3,q=1,r=1 the exact interval
is [5,16], whereas r=0 gives [4,16]; negative r=-1 gives [3,16].

All nine modules are root-imported and in the BAT production inventory.
All 32 public theorems have explicit axiom audits and exact-signature
regressions. Fifty regressions include positive/negative/zero/disjoint
h overlaps, exact m endpoints, the concrete lost and added boundary
points, actual phase-array support, triangular mass, signed endpoint
error specializations and both permanent counterexamples.

Still OPEN: initial conjugated A-process and dyadic selection, zero-shift
estimates, averaged translation and its common-interval errors, mixed
exponential derivatives and multiple partial summation, double-large-sieve,
sample spacing, scale assembly, the analytic pair and old-pair convex
deduction. The complete seven-variable Theorem 2, actual Taylor count,
finite C4 jets and source A-times-A entry are not reopened. The separate
nonconjugated 2003 route is not substituted for the initial A-process.

Corrected two-witness powering, the Heath--Brown energy relation, all nine
Add-est clauses and both counterexamples remain intact. EPZAE-28 and
boundary closure remain proved; EPZAE-29 still needs analytic pair
provenance. The false unrestricted growth contract and sharper Atkinson
branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,346 production files, 1,820 scanned
  Lean files and 10,678 build jobs. Audit: 10,029 target, 6,240 pinned
  and five anchor theorems (16,274 total). All 32 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-191338-7e77dde4.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_191859.log) and
  [manifest](../../logs/foundation_freeze_20260924_191859.json).
- All 1,841 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `139d22dedb82a5a3e31911a1bb99541e62ae59859b3b74a14f664d8df015f365`;
  foundation `3b0f166c299a00667bf585e7039be451ca364ccf9b0ef32a952bf48615569ba0`;
  foundation manifest `9ccf154b6d436f43c40eef6c32b6383cc9b48483fd1dcb8c26877e47b8556f09`.

The synchronized architecture has 541 nodes and 1,341 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos initial A-process and dyadic selection — historical checkpoint

Eleven new production modules prove 23 public theorems and define four
actual source objects. The initial conjugated A-process and actual
full doubled-block selection are proved. The fourth-derivative theorem
and analytic exponent pair remain OPEN. Completion stays 29/42.

[The centered conjugated Gram identity](Extension/TaoTrudgianYang2025/RobertSargosConjugateGram.lean)
starts from the actual zero-padded even-shift average. It reindexes every
term into `Re(conj(a(m-h))*a(m+h))`, proves negative-shift symmetry
and the exact diagonal, and counts signed shift multiplicities.
[Even-sum splitting](Extension/TaoTrudgianYang2025/SignedEvenSum.lean)
and [the initial A-process](Extension/TaoTrudgianYang2025/RobertSargosConjugateAveraging.lean)
retain the complete signed weighted correlation sum.
The separate nonconjugated 2003 construction is not substituted.

[The literal source phase](Extension/TaoTrudgianYang2025/RobertSargosSourceCenteredPhase.lean)
has exactly `h+1<=m<=M-h`; its padded inner-product and translated
sum identities are proved.
[The source A-process](Extension/TaoTrudgianYang2025/RobertSargosSourceAProcess.lean)
then bounds the original one-based exponential sum by
`3*M^2/H+(6*M/H)*norm(weighted symmetric phase sum)`, for
`0<H<=M`. It takes the norm after summing over h, not the sum of
individual correlation norms.

[Full doubled-block prefix control](Extension/TaoTrudgianYang2025/DoubledBlockPrefixes.lean)
uses halving with a one-coefficient cost at odd endpoints.
[Exact finite Abel summation](Extension/TaoTrudgianYang2025/LinearWeightAbel.lean)
removes the actual descending weight `1-h/H` with total variation
budget exactly one.
[The attained block selection](Extension/TaoTrudgianYang2025/DoubledBlockSelection.lean)
chooses an actual positive integer k with `2*k<=H`; no truncated
block is relabeled as a full doubled interval.

[The source-sequence consumer](Extension/TaoTrudgianYang2025/RobertSargosDyadicSequence.lean)
proves its coefficient bound M, its weighted-sum identity, and equality
of every selected block with `robertSargosSymmetricSum f M k`.
[Exact finite-log assembly](Extension/TaoTrudgianYang2025/RobertSargosInitialDyadic.lean)
and [the logarithmic source theorem](Extension/TaoTrudgianYang2025/RobertSargosInitialDyadicLog.lean)
prove, for every real phase f and `2<=H<=M), that some `k>0`,
`2*k<=H` satisfies

`norm(sum_{1<=m<=M} e(f(m)))^2 <=
  15*(log H/log 2)*(M^2/H+(M/H)*norm(robertSargosSymmetricSum f M k))`.

This is an actual source consumer through the initial dyadic selection,
with no supplied prefix bound, desired correlation estimate or analytic
exponent pair. The selected symmetric sum is exactly the object consumed
by the previously proved source A-times-A theorem. The small-k
third-derivative branch is still required before the later scale restriction.

All 11 modules are root-imported and in the BAT production inventory.
All 23 public theorems have explicit axiom audits and exact-signature
regressions. The 35 regressions also check genuine positive/negative
centered correlations, one-based phase endpoints, empty centered support,
an actual weighted source sum, the zero-index convention, a complete
doubled block, odd/power-of-two logarithms and both permanent counterexamples.

Still OPEN: small-block and zero-shift derivative estimates, averaged
translation and common-interval boundary errors, mixed exponential
derivatives and multiple partial summation, double-large-sieve, sample
spacing and parameter assembly. The source Step 0 short/long-length
reductions, fourth-derivative theorem and analytic pair also remain open.
The counting theorem, Taylor count, finite C4 jets, source A-times-A entry,
charged endpoint replacement and initial dyadic reduction are not reopened.

Corrected two-witness powering, the Heath--Brown energy relation, all nine
Add-est clauses and both counterexamples remain intact. EPZAE-28 and
boundary closure remain proved; EPZAE-29 still needs analytic pair
provenance. The false unrestricted growth contract and sharper Atkinson
branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,357 production files, 1,831 scanned
  Lean files and 10,689 build jobs. Audit: 10,141 target, 6,240 pinned
  and five anchor theorems (16,386 total). All 23 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-194338-87f51c8f.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_194839.log) and
  [manifest](../../logs/foundation_freeze_20260924_194839.json).
- All 1,852 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `2b3e3e0230398729e722180595fe19b2208997e7b4a5a1ff15460d6a1bdc193a`;
  foundation `c37370285cf085ce5510c99751d73c7fe89ea523b485515d7901f5b35e956b5d`;
  foundation manifest `6393e3e957f0077e7e395f50dc419abb91e7d2bed8eb3c6e3c730510f38221be`.

The synchronized architecture has 543 nodes and 1,346 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos common shifted interval and triple sum — historical checkpoint

Eight new production modules prove 20 public theorems and define four
actual finite source objects. Averaged translation, a genuinely common
m interval, charged boundary errors and the actual reordered triple-sum
consumer are proved. Completion stays 29/42; the fourth-derivative
theorem and analytic exponent pair remain OPEN.

[Integer translation and averaging](Extension/TaoTrudgianYang2025/IntegerIntervalShift.lean)
are exact, including empty intervals.
[The shifted support](Extension/TaoTrudgianYang2025/RobertSargosShiftSupport.lean)
is the literal translated intersection
`[max(h+1,h+1-q)-n,min(M-h,M-h-q)-n]`.
For `H<=h<2H`, `|q|<Q`, and `1<=n<=N`, the proved common
core is `[2H+Q,M-2H-Q-N]`; every shifted interval lies inside
`[-Q-N,M+Q]`. Its difference from the common core has cardinality
at most `4H+4Q+2N`, even when the core is empty.

This deliberately corrects an auxiliary containment in Section 4,
Step 3; it does not change the final paper theorem.
The printed lower endpoint `H+Q` fails, for example at
`M=100,H=3,Q=N=5,h=5,q=-4,n=1`: its proposed core contains 8,
but the shifted interval starts at 9. The printed outer interval
`[1,M]` also fails for `M=100,h=3,q=0,n=5`, whose shifted
interval starts at -1. Both failures are permanent numeric regressions;
the replacement containments and all omitted terms are proved and charged.

[The literal boundary bridge](Extension/TaoTrudgianYang2025/RobertSargosShiftBoundary.lean)
and [the averaged error](Extension/TaoTrudgianYang2025/RobertSargosAverageBoundary.lean)
apply this cardinality bound to unit-modulus phases.
[The actual shifted correlation](Extension/TaoTrudgianYang2025/RobertSargosShiftedCorrelation.lean)
retains the r-dependent h intersection and the full mixed phase.
[The weighted A-times-A consumer](Extension/TaoTrudgianYang2025/RobertSargosWeightedShift.lean)
uses the exact signed triangular mass `Q*R`; the new boundary
cost is `8*M*H^2*(4H+4Q+2N)`, in addition to the previously
proved `16*M*H^2*R` endpoint cost.

[Exact reordering](Extension/TaoTrudgianYang2025/RobertSargosShiftReorder.lean)
puts m outside the q,h,n sum before taking its norm.
[The actual triple-sum bound](Extension/TaoTrudgianYang2025/RobertSargosShiftedTripleBound.lean)
proves, for positive Q,R,N with `Q<=M` and `R<=2H`,

`norm(SymmetricSum)^2 <=
  8*M*H/(Q*R*N) * sum_r sum_m norm(ShiftedTriple(r,m))
  +16*M*H^2*R +8*M*H^2*(4H+4Q+2N)`.

The m sum is over the proved common core; r ranges over all signed
shifts. The triple sum is the actual q,h,n phase sum, not a supplied
bound. All zero shifts are still included: their analytic removal
is OPEN and is not hidden in the reordering.

All eight modules are root-imported and in the BAT production inventory.
All 20 public theorems have explicit audits and exact-signature regressions.
The 34 regressions also preserve both original counterexamples and test
the faulty auxiliary endpoints, corrected containment, boundary cardinality,
empty intervals, translation and actual source sums.

Still OPEN: small-block and zero-shift derivative estimates, mixed
exponential derivatives and multiple partial summation, double-large-sieve,
sample spacing and parameter assembly. The Step 0 short/long-length
reductions, fourth-derivative theorem and analytic pair remain open.
The counting theorem, Taylor count, finite C4 jets, initial dyadic
reduction, source A-times-A, charged endpoints and shifted averaging
are not reopened.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and boundary closure remain proved; EPZAE-29 still needs
analytic pair provenance. The false unrestricted growth contract and
sharper Atkinson branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,365 production files, 1,839 scanned
  Lean files and 10,697 build jobs. Audit: 10,197 target, 6,240 pinned
  and five anchor theorems (16,442 total). All 20 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-200527-b6a771be.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_201100.log) and
  [manifest](../../logs/foundation_freeze_20260924_201100.json).
- All 1,860 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `3268eb8147dcd7bb4aad1a773dca6fb1981027a884055aba8d3213821b02b2b7`;
  foundation `38347d7c6e906cf3ffb9f0d614810c234bec5617e0119c3900bb19b5e1529ad4`;
  foundation manifest `87d3ea5d0744487743137f6e563c8749a00b68570c2ae984e6f7f17fba3759df`.

The synchronized architecture has 545 nodes and 1,350 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Standard third-derivative estimate — historical checkpoint

Seventeen new production modules prove 31 public theorems and define
one actual correlation object. The ordinary third-derivative test is
proved for both curvature signs, every finite length and finite local
C3 regularity. This is not the sharper printed Robert--Sargos Lemma 3.
The source-specific small-block and zero-shift consumers remain OPEN;
completion stays 29/42.

[Continuous derivative transfer](Extension/TaoTrudgianYang2025/ContinuousDerivativeBounds.lean)
proves increment and unit-spaced second-difference bounds by mean-value
theorems. [The explicit scale bound](Extension/TaoTrudgianYang2025/SecondDerivativeScale.lean)
and [the continuous second-derivative consumer](Extension/TaoTrudgianYang2025/ContinuousSecondDerivative.lean)
apply the native van der Corput theorem to the actual additive character,
with a proved radians conversion and the reciprocal-curvature term retained.

[Shifted third-derivative curvature](Extension/TaoTrudgianYang2025/ThirdDerivativeShift.lean)
and [actual correlations](Extension/TaoTrudgianYang2025/ThirdDerivativeCorrelation.lean)
derive bounds for `sum_{n<N-r} e(F(A+n+r)-F(A+n))`, including empty
overlap. [Square-root shift sums](Extension/TaoTrudgianYang2025/SquareRootShiftSums.lean)
and [their majorant consumer](Extension/TaoTrudgianYang2025/ThirdDerivativeCorrelationSum.lean)
retain the actual sum of correlations.
[The literal Weyl entry](Extension/TaoTrudgianYang2025/ContinuousPhaseWeyl.lean)
proves padded reindexing, sign reversal and the finite source inequality.

[The assembled Weyl estimate](Extension/TaoTrudgianYang2025/ContinuousThirdDerivativeWeyl.lean),
[its normalization](Extension/TaoTrudgianYang2025/ThirdDerivativeWeylScale.lean),
[physical root-scale bounds](Extension/TaoTrudgianYang2025/ThirdDerivativeRootScale.lean)
and [integer floor choice](Extension/TaoTrudgianYang2025/ThirdDerivativeFloor.lean)
optimize the shift internally.
[The all-length squared theorem](Extension/TaoTrudgianYang2025/ContinuousThirdDerivativeSquare.lean)
also handles short sums directly.
[Norm conversion](Extension/TaoTrudgianYang2025/ThirdDerivativeNormScale.lean)
and [exact rational exponents](Extension/TaoTrudgianYang2025/ThirdDerivativeRpowScale.lean)
give [the standard third-derivative theorem](Extension/TaoTrudgianYang2025/ContinuousThirdDerivative.lean):

`norm(sum_{n<N} e(F(A+n))) <=
  20*C*(N*mu^(1/6)+sqrt(N)*mu^(-1/6))`.

The hypotheses are `C>=1`, `0<mu<=1`, the actual derivative chain
on `[A,A+N]`, and either `mu<=F'''<=C*mu` or
`-C*mu<=F'''<=-mu` throughout that interval.
[Finite-smoothness consumers](Extension/TaoTrudgianYang2025/FiniteSmoothThirdDerivative.lean)
derive the derivative chain from local C3 regularity only. No desired
exponential-sum bound, exponent pair, infinite smoothness or external
certificate is supplied as a hypothesis.

The exact sample set is `A,...,A+N-1`; the derivative interval includes
`A+N`. A source closed-interval consumer must prove this endpoint
coverage or charge the final sample separately. The theorem is not
silently applied outside the paper's domain.
Its secondary term `sqrt(N)*mu^(-1/6)` is weaker than the sharper
printed Lemma 3. Whether it suffices for each source budget must be
proved in the actual consumer.

All 17 modules are root-imported and in the BAT production inventory.
All 31 public theorems have explicit audits and exact-signature regressions.
The 42 regressions include a genuine cubic phase, empty/nonempty
correlations, square-root and floor endpoints, a physical cube-root
identity and both permanent counterexamples.

Still OPEN: actual small-block and zero-shift derivative consumers,
mixed exponential derivatives and multiple partial summation,
double-large-sieve, sample spacing and parameter assembly. Step 0
length reductions, the fourth-derivative theorem and analytic pair
remain open. Counting, finite C4 jets, initial dyadic reduction,
source A-times-A and corrected common shifted averaging remain proved.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and boundary closure remain proved; EPZAE-29 still needs
analytic pair provenance. The false unrestricted growth contract and
sharper Atkinson branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,382 production files, 1,856 scanned
  Lean files and 10,714 build jobs. Audit: 10,250 target, 6,240 pinned
  and five anchor theorems (16,495 total). All 31 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-204751-6ad586bb.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_205234.log) and
  [manifest](../../logs/foundation_freeze_20260924_205234.json).
- All 1,877 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `ad473d8c9b48c117cd583b62bf3bfe5741fa4188385b3d6d5e3ba7371e78c927`;
  foundation `8397afcbb96db0c0c6a4cf6dc6a86c4276034dafce4fe97a5039255cb3ad4242`;
  foundation manifest `acb4223d9d11bf61a9574fe7a22948f821c091f90081b32a2194de9fd68cbd60`.

The synchronized architecture has 547 nodes and 1,355 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos physical initial reduction — historical checkpoint

Eleven new production modules prove 18 public theorems.
The actual symmetric source phase, its closed interval, full doubled
block and small-block physical scales are now connected to the original
one-based exponential sum. The physical initial reduction is proved:
either its small branch satisfies the required squared lambda-scale
bound, or an actual large dyadic block is returned. Completion stays
29/42; zero shifts and the fourth-derivative theorem remain OPEN.

[The actual symmetric-phase derivative bridge](Extension/TaoTrudgianYang2025/RobertSargosSymmetricThirdDerivative.lean)
derives its first three derivatives and third curvature from finite
local C4 regularity of f and `lambda<=f''''<=C*lambda`.
It consumes the ordinary third-derivative theorem on the genuine phase
`f(x+h)-f(x-h)`, not a separately supplied analytic model.

[The closed-interval prefix bridge](Extension/TaoTrudgianYang2025/IntegerClosedIntervalPrefix.lean)
splits the last integer endpoint exactly.
[The literal centered-source estimate](Extension/TaoTrudgianYang2025/RobertSargosSourceThirdDerivative.lean)
charges that endpoint by one and never differentiates outside `[1,M]`.
Empty and singleton intervals are covered.
[The actual doubled-block theorem](Extension/TaoTrudgianYang2025/RobertSargosSymmetricBlockThirdDerivative.lean)
sums the source centered phases over exactly `H<=h<2H`.

[The polynomial scale budgets](Extension/TaoTrudgianYang2025/RobertSargosSmallBlockScale.lean)
and [their physical-parameter derivation](Extension/TaoTrudgianYang2025/RobertSargosSmallBlockParameters.lean)
show that `H<=lambda^(-1/7)`, `M>=lambda^(-8/13)` and
`0<lambda<=1/16` discharge both ordinary third-derivative terms.
[The actual small-block consumer](Extension/TaoTrudgianYang2025/RobertSargosSmallBlock.lean)
therefore proves `norm(SymmetricSum f M H)<=61*C*M`.
No correlation estimate or parameter budget is left as an assumed result.

[The initial selected-block dichotomy](Extension/TaoTrudgianYang2025/RobertSargosInitialSmallBlock.lean)
unpacks the previously proved dyadic witness.
[The physical floor choice](Extension/TaoTrudgianYang2025/RobertSargosPhysicalShift.lean)
sets `H=floor(lambda^(-2/13))` and proves its size bounds.
[The logarithmic/floor budget](Extension/TaoTrudgianYang2025/RobertSargosInitialFloorBudget.lean)
and [the physical source reduction](Extension/TaoTrudgianYang2025/RobertSargosPhysicalInitialReduction.lean)
prove, for `C>=1`, `0<lambda<=1/8192`,
`M>=lambda^(-8/13)` and the actual C4/fourth-derivative hypotheses,
the following alternative:

- the original sum S satisfies
  `norm(S)^2<=1860*C*(log M/log 2)*M^2*lambda^(2/13)`; or
- there is an actual integer k with `0<k`,
  `lambda^(-1/7)<k<=lambda^(-2/13)/2`,
  `2*k<=floor(lambda^(-2/13))`, and the exact initial
  logarithmic inequality involving `robertSargosSymmetricSum f M k`.

This closes the small-block branch and retains the genuine large-block
witness for the remaining argument. It does not close the large branch,
zero-shift removal, source length reductions or fourth-derivative theorem.
The ordinary third-derivative test is sufficient here; the sharper
printed Lemma 3 is neither assumed nor claimed proved.

All 11 modules are root-imported and in the BAT production inventory.
All 18 public theorems have explicit audits and exact-signature regressions.
The 30 regressions also check closed/empty/singleton endpoints,
actual centered and doubled source sums, polynomial scale cases,
the secondary-exponent margin and both permanent counterexamples.

Still OPEN: zero-shift removal, mixed exponential derivatives and
multiple partial summation, double-large-sieve, sample spacing and
remaining scale assembly. Step 0 short/long-length reductions,
the fourth-derivative theorem and analytic pair remain open.
The actual counting theorem, C4 jets, initial small-block reduction
and corrected common shifted averaging remain proved.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and boundary closure remain proved; EPZAE-29 still needs
analytic pair provenance. The false unrestricted growth contract and
sharper Atkinson branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,393 production files, 1,867 scanned
  Lean files and 10,725 build jobs. Audit: 10,288 target, 6,240 pinned
  and five anchor theorems (16,533 total). All 18 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-211646-c8474b8a.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_212220.log) and
  [manifest](../../logs/foundation_freeze_20260924_212220.json).
- All 1,888 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `af5e7085b866b63f7c77950feff3cee8379502b2bdbc0ae65c0c4a8f80868583`;
  foundation `20ecd1554652f6048d46d9b245f4bf45dd74ec13fd11aa333c1c60ad4cd23851`;
  foundation manifest `5a3e89f9bfa181c81801423c4aef46d8081fdda83f10552ef02a20b205fe09a7`.

The synchronized architecture has 549 nodes and 1,360 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.

## Robert–Sargos zero-r row — current checkpoint

Fifteen new production modules prove 25 public theorems and introduce
one actual source-sum definition. The nonzero-q, zero-r row is now
controlled at the actual floor parameters. Completion stays 29/42.

[The second-derivative range bridge](Extension/TaoTrudgianYang2025/ContinuousSecondDerivativeRange.lean)
covers both curvature signs and empty ranges.
[The genuine mixed curvature](Extension/TaoTrudgianYang2025/RobertSargosZeroRCurvature.lean)
and [finite-prefix consumer](Extension/TaoTrudgianYang2025/RobertSargosZeroRPrefix.lean)
derive the actual mixed phase from finite C4 regularity and
`lambda<=f''''<=C*lambda`. For positive h,q its second curvature lies
between `2*h*q*lambda` and `C*(2*h*q*lambda)`.

[The literal zero-r source](Extension/TaoTrudgianYang2025/RobertSargosZeroRSource.lean)
retains the true closed interval `[h+1,M-h-q]` for positive q.
An exact translation/conjugation identity handles negative q.
[The closed-source bound](Extension/TaoTrudgianYang2025/RobertSargosZeroRPositiveBound.lean)
charges its last endpoint by one, including empty intervals, and
[the signed consumer](Extension/TaoTrudgianYang2025/RobertSargosZeroRSignedBound.lean)
never assumes differentiation outside `[1,M]`.

[The actual h-block](Extension/TaoTrudgianYang2025/RobertSargosZeroRBlock.lean),
[signed square-root sums](Extension/TaoTrudgianYang2025/SignedSquareRootSums.lean),
[summed majorant](Extension/TaoTrudgianYang2025/RobertSargosZeroRMajorant.lean) and
[weighted row](Extension/TaoTrudgianYang2025/RobertSargosZeroRWeighted.lean)
preserve the h-mask and triangular q weight and explicitly exclude q=0.

[Root budgets](Extension/TaoTrudgianYang2025/RobertSargosZeroRRootBudget.lean),
[polynomial scale inequalities](Extension/TaoTrudgianYang2025/RobertSargosZeroRPolynomialBudget.lean),
[thirteenth-root and floor losses](Extension/TaoTrudgianYang2025/ThirteenthRootScales.lean)
and [actual floor budgets](Extension/TaoTrudgianYang2025/RobertSargosZeroRFloorBudgets.lean)
discharge every parameter inequality.
[The physical source theorem](Extension/TaoTrudgianYang2025/RobertSargosZeroRPhysical.lean)
proves the actual row contribution after multiplication by `8*M*H/(Q*R)`
is at most `1168*C*M^2`, with
`Q=floor(lambda^(-3/13))`, `R=floor(lambda^(-1/13))`,
`0<H<=lambda^(-2/13)/2`, `M>=lambda^(-8/13)`,
`0<lambda<=1/8192`, `C>=1`, and the actual C4/fourth-derivative hypotheses.
No desired source correlation estimate or floor budget is assumed.

All 15 modules are root-imported and in the principal BAT production
inventory; all 25 public theorems have explicit audits and exact-signature
regressions. The 39 regressions also cover signed and empty intervals,
source sums, exact curvature, zero exclusions, floor/polynomial cases
and both permanent counterexamples.

Still OPEN: the zero-q/nonzero-r column, zero-zero diagonal, combined
zero-shift removal, mixed derivatives and common-prefix multiple partial
summation, double-large-sieve, sample spacing, remaining scale assembly,
Step 0 length reductions, fourth-derivative theorem and analytic pair.
The already proved small-block branch and actual large-block witness
are retained. The sharper printed Lemma 3 is not assumed or claimed proved.

Corrected two-witness powering, the Heath--Brown energy relation,
all nine Add-est clauses and both counterexamples remain intact.
EPZAE-28 and boundary closure remain proved; EPZAE-29 still needs
analytic pair provenance. The false unrestricted growth contract and
sharper Atkinson branch remain open.


Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,408 production files, 1,882 scanned
  Lean files and 10,740 build jobs. Audit: 10,348 target, 6,240 pinned
  and five anchor theorems (16,593 total). All 25 new public theorems
  appear exactly once in the explicit audit and exact-signature
  regressions, with only permitted logical dependencies. The
  [extension log](logs/tao-trudgian-yang-build-20260924-215011-9a656b8c.log) has no errors,
  warnings, tactic suggestions or linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics, 8,857 build jobs,
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_215523.log) and
  [manifest](../../logs/foundation_freeze_20260924_215523.json).
- All 1,903 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `f730254e6d958cf725f04d55c6d6fa4fdf71959c`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
- Log SHA-256: extension `abf273589d77b68d0d3327c526604b614aea08a480e35037295dbaf9e3399a4e`;
  foundation `7d1f5532d150748919c72ecacc9a630afe8ee891c8e8fab63d637fe15a30abec`;
  foundation manifest `1046f329cd8008e746beaad1602792cbf3453b52132ab5adb36ee67f33703724`.

The synchronized architecture has 550 nodes and 1,365 edges,
with no duplicate or missing endpoints, class conflicts or unclassified
nodes. The whole-proof goal remains active and incomplete.
Recovery-record maintenance is permanently skipped; no such file was changed.
