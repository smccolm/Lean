# Tao--Trudgian--Yang 2025 research agenda

## Executive assessment

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

## Implementation status (19 September 2026)

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

## Next sprint

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
consumers only. Next prove the maximal phase-sum/Gram estimate with
the required height scales and spacing. The inspected adjacent prefix
Gram theorem has one common prefix at every height and interval (K,2K];
it cannot be applied directly to these height-dependent maxima on [M,2M).
Prove the variable-prefix and endpoint bridges before reusing that result.
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
