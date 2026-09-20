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
   witnesses. Prove the now-authorized cardinality/energy replacement in
   EPZAE-34 before using it analytically. See the preserved obstruction and
   repair status below.
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
The bounded general-energy reduction also needs a valid energy-powering
argument. The exact five-coordinate source claim owned by EPZAE-34 is
disproved, as recorded below; it cannot be used as an upstream theorem.

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

The general analytic powering theorem is still open: construct normalized
powered patterns with proved closed/half-open endpoint bridges, choose
uniform coefficient constants before scales, then extract the two
coordinate-preserving subsequences. EPZAE-34 stays unchecked. EPZAE-35
still owns the analytic Heath--Brown relation; EPZAE-36 must replay all
optimization constraints using the justified four-coordinate rules, and
EPZAE-37 must derive all nine unchanged endpoints.

The repair report includes a mathematical proof route and a static audit of
the pinned optimizer. Its Heath--Brown `2a` alternatives have zero `s`
coefficient, but historical five-coordinate transforms and finite boxes
must not be trusted without the new proof. No full certificate replay is
claimed. Authorization is no longer a blocker.

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
| False fifth-coordinate powering | Singleton patterns contradict `s' ≤ s/k` already for `k=2` | Preserve counterexample; prove authorized two-witness repair; prohibit scaled `s` constraints in all new certificates |
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
