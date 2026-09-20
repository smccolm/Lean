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
energy chain through clause (i), retaining the moment and short-zeta
inputs. These six modules have 38 named public theorem audits, an explicit
derivative-test constructor audit, and 14 semantic regressions, with root
and principal-runner coverage. The moment itself, short-zeta transfer,
other source moment parameters, and all final `Add-est` clauses remain open.

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
