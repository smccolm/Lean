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
are kernel-checked. The consumers remain conditional on actual powering
witnesses and the analytic relation; neither input is proved by defining the
target. General powering and all advertised endpoints remain open.

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
