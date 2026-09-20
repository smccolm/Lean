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
image-finset energy is proved equal to the indexed class energy. No advertised
paper theorem is claimed complete yet.

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
