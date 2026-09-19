# Lean extension

This directory contains the unified Lean 4.30 package. It imports both the
frozen ANTEDB compatibility subset and the canonical local `RiemannZeta`
package, including the Guth--Maynard publication contracts.

The currently kernel-checked modules provide dependency bridges, rational
function sign certificates, piecewise-envelope machinery, polyhedral witness
soundness, exact optimized-Bourgain endpoints/coverage, and analytic
exponent-pair semantics with its non-asymptotic equivalence. No advertised
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
