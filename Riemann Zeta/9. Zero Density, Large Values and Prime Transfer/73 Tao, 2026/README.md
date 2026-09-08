# Tao 2026 formalization

This directory is the active formalization project for Terence Tao,
*Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`. The paper and its TeX source are pinned under `Sources/`.

**Status:** Proposition 2.3(i),(iii) and complete Lemma 3.2 milestone.
Bertrand's clause (i), the exact Guth--Maynard application in clause (iii),
and the polynomial-coefficient powerful relation are proved and audited; none of the four main
Theorems 1.7--1.10 is proved or claimed. The isolated `Extension/` package
contains the compiled arithmetic-anatomy, interval, counting, and
asymptotic-language definitions required to state the source results, plus a
kernel-checked proof of Tao's global constant-length prime-free endpoint
measure bound, derived from the frozen Guth--Maynard/Gafni--Tao chain. It also
proves the exact unique `p²m` representation of `B¹` and Tao's finite
prime-indexed smooth-number sum. It also proves the unique `a²b³`
representation of positive powerful numbers and the exact finite squarefree-
cube sum for `VB¹`. Dominated convergence gives its normalized squarefree
`b⁻³ᐟ²` limit. A kernel-checked square-times-squarefree reindexing and the
Dirichlet series for the pinned Mathlib Riemann zeta function identify that
limit with `ζ(3/2)/ζ(3)`, proving the exact one-term asymptotic required by
Theorem 1.8.
The source's `H≥1` convention is enforced in every interval predicate, and the
exact type-`F₃` right-endpoint correspondence with the three-factorial square
equation is proved. The finite largest-index projection is also proved to hit
exactly `F₃∩[1,x]`, yielding the lower cardinal direction for Theorem 1.10.
The one-term `F₃¹` square-multiple characterization and its distinct-square
subfamily give an unconditional `⌊√x⌋-1` lower bound first for `F₃¹`, then
for `F₃` and factorial solutions; the corresponding triple is explicit.
These finite bounds have been lifted to the complete reverse-big-O half of
the square-root `PowerScale` contracts for Theorems 1.9 and 1.10.
The Erdős--Selfridge source is pinned, and the exact reduction from a repeated
factorial squarefree component to a square consecutive product is proved;
the no-square theorem itself remains to be formalized.
The finite counts for `B`, `VB`, and `F₃` also have audited exact
`nontrivial + one-term = total` decomposition identities.
For `VB¹`, the full source constant asymptotic
`#(VB¹∩[1,x]) ~ ζ(3/2)/ζ(3) √x` is proved and audited. The nontrivial-`VB`
upper bound remains open, so Theorem 1.8 itself is not yet claimed.
The elementary first step of Lemma 3.1 is also proved for positive starting
points: a very bad interval has `H<N`. The crosswalk records the genuine
`N=0,H=1` edge case in the paper's unrestricted wording.
For Lemma 3.2, every interval element now has a canonical, audited
factorization into its squarefree exponent-one coefficient and a powerful
core. In a very bad interval every prime of that coefficient is at most `H`,
the coefficient divides `H!`, and any two positions give the source's exact
linear relation. An exact interval-multiple count bounds the product of all
coefficients by a small-prime envelope. Finite Abel summation and Chebyshev's
explicit theta bound give `log(envelope) ≤ C H log H`; averaging over two
disjoint interval halves then selects distinct coefficients bounded by
`H^(3C)`. Thus the full nonzero-shift conclusion `a*n+h=b*m`, with `0<h<H`
and powerful `n,m`, is proved with one explicit absolute exponent.
The finite powerful-pair count entering Corollary 2.11 is additionally
reindexed by the unique square-times-squarefree-cube parameters with a proved
bijection and exact cardinal equality. The square-discriminant branch of
Lemma 2.10 is also proved for the source's nonzero integer shift: solutions
inject into the signed divisors of `a*h`, giving the required divisor-epsilon
estimate in that branch. The nonsquare norm
encoding is injective and the norm-one Pell action on fixed-norm fibers of
`ℤ[√D]` is verified. Fundamental-unit powers have an exponential coordinate
lower bound and an exact logarithmic candidate count. On a nonzero fixed-norm
fiber, two elements generate the same principal ideal exactly when they lie
in the same norm-one Pell orbit; that principal ideal is proved to divide
`(N)`, giving an exact orbit-to-ideal-divisor map. The Galois fundamental
identity also gives the required abstract at-most-two prime-splitting bound
for degree-two Galois extensions. The concrete field `ℚ[X]/(X²-D)` is now
proved irreducible and quadratic, `√D` is placed in its actual ring of
integers, and the canonical map `ℤ[√D] → 𝓞(ℚ(√D))` is proved injective.
Every fixed-norm point now generates a divisor of `(N)` in that maximal order;
the finite divisor set is constructed, its fibers are identified with
maximal-order unit association classes, and the at-most-two splitting theorem
is instantiated for every rational prime. The sharp `d(|N|)²` cardinal bound,
height control within each maximal-order unit orbit, and subsequent
quantitative assembly remain open.

Node 73 keeps the human-readable location assigned by the RH Map. The exact
1,226-module Lean import closure of `GafniTao.Theorem11` is frozen under this
node with per-file SHA-256 hashes. The first Tao-facing quantitative bridge is
proved. The literal variable-length dyadic prime-free set has now been shown
measurable and eventually contained in Gafni--Tao's discrepancy exceptional
set, with the higher-prime-power tail retained and bounded. The finite dyadic
assembly and the `theta >= 1` monotonicity case are also proved, yielding the
full source range `theta > 2/15`.

## Layout

- `Sources/`: exact paper artifacts, version pins, provenance, and hashes.
- `Dependencies/GafniTaoFrozen/`: immutable, hashed source closure of the
  Gafni--Tao theorem input, including its frozen Guth--Maynard foundation and
  PNT+ dependencies.
- `Extension/`: isolated Lean package named `Tao2026`, pinned to the exact
  Mathlib revision used by node 74.
- `Tools/`: reproducible snapshot refresh tooling and the evolving
  warning-failing project verifier. It is not yet the final proof-release
  verifier.

## Current verification

From this directory, run:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The runner checks all pinned source hashes, all 1,226 frozen dependency hashes and the exact
frozen file set, the raw Mermaid contract, toolchain/dependency pins, direct
production-root coverage, forbidden proof shortcuts in both production and
frozen source, the axiom audit, and the warning-free Lake build. Its current
success certifies Proposition 2.3(i),(iii), the exact one-term sums, the exact
zeta-ratio asymptotic for `VB¹`, complete Lemma 3.2, and the factorial endpoint/counting
bridges; it does not certify a main theorem.

## Project-control documents

The node follows the useful role separation established in node 74:

- `README.md`: public status, layout, and entry points.
- `Tao Architecture.md`: raw Mermaid planning dashboard; no Markdown wrapper.
- `Tao Checklist.md`: detailed readiness and future completion ledger.
- `Tao Goal Prompt.md`: activation contract for the future implementation
  agent.
- `Tao Research Agenda.md`: source-first sequencing and scope controls.
- `Tao Crosswalk.md`: active paper-to-Lean mapping and semantic-gap ledger.
- `Tao Sources.md` and `Sources/`: source policy, artifacts, pins, and hashes.
- `Tao Reproduction Manifest.md`: what can truthfully be reproduced now.

## Next legitimate step

For Theorem 1.8, formalize Theorem 2.5 and the generalized-Pell/Corollary 2.11
powerful-relation count, then combine them with the now-complete Lemma 3.2.
In parallel source order, the pinned Baker--Harman--Pintz input in Proposition
2.3(ii) remains the next missing analytic boundary for Section 4.

## Deliberate non-claims

This development milestone does not claim any of Theorems 1.7--1.10,
publication readiness, external review, or a route to the Riemann Hypothesis.
The formal connection to nodes 71 and 74 is limited to the frozen, hashed
dependency closure and the audited quantitative bridge described above.

## Repository synchronization

`push_to_github.bat` is the existing owner-operated repository synchronization
script. It is not called by the build or development verifier.
