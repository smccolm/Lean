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
is instantiated for every rational prime. The sharp `d(|N|)^2` cardinal bound,
the bridge from boxed norm points to the required logarithmic place cutoff,
and a uniform lower bound for the chosen growth base are now proved. Together
with the square-discriminant factorization, these close Lemma 2.10 for its
literal nonzero integer shift and polynomial parameter families. The full
maximal-order unit group itself is handled:
the field is proved totally real of signature `(2,0)`, its unit rank is one,
its torsion subgroup is exactly `{±1}`, and every unit has a unique
torsion-times-integer-power decomposition. After orienting the generator at a
nontrivial real place, units under the cutoff `B log λ_D` lie in an explicit
finite family of cardinality at most `2(2B+1)`.
Corollary 2.11 is also complete. The canonical square-times-squarefree-cube
representations are partitioned into exact four-coordinate dyadic blocks;
the two coordinate projections and the Lemma 2.10 square fiber give the three
source bounds, and their `2/5,2/5,1/5` interpolation yields the sharp
`x^(2/5+o(1))` estimate. The final theorem uses the literal signed-shift set
and the paper's uniform `a,b,|h| ≪ x` family contract.
The exact finite prime sum, logarithmic integral, periodicity convention, and
`C³` norm appearing in Theorem 2.5 are now represented by compiled Lean
definitions, and its `M=N,j=2` consumer is formally derived from the full
contract. The source's reciprocal exponential phase is also formalized: its
all-orders derivative, signed-factorial form, binomial `M_r` coefficient, and
normalized absolute derivative identity are proved and axiom-audited. The
coefficient-size bounds and exact Type I rescaling and Type II conjugate
correlation-phase identities are proved as well. The finite Type II inner sum
times its conjugate is expanded into the exact double correlation sum used in
the source, summed and rearranged over the outer support, and connected to the
bilinear sum by a coefficient-explicit finite Cauchy--Schwarz bound. Its
diagonal is exactly `#K`, splits from the off-diagonal part, and contributes at
most `#K·#S·L²`; only the displayed off-diagonal correlation norms remain in
the resulting bound. A uniform correlation estimate is propagated across at
most `#S(#S-1)` ordered off-diagonal pairs. Both transformed reciprocal
coefficients are proved nonzero for distinct
positive indices when the corresponding original coefficient is nonzero, so
the critical-interval machinery applies to every off-diagonal correlation.
Exact absolute-size bounds retain the source factor
`|n'-n|·j·B^(j-1)` in the higher-power numerator and accept explicit lower
support bounds in both denominators. Their normalized form is exactly the
source factor `|n'-n|/R` at product scale `KR`, with loss
`j(B/R)^(j-1)`, specialized to `j·2^(j-1)` on dyadic support. The product condition `mn∈I` is no
longer suppressed: the squared inner sums rearrange exactly to correlations
on `K ∩ (1/n)I ∩ (1/n')I`. The restricted expression is split exactly,
its diagonal is bounded by `#K·#S·L²`, and a uniform off-diagonal bound is
propagated to the final real squared-inner-sum inequality.
The Type I variable-support sum is also reduced exactly to the rescaled
integer phases with parameters `N/m, M/m^j`, under an explicit coefficient
envelope. The exact divisor-antidiagonal-to-product-box rearrangement and
outer/double coefficient-block decompositions now connect the weighted
Vaughan identity to literal `m*n∈I` Type I/II sums. This is proof
infrastructure only; the paper's quantitative polylogarithmic family
envelopes, Vinogradov/Weyl cancellation, Type I/II estimates, and the
derivative-to-Fourier-coefficient estimate remain open. Conditional Fourier
reconstruction is now proved. The finite Abel-summation identity and its explicit
`2 log b` bound are proved, so the source's logarithm-weighted alternate Type I
form follows once the corresponding unweighted prefix estimates are supplied.
The reverse prime partial-summation bridge is also proved, with the explicit
loss `1/log a` from prime-log prefix sums to the unweighted prime phase sum.
The low-frequency branch also has its exact elementary phase-variation input:
on `[X,2X]`, `|f'| ≤ (j+1)F/X` and hence the phase oscillation is at most
`(j+1)F`. The normalized additive character is proved `2π`-Lipschitz, and
complex finite Abel summation converts this into the exact comparison
`‖Σ(Λ(n)-1)e(f(n))‖ ≤ (1+2π(j+1)F)B` from a uniform initial-subinterval PNT
discrepancy bound `B`. The frozen `WeakPNT` is now wired into this estimate:
it proves global discrepancy `o(k)`, uniform dyadic-subinterval discrepancy
`o(P)`, and hence an `o(P)` phase comparison for every fixed bound on `F`.
The stronger uniform logarithmic saving needed for polylogarithmically growing
`F` remains part of the analytic proof.
The finite Fourier reduction is exact as well: every integer mode evaluates
to a reciprocal phase with rescaled `N,M`, finite prime sums and integrals
interchange with the mode sum, and the total error is controlled by the
coefficient `ℓ¹` norm times a uniform mode error. The source contract now uses
the correct complex-valued weight and sum-of-orders `C³` norm. The source
interval hypotheses prove every mode integrable automatically, and a retained
square box has exactly `(2R+1)²` modes, giving an explicit finite assembly
bound from uniform coefficient and mode-error envelopes. The source cubic
coefficient envelope `(1+|n|+|m|)^(-3)` is summable on `ℤ²`; the square boxes
exhaust all modes, their outer `ℓ¹` tails vanish, and the associated finite
Fourier polynomials converge uniformly to their infinite series. Continuous
periodic weights are now descended through `ℝ² → (ℝ/ℤ)²`, the torus and plane
character conventions are identified, and the torus Fourier theorem upgrades
that convergence to uniform convergence to the original weight whenever the
cubic coefficient estimate holds. A separate stability
theorem transfers any continuous uniform
approximation `‖W-V‖∞≤δ` to the full discrepancy, with explicit perturbation
cost `(2P+1)δ + Pδ/log P`; the actual two-torus coefficient is now factored
by Fubini in either coordinate order and the threefold periodic
integration-by-parts estimate gives cubic decay along either nonzero
frequency. Combining these directional bounds into the radial envelope and
relating the concrete derivative chains to `taoC3Norm` remain. For nested finite mode sets, the
uniform error is now discharged explicitly by the `ℓ¹` norm of the discarded
coefficients and propagated through the same stability theorem.
The preliminary `j=1` reduction is kernel-checked as exact equality with the
`j=2, M=0` phase after replacing `N` by `N+M`, including the finite prime and
prime-log sums.
The derivative cancellation expression
`N+M_r/t^(j-1)` now has exact pair-separation, one-interval cover, and
Lebesgue-measure bounds. On the source hypothesis `t^(j-1) ≤ 2X^(j-1)`, each
derivative-order exceptional set is covered by an interval of length at most
`16Xq`, and a finite union has the corresponding cardinality-times-measure
bound. The exact integer-point count is also bounded by
`#orders·(16Xq+1)`, completing the finite deletion bookkeeping. The exact
four-term Vaughan convolution identity,
including its nested-divisor and reciprocal-phase weighted forms, is now
proved and audited. Its three convolution terms are reindexed into bounded
product boxes and decomposed into exact short outer blocks, or double blocks
for Type II, without dropping the product restriction. The logarithmically weighted prime phase sum is also
split exactly from the Mangoldt phase sum; the oscillatory higher-prime-power
tail is bounded by the frozen local prime-power theorem with its explicit
majorant. The Type II decay kernel is regrouped exactly by natural distance;
each distance fiber has at most two points, reducing any nonnegative kernel
to a one-dimensional sum with only that sharp factor. The real-power sum is
now evaluated through an explicit antiderivative and bounded by
`1+(2^(1-c)/(1-c)) N_r F^(-c)` unconditionally in the stated finite regime.
The all-support zero-distance term proves that every pure `C N_r F^(-c)`
bound must dominate `1`. In the actual off-diagonal correlation sum the
center is erased, its zero-distance fiber is empty, and the positive-distance
sum has a pure `N_r F^(-c)` bound without an endpoint assumption. That
stronger bound is propagated through the squared-inner-sum reduction and an
actual short block. The analytic cancellation input remains open. A
source-shaped pointwise
correlation estimate now propagates through the ordered off-diagonal pairs
and the exact product-restricted Cauchy--Schwarz identity to a final
squared-inner-sum bound, retaining the kernel decay and additive error
separately. This is specialized to the actual shorter-than-dyadic inner block
and then to the exact outer/inner double blocks produced by Vaughan; block
membership discharges the diameter and nonzero-index obligations. Each block
is also proved to contain at most its chosen length, so the final estimate is
now stated directly in `q_outer` and `q_inner` in the endpoint-free
source-scale form, ready for logarithmic exponent
bookkeeping. The high-frequency implication is also formalized exactly:
`(log P)^d ≤ F` and `b+t ≤ dc` imply
`(log P)^b F^(-c) ≤ (log P)^(-t)` once `P≥e`. Theorem 2.5 is not claimed.

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
zeta-ratio asymptotic for `VB¹`, Lemmas 2.10 and 3.2, Corollary 2.11, and the
factorial endpoint/counting bridges. It also certifies the exact Theorem 2.5
interface, reciprocal-phase derivative/variation identities, and bidirectional finite
partial-summation/log-weight reductions, but not the analytic
equidistribution estimate itself. It does not certify a main theorem.

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

For Theorem 1.8, continue Theorem 2.5 from its compiled exact contract and
phase calculus and exact product-restricted, block-decomposed weighted Vaughan
identity through the Vinogradov/Weyl estimate, quantitative Vaughan family
envelopes, Type I/II bounds, and the derivative-to-coefficient decay step of
the Fourier argument; the subsequent weight reconstruction is already
formalized conditional on that decay.
Then prove the
subexponential second clause of Lemma 3.1 and combine it with the now-complete
Lemma 3.2 and Corollary 2.11.
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
