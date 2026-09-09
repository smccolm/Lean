# Tao 2026 Research Agenda

## Status and scope

This agenda governs the active formalization of Terence Tao, *Products of
consecutive integers with unusual anatomy*, arXiv `2603.27990v2`. The release
scope is now fixed by `Tao Goal Prompt.md` at Theorems 1.7--1.10; none is yet
claimed proved.

The paper studies bad and very bad intervals of consecutive integers, type
`F_3` intervals, and consequences related to the factorial equation
`a_1! a_2! a_3! = m^2`. Those abstract-level descriptions are orientation,
not Lean specifications.

## Phase 0 - repository groundwork (complete)

Complete:

- pin the paper and source archive;
- establish project-control document roles;
- reserve isolated source, dependency, package, and tool locations;
- provide an isolated Lake package and honest development check.

## Phase 1 - source reconstruction (active)

Read the v2 TeX in proof order. Produce an exact ledger of:

- definitions and counting conventions;
- theorem and lemma statements;
- parameter ranges and asymptotic uniformity;
- exceptional-set estimates and quantitative thresholds;
- imported results, with the form actually consumed;
- reductions connecting interval anatomy to factorial equations.

The output of this phase belongs in `Tao Crosswalk.md`; do not create a second
competing status document.

## Phase 2 - dependency design (first boundary complete)

The first required analytic boundary is now fixed at the recursive import
closure of `GafniTao.Theorem11`. Node 73 contains an immutable, per-file-hashed
copy of its 1,226 reachable Lean modules and imports that package rather than a
mutable sibling checkout. Further dependencies remain crosswalk-driven.

Properties enforced for this boundary and required of later ones:

- immutable commit/tag and source hashes;
- minimal public declarations rather than a mutable sibling checkout;
- no reverse import into the frozen releases;
- explicit attribution and license provenance;
- Windows-safe package paths, following node 74 where necessary.

## Phase 3 - statement freeze (public conclusion contracts complete)

The release scope is Theorems 1.7--1.10. Their proposition-valued conclusion
contracts now compile. Continue translating every supporting statement
literally enough that endpoint conventions, multiplicities,
uniformity, exceptional sets, and numerical constants remain visible. Record
every deliberate representation change in the crosswalk before proof work.

## Phase 4 - proof implementation (active)

Build from definitions and reusable lemmas toward the frozen source-facing
contracts. Research probes may be used, but they must remain outside the
production import root. Do not substitute theorem-shaped assumptions for
missing mathematics.

The compiled analytic chain now reaches Proposition 2.3(i) and the full
`theta > 2/15` range of Tao's constant-length Proposition 2.3(iii). It retains closed endpoint
conventions, bounds rather than discards all higher prime powers, performs the
finite dyadic-to-prefix conversion, and handles `theta >= 1` by monotonicity.
The Baker--Harman--Pintz 2001 paper is now pinned and hashed, with Theorem 1
and the closing quantitative estimate located. Clause (ii) of Proposition 2.3
still requires a Lean proof: the source proof is a full Harman-sieve argument
using Watt's fourth-moment estimate, Dirichlet-polynomial decompositions,
one- and two-dimensional sieve asymptotics, role reversals, and numerical loss
bounds. The next parallelizable mathematical layer is the earliest downstream
Section 3/4/6 consumer that does not presuppose this missing theorem. A
density-zero statement remains an inadequate replacement for the proved fixed
power saving.

The exact `VB¹` squarefree-cube sum now has its full source asymptotic.
Termwise domination controls the accumulated floor error, dominated
convergence produces the squarefree `b⁻³ᐟ²` limit, and the unique
square-times-squarefree decomposition identifies its constant as
`ζ(3/2)/ζ(3)`. The remaining Theorem 1.8 work is the nontrivial-`VB` upper
bound through Theorem 2.5, the second clause of Lemma 3.1, and the final
assembly from the now-complete Lemma 3.2 and Corollary 2.11.
The first, elementary `H<N` clause of Lemma 3.1 is now proved for `N≥1`.
The positive-start hypothesis is necessary under the literal definitions:
`{1}` (`N=0,H=1`) is powerful. The remaining subexponential length estimate
is the first consumer of the still-unformalized Theorem 2.5.
Lemma 3.2's arithmetic extraction is now formalized independently: removing
exactly the exponent-one primes leaves a powerful core, and global
powerfulness forces every removed prime to be at most `H`. The coefficient is
squarefree and divides `H!`; any two positions yield the exact relation
`an+h=bm`. Its quantitative step is now formalized too: the coefficient
product divides an explicit small-prime envelope, finite Abel summation plus
Chebyshev bounds its logarithm by `C H log H`, and averaging separately on two
interval halves selects distinct coefficients at most `H^(3C)`. Lemma 3.2 is
therefore complete. The exact finite reindexing for Corollary 2.11 is also
complete. Lemma 2.10 now has its squarefree-discriminant reduction, literal
quadratic norm encoding, the full square-discriminant divisor bound, and the
norm-one Pell action on fixed-norm fibers. Exponential growth and the exact
logarithmic count of coordinate-bounded fundamental-unit powers are now
proved. Equality of principal ideals is also proved equivalent to norm-one
orbit membership on each nonzero `ℤ[√D]` norm fiber. The first
maximal-order comparison is now complete: the concrete quadratic field and its maximal
order are constructed, `ℤ[√D]` embeds injectively, fixed-norm points map to a
finite ideal-divisor set whose fibers are maximal-order unit classes, and the
degree-two at-most-two prime-splitting estimate is instantiated for every
rational prime. Dirichlet's unit theorem is now specialized to this concrete
field: it is totally real of signature `(2,0)`, has unit rank one and torsion
exactly `{±1}`, and every maximal-order unit has a unique torsion-times-power
decomposition. Orienting the generator at a nontrivial real place gives a
growth base `λ_D>1`; a `B log λ_D` cutoff leaves at most `2(2B+1)` units.
The multiplicative `d(|N|)^2` ideal-divisor bound, boxed-point-to-place-height
bridge, and uniform lower bound for `λ_D` are now complete. They close the
literal signed, polynomial-family form of Lemma 2.10. Corollary 2.11 is also
complete: its exact dyadic fibers, three estimates, `2/5,2/5,1/5`
interpolation, logarithmic absorption, signed-shift symmetry, and uniform
linear-family theorem are all proved and audited. The next honest Theorem 1.8
boundary is Theorem 2.5 and its Lemma 3.1 consumer.

The cited source of Theorem 2.5 is now pinned exactly: Proposition 1.12(ii) of
Matomäki--Radziwiłł--Shao--Tao--Teräväinen, arXiv `2106.03335v1`, with both
the PDF and TeX archive hashed. The source proof exposes the real recursive
boundary: Fourier reduction to prime exponential sums, a prime-number-theorem
minor-frequency regime, Vaughan's identity, a Vinogradov derivative estimate,
and Type I/II estimates. The implementation may specialize to `M=N`, `j=2`
only if the resulting theorem is proved to supply every Tao consumer; it may
not replace this estimate by an assumed equidistribution contract.
The exact contract and that specialization bridge now compile. The reciprocal
phase's all-orders derivative identity, signed-factorial form, binomial
coefficient, normalized absolute form, coefficient-growth bounds, and the
upper/reverse-triangle/dominant-term derivative inequalities are also proved.
The critical-expression argument is now carried through exact pairwise
diameter bounds, a one-interval cover of length at most `16Xq` for each
derivative order, and a finite-union Lebesgue-measure estimate. The remaining
integer-point bookkeeping is now closed as well, with the exact finite-union
bound `#orders·(16Xq+1)`. The next proof boundary is therefore the
cancellation argument itself. The exact four-term
Vaughan convolution identity now also compiles, pointwise as nested finite
divisor sums and after weighting by the reciprocal phase. Next it must be
refined into the source's shorter-than-dyadic supported Type I/II pieces
before those estimates are proved.
The finite convolution-to-bilinear bridge is now exact: a weighted sum over
divisor antidiagonals is reindexed into a bounded product box with the literal
condition `m*n∈I`. Reassociating each nested Vaughan term through the
convolution of its first two factors puts all three convolution terms of the
Mangoldt reciprocal-phase identity into this same product-restricted form.
What remains here is the quantitative coefficient-support decomposition into
the source's polylogarithmically many multiplicative short intervals.
The intervening Abel-summation step is now kernel-checked: an exact finite
identity and explicit `2 log b` estimate reduce the alternate logarithmic
Type I form to uniform bounds for the unweighted initial subintervals.
The reverse prime-specific bridge is proved too: prime-log prefix bounds imply
the unweighted prime reciprocal-phase bound with factor `1/log a`.
For the low-frequency PNT branch, the phase derivative is now bounded by
`(j+1)F/X` on `[X,2X]`; a mean-value argument gives dyadic oscillation at most
`(j+1)F`. The additive character has a proved `2π` Lipschitz constant, so its
finite total variation is at most `2π(j+1)F`. Complex finite Abel summation
then proves the precise comparison with the integer phase sum from a uniform
initial-subinterval bound for `Λ-1`. The frozen qualitative `WeakPNT` has now
been connected to that interface: it yields global `o(k)` discrepancy,
uniform `o(P)` discrepancy on all subintervals of `[P,2P]`, and an `o(P)`
phase comparison for every fixed reciprocal-phase scale bound. The remaining
low-frequency input is the quantitative classical PNT discrepancy strong
enough for arbitrary logarithmic saving when that scale grows
polylogarithmically.
For the reduction of Proposition 1.12(ii) to (i), finite Fourier polynomials
are now complete: mode evaluation, prime-sum and integral interchange,
coefficient-weighted error aggregation, and bounded-frequency parameter
rescaling are proved. The actual source interval hypotheses now supply
integrability without an extra caller assumption; retained square modes have
exact count `(2R+1)²` and an explicit uniform-envelope assembly bound. The
uniform approximation is now propagated to the original continuous weight
with explicit costs `(2P+1)δ` for the prime sum and `Pδ/log P` for the
integral. The source radial envelope `(1+|n|+|m|)^(-3)` is now proved
summable on `ℤ²` by a separable `3/2`-power majorant. The square frequency
boxes exhaust all modes, their exact outer `ℓ¹` tail tends to zero, and any
coefficient family obeying the envelope yields uniform convergence of its
finite square Fourier polynomials to the infinite series. A continuous
`ℤ²`-periodic plane weight is descended to Mathlib's unit two-torus through
an open quotient map, the torus monomials are proved equal to the project's
plane characters, and Mathlib's reconstruction theorem identifies that
summable series with the original weight. Nested finite mode
truncations still have their exact discarded `ℓ¹` control through the full
prime/integral discrepancy. The one-dimensional analytic core is proved: three
periodic integrations by parts on `[0,1]` give the exact multiplier and a
cubic frequency bound by the uniform third-derivative norm. The actual
two-torus coefficient is now factored by Fubini in either coordinate order,
its real slices are identified with those unit-interval coefficients, and
cubic decay is obtained in either nonzero coordinate. The zero mode and both
directional estimates are now combined into the source radial envelope with
explicit constant `27`. Smooth periodicity propagates to every iterated
Fréchet derivative and reduces every derivative-norm range to the compact
fundamental square. The pure coordinate chains are constructed automatically,
so the unconditional source-facing bound
`|c_(n,m)| ≤ 27 * taoC3Norm W * (1+|n|+|m|)^(-3)` is proved from
`ContDiff ℝ ⊤ W` and `IsZ2Periodic W`. No Fourier coefficient-decay gap
remains; the unresolved Theorem 2.5 work is the quantitative prime-exponential
sum cancellation and its precise Vaughan family/count envelopes.
The source's initial reduction from `j=1` to `j=2` is also exact: replace
`N` by `N+M` and set the higher reciprocal coefficient to zero.
The reusable finite core of the shorter-than-dyadic decomposition is now
proved. Quotient blocks regroup an interval sum exactly, their number is
bounded by the relevant ceiling quotient, and any two entries in one block
have natural distance strictly below the chosen block length. Coefficients
supported on the original interval now decompose exactly into block
restrictions, both pointwise and inside arbitrary finite weighted sums, and
each restriction preserves the original norm bound. The bounded product form
now decomposes exactly into short outer blocks and, for Type II, short blocks
in both variables while retaining `m*n∈I`. What remains is to derive the
source's precise polylogarithmic number of nonzero families and logarithmic
coefficient bounds at its chosen scales; the analytic cancellation estimate
remains separate and open.
The Type II correlation expression now has an exact diagonal/off-diagonal
split. The diagonal identity `X_{n,n}=#K` gives the explicit bound
`#K·#S·L²`, leaving only off-diagonal `X_{n,n'}` norms for the analytic
cancellation estimate. One uniform off-diagonal estimate is then propagated
over the exact ordered-pair envelope `#S(#S-1)`.
The transformed linear and higher reciprocal coefficients are nonzero for
every distinct positive pair whenever the corresponding original coefficient
is nonzero; this discharges the nonvanishing premise of critical deletion.
Their absolute sizes are controlled with exact denominators and the
mean-value numerator bound `|n'^j-n^j| ≤ |n'-n|·j·B^(j-1)`; explicit positive
lower support bounds then control those denominators. Normalization at product
scale `KR` gives precisely `|n'-n|/R`, with higher loss `j(B/R)^(j-1)` and
the explicit dyadic specialization `j·2^(j-1)`. The source's product
restriction is also retained literally: summing the restricted inner squares
produces correlations supported on `K ∩ (1/n)I ∩ (1/n')I`, and the restricted
diagonal is its exact support cardinality, hence at most `#K`. The restricted
expression has an exact diagonal/off-diagonal split; a uniform off-diagonal
bound propagates over `#S(#S-1)` and yields the required real squared-inner-sum
inequality.
The next decay-kernel sum is reduced to one dimension without a cardinality
loss: fixed natural-distance fibers have at most two points, exact fiberwise
regrouping holds, and nonnegative kernels cost only the sharp factor two. The
real-power sum `(1 + d*F/N_r)^(-c)` is now bounded by an evaluated affine-rpow
integral and normalized to the source scale. Under `D≤N_r`, `F≥1`, `0≤c<1`,
and the explicit endpoint condition `1≤N_r F^(-c)`, the all-support pure bound
is `(1+2^(1-c)/(1-c))N_r F^(-c)`. The actual Type II correlation sum is
off-diagonal, however: its support is `S.erase n`, whose zero-distance fiber is
proved empty. Its positive-distance sum is bounded directly by the integral,
giving a pure `N_r F^(-c)` bound with no endpoint assumption; this stronger
form is propagated through the complete squared-inner-sum reduction, the
actual short block, and the exact Vaughan double blocks. The all-support
theorem still correctly retains the necessary additive `1`.
This decay estimate is no longer isolated from the Type II algebra: a
pointwise `Q(A·kernel(|n-n'|)+E)` hypothesis is summed over the exact ordered
off-diagonal pairs, and the result is substituted into the literal
product-restricted squared-inner-sum reduction. The remaining input at this
interface is the analytic proof of that pointwise correlation hypothesis with
the paper's concrete logarithmic factors. The finite theorem is specialized
to the actual inner quotient block and exact Vaughan double-block geometry;
the block diameter and nonzero reciprocal indices are now discharged
internally rather than left as interface assumptions. The exact bound
`#block≤q` is proved and substituted for both supports in the endpoint-free
form as well, leaving a pure source-scale squared-sum inequality in the
source-facing block lengths alone.
The high-frequency exponent conversion is also exact: under `P≥e`, a source
lower bound `(log P)^d≤F` converts `(log P)^b F^(-c)` into
`(log P)^(-t)` whenever `b+t≤dc`. What remains is to instantiate `b,d,t`
from the quantitative Vaughan and exponential-sum constants rather than an
informal `O(A)` exponent.
The preceding prime/Mangoldt replacement is no longer implicit: the exact
prime-logarithm plus higher-prime-power decomposition compiles, and the
oscillatory tail is controlled by the frozen local prime-power majorant.

The other newly isolated dependency is Erdős--Selfridge Theorem 1, whose
square case controls the factorial-squarefree-component fibers in Theorem
1.10. Its original 1975 paper is pinned and hashed. No completed Lean proof
was found: the otherwise relevant `formal-conjectures` declaration contains
`sorry`, so this theorem must be recursively formalized here (or imported only
from a future immutable, audited proof release).

## Phase 5 - release engineering

When real endpoints exist, add:

- a production root;
- `Audit.lean` with permitted-axiom enforcement;
- exact source and dependency closure checks;
- zero-diagnostic builds and forbidden-token scans;
- a truthful reproduction manifest and architecture update.

## Non-goals and non-claims

- treating the frozen Gafni--Tao closure as a proof of a Tao theorem;
- changing nodes 71 or 74;
- claiming a result about the Riemann Hypothesis.
