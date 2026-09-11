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
copy of its 1,339 reachable Lean modules and imports that package rather than a
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
now has its exact arithmetic and Theorem 2.5 interface: the source's
fractional rectangle is incompatible with very badness, the corresponding
prime sum is zero, and specialized Theorem 2.5 supplies the integral upper
bound. The fixed sine/flat-exponential cutoff is now explicitly constructed
and proved nonzero, nonnegative, `C∞`, periodic, and correctly supported. What
remains in this consumer is now purely geometric: the contradiction growth
hypothesis already supplies `ε25=3/2-(2/3+η)⁻¹>0` and `K=1`; the cutoff has a
fixed positive inner-rectangle minimum; its integral is real and nonnegative;
and its norm lower bound is reduced to the measure of an explicit good set in
`(H,2H)`, whose reciprocal membership transport is exact. It remains to prove
that this set has measure `≫H` by the source's two changes of variables. The
Theorem 2.5/Fourier smoothness index is now the genuine `∞`, rather than
Mathlib's stronger analytic index `⊤`.
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
sum cancellation and the precise Vaughan shorter-family count.
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
in both variables while retaining `m*n∈I`. The identity is now reassociated
into the source's canonical Type I and Type II coefficient pairs. Their
cutoff/tail supports and absolute envelopes `1`, `log P`, `1`, `log P` are
proved directly from `|μ|≤1` and `Λ*ζ=log`, and the source-oriented weighted
identity retains `m*n∈I`. The canonical family over `[1,B]` now uses budget
`(log₂ B+1)^101`, has exactly `(log₂ B+1)^102` indices, covers every positive
coefficient index, and decomposes arbitrary weighted sums and the complete
source-oriented Type I/II expression. The real-log comparison is proved, and
the extra subdivision power absorbs ceiling rounding to give the literal
relative width `(1+log(B)^(-100))M`; below the budget, blocks are singletons.
For `P≤B`, the compiled monotonic transfer gives the paper's literal
`(1+log(P)^(-100))M` width. The analytic cancellation estimate remains separate and open.
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
inequality. For `I=[a,b)` and a quotient outer block, that filtered support is
now proved equal to one explicit `Finset.Ico` with ceiling-divided endpoints
and length at most the outer block length. The actual canonical Vaughan
correlation is therefore rewritten exactly as `reciprocalPhaseSum` on an
interval, matching the input shape of the pending Vinogradov/Weyl estimate.
The analytic engine has now begun unconditionally in `WeylDifferencing`.
Shift pairs `(n,h)` are grouped by their exact boundary-truncated endpoint
`m=n+h`; the resulting window sums satisfy the `H`-fold averaging identity
and finite Cauchy--Schwarz inequality. Their squared norms are then expanded
and regrouped into the literal pair-correlation constraint
`n+h=n'+h'`. Both orders of the two shifts are identified exactly with a
truncated forward correlation or its conjugate; natural-distance regrouping
then proves a real correlation majorant and the divided finite van der Corput
inequality with the exact strict lag range. The zero lag is split as `N`, and
a uniform positive-lag hypothesis yields the recursive
`2(N+H+1)(N+H*C)` majorant. The theorem is specialized to the translated
source `reciprocalPhaseSum`; appended lag lists commute with sampling, and
real finite differences commute with differentiation on the positive ray.
The terminal affine case is also unconditional: the geometric sum telescopes
exactly after multiplication by `e(alpha)-1`, giving the nonresonant bound
`min(N, 2 / ‖e(alpha)-1‖)`. The denominator is exactly
`2|sin(π alpha)|` and is at least four times the distance from `alpha` to its
canonically rounded integer, yielding `min(N, 1/(2 dist(alpha,ℤ)))`. No
cancellation hypothesis is introduced at this stage. Arbitrarily many rounds
now propagate through `UniformIteratedPhaseBound` and the explicit nested
square-root `weylRecursiveMajorant`; the translated reciprocal phase has a
dedicated four-step interface matching the source's `k=5` invocation. Each
one-step real finite difference is now identified exactly with the interval
integral of its derivative. This gives both an absolute upper bound and signed
lower bounds when the derivative stays uniformly away from zero. For a globally
smooth phase these estimates now iterate through an arbitrary lag list, gaining
the exact product of its lags in both the upper and sign-independent separation
bounds. The iteration is now also localized to the positive ray and the exact
evaluation interval `[x,x+sum(lags)]`. Its reciprocal-phase specialization
converts the normalized source derivative window into explicit raw upper and
lower bounds for every admissible iterated difference, with factorial, scale,
power, and lag-product factors exposed. The lower bridge needs no assumed sign:
continuity and the intermediate value theorem prove that a derivative bounded
away from zero has constant sign on the evaluation interval. The derivative
of a terminal iterated difference is now identified with the difference of the
next original derivative, and its critical-regular lower and raw upper bounds
are frozen uniformly at `2X` and `X`; for four lags this is exactly the needed
fifth-derivative window. The frozen radian-normalized Kusmin--Landau theorem is
now converted exactly to the project's additive character. Mean-value and
second-difference arguments turn absolute first- and second-derivative windows
into monotone increments, and a source-facing theorem bounds the resulting
critical-regular nonlinear terminal reciprocal-phase sum by the inverse of its
explicit lag-product lower scale, subject to the expanded regular interval and
upper-one-period conditions. Admissible lag sums and products are now bounded
by `rH` and `H^r`, so this estimate is uniform over all admissible lag lists and
truncated lengths on one expanded regular interval and is composed directly
with the arbitrary-depth recursive majorant. The literal four-round theorem
uses derivative orders five and six and a single worst-case `H^4`
upper-smallness hypothesis. The required lag-sensitive refinement is now
explicit: `weylTreeMajorant` retains the precise accumulated lag list and
boundary-truncated length at every node, its reciprocal-phase leaves carry
`min(L, 1/(prod(lags)*scale))`, and the innermost lag sum is bounded by the
exact harmonic factor `harmonic H`. The successive outer sums are no longer
left as a tree: `weylTreeMajorant_lagProduct_le_closed` inductively reduces all
of them to `weylLagLengthCoefficient` and `weylLagScaleCoefficient`, whose
exact factors `iteratedRootHarmonic r H` are each at most `H`. The four-round
source wrapper is therefore a closed scalar estimate, and
`iteratedSqrt_four_pow_sixteen` verifies its inverse-scale term has the expected
sixteenth-root dependence. Successive Cauchy--Schwarz inequalities now give
the sharper exact product bound `H^11 * harmonic(H)^4`; together with the step
factor this yields the terminal sixteenth-power bound
`(6L)^15 * harmonic(H)^4 / (H+1)^4 / scale`, and the global adaptive wrapper
also exposes the standard bound `harmonic(H) <= 1 + log H`. Bounding every generalized
harmonic factor by `H`
now produces `weylLagScaleCoarseCoefficient`; after four rounds its sixteenth
power is exactly `(weylTreeStepFactor H L * H)^15`, and after multiplication by
the iterated inverse terminal scale the sixteenth power is exactly
`(weylTreeStepFactor H L * H)^15 / scale`. The source-facing coarse majorant is
proved. The length coefficient is now also eliminated as a recurrence:
`weylLagLengthFourMajorant` is the sum of four explicit nonnegative terms whose
sixteenth powers are exactly `D^8`, `E^8 D^4`, `E^12 D^2`, and `E^14 D`.
For `1≤L` and `H≤L`, the exact identity for `weylTreeStepFactor` proves
`E≤6L` and `D(H+1)≤6L²`; hence the four terms satisfy powered denominator
bounds with exponents `8,4,2,1`. Those four bounds and the coarse scale bound
are root-extracted and rewritten exactly as real `1/16` powers in a
source-facing five-term majorant with no hidden tree or scalar recurrence. The
canonical floor-rounded range `floor((2U)^(-1/4))` is defined for the explicit
upper fifth-derivative scale `U`; its fourth-power estimate, the comparison of
the lower and upper scales, and the exact upper-smallness condition are proved,
and both source estimates are instantiated at this range. Expanded critical
starts are now those whose `4H+1` forward real windows meet the critical union;
their count is at most `orders.card*(16Xq+4H+2)`. Filling each order's bad starts
to its integer interval hull preserves this deletion bound, while the union of
the at most two hull endpoints per order supplies a cut set of size at most
`2*orders.card`. Thus the global regular multiplier is `2*orders.card+1`, not a
multiple of `Xq`; the windows cover the full real evaluation intervals, and the
global source wrapper applies the sharp Weyl estimate at any upper-small range
to long components and the trivial bound to short ones. The adaptive choice
`min(L, floor((2U)^(-1/4)))` is proved to fit the interval and preserve
upper-smallness. The two branches satisfy the unified denominator estimate
`(H+1)^(-4) <= 2U+(L+1)^(-4)`; this is propagated into an effective global
majorant, whose critical width is fixed to the `1/128` power of
`2U+(L+1)^(-4)+1/F`. The latter is exactly
`240(5+j)^5 F/X^5+(L+1)^(-4)+1/F` and is bounded by the derivative-order factor
times the source-shaped three-term error. The optimized
range `min(floor(L*q), canonicalRange)` now removes the previously nondecaying
short-component term: both short penalties are bounded by `Lq` and `4Lq+1`,
the remaining harmonic logarithm is at most `log L`, and the terminal
denominator is bounded by `2U+(Lq)^(-4)`. This is propagated through the
global terminal root. The four diagonal roots are now absorbed by `72Lq`; the
optimized terminal root is at most
`100((5+j)^5+1)(1+log L)Xq`, and the complete majorant is at most the same
factor with constant `172`.  A global wrapper replaces `q` by the explicit
  `1/128` power of the normalized three-term source error; the endpoint constant
  is absorbed as well, leaving one coefficient times `X` and that power. An
  exact short/long split now removes the length term under `F≤X^4`, recovering
  the arbitrary-subinterval bound with explicit exponent `c=1/1024`.
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
  product-restricted squared-inner-sum reduction. For `N=M`, the transformed
  scale now has an exact distance lower bound; the Weyl width is at most
  `E^(1/1024)+4(1+distance*F/B)^(-1/1024)`. Its logarithm is uniformized by the
  outer block length, and the resulting pointwise theorem is propagated all
  the way through the endpoint-free double-block squared-sum estimate. The
  pair-dependent `F'/K^5≤E` premise is now discharged by the uniform
  `typeIIShortIntervalScaleError`, using the inner block's left endpoint and
  diameter. In the quadratic wrapper, the literal outer-block geometry reduces
  the endpoint and power-evaluation bundle to one expansion margin. The
  transformed-scale condition is further deduced from the uniform block error
  comparison `E≤1/K`. For the quadratic phase this comparison is now proved
  on large inner bands from `10F≤K^4(log Bcap)^100`: logarithmic block width
  gives `10qF≤K^4R`, which derives the former
  monomial condition `5q|N|≤K^5R^2` internally. The kernel and analytic propagation now accept arbitrary
  positive endpoints and are specialized to the exact dyadic blocks used by
  the canonical Vaughan family. Pairwise effective errors are dominated by
  `typeIIShortIntervalEffectiveErrorBound`, and the optimized range by its
  `1/128` power. On bands above the subdivision budget, the logarithmic width
  gives `5q≤K` and closes the expansion margin automatically. The canonical
  theorem now uses a source-faithful distance split. Scaled distance at most
  three is handled by the trivial correlation estimate and a kernel lower
  bound of `1/4`; farther pairs have inverse transformed scale at most `2/3`
  and the `1/4` upper-scale budget closes the effective error. That budget now
  follows from the pair-local `F'/K^5≤1/K`, and the standing `2≤log Bcap` assumption proves the
  common subdivision budget is large enough. The logarithmic lower split
  `(log Bcap)^d≤F`, `0≤d`, now supplies `F≥1` internally. The generic and
  canonical hybrid theorems now split every far pair at `F'=K^4`, prove the
  low branch by four-step Weyl using a pair-local error budget, and expose only
  the target kernel estimate for the high branch. The strengthened endpoint
  retains the intrinsic `(1/K)^(1/1024)` error from `F'≤K^4`, rather than a
  global short-block error; hence the upper source inequality is no longer
  required there. The lower split already supplies `F≥1`. The remaining
  non-singleton work is the actual high-transformed-scale Vinogradov estimate
  and its insertion into the quantitative Type II assembly. Its complete
  conditional principal-plus-deletion envelope now has a uniform logarithmic
  saving and is converted to the hybrid's exact
  `Q(4·kernel+3(log P)^(-T))` callback. Canonical inner-block membership
  discharges the transformed-scale upper bound with the exact factor `5`.
  This callback is now consumed by the canonical intrinsic-error double-block
  theorem, so no abstract high-pair estimate remains at that endpoint.
  The small inner singleton-band
  branch is purely diagonal and unconditional. The finite theorem is specialized
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
informal `O(A)` exponent. The complementary high-scale conversion is now
proved as well: for `c,ρ>0`, every polynomial logarithmic prefactor times
`exp(-c(log P)^ρ)` is eventually bounded by any requested negative logarithmic
power. The generic and canonical Type II hybrid endpoints retain this future
Vinogradov saving as its own additive error `V`, separate from the low-scale
Weyl error `E^(1/1024)`; no comparison between the errors is required. What
remains there is the Vinogradov exponential-sum estimate that
produces this factor. The parameter arithmetic is now closed uniformly:
`log F≤C(log P)^(3/2-ε)` yields
`(log P)^3/(log F)^2≥C⁻²(log P)^(2ε)` and hence the required eventual saving.
The more primitive source bound `F≤C exp((log P)^(3/2-ε))` is also converted
to that logarithmic hypothesis with an explicit adjusted constant. The full
regular-component derivative window is packaged for `1≤r≤R`; with
`α=(log P)^(4A)` and `q=(log P)^(-3A)`, all coefficient conditions and the
numerical smallness condition `log α·(log F)^2/(log X)^3<10^-3` are now
automatic under the source scale bounds. The exact cutoff
`R=10⌈log F/log X⌉+1` and its shifted budget `R+j≤log P` are also formalized;
for `j≤(log P)^(1/2)` the latter is eventual under the primitive source bound.
`Tao2026.Vinogradov` now assembles these ingredients into the full
source-cutoff derivative window on each regular interval. Thus the remaining
local high-scale task is the substantive Vinogradov exponential-sum
inequality, not cutoff or derivative-window bookkeeping. A conditional global
component theorem already transports such a local inequality to the complete
phase sum with the exact component multiplier and critical-deletion error. The
absolute-constant source statement is isolated exactly as
`VinogradovExponentialSumEstimate`, including `F≥X^4`, pointwise neighborhood
smoothness, the `10^-3` condition, and decay
`αX exp(-2^-18(log X)^3/(log F)^2)`; its global reciprocal-phase consumer is
complete. The proposition's Taylor front end is now internal: Tao's literal
ordinary-derivative polynomial, Lagrange remainder, normalized factorial
cancellation, and finite-interval shift error are all proved. Product shifts
are represented by pairs to retain multiplicities; their cardinality is
exactly `V²`, their errors sum into a uniform envelope, and division of the
unnormalized average is formalized even for intervals shorter than a shift.
The canonical floor-rounded `V=⌊X^(1/4)⌋` reduces the envelope to `√X` plus the
normalized top-derivative remainder. Both source factors are proved at most
one, and `√X+2π` is absorbed into nine copies of the target Vinogradov scale.
The interval pair sum is now decomposed into complete pointwise product sums
and an exact right-boundary strip bounded by `V⁴`. Removing the unit-modulus
constant Taylor phase rewrites each complete sum as the generic coefficient-only
bilinear polynomial sum `∑ e(∑ c_r x^r y^r)`. The exact trivial `V²` estimate
closes the branch where the normalized target is at least one. The remaining
local high-scale analytic task is therefore exactly the named
`VinogradovBilinearPolynomialNontrivialEstimate`; it implies the full
exponential-sum contract with an explicit total constant shift of eighteen.
The coefficient-selection stage inside this residual is now exact as well:
the block `[(4/3)(log F/log X),(7/4)(log F/log X)]` has at least `R/128`
integer degrees, and every one satisfies the medium window with `c₀=1/128`
for the floor-rounded range. The remaining task starts with the polynomial
mean-value estimate for a bilinear sum already carrying this positive-density
medium set. Its two Hölder steps and all intervening representation
combinatorics are now compiled: `∑ν=V^ℓ`, `∑ν²=J`, the equal-power-sum
solution count, and the exact equation-(16) inequality. The signed difference
support is also finite, has total multiplicity `(V^ℓ)²`, and lies in the
coordinate box `|d_j|≤ℓV^(j+1)`. The exact even-moment expansion, difference
regrouping, and Cauchy bound `μ(d)≤J` now establish equation (18). Work now
includes the full symmetric-box enlargement and the exact factorization of its
double character sum by coordinates. The geometric-series majorant is now
summed through rescaled, separated nearest-integer fibers, giving an explicit
harmonic integral-test bound for each coordinate. The two medium-window
endpoints are now combined—before losing their cancellation—into the source's
four-term logarithmic envelope, normalized by the side-length square. The
full product uses this saving on good coordinates and the sharp trivial bound
elsewhere. The scalar factors, exact medium-degree product, and explicit source
  block now yield `V^(-R^2/307200)` times the trivial box square. Work then enters
with the sharp constant and root layer: the scalar growth inequality is
discharged, the native frozen Wooley VMVT is proved, and its Ford moment is
exactly the local equation-(17) count. The trivial box square is collected as
`(3ℓ)^(2R)V^(R(R+1))`; the critical positive-power ledger equals `4ℓ²`, and
the compiled abstract assembly is
  `|B|^(2ℓ²) ≤ C² A V^(4ℓ²+2ε-δ)`. The constant ledger is now closed more
  strongly: `[(9/8)s,(7/4)s]` lies in the `c₀=1/4` window with weight at least
  `R²/193`; the scalar cost is only `1/1024`, so the product saves
  `V^(-255R²/197632)`. Native VMVT with `ε=δ/128` is composed and root-extracted,
  and the resulting exponent is proved to dominate `4·2⁻¹⁸/s²` despite the
  ceiling in `R=10⌈s⌉`. The floor in `V=⌊X^(1/4)⌋` costs at most a factor two in
  the exact source decay. The native p-adic concentration prime, coefficient,
  and starting depth are now retained through Section 12, giving the exact
  critical coefficient `C·(p^(B₀+1)κ_R)^ε`; a uniform rooted estimate for it
  implies the established coefficient contract, and the native development
  supplies every other field. The explicit supercritical Ford multiplier
  `3R+⌊R/5⌋` has loss `3R²/2800` and controlled cubic coefficient growth, but
  its larger root cannot deliver the target decay. The native critical
  coefficients for `40≤R<1000` are now absorbed into a single finite envelope;
  a rooted bound only for `R≥1000` is formally glued to that envelope and then
  passed through the existing nontrivial bilinear consumer. What remains is
  therefore one scalar assertion: uniform boundedness of the optimal rooted
  critical coefficient sequence on the infinite-degree tail. Defining the
  optimum by a supremum proves both that it supplies the VMVT estimate and that
  every possible witness bounds it; this scalar formulation is equivalent to
  the witness-based contract. The retained p-adic concentration data now map
  directly into this optimum with the exact Section-12 coefficient and root,
  so the remaining bound is stated identically at both interfaces. Bertrand's
  theorem supplies `R<p≤2R` for the concentration prime; quantitative bounds
  for the concentration constant and starting depth are the remaining fields.
  The coordinate-box root is proved uniformly between `1` and `3`, so only the
  VMVT coefficient root needs quantitative control. That root is exactly
  `C_R^(1/κ_R²)`: a fixed bound by `A≥1` is equivalent to the natural
  exponential-growth allowance `C_R≤A^(κ_R²)`. At the retained p-adic
  interface this becomes the one explicit target
  `C·(p^(B₀+1)κ_R)^ε≤A^(κ_R²)`; all downstream packaging is complete.
Its exact high-pair Type II
consumer is also proved:
the correlation support is rewritten to the ceiling-divided quotient interval,
whose endpoints and critical-deletion cost are discharged explicitly. The
raw component and deletion multiplicities are bounded by `log P`, and the
complete normalized envelope is eventually at most `3(log P)^(-T)` under the
explicit source budget `T+2≤3A`. Thus no separate asymptotic deletion
obligation remains once the named proposition is supplied. The fixed absolute
constant is preserved through an `...EstimateAt C` interface, and the result
is already packaged as the pointwise callback expected by the mixed
Weyl--Vinogradov Type II theorem. The canonical double-block consumer of this
callback is complete as well. The
transformed Type II correlation scale is proved to preserve this exponential
class on a named dyadic block, with exact multiplier `1+j·2^(j-1)` and hence
the fixed multiplier `5` for the canonical `N=M`, `j=2` case.
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
