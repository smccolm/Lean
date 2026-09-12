# Tao 2026 formalization

This directory is the active formalization project for Terence Tao,
*Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`. The paper and its TeX source are pinned under `Sources/`.

**Status:** Proposition 2.3(i),(iii), complete Lemma 3.2, unconditional
eventual Lemma 3.1 arithmetic-scale/geometric lower bounds, and the complete
Lemma 3.1 contradiction and full Theorem 1.8 assembly conditional on the
specialized Theorem 2.5 estimate. All four quantified upper/lower halves of
Proposition 2.1 are now proved and audited. The critical-prime-band
instantiation and finite exponent-grid argument also prove all of Lemma
1.6(i): `#(B¹∩[1,x]) = x/z^(2+o(1))` in the exact `QuotientPowerScale`
contract.
Bertrand's clause (i), the exact Guth--Maynard application in clause (iii),
and the polynomial-coefficient powerful relation are proved and audited; none of the four main
Theorems 1.7--1.10 is proved or claimed. The isolated `Extension/` package
contains the compiled arithmetic-anatomy, interval, counting, and
asymptotic-language definitions required to state the source results, plus a
kernel-checked proof of Tao's global constant-length prime-free endpoint
measure bound, derived from the frozen Guth--Maynard/Gafni--Tao chain. It also
proves the exact unique `p²m` representation of `B¹` and Tao's finite
prime-indexed smooth-number sum. The Proposition 2.1 route now also has the
exact positive-smooth-number Dirichlet-series Euler product and the finite
Rankin inequality in the source convention `p≤y`. Its exponential reduction
to the single sum `∑_{p≤y}p^(-sigma)` and exact Rankin saddle exponent are also
compiled. Exact finite Abel summation now rewrites that sum through
`Nat.primeCounting`, and Mathlib's explicit Chebyshev estimate supplies an
unconditional finite majorant. Its square-root remainder is further absorbed
into the standard explicit shape `C n/log n`. Estimating the resulting
backward difference by Bernoulli reduces it further to the canonical finite
sum `∑ n^(-sigma)/log n`. A canonical real divisor
`R=(log y)^(1/(1-sigma))` and integer cutoff `floor(y/R)` now give the
source-scale bound explicitly: after floor loss, the single condition
`2R≤sqrt y` implies both the cutoff-size estimate and the logarithmic
comparison with constant `2`. The actual saddle variables
`u=log X/log y` and `sigma=1-log u/log y` are now explicit, with the exact
identities `y^(1-sigma)=u` and
`-(1-sigma)log X=-u log u`. The square-root separation is suited to the
polylogarithmic regime; the critical `y=z^(alpha+o(1))` regime still needs a
sharper multi-scale power-log estimate. Its finite core is now proved:
every interval `[a,b)` retains the exact endpoint difference
`((b-1)^(1-sigma)-(a-1)^(1-sigma))/(1-sigma)` and its own denominator
`log a`, and an arbitrary monotone chain reassembles these bounds exactly.
The concrete saturated dyadic chain `min y 2^(i+1)` reaches `y` in exactly
`clog 2 y - 1` nonempty steps. A cardinality estimate on each active block
cancels the spurious `(1-sigma)â»Â¹` and reduces the chain to
`∑_{j≤m} 2^(j(1-sigma))/j`. Splitting this scalar sum at `m/2`, summing
the upper half geometrically, and using `2^delta-1≥delta log 2` gives the
closed terminal-scale bound `2^(m delta)/(m delta)` plus the lower-order
prefix `2^(m delta/2)(1+log m)`. These reductions are propagated through the
weighted-prime sum and source-facing Rankin exponent. The depth inequalities
now convert the terminal term to `2(2y)^delta/(delta log y)` and, at the exact
saddle, to `2*2^delta*u/log u`. The half-exponential prefix is now compressed
to `sqrt(2^delta*u) * (1+log(floor(m/2)))`; an explicit finite absorption
theorem gives the full scalar bound `5u/log u` whenever
`2(1+log(floor(m/2)))log u <= sqrt u`. The dyadic factor is bounded by
`1+log(log(2y)/log 2)`, and it is enough to
check the source-friendly fourth-root comparison
`8(1+log(log(2y)/log 2)) <= u^(1/4)`. The polylogarithmic source module now
discharges the resulting quadratic depth condition directly and optimizes the
full positive Rankin contribution; its matching lower bound is also proved.
The critical regime now has the exact filter-based contract
`log X/log x -> 1`, `log y/log z(x) -> alpha` for fixed positive `alpha`.
Within that contract, Lean proves `u/u_0 -> 1/alpha` and hence `u -> infinity`;
it also transfers the exact source decay `log z/u_0^2 -> 0` to
`log(2y)/u^2 -> 0`. This supplies the quadratic depth envelope
`log(2y)/log 2 <= u^2`, while direct source-scale domination proves the full
saddle range `X,y >= 2`, `u>1`, and `0<=sigma` eventually. The resulting
critical-regime theorem now gives the complete scalar bound `5u/log u`
without auxiliary asymptotic assumptions. The resulting finite Rankin
exponent is normalized exactly: Lean proves `u log u/log z -> 1/alpha`, its
positive dyadic error divided by `log z` tends to zero, and therefore obtains
`Psi(X,y) <= X/z^(1/alpha-epsilon)` eventually for every fixed positive
`epsilon`. The matching sharp lower estimate is now proved by the coarse CEP
packet described below.
For the critical lower branch, the exact integral depth `k=Nat.log y X` now
satisfies `k/u₀->1/alpha`, `log k/log₂x->1/2`, and
`k log k/log z->1/alpha`.  The frozen PNT also gives
`log pi(y)/log z->alpha` and eventually `2k<=pi(y)`.  Thus the integer saddle
and finite prime lattice are fully connected.  The finite lower-bound core is
now source-faithful rather than squarefree-only: Lean counts all prime
exponent vectors of total degree at most `k` by the exact stars-and-bars value
`choose(k+pi(y),pi(y))`, proves their products injective by unique
factorization, and embeds them into `Psi(X,y)`.  Independently, every
non-unit smooth number is partitioned uniquely by its largest prime factor,
giving the exact recurrence
`Psi(X,y)=1+sum_{p<=min(X,y)} Psi(X/p,p)`.  The exact
Chebyshev--Hildebrand weighted bridge is now compiled as well: multiplication
by `p^a` bijects smooth cofactors with divisible smooth numbers, double
counting prime multiplicities gives
`sum_n v_p(n)=sum_a Psi(X/p^a,y)`, and unique factorization yields the exact
finite logarithmic identity, including its nonnegative boundary-defect
decomposition and the recursive first-power inequality
`sum_{p<=y} log(p) Psi(X/p,y) <= Psi(X,y) log X`.
Iterating that inequality now gives the exact finite lower bound
`theta(y)^d <= Psi(X,y) (log X)^d` whenever `y^d<=X`, together with its
quotient form `(theta(y)/log X)^d<=Psi(X,y)`.
The fractional endpoint is no longer discarded: Lean defines
`b=floor(X/y^d)`, proves `1<=b<y` and `y^d*b<=X`, and admits a final weighted
prime packet up to `b`.  A thresholded form uses the pinned PNT estimate
`theta(b)>=b/2` above one fixed threshold and omits the packet below it, where
`b` is uniformly bounded.  The resulting denominator is now tracked exactly:
Lean proves `X/(B*2^d*(log X)^(d+1))<=Psi(X,y)`, shows that its logarithm is
`(2/alpha+o(1))*log z`, and therefore obtains the quantified diagnostic bound
`X/z^(2/alpha+epsilon)<=Psi(X,y)`.  This also proves that the elementary
weighted iteration is intrinsically one full `1/alpha` short of Tao's sharp
exponent.  The sharp asymptotic consumer is now compiled separately:
`HasCriticalSmoothLowerSaddle X y E` supplies the finite lower packet
`X*exp(-(u*log u+E))<=Psi(X,y)`, and `E/log z->0` implies
`X/z^(1/alpha+epsilon)<=Psi(X,y)`. For the source-sized choice
`E=C*u*log(log u)`, its required negligibility and the resulting sharp
consumer are both proved. Lean also proves `log u/log y->0` and hence
eventually `u<=y^(1/2)`.
The exact CEP source packet is compiled: its open--closed prime intervals are
pairwise disjoint, its normalized exponential weights sum to one as in (3.7),
and its multiplicities are `floor(alpha_j*u)`.  These data now instantiate the
collision-free reciprocal packet (3.11) and the smooth-cofactor density bridge
(3.10).  Lean also proves the exact reverse geometric moment, the aggregate
flooring ledger, and the resulting multiplier lower exponent in (3.6)--(3.8).
Each exact band cardinality is identified with the corresponding difference
of `Nat.primeCounting` at its floored endpoints; the reciprocal-prime input is
reduced to that literal endpoint bound and is wired through the full packet.
The canonical cofactor cutoff is the lowest-band floor, while the exact saddle
identity `X^(1/(log X/log y))=y` identifies the natural source cutoff with the
original `y`; the packet therefore feeds directly into `psiNat X y` without a
rounding loss. `SmoothNumberCEPCoarse` closes the finite saddle without a
shrinking-band PNT: fixed dyadic PNT blocks give endpoint reciprocal mass
`1/(16 log 2 log u)`, multiplicity `floor(u-2u/log u)`, cofactor depth at most
`10u/log u`, and total secondary loss at most `60u log(log u)`. Consequently
`IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat` proves
`X/z^(1/alpha+epsilon)<=Psi(X,y)` for every fixed positive `alpha,epsilon`.
Together with the critical upper theorem and both polylogarithmic theorems,
the four quantified halves of Proposition 2.1 are compiled and audited. The
shrinking-band source packet remains available as an optional source-faithful
route. The first downstream multiplicative instantiation is now complete:
uniform diagonalization over primes `z<p<3z`, dyadic reciprocal-prime mass,
and the exact `B¹` sum prove the lower half of Lemma 1.6(i). A finite grid on
the middle exponents `1/2≤alpha≤2`, together with the rounded square-root and
reciprocal-square endpoint ranges, proves the matching upper half. Thus
Lemma 1.6(i) is complete. The literal `floor(cX)` rounding, its logarithmic
invariance, preservation of the critical smooth-number regime, the exact
Granville-(3.24) quotient-limit target, and both automatic monotone halves of
Lemma 1.6(ii) are now compiled. The exact finite saddle sums `phiOne` and
`phiTwo` are also formalized: `phiOne` decreases continuously from infinity
to zero, its positive solution is unique, `phiOne'=-phiTwo`, and an exact
mean-value identity controls its response to changing `X`. Explicit
Abel--Chebyshev and prime-counting comparisons now prove that the exact saddle
tends to `1` throughout every critical regime. Its curvature is at least
`log(2) log(X)` and diverges, and fixed multiplicative dilation changes the
saddle by `o(1/log y)`. The exact
saddle phase is now literal as well: its exponential is exactly
`X^sigma` times the finite Euler product, its derivatives are
`log(X)-phiOne` and `phiTwo`, and the chosen saddle uniquely minimizes it.
The Gaussian saddle main term is defined and positive, and Rankin's bound is
evaluated there. A finite minimum-phase squeeze proves that fixed dilation
changes the minimized phase by `log(c)`, so the quotient of its exponential
parts tends to `c`. Prime-local logarithmic derivative bounds show that the
curvature quotient tends to `1`; consequently the quotient of the complete
Gaussian saddle main terms tends to `c`. The uniform asymptotic comparison
with `Psi`, and hence the reverse analytic comparison, remains.
The exact polylogarithmic contract is `log X/log x -> 1` and
`log y/log₂x -> A` for fixed `A>1`. Lean proves
`u/(log x/log₂x) -> 1/A`, `sigma -> 1-1/A`, the full dyadic scalar estimate,
`u log u/log x -> 1/A`, and that the positive dyadic error is `o(log x)`.
Thus `Psi(X,y) <= X/x^(1/A-epsilon)` eventually for every fixed positive
`epsilon`. Its matching lower estimate is compiled as well.  With the exact
depth `k=log_y X`, Lean proves `y^k<=X`, `k/(log x/log₂x)->1/A`,
`log pi(y)/log₂x->A`, and eventually `2k<=pi(y)`.  Granville's injective
prime-subset lattice and the integral binomial entropy inequality then give
`x^(1-1/A-epsilon)<=Psi(X,y)` eventually.  The multiplicative stability
clause remains open.
An additional finite Bernoulli/telescoping comparison already provides a
coarse sum-free bound with denominator `log 2`; the sharper range split needed
to recover the source-scale `log y` denominator is proved both abstractly and
for the canonical floored cutoff above.
It also proves the unique `a²b³`
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
Tao's complete Lemma 4.1 (`abound`) is now proved: every type-`F₃` interval
has `H<N`, is prime-free, and every witnessing smaller factorial index obeys
one uniform bound `a ≤ C H log N`. The proof formalizes the upper-half-prime
product divisibility, its exact Chebyshev-theta inequality, the pinned PNT
lower bound, and absorption of the finite exceptional range.
The shared arithmetic core of Lemma 4.2 is also proved at the literal scale
`P=H log²N`: eventually `a<P`; primes above `P` have even interval-product
valuation concentrated in one interval element; and in the large-`P` branch
`√(2N)<P<p`, such a prime cannot divide the product because `p²>N+H`.
The large-`P` equidistribution interface is now compiled as well: membership
of `{N/p}` in the final divisor arc produces an interval multiple, Tao's
smaller arc of width `1/(10 log²N)` is supported there for `P<p<2P`, the
corresponding prime sum vanishes exactly, and specialized Theorem 2.5 gives
the integral upper bound. A shrinking one-coordinate bump is explicitly
defined from the audited flat-exponential periodic bump and proved smooth,
periodic, nonnegative, and supported in the required arc. A second normalized
smooth-transition construction is proved to equal one on Tao's full inner
plateau arc. Its exact mass is at least `1/(60 log²N)` per unit interval.
The stretched-log contradiction hypothesis also supplies the complete
Theorem 2.5 parameter bound at `P` internally, yielding the source-growth form
of this integral upper estimate with multiplier one.
The reciprocal substitution `u=N/t`, its Jacobian comparison, and removal of
the logarithmic weight now give the matching prime-integral norm lower bound
and a single audited lower/upper logarithmic sandwich. The normalized family
has a uniform `O(log^12 N)` `C³` bound, and the final logarithmic contradiction
is complete. The proposition-valued Baker--Harman--Pintz interface implies
`4P≤N` eventually and closes the entire high-`P` branch conditional on that
interface and Theorem 2.5; the analytic proof of Proposition 2.3(ii) itself
remains open.
For the low-`P` branch, the explicit two-coordinate product cutoff is smooth,
periodic, nonnegative, and supported where an interval divisor is not
divisible by `p²`. Its prime sum vanishes exactly, its `C³` norm is
`O(log^12 N)`, and Theorem 2.5 gives a uniform polynomial-logarithmic integral
upper bound. The shrinking-band geometry is now complete: two exact changes
of variables, endpoint trimming, and occupied-unit-cell insertion give
prime-set measure at least `H/1920`; the fixed quadratic bump then supplies
the integral lower bound. The resulting logarithmic contradiction closes the
low-`P` branch and combines with the high-`P` branch into Lemma 4.2 conditional
on Theorem 2.5 and Proposition 2.3(ii). The source-shaped backward BHP theorem
is now proved to imply Tao's exact natural-endpoint proposition: sampling at
`N+2N^0.525` handles the orientation and Bertrand absorbs the finite range.
Only the pinned paper's analytic backward-interval theorem remains open here.
Lemma 4.2 also supplies the formerly abstract Theorem 1.10 gap input:
`⌈exp((log x)^(3/4))⌉` bounds every factorial-square triple tail and is proved
to be `x^o(1)`. Theorem 1.9 is now derived internally from that same Lemma
4.2, so the direct Theorem 1.10 bridge has exactly three remaining inputs:
the Erdős--Selfridge core, Theorem 2.5, and the analytic BHP theorem.
The Erdős--Selfridge source is pinned, and the exact reduction from a repeated
factorial squarefree component to a square consecutive product is proved;
the no-square theorem itself remains to be formalized.
The finite counts for `B`, `VB`, and `F₃` also have audited exact
`nontrivial + one-term = total` decomposition identities.
For `VB¹`, the full source constant asymptotic
`#(VB¹∩[1,x]) ~ ζ(3/2)/ζ(3) √x` is proved and audited. The complete finite
assembly for the nontrivial branch is now also proved: bounded interval
witnesses inject into Lemma 3.2 relation certificates with two explicit
multiplicity parameters; Lemma 3.1 and Lemma 3.2 give subpolynomial natural
budgets; and uniform Corollary 2.11 yields `x^(2/5+o(1))`. Consequently the
literal Theorem 1.8 endpoint is proved conditional only on analytic Theorem
2.5, through `taoTheorem18_of_taoTheorem25Specialized` and
`taoTheorem18_of_taoTheorem25`. It is not claimed unconditionally.
The elementary first step of Lemma 3.1 is also proved for positive starting
points: a very bad interval has `H<N`. The crosswalk records the genuine
`N=0,H=1` edge case in the paper's unrestricted wording.
The stronger-clause interface is now formalized through the exact source
rectangle: for `H<p≤2H`, the conditions `{N/p}≥0.9` and `{N/p²}<0.9` produce
an interval element divisible by `p` but not `p²`, contradicting very
badness. Thus supported weights have identically zero prime sum, and the
specialized Theorem 2.5 contract gives the required integral upper bound. An
explicit nonzero, nonnegative sine/flat-exponential cutoff is now proved
`C∞`, `ℤ²`-periodic, and supported in that rectangle. The contradiction growth
hypothesis now yields the exact Theorem 2.5 exponent with multiplier one. The
cutoff has a fixed positive minimum on the inner rectangle, its integral is
real and nonnegative, and its norm lower bound is reduced to the measure of
the exact inner good set; reciprocal-set membership is transported exactly.
Both source changes of variables now compile with their exact Jacobians. The
quadratic band has exact unit-period mass `43/50`; its uniform slice bound
implies quadratic reciprocal-set measure at least `H/32` whenever
`N/H²≥1/2`. A finite disjoint unit-cell covering, endpoint trimming, and the
slow-variation estimate now insert the first-coordinate fractional band and
give inner prime-scale measure at least `H/400` for `H≥200` under that scale
condition. The arithmetic boundary is now unconditional in the eventual form
needed by Tao: the frozen PNT, exact binomial factorization, central/general
binomial lower bounds, and a two-range logarithmic argument produce a prime
`p>H` whenever `2N<H²` for all sufficiently large `H`. Hence
`eventually_one_half_le_start_div_length_sq_of_veryBad` gives `N/H²≥1/2`, and
`eventually_veryBadInnerPrimeScale_measure_lower` gives the final `H/400`
measure bound. The stronger unrestricted Sylvester--Schur contract and its
standard binomial form remain documented interfaces, but are no longer a
Lemma 3.1 blocker. The fixed cutoff and Theorem 2.5 constants are now chosen
outside the eventual quantifiers, two logarithmic powers are proved to beat
the `H/log H` lower bound, and
`eventually_not_isVeryBadInterval_of_growth_of_taoTheorem25Specialized`
packages the complete contradiction assuming only the specialized Theorem
2.5 conclusion. `TaoLemma31Conclusion` now combines it with the positive-start
`H<N` clause and follows from both the specialized and full Theorem 2.5
contracts. The smoothness index was also corrected from
Mathlib's analytic `⊤` to its genuine `C∞` index `∞`.
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
propagated to the final real squared-inner-sum inequality. For interval `I`
and a quotient outer block, the filtered support is one explicit half-open
interval with ceiling-divided endpoints and length at most the outer block;
canonical Vaughan correlations rewrite exactly as `reciprocalPhaseSum`.
The Type I variable-support sum is also reduced exactly to the rescaled
integer phases with parameters `N/m, M/m^j`, under an explicit coefficient
envelope. The exact divisor-antidiagonal-to-product-box rearrangement and
outer/double coefficient-block decompositions now connect the weighted
Vaughan identity to literal `m*n∈I` Type I/II sums. The source-oriented
reassociation now identifies the canonical Type I/II coefficient pairs and
proves their exact support conditions and `1`, `log P`, `1`, `log P`
envelopes. The canonical family over `[1,B]` has exactly
`(log₂ B+1)^102` indices, covers every positive coefficient index, and gives
the exact one-family Type I and double-family Type II decomposition. The
strengthened budget `L=(log₂ B+1)^101` absorbs ceiling rounding and proves the
literal source support width `(1+log(B)^(-100))M`; small dyadic bands are
singleton blocks, and `P≤B` transfers this to the paper's literal
`(1+log(P)^(-100))M` width. Vinogradov/Weyl cancellation and quantitative Type I/II
estimates remain open. Conditional Fourier
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
frequency. These estimates and the zero mode are now combined into the radial
envelope with constant `27`. Iterated derivatives inherit periodicity, their
norm ranges reduce to the compact fundamental square, and the pure coordinate
chains are constructed automatically, yielding the unconditional source-facing
`taoC3Norm` coefficient estimate. For nested finite mode sets, the
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
actual short block. The first unconditional Weyl-differencing layer is also
proved: exact shifted-pair fibers give the averaged-shift identity, finite
Cauchy--Schwarz, and the summed window-square expansion with constraint
`n+h=n'+h'`. Both shift orders reduce to truncated forward correlations, and
natural-distance regrouping gives the divided finite van der Corput
inequality with its strict lag range. The zero lag, uniform recursive rule,
translation of `reciprocalPhaseSum`, appended-lag recursion, and commutation
of sampled real finite differences with derivatives on the positive ray are
also proved. The exact terminal affine geometric-sum identity and its
nonresonant `min(N, 2 / ‖e(alpha)-1‖)` bound are proved, as is its canonical
nearest-integer-distance form `min(N, 1/(2 dist(alpha,ℤ)))`. Uniform terminal
bounds propagate through any finite number of Weyl rounds via an explicit
nested square-root majorant, and the translated reciprocal phase has the exact
four-step interface needed by the source's `k=5` branch. Each one-step real
finite difference is exactly an interval integral of its derivative, with
absolute upper and signed lower derivative-separation bounds. For globally
smooth phases these estimates iterate with the exact product of all lags. They
now also iterate on the positive ray over the exact evaluation interval, with
direct reciprocal-phase upper and critical-regular lower bounds; continuity
supplies the required constant sign. Terminal iterated phases now have a
uniform critical-regular first-derivative window obtained from the next source
derivative, so four lags consume the fifth derivative exactly. The frozen
Kusmin--Landau theorem is now adapted exactly to `exp(2πix)`; mean-value and
second-derivative sign bridges turn absolute terminal derivative windows into
monotone increments. The resulting source-facing theorem proves the nonlinear
critical-regular terminal sum bound under explicit expanded-interval and
upper-one-period hypotheses. Exact `rH` lag-sum and `H^r` lag-product bounds
make this uniform over all admissible lags and truncated lengths on one
expanded regular interval and feed it through the recursive majorant; the
literal four-round theorem uses derivative orders five and six and a single
`H^4` upper-smallness condition. A second, exact lag-sensitive tree retains
each accumulated lag list and boundary-truncated length, accepts the source
leaf bound `min(L, 1/(prod(lags)*scale))`, and bounds the innermost lag sum by
the exact harmonic factor before the first square root. A general induction
collapses every successive outer lag sum to explicit scalar length and scale
recurrences with generalized harmonic factors at most `H`; the closed
four-round source theorem retains the expected inverse-scale sixteenth root.
The generalized harmonic factors are now also kept sharply: successive
Cauchy--Schwarz inequalities prove that the exact four-round scale coefficient
has sixteenth power at most `(6L)^15 * harmonic(H)^4 / (H+1)^4`. Thus the
terminal scale term retains the decisive harmonic-over-range gain, and a
source-readable wrapper bounds `harmonic(H)` by `1 + log H`.
Replacing those factors by `H` yields a coarse scale coefficient with exact
four-round sixteenth power `(QH)^15`, hence a complete scale term with power
`(QH)^15/scale`. The length recurrence is split into four explicit terms with
sixteenth powers `D^8`, `E^8D^4`, `E^12D^2`, and `E^14D`; exact step-factor
bounds give their denominator powers `8,4,2,1`. All four diagonal terms and the
scale term are extracted as sixteenth roots and rewritten exactly as real
`1/16` powers in a source-facing five-term majorant with no hidden recurrence.
The canonical floor-rounded range `floor((2U)^(-1/4))` is now proved to
discharge the exact upper-smallness condition and is installed in both root and
rpow source estimates. Expanded critical starts have the proved count
`orders.card*(16Xq+4H+2)`; their per-order interval hulls preserve this bound,
and at most two endpoint cuts per order give the improved regular multiplier
`2*orders.card+1`. Recovery of real expanded-interval regularity and a global
long/short-component theorem now work for every range satisfying the exact
upper-smallness inequality. The adaptive range
`min(length, floor((2U)^(-1/4)))` automatically fits the interval and preserves
that inequality, while using the sharp harmonic majorant. The two adaptive
branches are now unified by the exact denominator bound
`(H+1)^(-4) <= 2U+(L+1)^(-4)`. This feeds an optimization-ready global
majorant, with critical width fixed to the `1/128` power of the complete
effective error scale. That scale is normalized exactly to
`240(5+j)^5 F/X^5 + (L+1)^(-4) + 1/F` and bounded by the explicit derivative
factor times the source-shaped three-term error. Final parameter
optimization now additionally uses
`min(floor(L*q), canonicalRange)`: its short-component and expanded-window
penalties are proved to be at most `Lq` and `4Lq+1`, and its harmonic logarithm
is at most `log L`. Its fourth-power denominator is bounded by
`2U+(Lq)^(-4)`, and this has been propagated through the terminal root in the
global theorem. The four diagonal roots are now bounded by `72Lq`, the
optimized terminal root by `100((5+j)^5+1)(1+log L)Xq`, and the complete
majorant by the corresponding constant `172`. These estimates propagate to a
global fixed-power theorem and a wrapper using the explicit source-normalized
`1/128` power. The additive endpoint constant is absorbed into the same source
power, leaving one coefficient times `X`. Under `F≤X^4`, an exact short/long
interval dichotomy now removes the remaining length term on arbitrary
subintervals: the long case is absorbed into
`(F/X^5+1/F)^(1/1024)`, while the short case follows from cardinality. This
gives the source-shaped two-term degree-five bound under the stated
effective-error and expanded-interval regularity hypotheses. This theorem is
also specialized to the exact product-restricted Type II correlation support;
the off-diagonal transformed coefficient obligations and empty-intersection
case are discharged internally. In the final `N=M` specialization, an exact
transformed-scale lower bound yields the pointwise kernel-plus-error estimate
`E^(1/1024)+4(1+distance*F/B)^(-1/1024)`. Its varying interval logarithm is
uniformized by the outer block length and the result is propagated through the
endpoint-free kernel summation to the exact Vaughan double-block squared-sum
bound. The pairwise `F'/K^5≤E` premise is now discharged uniformly from the
inner block's left endpoint and diameter by the explicit
`typeIIShortIntervalScaleError`; proving that fixed block error
logarithmically negligible remains. In the quadratic specialization, outer
block geometry now discharges all endpoint and power-evaluation conditions;
the transformed-scale bound also follows once the block error is at most
`1/K`. In the quadratic case that comparison is now derived from the
source-shaped low-frequency condition `10F≤K^4(log Bcap)^100` on an inner
dyadic band above the Vaughan subdivision budget. The proved logarithmic
width supplies `q≤D/(log Bcap)^100≤R/(log Bcap)^100`, hence `10qF≤K^4R`;
the reciprocal-phase identity then gives the previous monomial bound
`5q|N|≤K^5R^2` internally.
The complete estimate is now generalized to arbitrary positive block
endpoints and specialized directly to the named dyadic blocks in the canonical
Vaughan double family. Its effective-error family is compressed to the scalar
`typeIIShortIntervalEffectiveErrorBound≤1`; on large Vaughan bands the proved
logarithmic width estimate supplies `5q≤K` and hence the expansion margin.
The canonical theorem now makes the source-faithful distance split internally.
Pairs with `distance·F/B≤3` use the trivial correlation bound and the proved
kernel lower bound `1/4`; farther pairs have inverse transformed scale at most
`2/3` and enter Weyl differencing. Thus no false polynomial lower bound on
`F` is required. Moreover, the `1/4` upper-scale budget follows intrinsically
from `F'≤K^4`, which gives `F'/K^5≤1/K`,
and the existing `2≤log Bcap` assumption now proves that the common Vaughan
subdivision budget dominates `4·(240·7^5)`. On non-singleton inner bands,
`sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_additiveError`
now performs the source's split separately for every far pair: `F'≤K^4` is
closed by the proved four-step Weyl theorem with intrinsic error
`(1/K)^(1/1024)`, while only
`K^4<F'` is exposed as the supplied high-scale analytic estimate with its own
nonnegative additive error `V`. Thus neither a global all-pairs-low
hypothesis nor the source upper bound is needed in the strengthened hybrid,
and no retained global block-error term remains. The logarithmic lower split
`(log Bcap)^d≤F`, `d≥0`, already supplies `F≥1`. The complete conditional
Vinogradov component envelope is now absorbed uniformly into
`3K(log P)^(-T)`, including both critical-deletion terms, under the explicit
budget `T+2≤3A`. The remaining local high-scale input is the actual
Vinogradov proposition. Conditional on it, the canonical quantitative Type II
double-block assembly is now complete. The
conditional estimate is already converted to the exact hybrid callback
`Q(4·kernel+3(log P)^(-T))`; canonical Vaughan inner-block membership supplies
the transformed-scale upper bound with its fixed factor `5`. The complementary inner singleton-band
case is purely diagonal and requires no phase hypothesis. A
source-shaped pointwise
correlation estimate now propagates through the ordered off-diagonal pairs
and the exact product-restricted Cauchy--Schwarz identity to a final
squared-inner-sum bound, retaining the kernel decay, low-scale Weyl error, and
independent high-scale error separately. This is specialized to the actual
shorter-than-dyadic inner block
and then to the exact outer/inner double blocks produced by Vaughan; block
membership discharges the diameter and nonzero-index obligations. Each block
is also proved to contain at most its chosen length, so the final estimate is
now stated directly in `q_outer` and `q_inner` in the endpoint-free
source-scale form, ready for logarithmic exponent
bookkeeping. The high-frequency implication is also formalized exactly:
`(log P)^d ≤ F` and `b+t ≤ dc` imply
`(log P)^b F^(-c) ≤ (log P)^(-t)` once `P≥e`. The high-scale arithmetic is
also closed: `log F≤C(log P)^(3/2-ε)` converts the Vinogradov exponent to at
least `C⁻²(log P)^(2ε)`, whose stretched exponential absorbs every polynomial
logarithmic prefactor. The source parameters `α=(log P)^(4A)` and
`q=(log P)^(-3A)` now supply the complete regular-component derivative window,
and `log α·(log F)^2/(log X)^3<10^-3` follows eventually from the primitive
source parameter bound and `log X≥c log P`. The literal source cutoff
`R=10⌈log F/log X⌉+1`, including the shifted derivative demand `R+j≤log P`,
also fits the available logarithmic budget eventually when
`j≤(log P)^(1/2)`. `Tao2026/Vinogradov.lean` assembles these facts with
critical deletion into the full source-cutoff derivative window on every
regular interval. Its conditional global component theorem then propagates
any local Vinogradov inequality stated solely from that derivative window to
the full phase sum, with explicit component and critical-deletion costs. The
source's absolute-constant lemma is represented exactly by
`VinogradovExponentialSumEstimate`, including pointwise neighborhood
smoothness on the summation interval, and a second theorem derives the complete
global reciprocal-phase bound from that single proposition. The first stage
of its pinned proof is now internal too: Tao's literal polynomial
`F_n(q)=∑_{r≤R}f^(r)(n)q^r/r!` is identified with the calculus Taylor
polynomial, the Lagrange remainder and factorial cancellation are proved, and
the original integer-interval sum is replaced by the shifted polynomial sum
with an explicit boundary-plus-Taylor error. The product multiset of shifts
`xy`, `1≤x,y≤V`, is represented by pairs so multiplicities are retained; its
cardinality is proved to be `V²`, the individual errors are summed into a
uniform envelope, and an exact cancellation lemma divides the unnormalized
average. The interval pair sum is now split into complete pointwise product
sums and an exact right-boundary strip of size at most `V⁴`. Each complete
product sum is rewritten, after removing its unit-modulus constant phase, as
the generic coefficient-only bilinear polynomial sum
`∑_{1≤x,y≤V} e(∑_{1≤r≤R} c_r x^r y^r)`. Thus the remaining local argument is
independent of the original function and interval. This reduction also handles
intervals shorter than a shift. At the canonical floor-rounded `V=⌊X^(1/4)⌋`, its error is
further reduced to the source's `√X` plus normalized top-derivative remainder.
Both factors in that remainder are proved at most one from `F≥X⁴`, the literal
cutoff, and the `10^-3` condition. The resulting `√X+2π` loss is absorbed into
nine copies of the target Vinogradov scale, as is the `V⁴` boundary strip.
The smallest exact residual is
`VinogradovBilinearPolynomialNontrivialEstimate`: it asks for the generic
bilinear estimate only when its normalized target is below one, since the
complementary branch follows from the exact trivial `V²` bound. A proved
instance yields `VinogradovExponentialSumEstimate`; the two reductions increase
the absolute constant by eighteen. In that nontrivial branch, the coefficient
selection is also complete: all degrees in
`[(4/3)(log F/log X),(7/4)(log F/log X)]` satisfy Tao's medium window with
`c₀=1/128`, and exact floor/ceiling counting supplies at least `R/128` such
degrees. Thus the remaining bilinear work begins at the polynomial mean-value
argument itself. The new `Tao2026.VinogradovMeanValue` module now carries that
argument through Tao's equation (18): it defines the curve representation
function, proves `∑ν=V^ℓ`, identifies `∑ν²` with the exact equal-power-sum
solution count, proves the three-factor Hölder interpolation (including its
Cauchy endpoint), and derives the unnormalized analogue of Tao's equation
(16). It also defines the signed power-sum difference support, proves its total
multiplicity is `(V^ℓ)²`, and places every coordinate in the symmetric box
`|d_j|≤ℓV^(j+1)`. The exact even-moment expansion, difference regrouping,
and sharp pointwise multiplicity bound `μ(d)≤J` now give equation (18). The
two supports are enlarged to the full symmetric box, and its double character
sum is factored exactly into Tao's product of one-dimensional coordinate sums.
The geometric-series reduction, capped reciprocal-distance kernel, rescaled
nearest-integer fibers, their separation and count, and the resulting explicit
one-dimensional integral-test estimate from Lemma 12 are now compiled. The
medium window is also converted to a coefficient-free normalized logarithmic
saving for each good coordinate. The scalar factors are now bounded by fixed
negative powers, reindexed over the actual medium degrees, and the explicit
  source block first gives the quadratic product saving `V^(-R^2/307200)` times the
  trivial box square. The scalar growth condition is now discharged from the
original nontrivial-scale hypotheses. The frozen native Wooley development
proves the full VMVT, and its finite Ford count is identified exactly with the
local equation-(17) count. The trivial box square is now collected exactly as
`(3ℓ)^(2R) V^(R(R+1))`. At the critical moment
`ℓ=R(R+1)/2`, the complete positive-power ledger is proved to equal
`4ℓ²`; its real-power normalization and the abstract equation-(18) assembly
  `|B|^(2ℓ²) ≤ C² A V^(4ℓ²+2ε-δ)` also compile. A sharper production block
  `[(9/8)(log F/log X),(7/4)(log F/log X)]` lies in the genuine `c₀=1/4`
  window and has floor-rounded weighted mass at least `R²/193`. Absorbing only
  `1/1024` of each degree gives the coordinate product saving
  `V^(-255R²/197632)`. With native VMVT loss `ε=δ/128`, exact critical-root
  extraction leaves exponent `16065R²/(12648448·2ℓ²)`. This exponent is proved,
  including `R=10⌈log F/log X⌉`, to dominate the source target, and the floor in
  `V=⌊X^(1/4)⌋` costs only a factor two. `VinogradovWooleyCoefficient` now
  retains the native p-adic concentration data `(p,C,B₀)` and proves that its
  exact Section-12 coefficient is `C·(p^(B₀+1)κ_R)^ε`; a uniform rooted bound
  for this displayed expression implies the existing critical coefficient
  contract. `VinogradovFord` separately verifies the explicit supercritical
  multiplier `3R+⌊R/5⌋`, loss `3R²/2800`, and cubic coefficient growth. Its
  larger extraction power is insufficient for the prescribed `2⁻¹⁸` decay,
  while `VinogradovFiniteDegree` packages all native critical constants for
  `40≤R<1000` into one finite envelope. It proves that a rooted bound restricted
  to `R≥1000` implies the global coefficient contract and the nontrivial
  bilinear estimate. Thus the remaining work is precisely the infinite-degree
  scalar boundedness of the optimal rooted critical coefficient sequence. The
  optimum is the supremum of the normalized counts; it is a valid witness and
  is bounded by every other witness, making this scalar condition equivalent
  to the original tail contract rather than a stronger choice-dependent one.
  `VinogradovOptimalWooley` directly bounds the optimum and its critical root
  by the retained `C·(p^(B₀+1)κ_R)^ε` expression. Its prime is selected
  in the Bertrand range `R<p≤2R`. The coordinate-box root lies in `[1,3]`,
  reducing the residual, up to an absolute factor, to the VMVT coefficient
  root and therefore to growth of `C` and `B₀` alone. The coefficient root is
  exactly `C_R^(1/κ_R²)`; a fixed bound `A` is equivalent to the unrooted
  allowance `C_R≤A^(κ_R²)`, not uniform boundedness of the raw coefficients.
  Thus the p-adic frontier is the single explicit inequality
  `C·(p^(B₀+1)κ_R)^ε≤A^(κ_R²)`; it now has a direct bilinear consumer.
Its Type II
consumer rewrites each actual high transformed-scale correlation to the
ceiling-divided quotient interval and discharges its endpoint geometry. Raw
component counts are also simplified to `log P`, and the resulting full
principal-plus-deletion envelope has the uniform logarithmic saving above.
That nontrivial coefficient-only bilinear estimate from the
Iwaniec--Kowalski mean-value argument remains open, and hence so does the Vinogradov
exponential-sum inequality itself.
Theorem 2.5 is not claimed.

Node 73 keeps the human-readable location assigned by the RH Map. The exact
1,339-module Lean import closure of `GafniTao.Theorem11` and the native Wooley
VMVT bridge is frozen under this
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

The runner checks all pinned source hashes, all 1,339 frozen dependency hashes and the exact
frozen file set, the raw Mermaid contract, toolchain/dependency pins, direct
production-root coverage, forbidden proof shortcuts in both production and
frozen source, the axiom audit, and the warning-free Lake build. Its current
success certifies Proposition 2.3(i),(iii), the exact one-term sums, the exact
zeta-ratio asymptotic for `VB¹`, Lemmas 2.10 and 3.2, Corollary 2.11, and the
factorial endpoint/counting bridges and complete finite Lemma 4.3 extraction.
It also certifies the injective interval-certificate encoding and arbitrary-
budget finite counting reduction that begins the Theorem 1.9 case split. The
bounded-length branch now has an exact smooth-coefficient refinement: its two
coefficient ranges have cardinality exactly `psiNat x P²`, and its endpoint
count is bounded by `A·psiNat(x,P)²·G³` times the uniform Lemma 2.10 budget.
An iterated square-times-squarefree encoding and Chebyshev's prime-counting
bound then prove directly that `psiNat(x,⌈C log(x+2)⌉)=x^o(1)`. Combined with
Lemma 4.1, this closes the actual fixed-bounded-length endpoint family with an
`x^o(1)` bound, without assuming Proposition 2.1(ii). It
also certifies the exact Theorem 2.5
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

For Theorem 1.8, continue Theorem 2.5 from its compiled exact contract, phase
calculus, complete Fourier coefficient decay/reconstruction, and exact
source-oriented, coefficient-bounded, product-restricted, block-decomposed
weighted Vaughan identity through the Vinogradov/Weyl estimate and quantitative
Type I/II bounds.
Completing that analytic theorem now directly instantiates the proved
Theorem 1.8 endpoint; no finite counting or asymptotic assembly remains.
In parallel source order, the pinned Baker--Harman--Pintz input in Proposition
2.3(ii) remains the next missing analytic boundary for Section 4.

## Deliberate non-claims

The Section 6 branch now includes the audited arithmetic core of Lemma 6.1:
non-singleton bad intervals satisfy `H≤N` and are prime-free, while the isolated
Sylvester--Schur input yields the source `p₀²m` witness together with
largest-prime smoothness for every interval element. The dyadic-window
comparability is recorded with its exact natural rounding, `N<x≤4N+1`.
The corrected exact core of Lemma 6.2 is also audited: the source power-of-two
choice gives a contained bad endpoint subinterval of length
`2≤H'≤H<4H'`, retaining the same largest prime and `p₀²m`, with exact scale
bounds `x≤4N'+1` and `N'+H'≤2x`. The source's claim that this child
automatically intersects the identical `[x/2,x]` window is not assumed;
containment alone does not imply it, so the later maximal transfer must use
the proved comparable-scale statement.
The finite maximal-function precursor is now compiled as well. Bounded
admissible and comparable-scale normalized families and their unions are
explicit, and every point of the admissible union has a four-length enlarged
interval on which the normalized union occupies at least one tenth of the
lattice points. A kernel-checked greedy selection of maximal-length intervals
then supplies pairwise disjoint representatives whose threefold enlargements
cover the family. This proves the finite weak-`(1,1)` inequality and the exact
comparison `#admissibleUnion≤30·#normalizedUnion`.
Definitions 6.3--6.4 are now represented by exact finite predicates with
explicit lower and upper cutoffs for the source's slowly varying prime window.
The ordered 1000-prime anatomy and smooth remainder imply both
`p₀<squareThreshold` and the exact displayed quotient bound for `m'`. The
large-square failure branch of Proposition 6.5 has also been reduced to an
explicit finite exceptional union with cardinality bounded by
`(2L+1)∑_{D≤d≤2x}⌊2x/d²⌋`. The reciprocal-square tail is now telescoped to
the closed real bound `(2L+1)(2x)/(D-1)`. The literal source choices
`L=⌈(log x)^20⌉₊` and `D=⌈z(x)^3⌉₊` are now substituted, and the compiled
comparison `(log x)^20+1≤2√z(x)` yields
`#exceptional≤24x/z(x)^(5/2)` eventually. The actual finite union of short
normalized intervals failing (ii) is proved to lie in that cover, closing
condition (ii) with the weak source alternative `δ=1/2`; the other
non-typical branches remain open. For condition (i), the finite large-sieve
core is now source-facing: every normalized start avoids the `H` distinct
classes `-1,…,-H` for all primes `p₀<p≤2p₀`, these restrictions are assembled
by the tensor Corollary 2.9 machinery, and the actual fixed-`(p₀,H)` interval
union has the resulting explicit weighted bound. The ambient-start maximal
degree and its eventual PNT range are compiled. Tao's smaller literal cofactor
budget `2x/p₀²` and floor-defined degree now drive a second, source-faithful
large sieve. Both square-endpoint orientations become `H` distinct affine
forbidden classes on `m`; smoothness proves avoidance, the tensor ratio is
preserved, and the two survivor covers recombine into the explicit fixed-fiber
bound with factor `16`. Discharging the source scale range, optimizing the
exponential weight, and summing the fibers remain. The first optimization
step is now compiled: the PNT count gives the exact base
`H/(8k log(2p₀))`, and `8k log(2p₀)≤H^(1/10)` upgrades it to the source
`H^(0.9k)`-weighted fixed-fiber inequality. Floor maximality is also expanded
through the quotient budget to prove
`2x<(2p₀)^(2k+4)` and `log(2x)/log(2p₀)<2k+4`. For the valid finite range
`k≥4`, this gives the corrected quarter-bound. The stronger comparison
`8k log(2p₀)≤H^(3/50)` absorbs the leading interval-length factor, yielding
the explicit fixed-fiber decay `H^(-0.9(k-1))` and its canonical exponential
form. The literal long cutoff eventually discharges this stronger denominator
comparison uniformly in `p₀`. In the complementary `k<4` range, maximality
forces `2x<(2p₀)^10`; the unsieved two-orientation cofactor cover then gives
the fixed power-saving fiber bound `4096x^(9/10)`. The exact AM--GM prime-scale
saddle is now compiled as well: the literal long cutoff gives numerator
`≥(9/2)log x log₂x`, hence the canonical `k≥4` fiber bound
`#fiber≤128x/(p₀z(x)^6)` eventually. More importantly, the paper's invalid
quarter comparison at `k=2,3` is replaced by a valid eighth-comparison for
all `k≥2`. The relaxed constants still prove
`#fiber≤128x/(p₀z(x)^4)`. On `p₀^20≤x^3`, nonempty fibers and the literal long
range discharge every remaining square-scale, degree, PNT, and large-budget
side condition eventually. `BadIntervalLongSum` now sums the exact finite
dyadic-length and moderate-prime fibers. The dyadic count and harmonic prime
majorant cost two logarithmic factors, both absorbed by one factor of `z(x)`;
the actual long moderate-prime normalized failure union is therefore
eventually bounded by `x/z(x)^3`.
`BadIntervalLargePrimeSum` handles the preceding large-distinguished-prime
disposal on Tao's exact ceiling-rounded `H<x^(7/50)` range. The unsieved
cofactor cover gives `8Hx/p₀²` per fixed fiber; summing dyadic lengths and the
reciprocal-square tail above `x^(3/20)` proves that the actual normalized
large-`p₀` union is eventually at most `x^(199/200)`. Both source power
conditions `H^50<x^7` and `p₀^20>x^3` have exact cutoff bridges.
`BadIntervalLargeLength` closes the complementary preliminary
`H≥x^(7/50)` branch. It chooses the fixed spare exponent `41/300`, strictly
between `2/15` and `7/50`, and uses one greedy disjoint selection across all
lengths. The selected real start segments lie in the literal prime-free
endpoint set at outer scale `2x`; their total measure pays for the selected
natural intervals, giving `#union≤6 primeFreeEndpointMeasure(2x,41/300)`.
Proposition 2.3(iii) therefore yields an existential fixed power saving for
the actual large-`H` normalized failure union.

This development milestone does not claim any of Theorems 1.7--1.10,
publication readiness, external review, or a route to the Riemann Hypothesis.
The formal connection to nodes 71 and 74 is limited to the frozen, hashed
dependency closure and the audited quantitative bridge described above.

## Repository synchronization

`push_to_github.bat` is the existing owner-operated repository synchronization
script. It is not called by the build or development verifier.
