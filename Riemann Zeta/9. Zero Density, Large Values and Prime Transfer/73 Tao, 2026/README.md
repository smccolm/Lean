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
Lemma 1.6(ii) are now compiled. The complete Lemma 1.6(ii) contract is also
derived from that quotient limit: the resulting half-ratio is iterated through
fixed powers of two and exact floor bracketing handles every `c>0`. The exact finite saddle sums `phiOne` and
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
with `Psi` is now an exact proposition-valued contract and is proved to imply
Granville's quotient limit and the stability clause; its analytic proof remains.
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
 measure bound. The same binomial proof now works uniformly for every start at
 all sufficiently large lengths. A Bernoulli monotonicity argument and the
 explicit fixed-length threshold `H^H+1` reduce the stronger unrestricted
 Sylvester--Schur contract to a finite bounded rectangle. The first forty-eight
 length rows are now discharged uniformly over every start by
 `sylvesterSchurBelow_fortyNine`; the remaining rectangle has `H>=49` and remains
 open. A separate start-uniform theorem also shows that every length works
 beyond one common start cutoff; consequently the residual rectangle is no
 longer a Lemma 3.1 or Theorem 1.7 blocker. The fixed cutoff and Theorem 2.5 constants are now chosen
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
non-singleton bad intervals satisfy `H≤N` and are prime-free. A local
large-prime witness yields the source `p₀²m` witness together with
largest-prime smoothness for every interval element; the eventual start-uniform
theorem supplies it at all sufficiently large admissible scales. The dyadic-window
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
converse arithmetic construction is also compiled: if the smooth cofactor
has at least 1000 prime factors above the lower cutoff, counted with
multiplicity, its 1000 largest factors give the ordered anatomy and the
remaining product is smooth below the last selected factor. Consequently,
after excluding the length and square failures, failure of condition (iii)
forces fewer than 1000 such factors. The
large-square failure branch of Proposition 6.5 has also been reduced to an
explicit finite exceptional union with cardinality bounded by
`(2L+1)∑_{D≤d≤2x}⌊2x/d²⌋`. The reciprocal-square tail is now telescoped to
the closed real bound `(2L+1)(2x)/(D-1)`. The literal source choices
`L=⌈(log x)^20⌉₊` and `D=⌈z(x)^3⌉₊` are now substituted, and the compiled
comparison `(log x)^20+1≤2√z(x)` yields
`#exceptional≤24x/z(x)^(5/2)` eventually. The actual finite union of short
normalized intervals failing (ii) is proved to lie in that cover, closing
condition (ii) with the weak source alternative `δ=1/2`. The deficient-factor
disposal is also quantitative: deficient packets cover the actual remaining interval union and
give the target `4L ∑_{p₀}∑_a Ψ((2x/p₀²)/a,y)`, where `a` is a product of
fewer than 1000 admissible large primes. This distinct-product sum is also
bounded by the literal finite sum over all multiplicity-retaining factor lists
of length below 1000. At `y=⌊z(x)^(9/10)⌋`, uniform critical smooth-number
estimates retain every reciprocal factor, elementary harmonic bounds control
the list mass, and the full polylogarithmic loss is absorbed to prove the
central-band actual-union bound `x/z(x)^(2+1/200)` eventually for
`z(x)^(9/10)<p₀≤z(x)^(11/10)`. A 600-cell mesh also closes both fixed
outside-central windows, proving the actual short-union bound
`x/z(x)^(2+1/1000)` on `z(x)^(2/5)<p₀≤z(x)^(9/10)` together with
`z(x)^(11/10)<p₀≤z(x)^(5/4)`. The corresponding concrete non-typical family
is now assembled across all eight failure branches and satisfies the audited
fixed-cutoff bound `#union≤x/z(x)^(2+1/4000)` eventually.
`BadIntervalSlowCutoff` upgrades this to the source window. Its row
`d=n+10` uses exact natural cutoffs `⌊z(x)^(1-2/d)⌋` and
`⌈z(x)^(1+2/d)⌉`; moving low/high meshes and the intervening deficient range
give `#union≤x/z(x)^(2+1/(128d²))`. A countable diagonal chooses
`q(x)→∞`, proves both cutoff log-ratios tend to one despite floor/ceiling
rounding, and yields the selected actual-union bound `#union≤x/z(x)^2`.
This closes the source-facing Proposition 6.5 cutoff contract.
`BadIntervalSlowCutoffLogSaving` retains the row exponent through the diagonal:
one selector gives, for every fixed `epsilon>0`, the stronger eventual bound
`#union≤badOneTermCount(x)/log(x)^(1-epsilon)`.
`BadIntervalRandomModel` starts Proposition 6.6 on a literal finite
probability space. The 1001 tuple coordinates have exact uniform laws on their
half-open dyadic prime bands and are proved mutually independent under the
product measure. The tuple product `p₀²p₁⋯p₁₀₀₀m'`, divisibility indicators,
typical event, and event probability are defined; the anti-sieve moment bound
is now under way. `BadIntervalAntiSieve` proves the exceptional `p∣l`
contribution is pointwise at most `H log H`, strengthens this eventually to
`H log z(x)` for every admissible `H`, and proves the corresponding event is
empty with probability zero. `BadIntervalSmallPrimeMoment` fixes the literal
cutoff `⌊z(x)^(1/100)⌋`, excludes `p∣l`, retains the source exponent `50`,
and proves the exact ordered-50-tuple expectation expansion into joint
divisibility probabilities. The tuple lcm is explicit, and each joint event
is proved either empty or exactly a single primitive residue-class fiber
modulo that lcm. `BadIntervalLargePrimeMoment` defines the literal unweighted
large-prime contribution over `1≤l<H`, proves exact finite formulas for its
mean, second moment, variance, and double covariance expansion, and performs
the source diagonal reduction. When `H≤lowerPrime`, distinct shifts carrying
the same prime have empty joint event and nonpositive covariance; consequently
the variance is bounded by the mean plus only the distinct-prime covariance
sum. The analytic bounds for those remaining terms are still open.
`BadIntervalLargePrimeCharacter` proves the corresponding exact CRT layer:
each one-prime event is empty or one primitive residue fiber modulo `p`, and
each distinct-prime joint event is empty or one primitive fiber modulo `pp'`.
Both probabilities are thereby bounded by the existing all-character
1000th-moment expression at their literal moduli.
`BadIntervalLargePrimeExceptional` converts the aggregate Lemma 5.1 character
count into a count of exceptional prime conductors, giving the exact stronger
exponent `2/125`. The common-factor aggregate and uniform-cardinality modules
then retain a fixed prime `p`, vary `p'`, and prove that one eventual constant
works pointwise for every admissible family. `BadIntervalLargePrimePairs`
specializes this to the literal product conductors `pp'`, establishing the
  uniform exceptional-partner count required in Proposition 6.8, conditional
  only on analytic Burgess.
  `BadIntervalPrincipalCharacter` now splits the principal character before
  weak AM--GM, replacing the former factor-1000 principal contribution by one
  exact main term. The principal tuple expectation is the probability that
  `p₀²p₁⋯p₁₀₀₀m'` is coprime to the modulus. When `m'` is
  coprime to `p`, or to `pp'`, its deficit from one is bounded by the union of
  coordinate collisions, with explicit cost at most one reciprocal dyadic-band
  cardinality per coordinate and per prime. The following modules close the
  finite nonprincipal conversion and crude fallback; their common PNT scale
  instantiation and dyadic aggregation remain. `BadIntervalLargePrimeNonprincipal` proves that every
  nonprincipal character modulo a prime is primitive and, outside the union
  of coordinate-wise exceptional conductors, bounds the entire remaining
  one-prime moment by `φ(p) * ∑ P_j^(-8)`. It then substitutes this bound into
  the collision inequality to obtain the direct deviation from `1/φ(p)`.
  This closes the improved nonprincipal error conversion for the one-prime
  branch of Proposition 6.7.
  `BadIntervalLargePrimeProductNonprincipal` performs the exact ambient
  conductor regrouping for `pp'` under band separation. When every nontrivial
  divisor conductor is unexceptional, `∑_{d|pp'} φ(d)=pp'` gives the complete
  error `pp' * ∑ P_j^(-8)` and a direct product-modulus deviation theorem. The
  companion `BadIntervalLargePrimeProductCollision` module removes the
  separation condition: only the two modulus primes can alter a change-level
  average, giving error at most `4/card`, and convexity propagates this as an
  explicit `(4/card)^1000` correction. The resulting product deviation theorem
  has no band-separation hypothesis.
  `BadIntervalLargePrimeCrude` starts the finite fallback count with the exact
  bound `#({r in [Z,2Z) prime : r ≡ a mod q}) ≤ ⌊2Z/q⌋+1`, together with its
  normalized real form for freezing tuple coordinates.
  `BadIntervalPrimeTupleUniform` identifies the full product measure with
  exact uniform counting on the Cartesian prime-band support, including the
  common singleton mass and a cardinal formula for every event.
  `BadIntervalPrimeTupleFiber` freezes one ordinary coordinate and proves the
  exact support-cardinality cancellation. Uniform coordinate fibers give an
  `M/card` probability bound; pairwise congruence gives the elementary
  `(⌊2P/q⌋+1)/card` bound. Factoring `p₀²p₁⋯p₁₀₀₀m'` by the
  selected coordinate supplies the coprime single- and joint-divisibility
  estimates. Splitting off noncoprime source products and applying the existing
  collision unions removes that condition, at the explicit cost of one or two
  coordinate-collision sums.
  `BadIntervalPrimeTupleMultiFiber` implements the source's stronger freezing
  of two coordinates in Proposition 6.7(i) and three in Proposition 6.8(i).
  It first proves exact cancellation for an arbitrary finite coordinate set
  and a general selected-product residue theorem. Products of two sampled
  primes represent a natural number at most twice, while products of three do
  so at most six times. The resulting exact finite probability numerators are
  `2(⌊4P₁P₂/p⌋+1)` and `6(⌊8P₁P₂P₃/(pp')⌋+1)` over the corresponding exact band
  cardinality products; prime moduli and nonzero shifts discharge the cofactor
  coprimality assumptions.
  `BadIntervalLargePrimeCrudeNormalize` then turns these exact ratios into the
  source-shaped bounds `16L²/p` and `96L³/(pp')` under the common finite band
  inequality `P_j≤L·#band(P_j)` and the explicit modulus-below-product
  condition. The next module supplies the PNT/anatomy-scale specialization.
  `BadIntervalLargePrimeCrudeSource` performs that specialization under the
  exact 1001-coordinate contract of divergence and
  `log(P_j)/log(z)→1`. The PNT and finite-coordinate uniformization give
  `P_j≤4log(z)#band(P_j)` and nonempty bands simultaneously, yielding eventual
  bounds `256log²(z)/p` and `6144log³(z)/(pp')`. Exact dyadic aggregation is
  the next boundary.
  `BadIntervalLargePrimeProbabilityBounds` now turns the improved character
  estimates into literal event estimates. It proves the absolute one-prime
  deviation from `1/φ(p)`, upper bounds the one- and two-prime events including
  their empty branches, and combines those errors with
  `φ(pp')=φ(p)φ(p')` to obtain an explicit distinct-prime covariance bound.
  Finite dyadic aggregation is the remaining boundary.
  `BadIntervalLargePrimeAggregation` now carries out the exact finite
  anti-sieve partition: ordinary single conductors and distinct-prime pairs
  receive the improved bounds, exceptional terms receive supplied crude
  majorants, and the result is inserted into the diagonal variance reduction.
  The remaining boundary is analytic cardinality and source-scale summation.
  `BadIntervalLargePrimeExceptionalPartition` resolves that pair predicate:
  the only nontrivial divisors of `pp'` are `p`, `p'`, and `pp'`, so every bad
  pair is covered by one of the two exceptional-prime unions or the existing
  common-factor exceptional-partner union. Its union over the 1000 coordinate
  scales has exact sum-cardinality and factor-1000 bounds.
  `BadIntervalLargePrimeBlockSum` then establishes the exact dyadic
  first-moment consumer. It proves the anti-sieve range equals `[R,2R)`,
  bounds `1/φ(p)` by `2/R`, derives the eventual PNT main sum `4/log R`, and
  keeps the uniform improved error and exceptional-cardinality/crude product
  visible in the complete shift-prime block estimate.
  `BadIntervalLargePrimeCovarianceBlockSum` supplies the parallel exact
  two-band covariance consumer: the complete ordered distinct-prime sum has
  literal multiplicity `(H-1)^2`, with the improved contribution charged to
  the full product of band cardinalities and the exceptional contribution to
  the exceptional ordered-pair cardinality times a supplied crude joint
  bound. Burgess cardinality insertion and dyadic scale summation remain.
  `BadIntervalLargePrimeExceptionalPairCard` then reduces that exact pair
  cardinality to exceptional first endpoints, exceptional second endpoints,
  and common-factor exceptional partners, with a real-valued interface ready
  for the Burgess estimates. `BadIntervalLargePrimeErrorNormalize` and
  `BadIntervalLargePrimeErrorSource` expose all three coordinate error
  aggregates and, from `P_j=z^(1+o(1))` plus PNT, give explicit uniform source
  envelopes for the one-prime, joint, and covariance errors.
  `BadIntervalLargePrimeErrorPower` absorbs the fixed logarithmic powers and
  converts those envelopes, and the literal errors themselves, to the source
  forms `3R^-1.001` and explicit-constant
  `R^-1.001 S^-1` joint/covariance bounds for ordered source-range selectors.
  `BadIntervalLargePrimeAdaptiveExceptional` corrects the endpoint-count
  quantifiers across the full modulus range: the threshold
  `max(P_j^-0.008,R^-0.01)` stays inside the uniformly bounded exceptional
  squared moment and gives the required Burgess-conditional `O(R^0.02)`
  union over all 1000 ordinary coordinates. The exact cofactor-family moment
  identity and its pointwise-uniform form give the analogous
  Burgess-conditional `O(S^0.02)` product-partner count uniformly in the fixed
  prime. `BadIntervalLargePrimeAdaptiveError` now consumes adaptive
  emptiness in the actual character expansions. Its one-prime error differs
  from the fixed error by only `1000R^-10`, and its adaptive joint and
  covariance errors retain explicit `R^-1.001 S^-1` bounds on ordered source
  bands. `BadIntervalLargePrimeAdaptivePartition` handles the subtler mixed
  product fibers without strengthening the exceptional set: conductor `p`
  uses scale `R`, while `p'` and `pp'` use scale `S`. The two endpoint sets
  and adaptive partner set cover failure of this exact predicate, and the
  mixed product moment and literal joint-probability bound compile; its joint
  and covariance errors have the ordered `R^-1.001 S^-1` source power.
  `BadIntervalLargePrimeAdaptiveBlockSum` inserts these exact sets and errors
  into both finite consumers. The adaptive exceptional-pair cardinality is
  reduced to its two endpoint families and partner fibers, the one-band sum
  retains its `(H-1)` multiplicity, and the two-band covariance sum retains
  `(H-1)^2`. `BadIntervalLargePrimeAdaptiveSource` then inserts the adaptive
  Burgess endpoint/partner estimates and the mixed improved source powers into
  both complete blocks. It gives the exceptional pair count the source shape
  `R^0.02·#band(S)+#band(R)·S^0.02`.
  `BadIntervalLargePrimeAdaptiveGeometry` adds the source-faithful fixed
  margin `R,S≤z^1.01`, proves admissibility of the common conductor interval
  `(R-1,2S-1]` and the stronger partner square-root range, and proves crude
  bounds simultaneously over every prime or prime pair in the complete
  bands. `BadIntervalLargePrimeAdaptiveComplete` inserts those facts into
  both Burgess consumers. Primes dividing `m'` are now proved to have zero
  probability and covariance, removing the former whole-band coprimality
  assumption. `BadIntervalLargePrimeDyadicScales` gives a disjoint exact
  dyadic decomposition of the literal source cutoff and a logarithmic scale
  count. `BadIntervalLargePrimeAdaptiveUniform` chooses one Burgess constant
  for all retained scales, sums the first-moment and covariance blocks, and
  proves the literal source bounds `mean ≤ 2000000 H` and
  `variance ≤ 2000001 H`, conditional on the explicit Burgess theorem.
  `BadIntervalCharacterExpansion` now applies exact normalized
Dirichlet-character orthogonality to such a fiber, integrates the identity,
factors every tuple-character expectation by coordinate independence,
identifies the coordinate expectations with normalized dyadic prime-character
averages, discards the residual and squared-coordinate factors at cost one,
and proves the source weak AM--GM reduction to the all-character sum of
1000th powers. It then bounds the reciprocal totient by the explicit source
factor `2^50/lcm`, inserts every fiber estimate into the ordered fiftieth
moment, reorders the resulting tuple/character/coordinate sums, and obtains
one tail coordinate controlling the complete moment with the exact factor
`1000`. `PrimeCharacterSums` defines Tao's normalized sum `s_Z(χ)` and exact
exceptional threshold `Z^(-1/125)`, proves its 1000th power is `Z^(-8)`, and
splits primitive nonprincipal characters exactly. The unexceptional moment is
at most `φ(q)Z^(-8)`, while every exceptional 1000th power is reduced to its
square. Primes above the small cutoff are proved coprime to the tuple lcm, so
ambient character sums equal their primitive counterparts exactly. The
principal term is `1`, and all other characters are regrouped by their exact
positive conductor, yielding a divisor sum of exceptional squared moments
plus `φ(d)Z^(-8)`. This bound is inserted into every ordered tuple term and,
after the exact factor-1000 pigeonhole, into the complete fiftieth moment.
`SmallPrimeMertens` now replaces the tuple lcm by the exact product of its
distinct prime support, groups the 50 logarithms by positive multiplicity,
and separates one `log p/p` factor per support prime from the repeated
logarithms. It proves the exact repeated exponent `50-#support`, applies the
existing explicit weighted-prime estimate `≤ log 4 * (2 + log Y)`, and bounds
every fixed-prime shift fiber by `H^50`, including a generic fiberwise sum
reduction. Exact support regrouping, a uniform `50^50` support-fiber bound, and
an elementary-symmetric inequality now sum all ordered-prime equality patterns,
giving an explicit `H^50 O(log(cutoff)^50)` coefficient bound. The conductor
expression is split into principal, exceptional-square, and totient-error
parts. The principal and totient-error parts are closed, the latter using
`∑_{d∣q}φ(d)=q` and Chebyshev theta. `ExceptionalCharacterBHM` proves the
finite weighted Bombieri--Halász--Montgomery inequality (Lemma 5.3), including
Hermitian row-only reduction, exact prime-indicator pairing and energy, the
diagonal-plus-`J-1`-off-diagonal Gram-row estimate, exact normalization to
`s_Z`, and the Markov inequality `J Z^(-2/125) ≤ ∑|s_Z|²`. The remaining small-prime
work is the Burgess and fundamental-lemma input to Lemma 5.1 and its
application to the isolated exceptional sum.
`FundamentalSieveWeights` now formalizes the Lemma 5.4 divisor-sum weight,
proves its exact value one on dyadic primes above the sieve level, its exact
floor-weighted finite mass expansion, and the elementary coefficient `ℓ¹`
bound. The floor replacement now has the exact error bound
`|Σν-XΣλ_d/d|≤R`, with a direct theorem transferring any main-mass bound to
`Σν≤XB+R`. The remaining Lemma 5.4 obligation is the coefficient construction
with squarefree support, nonnegativity, and its `O(1/log R)` estimate.
As a proved alternative, `SelbergPrimeWeights` instantiates the frozen Selberg
sieve at density `1/d`. The resulting real coefficients have level/primorial
support and `λ₁=1`; their divisor weight is globally nonnegative and one on
primes above the level. The exact compiled estimate is
`Σ_{n≤X}ν(n)≤2X/log R+R(1+log R)^3`. This is adequate for Tao's later power
separation, while the source-exact `{−1,0,1}` Rosser clause remains open.
`ExceptionalCharacterSelberg` now connects this weight to the normalized BHM
estimate without an intermediate analytic contract: zero removal, divisor
expansion, exact `n=md` prefix reindexing, multiplicative divisor extraction,
and the diagonal bound are proved. The remaining hypothesis is precisely the
unshifted Burgess prefix estimate for each distinct-character product.
`ExceptionalCharacterFamilies` makes that product source-exact. It packages
the primitive `q₁q₂` family, proves the pair lcm is squarefree and bounded by
`Z^3.09`, and proves globally (including nonunit inputs) that
`χ_j(n)conj(χ_k(n))` is the value of one quotient Dirichlet character.
`ExceptionalCharacterBurgess` sharpens the terminal interface to exactly the
sieve prefixes `⌊(2Z-1)/d⌋` and records the source-shaped explicit cubefree
Burgess target with saving `0.0163`, a fixed lower cutoff, and range
`q≤H^3.1`. It also defines cube-free literally, proves the squarefree consumer
periods qualify, and encodes the cited `r=7` estimate as
`A H^(6/7)q^(2/49+ε')`. With `ε'=1/2000000`, exact exponent arithmetic proves
that estimate implies the decimal target. It also proves an exact
primitive-to-imprimitive bridge: Möbius inversion rewrites every
changed-level prefix as a divisor sum of primitive prefixes, and the proved
divisor-epsilon estimate absorbs this finite loss using half of `ε'`.
Accordingly the remaining analytic target is only the primitive cube-free
estimate at `ε'=1/4000000`. The 1962 prime-modulus precursor is pinned and
hashed with Lemmas 2--4 proof locators. Exact periodicity now narrows this
target further: complete periods cancel, every prefix is its `H % q` prefix,
and `|χ|≤1` gives the trivial estimate. The analytic proof is required only
for `q^(2/7+7ε')<H<q`, a range proved equivalent to the factor-shaped
condition `q^(2/49+ε')<H^(1/7)`. The essential 1963 composite source
remains unpinned. The PDF and TeX source of the explicit modern cube-free
treatment arXiv `2511.17778v2` are pinned separately as auxiliary proof
architecture, with locators for its shifted-moment theorem, complete
Weil-type lemma, and gcd-tuple bounds. `BurgessMoment` now proves the exact
finite `2r`-moment expansion into complete quotient-character correlations,
the diagonal/nondegenerate split, and the injective coding estimate
`#degenerate≤r^(2r)B^r`. It derives the standard
`r^(2r)B^r q+B^(2r)W` moment bound and its literal `r=7` fourteenth-moment
specialization. It now also defines the source's exact
`A_j=∏_{i≠j}(b_i-b_j)`: finite fiber summation proves every nondegenerate tuple
has a singleton shift and hence a nonzero `A_j`. The relaxed
`∑_{A_j≠0}gcd(|A_j|,q)` weight and `(4r)^ω(q)√q` factor expose a literal
proposition-valued composite Weil boundary, which feeds both the general and
`r=7` moments. The gcd-weight sum is now proved: counting divisor multiples,
splitting around a fixed shift, and factorizing the independent coordinates
gives `∑_uv weight≤2rB(2Bτ(q))^(2r-1)`, with checked general and `r=7`
moment consumers. The fixed-base prime-factor and divisor-epsilon estimates
then absorb `28^ω(q)τ(q)^13`, proving for every `ε>0` that the composite Weil
predicate implies
`moment≤7^14B^7q+C_εB^14q^(1/2+ε)` for some positive `C_ε`. Proving the
composite Weil boundary remains. `BurgessWeilCRT` now proves its exact
multiplicative layer: canonical characters on coprime factors multiply back
to the global character, the complete quotient correlation factors exactly,
and both `(4r)^ω(q)√q` and a fixed `gcd(|A_j|,q)` contribution multiply. Local
bounds sharing the same coefficient witness therefore assemble into the
relaxed global gcd-weight bound. The changed-level product identity also
shows that primitivity descends to each local character: any proper local
conductor would induce a proper global factorization, contradicting the
global conductor equality after cancellation. The remaining pieces are
iteration over cube-free moduli and the prime and prime-square Weil estimates.
`BurgessWeilIteration` now closes the former: every nontrivial cube-free
modulus splits as `p^k n` with `k=1` or `2`, coprime factors, and `n<q`.
Strong induction preserves one fixed nonzero `A_j` through all CRT factors,
and the relaxed-weight insertion gives the complete composite predicate from
only the primitive local estimates modulo `p` and `p^2`. Those local estimates
are now the sole remaining complete-Weil obligation. Their coefficient
dichotomy is also compiled: if `p ∣ |A_j|`, the trivial modulus bound and the
gcd weight prove the required estimate at both levels. The nontrivial
boundary splits into independent primitive prime and prime-square predicates
under `gcd(|A_j|,p)=1`; a checked theorem recombines them all the way to the
composite predicate.
`BurgessWeilPrimeSquare` closes the prime-square predicate by a literal finite
stationary-phase calculation. It decomposes every class modulo `p^2`
uniquely as `a+pt`, proves singular fibers vanish, and constructs the
nontrivial additive character obtained by restricting a primitive character
to `1+pt`. Exact first-order product identities identify each nonsingular
fiber with that additive character at frequency `F'/F-G'/G`, hence give
nonstationary cancellation. Coprimality of the selected `A_j` proves the
stationary polynomial `F'G-FG'` nonzero at its tagged simple root; its at most
`2r` roots give the desired `4rp` bound. The prime local Weil bound is now the
only remaining complete-sum input.
`BurgessWeilPrime` now states that input in its final normalized form. The
prime Burgess correlation is exactly a complete nontrivial
multiplicative-character sum for a quotient of two tagged products of linear
factors. Coprimality of the chosen `A_j` forces one tagged root to be unique
modulo `p`; a checked bridge shows that the general `4r√p` bound for this sum
implies the primitive prime predicate and then the complete cube-free
composite Weil predicate. This normalized finite-field Weil bound remains
open.
`BurgessWeilPrimePolynomial` further verifies the usual non-power condition.
It clears the inverse character with exponent `orderOf χ-1`, proves exact
equality with a polynomial character sum, and computes the unique tagged
root multiplicity as `1` or `orderOf χ-1`. The resulting split polynomial is
therefore not an order-th power and has at most `2r` distinct roots. A checked
bridge now reduces the whole Burgess boundary to the standard
split-polynomial Weil estimate `TaoPrimeSplitPolynomialWeilBound`.
`BurgessWeilPrimeLowRoots` proves that estimate for one and two distinct
roots. The one-root sum is zero, while an affine change of variables identifies
the two-root sum with a Jacobi sum of norm at most `√p`. A checked bridge now
restricts the sole remaining prime input to
`TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore`.
`BurgessWeilPrimeActiveRoots` sharpens that boundary by deleting roots whose
multiplicity is divisible by the character order. The deletion is exact away
from those roots, and their zero-locus correction is at most their cardinality,
which the existing target absorbs. Thus only
`TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore` remains: the case of
at least three multiplicities nonzero modulo `orderOf χ`.
`BurgessWeilPrimeThreeRoots` closes exactly three active roots for the cleared
Burgess polynomial. The polynomial has exact degree `r * orderOf χ`, so its
active multiplicity sum is divisible by the character order. A verified
fractional-linear change sends one root to infinity and leaves a two-root
Jacobi sum with one deleted point. Its `√p+1` bound, plus all inactive-root
corrections, is absorbed by the existing allowance. Hence the actual open
prime input is `TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore`.
`BurgessWeilPrimeLargeCharacteristic` then proves the trivial bound `p` and
shows it already implies `2D√p` when `p ≤ 4D²`. Thus the remaining
four-active-root input may additionally assume `4D² < p`.
`BurgessWeilPrimeFourRoots` gives the exact four-root normalization. A
fractional-linear permutation sends one active root to infinity; degree
divisibility cancels the common denominator character and leaves a canonical
three-point hypergeometric sum with one deleted value. Its checked lift shows
that a `2√p` canonical estimate proves the full exactly-four-active-root
polynomial target. The generic large-characteristic residual now starts at
five active roots; the separate canonical hypergeometric estimate remains
analytic input.
`BurgessWeilPrimeSourceResidual` removes the last arbitrary-polynomial
strength from this production route. The remaining higher-root estimate is
stated only for `primeLinearOrderPolynomial p r χ b`, the literal cleared
Burgess polynomial. Its bridge handles every lower-root and small-
characteristic branch internally, requires the canonical hypergeometric
estimate only for `p > 64`, and still proves the complete cube-free Weil
predicate.
The canonical input is additionally reduced to three powers of the one
ambient character, with each exponent normalized below `orderOf χ` by exact
`pow_mod_orderOf` identities. Thus no independent character triples or
unbounded multiplicity exponents remain in the production assumption.
An exact scaling reindexing then sends the finite marked points from
`(0,λ,μ)` to Legendre form `(0,1,t)`, extracting only a character constant of
norm at most one. The four-root input therefore has a single geometric
parameter `t ≠ 0,1`.
`ExceptionalCharacterScales`
selects `R=⌊Z^0.0001⌋` and proves that
all those prefixes eventually exceed any fixed cutoff and satisfy the Burgess
range uniformly; Bertrand supplies prime-band nonemptiness. Thus a proof of
the explicit Burgess target feeds the finite normalized family estimate with
no residual scale hypotheses. `ExceptionalCharacterNormalization` identifies
the exact band cardinality with `π′(2Z)-π′(Z)`, proves it is asymptotic to
`Z/log Z`, and obtains the eventual lower bound `Z/(2 log Z)`.
`ExceptionalCharacterAbsorption` proves both Selberg diagonal terms are
`O(Z/log Z)` and, under `J≤A Z^(2/125)`, turns the exact `0.0002` exponent
margin into an `o(Z/log Z)` off-diagonal bound. Its resulting moment constant
is independent of `A`, so a finite truncation at `⌊A Z^(2/125)⌋` executes
Tao's self-improving argument. Conditional only on explicit Burgess, the final
theorem gives both `J≪Z^(2/125)` and a uniformly bounded exceptional second
moment. The analytic Burgess proof is the remaining Lemma 5.1 obligation.
`ExceptionalCharacterFixedLevel` takes `q₂=1` to transport that result to the
literal `taoExceptionalPrimitiveCharacters q Z` finsets appearing in the
conductor reduction. Cardinality and the squared sum are preserved exactly,
and the source's stronger `O(λ⁻²)` tail conclusion is compiled as well.
`ExceptionalCharacterAggregate` removes the remaining fixed-conductor
restriction. Equality of two primitive lifts at their lcm is proved to force
equality of their conductors and characters, so every finite collection is
automatically separated. A dependent sigma family over any admissible finite
conductor set preserves both the total cardinality and the complete double
squared-moment sum exactly. Consequently one Burgess-conditional Lemma 5.1
application uniformly bounds the union over the entire conductor set, which
is the family shape required by the exceptional divisor sum in Section 6.
`SmallPrimeExceptionalConductors` now constructs that literal Section 6
conductor set as the union of the nontrivial divisors of every tuple modulus.
The tuple lcm and all its divisors are squarefree, and every conductor is at
most `taoSmallAntiSievePrimeCutoff x ^ 50`. The exact rounded comparison
`cutoff^50<⌊z^(9/10)⌋` is proved eventually; hence every character scale
above the source lower distinguished-prime scale satisfies the Lemma 5.1
square-root range. Applying the aggregate theorem once to the maximal finite
admissible conductor universe gives a single eventual constant for every
admissible subset and all 1001 selectors. Exact divisor-set inclusion and the
completed logarithmic-lcm Mertens bound absorb the literal exceptional sum
into a fixed multiple of the principal majorant. Since
`P_j⁻⁸ cutoff⁵⁰≤1`, the explicit totient error is absorbed into the same
principal majorant. The resulting theorem bounds the entire source-facing
small-prime fiftieth moment by a fixed elementary majorant, conditional only
on Burgess.
`BadIntervalProbabilityNormalization` and `BadIntervalTypicalAntiSieve` turn
the completed small- and large-prime moments into the literal source
Proposition 6.6 estimate. Markov, Chebyshev, and the deterministic logarithmic
partition give `Pr(typical)≤B(8log₂(x))^50/(Hlog(z)^2)` conditional on Burgess.
`BadIntervalProbabilityUniform` strengthens this to one constant eventually
simultaneous in every positive admissible `H` and every remainder `m'`, proves
the exact finite probability/cardinality identity for the typical support, and
exports the resulting tuple-count bound. `BadIntervalTypicalCounting` performs
the exact smooth-remainder sum, restores its `Psi` factor, and sums all dyadic
lengths with geometric cost `2`. Its evaluation image lies in
`B¹∩[1,2x]`, and the full fixed-prime-scale count is reduced to a uniform
evaluation-fiber bound times `badOneTermCount (2x)`.
`BadIntervalTypicalScales`, `BadIntervalTypicalEnlargement`,
`BadIntervalTypicalMultiplicity`, and `BadIntervalTypicalGlobal` now assemble
every ordered 1001-coordinate scale choice, implement the source's enlarged
bands, and prove one global representation-fiber bound `1000^1000` into the
one-term bad set at a fixed absolute dilation. PNT comparison of the original
and enlarged bands costs `8^1001`; `BadIntervalTypicalAssembly` combines this
with the uniform Proposition 6.6 estimate and proves that its explicit
assembly factor tends to zero. Consequently the complete global typical-tuple
count is little-o of the dilated `badOneTermCount`, conditional on Burgess.
`BadIntervalTypicalWeighted` upgrades this to the length-weighted count needed
for interval unions: the factor `2^r` cancels Proposition 6.6's `1/2^r`, the
number of retained dyadic lengths is at most `50 iteratedLog x`, and the new
weighted assembly factor still tends to zero. `BadIntervalTypicalUnion` then
chooses a canonical prime, cofactor, and 1000-prime anatomy for every forward
typical interval whose left endpoint `N+1` is the tuple product. The reflected
modules prove the symmetric `v-l` moment and source mean/variance estimates,
normalize them to the same uniform tuple-support bound, assemble the backward
length-weighted family, and construct an injective right-endpoint code with
tuple start `N+H`. The exact orientation split therefore proves that the full
actual typical union is little-o of the same dilated `badOneTermCount`,
conditional on Burgess, and the quantitative assembly retains an explicit
fixed logarithmic saving. `BadIntervalRecombination` combines this with the
Proposition 6.5 slow diagonal and applies the exact factor-`30` maximal
transfer. Its scale-local form uses the proved eventual admissible-scale
large-prime theorem, so conditional on explicit Burgess and Lemma 1.6(ii), the
resulting local nontrivial dyadic-window count has a
`1/log(x)^(1-epsilon)` saving relative to `badOneTermCount x`. An exact finite
power-of-two cover also bounds the global nontrivial bad count by the sum of
these local window counts. `BadIntervalDyadicSummation` isolates the exact
adjacent ratio `B¹(2^r)/B¹(2^(r+1))->1/2`; conditional on it, the logarithmic
weights contract geometrically, the finite prefix is absorbed, the top
endpoint is compared through `[x,2x]`, and the exact
`TaoTheorem17Conclusion` follows. `BadOneTermRegularVariation` now proves that
adjacent ratio from `TaoCriticalSmoothDilationLimitConclusion`: a slowly
widening central prime packet has complementary mass `o(B¹(x))`, and uniform
dilation by `1/2` gives `B¹(x/2)/B¹(x)->1/2`. The completed saddle-main-term
 stability reduces the dilation limit to
 `TaoCriticalSmoothSaddleAsymptoticConclusion`. The scale-local refinement now
 invokes `eventually_admissibleSylvesterSchurAtScale`, obtained from the common
 start cutoff, throughout maximal transfer and dyadic summation. Thus
 `taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess` needs only
 that sharp saddle asymptotic and analytic Burgess; those two inputs remain
 open. The same dilation limit now
also proves Lemma 1.6(ii), so that clause is no longer a separate input; no
main theorem is claimed.
For condition (i), the finite large-sieve
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
`BadIntervalSmoothBranches` handles the easy small-`p₀` smooth branch. It
proves that the actual normalized interval union with `p₀≤y` is contained in
the `y`-smooth naturals up to `2x`, constructs the exact floored cutoff
`⌊z(x)^β⌋`, and proves that this cutoff is a critical smooth-number regime.
Consequently its union has the uniform bound
`2x/z(x)^(1/β-ε)` for fixed `β,ε>0`; at `β=2/5`, `ε=1/10` this gives the
explicit acceptable saving `2x/z(x)^(12/5)`.
For the later prime bands, the same module also builds the two exact
square-endpoint smooth-cofactor covers and proves the fixed-fiber reduction
`#U(p₀,H)≤2H Ψ(⌊2x/p₀²⌋,p₀)`. It assembles the actual short union over
dyadic lengths and a 60-cell exponent grid. On the concrete large-smooth
range `z(2x)^(6/5)<p₀≤z(2x)^3`, the grid retains a fixed exponent margin;
after absorbing the full logarithmic length cost and fixed dilation, the
audited source-scale conclusion is `#union≤x/z(x)^(2+1/800)`.
Moreover `log z(2x)/log z(x)→1` is proved exactly, and the literal source
range `z(x)^(5/4)<p₀≤⌈z(x)^3⌉` is eventually embedded into the
60-cell range, giving the same bound for the source-defined actual union.
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

## Prime-equidistribution release 2.57

`BurgessAmplification` begins the previously missing passage from the complete
fourteenth moment to character prefixes. It proves exact interval splitting
and shift differencing, the sharp `2K` boundary error, affine reindexing by a
residue coprime to the conductor, preservation of the sum norm under that
reindexing, and the finite-sum exchange which produces `burgessShiftSum` from
the additive Burgess average. The coprime multiplier-pair set and its residue
multiplicity are explicit; their first moment and the exact weighted
regrouping of the complete affine average are proved. No new analytic
hypothesis is introduced.

The remaining amplification work is the residue-multiplicity collision
estimate, Hölder step against the fourteenth moment, and the final choice and
optimization of the Burgess parameters. Analytic Burgess
and hence Theorems 1.7--1.10 remain unproved unconditionally.

## Prime-equidistribution release 2.58

The residue multiplicity's second moment is now identified exactly with an
ordered collision count. Unit cancellation turns every such collision into
the cross-multiplied congruence used in the pinned explicit Burgess proof.
The source-shaped three-factor Hölder estimate is also complete: its factors
are the proved first moment, this collision cardinality, and the existing
complete `2r` character moment. The same theorem is exposed directly for the
coprime affine average.

What remains in this segment is the arithmetic upper bound on collision
fibers, followed by the induction/error term and parameter optimization.

## Prime-equidistribution release 2.59

The fixed-multiplier arithmetic collision estimate is now proved. Under
`2*A*H <= q`, congruence collisions cannot wrap modulo `q`; after division by
`gcd(a,c)`, distinct points in a fiber are spaced by the reduced multipliers.
Consequently each fiber has cardinality at most
`H / (max a c / gcd a c) + 1`. The complete collision set is decomposed
exactly by its multiplier pair and bounded by the corresponding finite
`max/gcd` sum.

The remaining elementary amplification step is to estimate that finite gcd
sum in the source's divisor-sum form. The Burgess induction, boundary-error
absorption, and `r = 7` parameter optimization then remain; analytic Burgess
and Theorems 1.7--1.10 are still not unconditional results of this project.

## Prime-equidistribution release 2.60

The remaining collision divisor sum is now bounded. A fixed upper multiplier
`c` contributes at most `H*tau(c)`; the exact summatory-divisor identity and a
harmonic comparison then give `sum_{c<=A} tau(c) <= A*harmonic(A)` over the
reals. Thus the complete residue-collision count has the required
diagonal-plus-`O(A*H*log A)` form, with the explicit term
`2*H*A*harmonic(A)`.

The next frontier is no longer collision counting. It is the Burgess
induction that absorbs the `2ab` translation boundary and combines this
second moment with the compiled Hölder and fourteenth-moment estimates,
followed by the concrete `r = 7` parameter optimization.

## Prime-equidistribution release 2.61

The exact pre-Hölder Burgess recursion now compiles. A real-valued residue-
multiplicity regrouping bounds the sum of the norms of the affine `b`-averages.
An arbitrary function `E` can then majorize both shorter boundary intervals,
and the final theorem gives
`#A*B*|S(N,H)| <= sum_x v_A(x)|W_B(x)| + 2*sum_{a,b} E(ab)`
under `A*B <= H`, matching equation (28) of the pinned explicit proof.

What remains is to insert the inductive Burgess power into `E`, estimate its
finite boundary sum, combine Hölder with the collision and complete-moment
bounds, and perform the `r = 7` parameter optimization.

## Prime-equidistribution release 2.62

The inductive power boundary is now inserted into the exact recursion.
Monotonicity collapses the coprime-multiplier sum to its endpoint, and a
finite endpoint estimate gives
`sum_{b<=B} C*(A*b)^alpha*Q <= B*C*(A*B)^alpha*Q` for nonnegative data.
After division by the positive averaging denominator, the compiled normalized
recurrence is
`|S(N,H)| <= M/(#A*B) + 2*C*(A*B)^alpha*Q`.

The remaining main-term package is root extraction from powered Hölder,
followed by the harmonic collision bound, the complete fourteenth moment,
and the exact `r = 7` parameter choice.

## Prime-equidistribution release 2.63

The powered Hölder inequality has now been converted into its usable rooted
form. Monotonicity then inserts both the harmonic collision estimate and the
complete fourteenth-moment bound under the `1/14` power. A single compiled
theorem combines this main term with the normalized power-boundary recursion.

The Burgess amplification frontier is consequently scalar: lower-bound the
coprime multiplier count, select integral `A` and `B`, discharge the no-wrap
and shortening conditions, and absorb the boundary term. The composite Weil
input is still explicit rather than silently assumed.

## Prime-equidistribution release 2.64

The coprime-multiplier denominator now has a quantitative lower bound. Exact
Möbius inversion proves
`A*phi(q)/q - tau(q) <= #{a<=A : (a,q)=1}`, together with the corresponding
affine-pair statement and a half-density corollary once the divisor error is
dominated.

This deliberately uses `tau(q)` rather than Tao's sharper
`2^(omega(q)-1)` error; the project already has the divisor power bounds
needed to absorb that loss. The next task is the concrete integer parameter
selection. The elementary companion inequality `q/phi(q) <= tau(q)` is also
compiled, so `2*tau(q)^2 <= A` alone implies the required half-density
denominator. The remaining estimates concern that rounded condition, the
harmonic factor, and the Burgess range inequalities.

## Prime-equidistribution release 2.65

The Burgess recurrence is now cardinality-free and scalar. Divisor-power
absorption makes `2*tau(q)^2<=A` automatic in the intended lower interval
range, while `A<=H` compresses the collision bracket to
`3*H*A*harmonic(A)`.

The formal parameter choice is `B=floor(q^(1/14))`, `A=H/(K*B)`. Its floor
losses and all current admissibility conditions are compiled, including the
quadratic hypothesis implying `2*A*H<=q`. The remaining Burgess work is the
epsilon absorption/power simplification and the inductive boundary closure;
the composite complete-Weil input remains explicit.

## Prime-equidistribution release 2.66

The first post-parameter exponent calculation is compiled. Harmonic and
reciprocal-totient losses have explicit conductor-power bounds; the complete
moment reduces to `q^(3/2+epsilon)` and hence to
`q^(3/28+epsilon/14)` after the fourteenth root. Exact factorization gives
the combined main factor
`A^(13/14)*H^(13/14)*q^(3/28+epsilon/14+delta/14)`.

What remains is the final substitution of the already rounded `A,B`, which
produces `H^(6/7)*q^(2/49+epsilon)`, followed by strict boundary absorption.

## Prime-equidistribution release 2.67

The rounded substitution is now formalized. The exact quotient and floor
losses yield a normalized parameter factor
`2*K^(1/14)*H^(6/7)/q^(13/196)`, and its combination with the rooted complete
moment produces the target Burgess main exponent
`H^(6/7)*q^(2/49+epsilon/14+delta/14)`.

The next step is to include the reciprocal-totient epsilon loss and package
the total exponent budget, then choose the safety factor so the normalized
inductive boundary is strictly contractive. The composite complete-Weil input
remains explicit.

## Prime-equidistribution release 2.68

The reciprocal-totient loss and final epsilon allocation are now compiled,
giving the rounded main term at exactly
`H^(6/7)*q^(2/49+eta)`. Separately, the exact inequality `K*A*B<=H` turns the
normalized affine error into a contractive term; `K=128` is formally proved
to leave at most one half of the induction majorant.

The next step is recurrence-level assembly of these two estimates. The
complete fourteenth-moment/Weil input remains the genuine analytic hypothesis.

## Prime-equidistribution release 2.69

The rounded Burgess recurrence now closes by strong induction. Both affine
endpoint errors use strictly shorter lengths, the half-boundary is absorbed
by the chosen uniform coefficient, and sublengths below the core threshold
use the trivial estimate. For sufficiently large conductors this proves the
primitive `H^(6/7)*q^(2/49+eta)` estimate throughout the exact quadratic
no-wrap range.

The remaining large-length completion is the Pólya--Vinogradov Fourier
estimate. The source-specific prime complete-Weil residual remains the other
analytic input.

## Prime-equidistribution release 2.70

The Pólya--Vinogradov completion is now formalized. Primitive finite Fourier
inversion and an exact DFT proof of `|tau(chi)|=sqrt(q)` reduce every
`H<q` interval to a geometric kernel whose full frequency norm is at most
`10*(H+q*harmonic(q))`. Consequently
`|S(N,H)|<=10*sqrt(q)*(1+harmonic(q))`.

The harmonic factor is absorbed into `q^eta`. Outside the quadratic
no-wrap range, its failure yields exactly the `q^(45/98)` length power
needed to recover `H^(6/7)*q^(2/49+eta)`. The medium and large branches are
combined, the finitely many small conductors are handled explicitly, and the
primitive all-prefix, all-character cubefree, and decimal Burgess contracts
are exported. They remain conditional only on the source-specific prime
complete-Weil residual.

## Prime-equidistribution release 2.71

`BurgessWeilPrimeKummer.lean` consolidates the remaining prime assumptions
into the sharp classical Kummer statement. For a split polynomial not equal
to `C(c)*Q^(orderOf χ)` with `c≠0`, the required estimate is
`(t-1)*sqrt(p)`, where `t` is the number of distinct roots.

The tagged Burgess root is now proved to exclude this full scalar-power
exception by exact root-multiplicity arithmetic. The sharp statement implies
the existing split-polynomial, prime quotient, composite complete-Weil, and
therefore all-prefix Burgess contracts. The Kummer estimate itself remains
the sole Burgess analytic input.

## Prime-equidistribution release 2.72

`SylvesterSchurSmallLengths.lean` proves the unrestricted large-prime
conclusion for every start at lengths `1<=H<=48`. It combines monotone
binomial-growth propagation from verified small baselines with kernel-checked
finite prime certificates, using the uniform baseline `T=3H` above length ten.

Consequently the finite Sylvester--Schur residual that then fed Theorem 1.7 was
restricted to `H>=49`. The full theorem remains open; this release removes forty-eight
complete rows without introducing a conditional interface.

## Prime-equidistribution release 2.73

`SylvesterSchurEventual.lean` proves one common start cutoff after which the
large-prime conclusion holds for every positive interval length. Large lengths
use the existing all-start tail; the finitely many smaller lengths use their
fixed-length `H^H+1` thresholds.

Because admissible interval starts grow with the ambient dyadic scale,
`eventually_admissibleSylvesterSchurAtScale` supplies exactly the local witness
needed in Theorem 1.7. New scale-local variants carry it through normalized
subintervals, the factor-30 maximal bound, typical/non-typical recombination,
dyadic windows, tail summation, and the finite prefix. The compiled endpoint
`taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess` therefore has
only two open analytic inputs: Burgess and the critical smooth-number saddle
asymptotic. The unrestricted Sylvester--Schur finite rectangle remains open as
an independent theorem, not as a Theorem 1.7 dependency.

## Prime-equidistribution release 2.74

`BurgessWeilPrimeKummer.lean` now gives the exact distinct-root trace normal
form for the remaining prime character sum. It proves both directions of the
exceptional-power criterion for nonzero split polynomials: all root
multiplicities are divisible by `orderOf χ` exactly when the polynomial is a
nonzero scalar multiple of an order-th power. The equivalent endpoint
`TaoPrimeKummerRootProductWeilBound` therefore exposes only the genuine
finite-field trace estimate `(t-1)*sqrt(p)`.

## Prime-equidistribution release 2.75

The sharp Kummer trace estimate is now proved for one and two distinct roots:
character orthogonality gives zero in the first case, and the existing Jacobi
sum theorem gives `sqrt(p)` in the second. The equivalent residual
`TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore` feeds the composite
Burgess chain directly. Only the three-or-more-root finite-field trace bound
remains in this analytic branch.

## Prime-equidistribution release 2.76

The sharp `2*sqrt(p)` Kummer estimate is now proved for every three-root split
polynomial whose degree is divisible by the character order. Active-root
separation reduces both possible cases to the existing Jacobi/projective
identities with at most one deleted-point contribution. The exact equivalent
residual now contains only four-or-more-root traces and degree-nondivisible
three-root traces. Tao's degree-divisible Burgess family therefore has no
remaining three-root case.

## Prime-equidistribution release 2.77

Every degree-nondivisible three-active-root Kummer trace is now translated
exactly to the existing three-point hypergeometric endpoint. Inactive-root
and small-characteristic cases are discharged separately. Hence the full
Kummer theorem follows from precisely the three-point hypergeometric estimate
and a pure four-or-more-root Kummer trace estimate, with a direct bridge to
the complete composite Burgess chain.

## Prime-equidistribution release 2.78

Under the three-point hypergeometric endpoint, the sharp Kummer estimate is
now proved for every degree-divisible four-root polynomial. The two-, three-,
and four-active-root branches use the existing Jacobi and Möbius reductions,
with inactive-point losses absorbed inside `3√p`. The equivalent residual is
five-or-more roots or degree-nondivisible four roots; Tao's degree-divisible
Burgess family therefore starts at five roots.

## Prime-equidistribution release 2.79

Degree-nondivisible four-active-root traces now translate exactly to a new
four-point hypergeometric endpoint with sharp allowance `3√p`. All other
four-root active/inactive splits follow from the established lower-point
bounds and deleted-point accounting. Assuming the three- and four-point
endpoints, the full Kummer theorem is therefore equivalent to a pure
five-or-more-root residual, with a direct composite Burgess bridge.

## Prime-equidistribution release 2.80

Five local characters with trivial product now admit an exact Möbius
reduction to the four-point endpoint plus one deleted value. This proves the
sharp `4√p` Kummer bound for every degree-divisible five-root polynomial.
The generic residual becomes six-or-more roots or degree-nondivisible five
roots, while the exact cleared Burgess polynomial now has a source-specific
residual beginning at six active roots.

## Prime-equidistribution release 2.81

The four-point input on the exact Burgess path is now restricted to powers of
one character, exponents reduced modulo the character order, primes above
`64`, and the two cross-ratio parameters in the normal form `0,1,t,u`.
Power-specific five-root and split-polynomial bridges feed this reduced input
directly into the existing six-active-root source residual. The remaining
finite-field work is therefore two explicit reduced hypergeometric estimates
and the source-specific trace bound beginning at six active roots.

## Prime-equidistribution release 2.82

Six degree-balanced active roots now Möbius-reduce exactly to a five-point
power-character trace and one deleted value. Exponent reduction and scaling
normalize that trace to `0,1,t,u,v` above `64`. The exact cleared Burgess
residual consequently begins at seven active roots and is connected directly
to the composite endpoint, conditional on the three reduced lower-point
trace estimates.

## Prime-equidistribution release 2.83

The complete-Weil hypothesis used by the final Burgess proof is now literally
fixed at `r=7`. The specialization runs through the fourteenth moment,
amplification, rounded induction, Pólya--Vinogradov, and the explicit
cubefree endpoint. A separate fixed-order prime/prime-square CRT induction
and prime quotient bridge mean that the exact seven-active-root source
residual is likewise stated only for `Fin 7`; the all-orders interface is no
longer an assumption on the production path.

## Prime-equidistribution release 2.84

Seven degree-balanced active roots now Möbius-reduce to a six-point
power-character trace and one deleted value. The six finite exponents are
reduced modulo the source character order and scaling normalizes the marked
points to `0,1,t,u,v,w` above `64`. The exact fixed-`r=7` Burgess residual
therefore begins at eight active roots, conditional on four reduced
lower-point trace endpoints.

## Prime-equidistribution release 2.85

The fixed-order source residual is now restricted to the exact finite window
of eight through fourteen active roots. The upper bound follows internally
from the `2r` distinct-root bound for the cleared polynomial at `r=7`, and the
window has direct fixed prime-quotient and composite bridges. No impossible
cardinality above fourteen remains in the Burgess assumption.

## Prime-equidistribution release 2.86

Eight degree-balanced active roots now Möbius-reduce to a seven-point
power-character trace plus one deleted projective value. The finite trace is
normalized to powers of one character with exponents below its order and to
the marked points `0,1,t,u,v,w,z` for `p > 64`. The exact fixed-order source
residual therefore occupies only the six cardinalities `9..14`.

## Prime-equidistribution release 2.87

Nine degree-balanced active roots now Möbius-reduce to an eight-point
power-character trace plus one deleted value. Exponents are reduced modulo
the ambient character order and scaling gives the six-parameter marked-point
form `0,1,t,u,v,w,z,r₀` for `p > 64`. The literal source residual is now the
five-cardinality window `10..14`.

## Prime-equidistribution release 2.88

Ten degree-balanced active roots now Möbius-reduce to a nine-point
power-character trace plus one deleted value. Exponents are reduced modulo
the ambient character order and scaling gives the seven-parameter marked-point
form `0,1,t,u,v,w,z,r₀,s₀` for `p > 64`. The literal source residual is now the
four-cardinality window `11..14`.

## Prime-equidistribution release 2.89

Eleven degree-balanced active roots now Möbius-reduce to a ten-point
power-character trace plus one deleted projective value. Exponents are reduced
modulo the ambient character order and scaling gives the eight-parameter
marked-point form `0,1,t,u,v,w,z,r₀,s₀,a₀` for `p > 64`. The resulting
`9*sqrt(p)+1` estimate closes exact cardinality eleven, leaving the literal
source residual on only the three-cardinality window `12..14`.

## Prime-equidistribution release 2.90

Twelve degree-balanced active roots now Möbius-reduce to an eleven-point
power-character trace plus one deleted projective value. Exponents are reduced
modulo the ambient character order and scaling gives the nine-parameter
marked-point form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀` for `p > 64`. The resulting
`10*sqrt(p)+1` estimate closes exact cardinality twelve, leaving the literal
source residual on only the two-cardinality window `13..14`.

## Prime-equidistribution release 2.91

Thirteen degree-balanced active roots now Möbius-reduce to a twelve-point
power-character trace plus one deleted projective value. Exponents are reduced
modulo the ambient character order and scaling gives the ten-parameter
marked-point form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀` for `p > 64`. The resulting
`11*sqrt(p)+1` estimate closes exact cardinality thirteen, leaving the literal
fixed-`r=7` source residual only at exact active-root cardinality fourteen.

## Prime-equidistribution release 2.92

Fourteen degree-balanced active roots now Möbius-reduce to a thirteen-point
power-character trace plus one deleted projective value. Exponents are reduced
modulo the ambient character order and scaling gives the eleven-parameter
marked-point form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀` for `p > 64`. The
resulting `12*sqrt(p)+1` estimate closes exact cardinality fourteen.

Because the literal `r=7` source polynomial has at most fourteen distinct
roots, the exact-card bridge eliminates the fixed-order source residual. The
production prime quotient and cube-free composite bounds now follow from the
reduced trace endpoints through thirteen points alone. Those analytic
endpoints remain hypotheses, so no unconditional Burgess or Theorem 1.7 claim
is made.

## Prime-equidistribution release 2.93

`ErdosSelfridgeSource` now transcribes the stronger prime-multiplicity
statement of Erdős--Selfridge Theorem 2. The local half-open product is proved
equal to the source interval `[N+1,N+H]`; the least prime `p^(H)` is constructed
from Euclid's theorem; and Bertrand proves `p^(H) <= N+H` in the residual
range `H<N`. Specializing the source exponent to two then turns a hypothetical
square into even valuation at every prime, contradicting Theorem 2's witness.

This gives audited bridges from the prime-multiplicity contract to the exact
square proposition and onward to the existing Theorem 1.10 endpoint, including
the direct Theorem 2.5 plus Baker--Harman--Pintz consumer. The pinned
`erdos137` candidate was also checked at its exact commit: its relevant
unconditional interval facts are already subsumed by the local extraction
layer, and it does not prove the Erdős--Selfridge perfect-power theorem. The
new source contract therefore remains an explicit unproved input; Theorem
1.10 is not claimed unconditionally.

## Prime-equidistribution release 2.94

`ErdosSelfridgePowerFree` now formalizes the first contradiction step of the
1975 proof, equation (3). For every positive `m`, the canonical coefficient
reduces each prime valuation modulo `l`, and Lean proves
`m = powerFreePart l m * powerRootPart l m ^ l` together with the strict
valuation bound `v_p(powerFreePart l m) < l`.

Under failure of the source prime-multiplicity conclusion, exact uniqueness of
a multiple for every prime `p >= H` transfers the product valuation back to
its single interval element, including the boundary `p=H`. Consequently every
factor in `[N+1,N+H]` has the source decomposition `a*x^l` with `a`
`l`-power-free and all prime factors of `a` strictly below `H`. The remaining
Erdős--Selfridge proof begins with the source's distinct-product Lemma 1.
