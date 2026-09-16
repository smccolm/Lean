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
4.2. Unrestricted Sylvester--Schur and Hanson's all-length primorial bound now
prove the required Erdős--Selfridge square theorem internally. Thus the direct
Theorem 1.10 bridge has exactly two remaining analytic inputs: Theorem 2.5 and
the Baker--Harman--Pintz theorem.
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
`sylvesterSchurBelow_oneHundredOne`.  An explicit Chebyshev/square-root
argument proves every row `H>=121`; a final kernel certificate closes all
twenty rows `101<=H<121`. Thus unrestricted Sylvester--Schur is proved. The
fixed cutoff and Theorem 2.5 constants are now chosen
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
double-block squared-inner-sum assembly is now complete. The literal source
convolution block is now connected to that estimate as well:
`typeIIProductRestrictedOuterSum` gives its exact product-restricted outer-sum
form, Cauchy--Schwarz feeds the squared inner sums, and bounded product support
is enlarged exactly to the canonical Vaughan block. The actual source beta
coefficient has norm at most one and the gamma coefficient is bounded by
`log(2B)`, so
`eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov`
delivers the conditional estimate for the literal Type II double block.
Finally, `norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks`
reassembles arbitrary block estimates into the full convolution norm. The
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
source-scale form. What remains at this layer is the source regime split and
the asymptotic summation/simplification of all block majorants, together with
the Type I and Fourier assembly. The high-frequency implication is also
formalized exactly:
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

## Prime-equidistribution release 2.95

`ErdosSelfridgeProductSeparation` now proves source equation (2), equation
(4), and the full Lemma 1. A failed prime-multiplicity conclusion, together
with the Sylvester--Schur large-prime witness, first forces `H^l<N`.
Products of distinct equally sized subfamilies of `[N+1,N+H]` are then
separated below exponent `l`.

The stronger rational clause is also internal: after cancelling the gcd of
the proposed numerator and denominator, a sharp lower bound for the gap
between rational `l`-th powers contradicts the interval-product upper gap.
Equation (3) transfers this to the canonical power-free coefficients, proving
both rational-power exclusion and product injectivity for every `1<=r<l`.
The next source obligation is Lemma 2's maximal-valuation deletion and
factorial-divisibility argument; the public Theorem 1.10 status is unchanged.

## Prime-equidistribution release 2.96

`ErdosSelfridgeDeletion` now proves the complete source Lemma 2. For each
prime `p<H`, a position maximizing the `p`-adic valuation of its interval
element is selected. Every retained canonical coefficient is valuation-wise
bounded by the distance from that position, and the product of all nonzero
distances is exactly `m!*(H-1-m)!`, which divides `(H-1)!`.

The possibly repeated choices are padded to an exact deletion set of
cardinality `primeCounting (H-1)`. Lean verifies that the survivor set has
cardinality `H-primeCounting (H-1)` and that its coefficient product divides
`(H-1)!`, precisely equation (9). At exponent two, the discarded valuation
is at most one; this also proves the source square-case divisibility equation
(21). The next Erdős--Selfridge boundary is the large-length square-case
inequality and the finite residual case analysis.

## Prime-equidistribution release 2.97

`ErdosSelfridgeSquareDensity` proves the first exact ingredient of source
equation (22). For every divisor `d` of a block length `L`, Lean counts exactly
`L/d` multiples of `d` in `(N,N+L]`. Inclusion--exclusion at `d=4,9,36`
therefore shows that exactly twelve values in every block of 36 are divisible
by `4` or `9`.

Using the prime-square characterization of squarefreeness, every squarefree
value avoids those twelve positions. Thus at most 24 values in any block of
36 consecutive positive integers are squarefree; the equivalent offset form
for `N+(i+1)`, `i<36`, is also proved and audited. The next source obligation
is to combine this density lemma with distinctness of the squarefree
coefficients to prove the full product lower bound (22), then equation (23)
and the finite residual cases.

## Prime-equidistribution release 2.98

Source equation (22) is now complete in cleared-denominator form. Lean proves
the global count `3*Q(M)≤2*M` for squarefree positive integers once `M≥44`,
using a finite `44≤M<80` sieve check followed by the 36-block recurrence. It
then identifies the first 64 squarefree values exactly, verifies their strict
base product inequality, and proves their increasing enumeration is
pointwise minimal among all 64-element positive squarefree finsets.

Deleting the maximum coefficient and applying the cumulative count propagates
the strict inequality to every cardinality `H≥64`. Finally, source Lemma 1
proves that the canonical coefficients of a counterexample are distinct, so
`powerFreePart_two_equation22_of_failure` gives equation (22) for the actual
Erdős--Selfridge family. Equation (23)'s 2- and 3-adic comparison is now the
next source boundary.

## Prime-equidistribution release 2.99

`ErdosSelfridgeSquareValuations` exposes the exact valuation ledger between
equations (21) and (23). Lean proves that every prime below `H` occurs exactly
once in the source primorial, then cancels the complete 2- and 3-adic content
of equation (21) in a natural-number divisibility theorem.

Combining that sharpened ledger with the canonical equation-(22) theorem
gives `powerFreePart_two_preEquation23_of_failure`, the exact strict integer
inequality immediately preceding the paper's logarithmic estimates. The four
explicit valuation bounds, the displayed real-power form of equation (23),
and its primorial contradiction remain open.

## Prime-equidistribution release 3.00

The Erdős--Selfridge square-case development now proves all four logarithmic
valuation bounds used between equations (22) and (23). Binary and ternary
digit-sum estimates control the factorial valuations, while exact recursive
counts of interval elements with odd `2`-adic or `3`-adic valuation control
the coefficient-product valuations.

The release also cancels `(H-1)!` over `ℝ`, rewrites the remaining natural
powers as real powers, and combines the bounds in
`powerFreePart_two_preEquation23_logarithmic_of_failure`. The numerical
real-power estimate producing `14/3`, the primorial contradiction, and the
finite residual lengths are still not claimed.

## Prime-equidistribution release 3.01

The exact logarithmic inequality is now simplified to the source's displayed
equation (23). `erdosSelfridge_equation23_root_factor_le` supplies a rigorous
slack estimate for the residual cube- and square-root factors, and
`erdosSelfridge_equation23_of_failure` concludes
`(3/2)^H 2^(2H/3) 3^(H/4) < (14/3)H² ∏_{p<H}p`.
The primorial contradiction and finite residual square cases remain open.

## Prime-equidistribution release 3.02

`ErdosSelfridgePrimorial` now closes the asymptotic large-length consequence
of equation (23). It proves `prod_{p<H} p <= 3^H` eventually from the frozen
prime number theorem, rewrites the left side as a power of an effective base
strictly larger than `3`, and absorbs the polynomial factor by standard
polynomial-versus-exponential growth.

Thus `eventually_not_erdosSelfridgePrimeMultiplicityFailureAt_two` excludes
all sufficiently large square-case counterexamples. This release does not
claim the paper's explicit numerical cutoff; making that cutoff effective and
checking the remaining finite lengths are the next Section 3 tasks.

## Prime-equidistribution release 3.03

`ErdosSelfridgeFinite` begins Section 3.2. A general candidate-set theorem
embeds the distinct canonical coefficients into the positive divisors of the
prime product below `H`; exact finite cardinalities close lengths `3` and `5`.

At length `4`, Lean proves that the coefficient set is exactly `1,2,3,6`,
uses its square product in equation (3), and derives the forbidden square
product of four consecutive integers. Thus every square-case failure with
`3 <= H <= 5` is excluded. The next finite source case is `H=6`, including
its exceptional residue class modulo `5`.

## Prime-equidistribution release 3.04

The finite Erdős--Selfridge analysis now includes `H=6`. Exact modular
enumeration proves that, unless `5 | N+1`, five positions have coefficients
supported only on `2` and `3`, contradicting their four possible values.

In the exceptional class, the middle four coefficients exhaust `1,2,3,6`;
their product and equation (3) force a square product of four consecutive
integers. The public combined theorem now excludes every square-case failure
with `3 <= H <= 6`. The remaining uniform finite count begins at `H=7`.

## Prime-equidistribution release 3.05

The finite Erdős--Selfridge analysis now also excludes `H=7`. Among seven
consecutive integers at least five avoid divisibility by `5`; their canonical
squarefree coefficients must be five distinct members of the four-element
set supported on `2` and `3`, an immediate contradiction.

The new public combined theorem covers `3 <= H <= 7`, while retaining the
release-3.04 theorem for downstream compatibility. The next finite source case
is the exceptional residue split at `H=8`.

## Prime-equidistribution release 3.06

The `H=8` source split is complete. An exact reduction to the `35` residue
classes produces five positions avoiding `5` and `7` except when
`7 | N+1` and `5 | N+2`. The ordinary branch is a five-to-four coefficient
pigeonhole argument.

In the exceptional class, the four consecutive middle terms have
coefficients exactly `1,2,3,6`; equation (3) makes their product a square,
contradicting the exact four-consecutive identity. The public finite endpoint
now excludes all square-case failures with `3 <= H <= 8`; the next length is
`H=9`.

## Prime-equidistribution release 3.07

The finite square-case analysis now reaches length thirteen. Exact periodic
counts give five terms avoiding `5,7` in the first nine positions and five
terms avoiding `5,7,11` in the first twelve. Monotonicity carries those counts
through the prime-stable ranges `9 <= H <= 11` and `12 <= H <= 13`.

Lemma 1 makes the corresponding coefficients distinct, while equation (3)
restricts them to the four products `1,2,3,6`. The public combined endpoint
now excludes all square-case failures with `3 <= H <= 13`. The remaining
finite analysis begins at `H=14`.

## Prime-equidistribution release 3.08

A reusable interval-union count now closes lengths fourteen through seventeen.
It bounds the positions divisible by `5,7,11,13`, using exact counts when a
prime divides the interval length, and leaves five distinct coefficients among
the four values `1,2,3,6`.

The public combined endpoint now excludes every square-case failure with
`3 <= H <= 17`. The remaining finite analysis begins at `H=18`.

## Prime-equidistribution release 3.09

Sharp prime-union counts and a generic coefficient-support transfer now close
lengths eighteen through twenty. Five coefficients survive removal of every
prime above three, but all five must be distinct divisors of six. The public
combined endpoint reaches `3 <= H <= 20`; the next range starts at `H=21`.

## Prime-equidistribution release 3.10

The complete finite square-case residual is now closed. A kernel-checked
ceiling sum for every `21 <= H <= 70` leaves nine coefficients supported on
`2,3,5`, which cannot be distinct among the eight divisors of `30`. The public
finite endpoint now excludes every failure with `3 <= H < 71`.

## Prime-equidistribution release 3.11

The exact large-length split is now compiled. Direct kernel arithmetic rules
out every `71 <= H <= 296`, while a rational equation-(23) base bound and
ratio induction prove exponential dominance for every `H >= 297`. The public
square conclusion is connected across all lengths conditional on the one
remaining elementary primorial statement `prod_{p<H} p <= 3^H`.

## Prime-equidistribution release 3.12

`ErdosSelfridgeHanson.lean` proves the remaining primorial statement for every
natural length.  It formalizes Hanson's Sylvester-sequence factorial
coefficient, proves that every prime below the length divides it, and turns a
fixed `2,3,7,43` multinomial into an exact integer entropy estimate.  A
kernel-checked block certificate handles lengths below `1400`; above that
cutoff, exact base and floor-loss inequalities give the induction step.

Consequently `ErdosSelfridgeThreePrimorialConclusion` is now discharged
internally.  The complete Erdős--Selfridge square conclusion is available
conditional only on the independent `SylvesterSchurConclusion` contract.

## Prime-equidistribution release 3.13

`SylvesterSchurFactorialThreshold.lean` sharpens the remaining unrestricted
Sylvester--Schur reduction.  If `r` bounds the number of primes at most `H`,
the exact inequality `H! 2^r < (N+1)^(H-r)` now forces a prime larger than
`H` in the consecutive product.  Retaining `r=pi(H)` gives the start cutoff
`H! 2^pi(H)+1`; replacing `pi(H)` by `H-1` recovers the classical
`H! 2^(H-1)+1` cutoff.

Thus the global Sylvester--Schur contract is reduced to a strictly smaller
finite rectangle than the earlier `H^H+1` construction.  The rectangle is
still open, so no unconditional Sylvester--Schur or main-theorem release is
claimed.

## Prime-equidistribution release 3.14

`SylvesterSchurHundred.lean` extends the unconditional uniform length range
from `H<49` to `H<101`.  For every `49<=H<=100`, kernel computation verifies
the binomial-growth baseline at upper index `3H` and a bounded witness below
that baseline.  Monotonicity then covers every larger start.

The unrestricted Sylvester--Schur residual is consequently confined to the
exact-prime-count factorial rectangle with `H>=101`.

## Prime-equidistribution release 3.15

`SylvesterSchurSqrtEnvelope.lean` replaces the coarse one-factor-per-small-
prime estimate in the central range by a square-root factorization split.
Prime-power contributions below `sqrt n` cost at most `n^sqrt(n)`; above the
split they have exponent at most one.  The elementary three-multiple
valuation lemma further restricts supported high primes to `p<=n/3`, and
Hanson's theorem gives
`choose n k <= n^sqrt(n) * 3^(n/3+1)` under the no-prime-above-`k`
hypothesis when `2k<=n`.

The module exports audited numerical-gap criteria forcing a prime above `k`
in both the binomial coefficient and the original consecutive product.  The
remaining task is to prove the required explicit gap uniformly on a large-
length central region and combine it with the factorial cutoff; the
unrestricted theorem is not yet claimed.

## Prime-equidistribution release 3.16

`SylvesterSchurCentralTail.lean` proves the release-3.15 numerical gap with
the explicit cutoff `H>=34134`.  Its natural-number proof first establishes
`x<=2^(sqrt(x)/16)` above the checked square-root threshold `320`, obtains
`(3H)^sqrt(3H)<=2^(H/4)`, and finishes with an inductive comparison of the
fixed bases `162` and `256`.

Thus every interval with `H>=34134` and `H<N<=2H` now unconditionally has a
prime divisor above `H`.  This removes the full large-length central strip;
the remaining Sylvester--Schur work consists of noncentral starts together
with the bounded-length bridge from `101` through `34133`.

## Prime-equidistribution release 3.17

`SylvesterSchurExplicitTail.lean` upgrades the large-length result from a
central strip to every start.  For `N+H<=1024H`, the release-3.15
square-root/Hanson envelope is absorbed using exact logarithmic bounds valid
from `H>=4^101`.  At `1024H`, Mathlib's explicit Chebyshev estimate places the
prime-count factor below the binomial-growth margin.  The already checked
growth monotonicity covers every larger upper index.

The theorem `exists_large_prime_dvd_consecutiveProduct_of_explicit_tail` is
therefore uniform in all `H<N` once `H>=4^101`.  Together with the proof below
`101` and the exact factorial start cutoff, this leaves the explicit finite
rectangle `101<=H<4^101`,
`N+1 < H! * 2^pi(H)+1`.  The module proves that this exact rectangle implies
the unrestricted Sylvester--Schur conclusion.

## Prime-equidistribution release 3.18

The explicit all-start argument has been quantitatively tightened without a
new external input.  The near/far transition is now `N+H=64H`, and the
certified estimate `log H<=sqrt(H)/40` begins at `H=250000`.  The near branch
absorbs the square-root/Hanson envelope through `64H`; at that same endpoint,
the explicit Chebyshev prime-count bound proves the binomial-growth baseline,
which propagates to every larger upper index.

Thus every start `H<N` is closed for `H>=250000`.  The exact remaining
Sylvester--Schur rectangle is `101<=H<250000` with
`N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.19

The low-prime part of the square-root envelope now retains its exact
cardinality: its exponent is `pi(sqrt(n))`, not `sqrt(n)`.  An elementary
reduced-residue count, including a finite kernel certificate below `690`,
proves `pi(m)<=m/4` from `m=120`.

This sharpens the near branch through `64H` to start at `H=10000`.  A second
modulo-210 count proves `pi(H)<=H/4` on the far branch; at `64H` that bound
fits the exact binomial-growth margin throughout `10000<=H<250000`, while
release 3.18 handles all larger lengths.  Hence every start `H<N` is now
closed for `H>=10000`, and the exact remaining Sylvester--Schur rectangle is
`101<=H<10000`, `N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.20

A bounded exact prime-count certificate now proves
`6*pi(m)<=m+84` for every `100<=m<800`.  This is precisely the square-root
range arising from `6000<=H<10000` and `2H<=n<=64H`.  Together with the
certified inequality `log H<=13*sqrt(H)/100`, it closes the near branch on
that entire bridge.  The far binomial-growth baseline, now stated from
`H>=2200`, closes the complementary starts.

Consequently every start `H<N` is closed for `H>=6000`.  The exact remaining
Sylvester--Schur rectangle is `101<=H<6000`,
`N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.21

The near/far transition is now adaptive.  On `2200<=H<3000` it occurs at
`16H`; on `3000<=H<6000` it occurs at `20H`.  A compact kernel certificate
proves `4*pi(m)<=m+12` for `60<=m<400`, exactly covering the square-root
ranges in the two near branches.  The corresponding logarithmic estimates
and `pi(H)<=H/4` close both far baselines.

Thus every start `H<N` is closed for `H>=2200`.  The exact remaining
Sylvester--Schur rectangle is `101<=H<2200`,
`N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.22

Three adaptive bands now carry the effective tail down to `H=512`: transition
`5H` on `512<=H<625`, `6H` on `625<=H<1134`, and `5H` again on
`1134<=H<2200`.  Exact kernel certificates establish `pi(H)<=H/5` and
`pi(H)<=H/6` on the needed finite ranges.  Above the final exact anchor
`pi(1906)=291`, four checked counts of integers coprime to `210` finish the
upper range without an external prime table.

Thus every start `H<N` is closed for `H>=512`.  The exact remaining
Sylvester--Schur rectangle is `101<=H<512`,
`N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.23

An exact bounded central-binomial certificate proves the far growth baseline
already at `n=2H` for every `121<=H<512` except
`H=139,140,199,200,201`.  The first exceptional pair is bridged by the
prime-counted square-root envelope through `n=281`, and the remaining triple
through `n=403`; exact binomial growth begins at those same endpoints.

Together with release 3.22, every start `H<N` is now closed for `H>=121`.
The remaining Sylvester--Schur rectangle has only the twenty length rows
`101<=H<121`, with `N+1 < H! * 2^pi(H)+1`.

## Prime-equidistribution release 3.24

The common upper index `243` satisfies the binomial-growth baseline for every
remaining length `101<=H<121`. Below that endpoint there are only 420
admissible `(N,H)` pairs; one bounded kernel certificate supplies a prime
`p>H` dividing each consecutive product. Therefore `sylvesterSchur` proves
the unrestricted `SylvesterSchurConclusion` with no residual hypothesis.

Hanson's all-length primorial theorem then gives the exact square
specialization of Erdős--Selfridge. Every factorial squarefree fiber is
unconditionally bounded by two, and the public Theorem 1.10 consumer now
requires only Theorem 2.5 and Proposition 2.3(ii), or equivalently the pinned
Baker--Harman--Pintz input.

## Prime-equidistribution release 3.25

The conditional high-scale Type II estimate now reaches the literal Vaughan
convolution term.  `TypeIIConvolutionBridge.lean` supplies the exact outer-sum
identity, the product-restricted Cauchy--Schwarz inequality, the bounded/full
block support equivalence, and the actual source coefficient bounds.  It also
reassembles per-block square bounds into the full convolution norm.

`TypeIISourceBlock.lean` composes this bridge with the existing mixed
Weyl--Vinogradov squared-inner-sum theorem.  Thus, conditional only on the
named `VinogradovExponentialSumEstimate` and its source parameter hypotheses,
the norm square of every admitted literal source Type II double block has the
full low-scale Weyl plus high-scale logarithmic-saving majorant.  Theorem 2.5
is not yet claimed: proving the Vinogradov proposition, closing all source
regime splits, summing/simplifying the Type I and Type II block bounds, and
finishing the Fourier assembly remain.

## Prime-equidistribution release 3.26

The Type II source-family regime split and finite summation are now complete.
If an outer or inner dyadic scale is below the common logarithmic subdivision
budget, the corresponding Möbius-tail or divisor-tail coefficient vanishes
exactly once the source cutoff dominates twice that budget.  Thus only
large--large block pairs consume the conditional mixed Weyl--Vinogradov
estimate.

`vaughanTypeIISourceBlockMajorant` records the resulting explicit block
majorant, and
`eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov`
sums its square roots over the complete literal Type II convolution.  A
uniform block-square bound costs exactly `(log₂ B+1)^204`.  Remaining Type II
work is to instantiate the source cutoffs and scale inequalities uniformly
and simplify the displayed majorant to the required logarithmic saving;
`VinogradovExponentialSumEstimate`, Type I, and Fourier closure also remain.

## Prime-equidistribution release 3.27

The source cutoff is now canonical rather than hypothetical:
`vaughanSourceTailCutoff b = ⌊b^(1/3)⌋₊`.  The cube-root cutoff eventually
dominates twice the exact `(log₂ b+1)^101` subdivision budget, and its floor
loss is absorbed by the strict exponent gap `1/4<1/3`.  Consequently, when
`P≤b`, it also supplies the uniform lower scale
`2 exp((1/4) log P)≤U` needed by every surviving outer block.

The family proof now uses the actual dyadic cutoff tests, deletes blocks with
empty product support, and derives each surviving block's phase-scale premise
from the single global inequality
`2b (log b)^d≤|N|`.  The public canonical-cutoff theorem therefore has no
blockwise scale hypotheses and no free cutoff parameters.  The remaining
Type II work is the analytic `VinogradovExponentialSumEstimate` and the
uniform simplification of the explicit summed majorant; Type I and Fourier
closure remain downstream.

## Prime-equidistribution release 3.28

`TypeIISourceBlock` now fixes the derivative-order family itself to `{5,6}`.
The fully canonical family theorem therefore exposes neither cutoff parameters
nor an auxiliary order set.  Surviving blocks have outer endpoint above
`B^(1/4)` and doubled inner scale above `2B^(1/4)`.

Each canonical short-block length is at most `B/(log B)^100`, its outer block
cardinality is at most that length, and `1+log q≤2log B`.  These facts replace
the exact component-count expression by one absolute constant times
`log B*K`, yielding the audited
`vaughanTypeIICanonicalGeometricBlockMajorant`.  Its comparison theorem is the
first uniform geometric compression of every exact source block.  The
Vinogradov proposition and the remaining power/logarithm absorption across the
full square-root sum are still explicit open tasks.

## Prime-equidistribution release 3.29

The Type II simplification now retains the source-critical local widths
`2^s/(log b)^100` and `2^t/(log b)^100`.  On every nonempty product block,
the dyadic product is at most `b`; the two expanded analytic monomials are at
most `b²`.  Exact denominator bookkeeping therefore gives the three squared
block exponents `298`, `197`, and `297`.

The purely diagonal monomial is sharper: survival beyond the canonical inner
cutoff gives `D²E≤b²/b^(1/4)`.  The audited
`vaughanTypeIICanonicalPowerSavedBlockMajorant` retains this power saving, and
the full conditional convolution theorem sums its square roots over the exact
canonical family.  Remaining Type II work is to absorb the reciprocal-phase
and endpoint factors, sum the resulting family bounds, and prove the named
Vinogradov proposition.

## Prime-equidistribution release 3.30

The last block-dependent Type II decay factors are now eliminated.  A global
lower bound `(log b)^d≤F` replaces `F^(-1/1024)` by
`(log b)^(-d/1024)`, while survival beyond the outer cutoff replaces the
inverse endpoint contribution by `b^(-1/4096)`.

The resulting block-independent ledger is flattened exactly: its diagonal
term is `b^(7/4)/(log b)^298`, and its other squared-block denominators remain
`197` and `297`.  The complete canonical double sum is evaluated as
`(log₂ b+1)^204 sqrt(R)` and then bounded by
`(3 log b)^204 sqrt(R)`.  The remaining Type II work is the final choice and
absorption of `d,T` into an arbitrary target logarithmic saving, plus the
still-open `VinogradovExponentialSumEstimate`; Type I and Fourier closure
remain downstream.


## Prime-equidistribution release 3.31

The flattened Type II ledger is now absorbed into an arbitrary requested
logarithmic saving.  Under the source comparison `P≤b≤2P`, fixed powers of
`b` dominate every logarithmic target, `log b≤2log P`, and square-root
extraction cancels the exact family exponent `204`.

For target `S≥0`, the audited specialization fixes
`d=2048S+216064`, `T=2S+111`, and the matching Vinogradov parameter.
It yields the literal conditional bound
`C b/(log P)^S` for the complete canonical Type II convolution.  Thus the
remaining Type II obstruction is the named
`VinogradovExponentialSumEstimate` itself; quantitative Type I and the final
Fourier assembly still remain for Theorem 2.5.

## Prime-equidistribution release 3.32

The literal Type I terms in Vaughan's identity are now connected to the
one-dimensional analytic interface.  Each canonical outer block becomes an
exact product-restricted Type I outer sum, and each inner fiber over
`[a,b)` is identified with `[⌈a/m⌉,⌈b/m⌉)` carrying the rescaled phase
`(N/m,M/m^j)`.

The unit and `log(2B)` source coefficient envelopes are propagated through
the full outer family.  The logarithmically weighted term also feeds the
existing finite Abel-summation theorem directly.  Thus the remaining Type I
boundary is quantitative cancellation for the exposed unweighted prefix
sums, followed by the final Fourier recombination.

## Prime-equidistribution release 3.33

The Type I bridge now retains actual nonzero coefficient support through the
triangle inequality. Active indices satisfy `mâ‰¤U` in the first term and
`mâ‰¤UV` in the second, giving the exact block-cardinality bounds needed for
quantitative summation.

A uniform inner bound `Q` yields complete-family losses
`(logâ‚‚ B+1)^102 U` and `(logâ‚‚ B+1)^102 log(2B) UV`. The remaining task is
to obtain `Q` from high-scale reciprocal-phase cancellation and Abel
summation, then absorb these explicit factors.

## Prime-equidistribution release 3.34

The Type I rescaling now includes the quantitative source-to-fiber geometry.
The reciprocal-phase scale is exactly invariant before ceiling rounding and
antitone afterwards.  Every source subinterval of `[P,2P)` therefore maps
inside `[ceil(P/m),2ceil(P/m))`, and the source inequality
`F(P) <= (P/m)^4` supplies the low-scale condition required at the rounded
inner scale.

These are finite algebraic and order-theoretic theorems, not a cancellation
claim.  The next boundary is the endpoint buffer and effective-error premise
of the existing four-step Weyl estimate, followed by insertion into the
uniform Type I callback.

## Prime-equidistribution release 3.35

The quadratic Type I fibers now enter the analytic Weyl layer.  Each dyadic
fiber is split exactly into at most ten canonical blocks.  On every nonempty
block, the optimized four-step range is at most the block length, and the
ten-block geometry supplies the endpoint margin and quadratic power bound.

A new dyadic comparison shows that the reciprocal-phase scale falls by at
most a factor four.  Thus a single source budget bounds the effective error
at every local block scale, and the two-term Weyl estimate is proved for each
piece.  Uniformizing the local two-term widths and summing the ten pieces
remains before the active Type I family theorem can be instantiated.

## Prime-equidistribution release 3.36

All local quadratic widths are now uniformized by the source expression
`(F/D^5+4/F)^(1/1024)`. The ten block estimates sum to one explicit bound for
the complete dyadic interval.

The same proof is exported for every subinterval of `[D,2D)`. This is the
strong form needed for logarithmic Abel summation: every initial prefix is
covered with the same constant and source budget. Substitution of the
ceiling-rounded Type I parameters and uniform control over active outer
indices remain.

## Prime-equidistribution release 3.37

The quadratic subinterval estimate is now specialized to every literal Type
I fiber at `(N/m,M/m^2,ceil(P/m))`. A named admissibility predicate exposes
the exact rounded-scale, fourth-power, and effective-error premises, while an
explicit ten-block rescaled majorant controls both the complete unweighted
fiber and every prefix needed for the logarithmic Abel argument.

These estimates instantiate both complete active-support Vaughan callbacks.
Thus all Type I convolution bookkeeping is closed conditionally on uniform
active-index admissibility and a common bound `Q`. What remains is the
source-parameter inequality which supplies those premises and absorbs the
explicit `U`, `UV`, logarithmic, and family-count factors.

## Prime-equidistribution release 3.38

The Type I analytic callback now follows the source's genuine two-regime
argument. Each rounded fiber is classified by whether its transformed phase
scale is below or above `D^4`. The low branch uses the quadratic Weyl
subdivision; the high branch invokes the fixed-constant Vinogradov theorem
with its full critical-deletion envelope.

This hybrid estimate holds for every fiber subinterval, feeds finite Abel
summation, and propagates through both complete active Vaughan families. The
paper's exponential frequency bound and a fixed-power lower bound for `D`
now imply all eventual high-branch side conditions. Only the branch-local
low-scale budget and the common logarithmic majorant remain to finish the
quantitative Type I estimate.

## Prime-equidistribution release 3.39

The branch-local low-scale budget is now automatic. In the Weyl branch,
`F(D) <= D^4` turns the effective-error expression into an explicit quantity
at most one for all sufficiently large `D`; source-to-fiber ceiling
comparison supplies the required transformed-scale lower bound.

For both canonical Type I coefficient families, active support implies
`D=ceil(P/m) >= B^(1/4)` eventually. `TypeISourceBlock.lean` combines this
geometry with the global source frequency bounds and proves the full hybrid
admissibility predicate for every active index. What remains is the uniform
logarithmic absorption and summation of the already explicit hybrid
majorants; Theorem 2.5 is not yet claimed.

## Prime-equidistribution release 3.40

Type I family aggregation now preserves the reciprocal outer-index decay of
the analytic fiber length. The sum of `1/m` over either canonical active
support is bounded by `harmonic U` or `harmonic (UV)`, and complete-family
theorems turn every inner estimate `(P/m)Q` into a bound with only that
harmonic loss across each short-interval family.

Thus the polynomial cutoff losses `U` and `UV` no longer obstruct the target
logarithmic saving. The remaining Type I task is to replace the current
maximum envelope by branch-sensitive low-Weyl/high-Vinogradov absorption and
feed its `(P/m)` bound into these harmonic aggregators.

## Prime-equidistribution release 3.41

The branch-sensitive Type I majorant is now fully absorbed. High fibers use
only the source Vinogradov envelope, while low fibers reduce to the explicit
width `(1/D + 16/(log B)^d)^(1/1024)` and use the active quarter-power lower
bound for `D`. No unused Weyl expression survives in the high branch.

Both complete canonical Vaughan Type I families now satisfy arbitrary
logarithmic savings. The exact ledger loses 104 powers of the logarithm;
the exported theorems use `T=S+104` and the explicit budgets
`S+106<=3A` and `1024*(S+105)+1<=d`. Quantitative Type I is therefore closed,
conditional on the named source Vinogradov estimate. The remaining Theorem
2.5 work begins with the Type I/Type II/Vaughan assembly and then the
Mangoldt, prime, and Fourier transfer layers.

## Prime-equidistribution release 3.42

The complete Type I and Type II estimates are now inserted into the literal
Vaughan decomposition. `MangoldtSourceBlock.lean` proves that the canonical
initial cutoff term vanishes on every sufficiently large dyadic block and
then combines the remaining three convolution terms without changing their
signs, coefficients, supports, or phase.

The resulting theorem gives arbitrary logarithmic saving for the quadratic
Mangoldt reciprocal-phase sum using the shared exponent
`2048*S+216064`. This closes the Vaughan assembly itself, conditional on the
named Vinogradov estimate. Remaining work is to consolidate the equivalent
scale and `|N|` hypotheses into the source-facing frequency range and carry
the Mangoldt estimate through prime partial summation and Fourier assembly.

## Prime-equidistribution release 3.43

The quadratic Mangoldt estimate now exposes exactly one source-frequency
range. The lower `|N|` inequality supplies the logarithmic Type I scale and
the fixed threshold 64, while `F(N,N,2,P) <= 2|N|` transfers the upper
frequency bound. Thus the completed Vaughan theorem no longer asks callers
to repeat equivalent Type I and Type II hypotheses.

What remains in this chain is the Mangoldt-to-prime conversion and insertion
into the existing Fourier assembly for smooth periodic weights.

## Prime-equidistribution release 3.44

`PrimeSourceBlock.lean` now transports the unified quadratic Mangoldt bound
to unweighted primes. It aligns the half-open prime interval with the frozen
prime-power-tail convention exactly, proves a dyadic quarter-power tail
bound, and absorbs that tail into every requested logarithmic saving.

Uniform control of all initial prefixes gives the log-weighted prime bound;
reverse Abel summation then yields the complete high-frequency unweighted
quadratic prime exponential-sum estimate under the same single source range.
The remaining Fourier boundary is the logarithmic integral for nonzero modes
and its combination with the low-frequency and zero-mode contributions.

## Prime-equidistribution release 3.45

`FourierSourceBlock.lean` now connects the completed prime estimate to the
literal Fourier definitions in the diagonal `(1,1)` case. The half-open
Fourier prime sum is exactly the reciprocal-phase sum with coefficients
`(N,N)`, and integration by parts gives the matching logarithmic integral the
explicit bound `6*P^2/(|N|*log P)` on a dyadic subinterval.

The combined theorem bounds the diagonal Fourier discrepancy by the prime
logarithmic saving plus this inverse-frequency integral term. This release
does not claim general Fourier completion: a mode `(q1,q2)` produces unequal
phase coefficients `(q1*N,q2*N)`, which the current diagonal Type I/II source
theorems do not cover. The exact general-mode identification, derivative, and
same-sign nonstationarity are nevertheless now formalized. Unequal-parameter
high-frequency estimates, opposite-sign stationary cases, and the low-
frequency and zero-mode branches remain open.

## Prime-equidistribution release 3.46

`UnequalTypeIIVinogradov.lean` generalizes the complete high-pair Type II
Vinogradov interface from the diagonal phase `(N,N)` to independent
coefficients `(N,M)`. The transformed correlation uses the linear parameter
derived from `N` and the quadratic parameter derived from `M`; the existing
general dyadic-block estimate bounds their combined scale by the same factor
five under separate source upper bounds.

The fixed envelope, eventual logarithmic saving, decay-kernel callback, and
canonical Vaughan-block callback are all compiled and audited in this form.
The low-scale Weyl distance-kernel comparison remains diagonal, so this does
not yet constitute the full unequal Type II family estimate or Theorem 2.5.

## Prime-equidistribution release 3.47

`UnequalTypeIIWeyl.lean` supplies the missing low-scale Type II comparison for
independent reciprocal coefficients `(N,M)`. The proof uses the quadratic
transformed term together with the canonical inner-band lower bound, then
combines it with the linear transformed term by a max split.

The unequal estimate now passes through the fixed-block logarithmic wrapper,
near/far kernel aggregation, the Vinogradov high-pair callback, canonical
Vaughan inner blocks, and an actual weighted Vaughan Type II double block.
Summation over the complete double-block family and the ensuing unequal
Mangoldt/prime/Fourier endpoints remain the next boundary.

## Prime-equidistribution release 3.48

The complete Vaughan Type II family now retains independent reciprocal-phase
coefficients. `UnequalTypeIISourceBlock.lean` performs finite block-family
summation and every subsequent majorant compression through arbitrary
logarithmic saving. Its blockwise synthetic diagonal coefficient has exactly
the unequal phase scale, permitting exact reuse of the prior scalar
compression proof.

`UnequalMangoldtSourceBlock.lean` combines this result with the already-
general Type I estimates and exports a unified source range with separate
upper bounds for the two coefficients. `UnequalPrimeSourceBlock.lean`
completes prime-power removal and reverse Abel summation. Thus all modes with
nonzero quadratic coefficient now have a prime exponential-sum estimate.
The remaining Fourier work is the zero-quadratic branch, general integral
estimates (especially opposite-sign stationary geometry), low frequencies,
and final mode assembly.

## Prime-equidistribution release 3.49

`UnequalFourierSourceBlock.lean` now controls the logarithmically weighted
integral for independent same-sign reciprocal coefficients. The positive
chamber is proved by an exact integration-by-parts amplitude and monotonicity
calculation; conjugation supplies the negative chamber with the same bound.

The result is combined with the unequal prime estimate to give the literal
Fourier-mode discrepancy for both same-sign chambers. Remaining work is
localized to opposite-sign stationary geometry, modes on the coordinate
axes, low frequencies, and the finite Fourier assembly.

## Prime-equidistribution release 3.50

`StationaryFourierSourceBlock.lean` formalizes the exact critical point
`-2*B/A`, uniqueness of derivative vanishing, and factorization of derivative
size as `|A|` times distance to the critical point. When that point lies in
the source dyadic range, the existing phase-scale hypothesis yields both a
linear-coefficient lower bound and a quantitative far-region derivative
lower bound.

An exact three-piece interval identity isolates a radius-`δ` stationary
neighborhood, whose contribution is bounded by `2*δ/log P`. The remaining
opposite-sign task is now precisely the two far-piece cancellation bounds and
choice of `δ`; axis modes and final Fourier assembly remain separate.

## Prime-equidistribution release 3.51

The two stationary far pieces are now bounded. Exact integration by parts on
intervals avoiding the critical point gives monotone endpoint estimates on
the left and initial right segment. A separate pointwise amplitude-derivative
bound controls the post-turning tail, and the pieces reassemble without an
unstated monotonicity assumption.

After inserting `A >= (16/5)*P*L`, the formal choice `δ=P/sqrt L` proves the
interior stationary integral bound `50*P/(sqrt L*log P)` for `L>=4`.
Endpoint-clipped stationary intervals and the sign-conjugate wrapper are the
remaining opposite-sign work; coordinate-axis modes, low modes, and the final
Fourier assembly also remain open.

## Prime-equidistribution release 3.52

The optimized stationary estimate is now endpoint-safe: the radius
`P/sqrt L` neighborhood may be clipped on the left, right, or both sides.
Exact interval additivity reduces each case to the already proved one-sided
far bounds and the central length estimate, with the same constant `50`.

Conjugation unifies both opposite-sign orientations. The bound is then
inserted into the literal Fourier integral and combined with the unequal
prime exponential-sum theorem. Thus the nonzero-coefficient stationary
Fourier chamber has a source-range discrepancy theorem. Coordinate-axis
modes, low frequencies, and final mode assembly remain open.

## Prime-equidistribution release 3.53

`CoordinateAxisFourierSourceBlock.lean` closes the pure quadratic coordinate
axis. The generalized integration-by-parts machinery now includes a
nonnegative-amplitude-derivative variant, yielding
`16*P^3/(|B|*log P)` and hence `P/(L*log P)` from the exact pure quadratic
source scale. This is combined with the existing unequal prime estimate in a
literal Fourier-mode discrepancy theorem.

Only the pure linear coordinate axis remains among high-frequency modes. It
needs a distinct Type II cancellation argument; the existing quadratic Weyl
and Vinogradov branches both genuinely consume nonvanishing of the quadratic
coefficient. Low-frequency control and final Fourier assembly also remain.

## Prime-equidistribution release 3.56

The pure linear coordinate axis is now complete. `LinearAxisTypeII.lean` and
`LinearAxisTypeIISourceBlock.lean` supply the full Type II source family, while
`LinearAxisTypeI.lean` supplies both zero-quadratic Vaughan Type I families.
The exact Vaughan identity, prime-power removal, and reverse Abel summation
then yield the pure-linear prime exponential-sum estimate.

`LinearAxisFourierSourceBlock.lean` combines that prime theorem with the
existing `2*P/(L*log P)` pure-linear integral estimate, giving the literal
prime-minus-integral discrepancy. Both coordinate axes are now complete. Low
frequencies and final Fourier assembly remain open; Theorem 2.5 is not
claimed.
