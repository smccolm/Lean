# Tao 2026 Research Agenda

## Status and scope: verified release 5.10

The owner-approved completion amendment permits endpoint-equivalent,
hypothesis-free substitutions. Native quantitative PNT is accepted for the
exact Section 4 upper-scale consumer in place of BHP, and the proved Selberg
upper-sieve weight is accepted for every Lemma 5.1 consumer in place of the
literal Rosser construction. BHP `0.525` and `{-1,0,1}` Rosser weights remain
unproved stronger alternatives outside the four-endpoint completion scope.

All four unchanged Theorem 1.7--1.10 contracts are proved without additional
mathematical hypotheses. The integrated 10284-job build and canonical release
verifier passed on 2026-09-19, including the explicit standard-axiom audit
and all 10 semantic regression assertions. The reproduction manifest records
the complete unsuppressed log and its SHA-256.

The final Section 4 argument uses native quantitative PNT: constancy of
Chebyshev theta on a prime-free interval, the quantitative theta error, and
Bertrand imply `4 H (log N)^2 ≤ N` eventually. This is precisely the upper
scale consumed by both existing Lemma 4.2 contradictions. The complete lemma
then supplies the established Theorems 1.9 and 1.10 counting chains without
changing any public hypothesis or conclusion.

Theorem 1.7 uses the completed simple-root Stepanov, norm-fiber cancellation,
Newton amplification, unique-tag prime quotient, cubefree Burgess, and sharp
critical saddle chain. Theorem 1.8 uses the unconditional specialized
Theorem 2.5 and Section 3 counting/asymptotic chain.

BHP's stronger `0.525` statement remains unformalized, and the broader
arbitrary-multiplicity Kummer interfaces remain conditional alternatives.
They are possible future library work, not assumptions or unresolved
dependencies of the four-theorem release. The original source-program
requests and older progress descriptions below are historical records;
the release does not claim every stronger auxiliary paper statement.

## Historical status and scope: 5.08

Release 5.08 proves Theorem 1.7 unconditionally. The Stepanov construction
uses a simple root to separate orders of vanishing, and its explicit
dimension and natural-floor parameter calculations give square-root norm-
fiber bounds. Character cancellation and translation give the eventual
extension estimate. Newton recurrence amplification then proves the sharp
simple-root Weil bound. The unique-tag Burgess consumer fits this hypothesis
after a block swap and character inversion when necessary. The prime-square,
CRT, Burgess, and critical saddle chains reach `taoTheorem17_unconditional`.
The general arbitrary-multiplicity Kummer contracts remain conditional
alternatives; they are not required for this endpoint.

The next mathematical obligation is Proposition 2.3(ii)/BHP, still the sole
premise of Theorems 1.9 and 1.10. The whole-proof goal remains active.

This agenda governs the active formalization of Terence Tao, *Products of
consecutive integers with unusual anatomy*, arXiv `2603.27990v2`. The release
scope is now fixed by `Tao Goal Prompt.md` at Theorems 1.7--1.10. Theorems 1.7
and 1.8 are proved unconditionally; Theorems 1.9 and 1.10 remain active.

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

## Historical Phase 1 - source reconstruction

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

## Historical Phase 4 - proof implementation

Build from definitions and reusable lemmas toward the frozen source-facing
contracts. Research probes may be used, but they must remain outside the
production import root. Do not substitute theorem-shaped assumptions for
missing mathematics.

The four quantified upper/lower conclusions of Proposition 2.1 are now
compiled and axiom-audited. The last critical lower half is discharged by a
coarse CEP construction using fixed dyadic PNT blocks: its endpoint reciprocal
mass is at least `1/(16 log 2 log u)`, its multiplicity is
`floor(u-2u/log u)`, its cofactor depth is at most `10u/log u`, and its full
secondary loss is at most `60u log(log u)`. This yields the unconditional
theorem `IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat`.
The shrinking-band CEP construction is no longer a proof blocker. The first
downstream instantiation is complete: selector diagonalization makes the
critical lower estimate uniform for primes in `z<p<3z`, reciprocal-prime mass
and the exact `B¹` identity then prove the lower half of Lemma 1.6(i). The
matching upper proof closes Lemma 1.6(i) by combining a
uniform `alpha=1/2` small-prime estimate, a reciprocal-square large-prime
tail, and a finite exponent grid in the middle; `alpha+1/alpha≥2` controls
each grid cell and the fixed number of cells is absorbed into `z^epsilon`.
The remaining Lemma 1.6 task is the reverse analytic half of the separate
constant-factor stability clause (ii). `SmoothNumberStability` now fixes the
literal `floor(cX)` endpoint, proves its ratio and logarithmic limits and
critical-regime preservation, and reduces the source clause to Granville
(3.24)'s quotient limit. Cutoff monotonicity supplies the other direction for
both contractions and expansions. `SmoothNumberSaddlePoint` now removes the
first analytic prerequisite: it constructs the unique positive solution of
`sum_{p<=y} log(p)/(p^sigma-1)=log X`, proves the positive `phiTwo` formula
and `phiOne'=-phiTwo`, and gives an exact mean-value identity controlling the
change in the saddle when `X` changes. `SmoothNumberSaddleRegimes` adds
explicit finite upper/lower comparisons and proves that this exact saddle
tends to `1` throughout the critical regime. It also proves the curvature
lower bound `phiTwo >= log(2) log(X)`, an exact finite secant estimate, and
that fixed dilations move the saddle by `o(1/log y)`. The phase infrastructure is
also exact: `SmoothNumberSaddlePhase` identifies the
finite Euler product, proves both derivatives, defines the Gaussian main term,
and proves the saddle is its unique positive global minimum. What remains here
is narrowed further by the exact minimum-phase squeeze: fixed dilation changes
the minimized phase by `log(c)`, so its exponential quotient tends to `c`.
`SmoothNumberSaddleCurvature` bounds every prime-local logarithmic curvature
derivative uniformly, proves the `phiTwo` quotient tends to `1`, and combines
this with phase and saddle stability to prove that the complete Gaussian main
term quotient tends to `c`. The remaining task is the uniform
Hildebrand--Tenenbaum/Granville saddle-point evaluation of `Psi`, including
an error small enough to derive (3.24). Its precise uniform
`Psi/mainTerm -> 1` form is now `TaoCriticalSmoothSaddleAsymptoticConclusion`;
Lean proves this contract implies the quotient-limit and `IsTheta` targets.
The small-distinguished-prime disposal in Proposition 6.5 now consumes the
proved critical upper estimate directly. The actual union with `p₀≤y` is
embedded into `Psi(2x,y)`, and the floored scale `y=⌊z(x)^β⌋` is proved to
remain critical. This gives `2x/z(x)^(1/β-ε)` uniformly for fixed positive
parameters, including the explicit `2x/z(x)^(12/5)` bound at `β=2/5`.
The later smooth prime bands now have their exact finite endpoint reduction:
the fixed `(p₀,H)` union is covered by two smooth-cofactor families and has
cardinality at most `2H Ψ(⌊2x/p₀²⌋,p₀)`. A concrete 60-cell grid now performs
the prime-band and dyadic-length aggregation from exponent `6/5` through
`3`. Each cell retains a fixed margin above exponent two, and arbitrary
logarithmic losses plus the `2x` dilation are absorbed, yielding the actual
union bound `x/z(x)^(2+1/800)`. The proved slow-variation identity
`log z(2x)/log z(x)→1` also embeds the literal fixed source branch
`z(x)^(5/4)<p₀≤⌈z(x)^3⌉` into this grid. The exact arithmetic reduction is
proved: 1000 multiplicity-counted prime
factors above the lower cutoff construct `TypicalPrimeAnatomy`, including a
remainder smooth below the last selected factor; hence an interval still
failing condition (iii) has fewer than 1000 such factors.
The ensuing finite counting reduction is also compiled: canonical deficient
packets cover the actual short, square-avoiding non-typical union, dyadic
lengths are summed, producing the intermediate analytic target
`4L ∑_{p₀}∑_a Ψ((2x/p₀²)/a,y)` over products `a` of fewer than 1000 primes in
`[y,p₀]`. The product index is expanded into the literal finite universe of
factor lists of length below 1000. A uniform selector argument at
`y=⌊z(x)^(9/10)⌋` retains the exact reciprocal `1/(p₀²∏q)` weight; elementary
harmonic and reciprocal-square tails bound the complete list mass, and the
resulting fixed logarithmic loss is absorbed into `z(x)^(1/200)`. Thus the
actual central deficient condition-(iii) union, with
`z(x)^(9/10)<p₀≤z(x)^(11/10)`, satisfies
`#union ≤ x/z(x)^(2+1/200)` eventually.
The two fixed outside-central gaps are now closed as well. A fine 600-cell
mesh retains a uniform margin on `2/5<p₀-exponent≤9/10` and
`11/10<p₀-exponent≤5/4`; one-percent endpoint slack transfers the source
cutoffs to the cofactor scale `2x`, and a generic fixed-constant length
absorption yields the actual-union estimate
`#union≤x/z(x)^(2+1/1000)`. For each row denominator `d=n+10`, the same
construction is now made quantitative on the moving source window with exact
lower cutoff `⌊z(x)^(1-2/d)⌋` and upper cutoff `⌈z(x)^(1+2/d)⌉`. Moving low
and high exponent meshes retain a margin `1/(4d²)`, while the full intervening
deficient-factor range retains its reciprocal weights and a `1/d²` margin.
The resulting eight-branch fixed-row family satisfies
`#union≤x/z(x)^(2+1/(128d²))`. Countable diagonalization chooses a single
`q(x)→∞`; floor- and ceiling-ratio lemmas prove that both selected cutoff
logarithms divided by `log z(x)` tend to one, and the selected actual union is
eventually at most `x/z(x)^2`. Thus the source-facing Proposition 6.5 cutoff
diagonal is closed.
The next layer now gives Proposition 6.6 its literal probability model.
`BadIntervalRandomModel` places the 1001 coordinates on a finite product
measure, gives coordinate `j` the uniform law on the primes in `[Pⱼ,2Pⱼ)`,
and proves both the exact pushforward mass formula and mutual independence.
The source product, its divisibility indicators, and the typical-interval
event are defined on this space. The exceptional `p∣l` branch is now closed
deterministically: the contribution is at most `H log H`, then `H log z(x)`
at the source scale, so its large event is empty and has measure zero. The
small-prime branch now has its exact cutoff, `p∤l` index set, fixed fiftieth
moment, and ordered-tuple expectation expansion into joint divisibility
probabilities. The tuple lcm is explicit, and an exact CRT precursor proves
that every joint event is either empty or one primitive residue-class fiber
modulo this lcm. The exact normalized Dirichlet-character expansion of that
fiber now compiles, as do its integrated probability identity, exact
independent-coordinate factorization, identification with normalized dyadic
prime-character averages, and weak AM--GM reduction to the all-character sum
of 1000th powers. The lcm/totient comparison supplies the exact `2^50/lcm`
coefficient, and this estimate is now inserted into the entire ordered
fiftieth moment. Exact finite reordering followed by pigeonholing selects one
of the 1000 tail coordinates with factor `1000`. `PrimeCharacterSums` starts
the Section 5 analytic interface: `s_Z(χ)`, the exact threshold
`Z^(-1/125)=Z^(-0.008)`, the primitive exceptional/unexceptional partition,
the unexceptional total `≤φ(q)Z^(-8)`, and reduction of every exceptional
1000th power to the squared moment of Lemma 5.1 all compile. The source
conductor footnote is now exact: scale separation gives coprimality with the
tuple lcm, hence equality with the primitive counterpart. The principal term
is one, the nonprincipal terms are partitioned by exact positive conductor,
and every fixed fiber injects into the primitive nonprincipal characters.
This bounds the full ambient moment by a divisor sum of exceptional squares
and `φ(d)Z^(-8)` errors. The bound is now inserted termwise into the actual
ordered tuple sum, and the factor-1000 coordinate pigeonhole controls the full
fiftieth moment by the resulting explicit conductor-reduced expression. The
new `SmallPrimeMertens` layer identifies the tuple lcm with the product of its
distinct prime support and proves that the support multiplicities sum to 50.
Thus the coefficient is exactly one `log p/p` per support prime times repeated
logarithms of total exponent `50-#support`. The explicit finite weighted-prime
bound `log 4 * (2 + log Y)` is inserted pointwise, and fixed ordered prime
tuples have at most `H^50` compatible shift tuples, with a generic fiberwise
summation theorem. Exact support regrouping, the uniform `50^50` support-fiber
bound, and an elementary-symmetric inequality sum all equality patterns and
give `H^50 O(log(cutoff)^50)`. The conductor expression is split into
principal, exceptional-square, and totient-error pieces. The first and third
are bounded explicitly, using the totient-divisor identity and Chebyshev theta
for the latter. The new `ExceptionalCharacterBHM` layer proves Lemma 5.3 as an
exact finite weighted inequality. Hermitian symmetry supplies the column bound
from a single Gram-row hypothesis; the weighted prime indicator recovers the
literal dyadic prime sum and has energy equal to the band cardinality; and each
row is split into its diagonal plus `J-1` uniform off-diagonal terms. Exact
division by the band cardinality recovers the normalized `s_Z` estimate, and
the exceptional threshold gives `J Z^(-2/125) ≤ ∑|s_Z|²` by a compiled finite
Markov argument. The large-prime mean/variance estimates of Propositions
6.7--6.8 now hold on the literal source cutoffs conditional on explicit
Burgess. The isolated small-prime exceptional sum is inserted uniformly under
that hypothesis. Exact Markov and Chebyshev bounds, followed by the
deterministic three-branch logarithmic partition, prove the source-facing
Proposition 6.6 probability estimate
`B(8 log₂(x))^50/(H log(z)^2)`. Thus probability normalization is complete
conditional on explicit Burgess; proving that analytic Burgess estimate is
the remaining obstruction to an unconditional Proposition 6.6. The endpoint
now has the source-required quantifier order: one constant is eventually
simultaneous in every admissible `H` and every remainder `m'`. Its exact finite
support identity converts the probability bound into a tuple-cardinality bound
with the product of the 1001 band cardinalities restored. The next direct
Theorem 1.7 layer now performs the fixed-prime-scale part of that sum.
`BadIntervalTypicalCounting` uses the exact lower-endpoint product budget,
identifies the smooth remainder count with `Psi`, and sums the power-of-two
lengths with absolute geometric cost `2`. The representation-value image is
proved to lie in `B¹∩[1,2x]`, and the domain count is reduced exactly to a
uniform fiber-cardinality estimate. That finite assembly is now complete:
`BadIntervalTypicalScales` supplies the moving ordered scale grid;
`BadIntervalTypicalEnlargement` implements the doubled/quadrupled bands;
`BadIntervalTypicalMultiplicity` and `BadIntervalTypicalGlobal` prove the
absolute `1000^1000` fiber bound before and after summing all scale choices;
and `BadIntervalTypicalAssembly` absorbs the PNT band comparison into a factor
tending to zero. Conditional on explicit Burgess, the complete global typical
tuple count is therefore little-o of `badOneTermCount` at one fixed dilation.
`BadIntervalTypicalWeighted` now proves the length-weighted analogue: the
interval length cancels the inverse-length probability factor, the remaining
`O(log₂ x)` length-scale loss is absorbed, and the weighted assembly factor
tends to zero. `BadIntervalTypicalUnion` canonically and injectively embeds
every forward typical interval, whose left endpoint is the tuple product, into
that weighted family. The backward modules now mirror the entire chain with
the symmetric divisibility indicators `v-l`: exact small-prime moment,
large-prime source mean and variance, Markov--Chebyshev normalization, uniform
support count, smooth-remainder/all-scale weighted assembly, and a canonical
injective code whose tuple product is the right endpoint `N+H`. The exact
orientation cover therefore proves little-o for the full actual typical union
at the fixed dilation, conditional on Burgess. The weighted assembly now also
retains an explicit logarithmic saving. `BadIntervalSlowCutoffLogSaving`
preserves the matching `1/log(x)^(1-o(1))` margin through the Proposition 6.5
diagonal and normalizes it by the actual one-term count.
`BadIntervalRecombination` combines the two branches, applies the factor-30
maximal transfer, and proves the resulting local dyadic-window estimate
conditional on Burgess and Lemma 1.6(ii). The needed large prime is supplied
by the proved eventual start-uniform Sylvester--Schur theorem at every
sufficiently large admissible scale. It also proves the
exact finite power-of-two cover of the global nontrivial bad count.
`BadIntervalDyadicSummation` identifies the precise extra regular-variation
input needed here: `badOneTermCount(2^r)/badOneTermCount(2^(r+1))->1/2`. From
that ratio it proves geometric summability after every fixed logarithmic
weight, absorbs the finite prefix, compares the last endpoint in `[x,2x]`, and
derives the exact conditional `TaoTheorem17Conclusion`.
`BadOneTermRegularVariation` now proves the adjacent ratio from the sharp
critical smooth-number dilation limit. It isolates a slowly widening central
prime packet in the exact `B¹` sum, proves all four complementary ranges have
diagonal `o(B¹(x))` mass, uniformizes dilation by `1/2` on the central packet,
and squeezes `B¹(x/2)/B¹(x)` to `1/2`. The completed saddle-main-term
stability shows that `TaoCriticalSmoothSaddleAsymptoticConclusion` implies the
needed dilation limit. The same half-ratio gives
`B¹(x) <= 4 B¹(floor(x/2))`; finite iteration and exact power-of-two
bracketing of every `floor(cx)` prove the full `TaoLemma16iiConclusion`.
 Thus Lemma 1.6(ii) is no longer an independent analytic input. The large-length
 tail and the finitely many fixed-length thresholds also give one start cutoff
 beyond which Sylvester--Schur holds at every length. Since admissible starts
 grow with the dyadic scale, the unrestricted theorem is no longer a dependency
 of Theorem 1.7. Its global finite residual remains independently restricted
 to rows `H>=101`.
 Proving the sharp saddle asymptotic and removing analytic Burgess are the two
 genuine remaining inputs to Theorem 1.7. The
source-exact fundamental-lemma coefficients remain separately open, although
the proved Selberg alternative already supplies the diagonal estimate needed
here.
The finite Lemma 5.4 algebra is now isolated in `FundamentalSieveWeights`: its
divisor-sum weight equals one on the dyadic prime band, its positive-interval
mass is exactly the floor-weighted coefficient sum, and bounded coefficients
have `ℓ¹` mass at most the sieve level. The floor replacement is quantitative:
the mass differs from `X Σ_{d≤R}λ_d/d` by at most `R`, and any upper bound for
that coefficient main mass transfers directly with this additive error. The
remaining sieve task is the actual fundamental-lemma construction proving
squarefree support, nonnegativity, and logarithmic main mass.
An unconditional fallback is now compiled in `SelbergPrimeWeights`. The
library Selberg construction at density `1/d` gives a literal globally
nonnegative divisor weight equal to one on primes above its level, with main
mass at most `2/log R`. Its coefficients satisfy `|λ_d|≤3^ω(d)`, so the exact
finite mass bound has error `R(1+log R)^3` rather than Tao's sharper `R`.
This polylogarithmic loss is harmless for the later power-separated level,
but the source-exact `{−1,0,1}` Rosser construction remains a separate task.
The new `ExceptionalCharacterSelberg` bridge now feeds this concrete weight
through the finite BHM theorem. Exact finite identities remove `n=0`, expand
the weighted correlation, and reindex each divisor restriction as an ordinary
prefix. Pointwise multiplicativity extracts the divisor factor at norm cost
at most one. Consequently the finite normalized second-moment bound has only
one unresolved analytic hypothesis: a uniform Burgess bound for the unshifted
pair correlations of distinct characters.
`ExceptionalCharacterFamilies` now removes the remaining arithmetic ambiguity
from that hypothesis. It packages the primitive moduli `q₁q₂,j`, proves the
pair lcm is `q₁ lcm(q₂,j,q₂,k)`, squarefree, and at most `Z^3.09`, and proves
the raw correlation equals the quotient Dirichlet character at that level for
all natural inputs, including zeros at nonunits. The full normalized family
estimate is therefore reduced to a named cubefree prefix bound.
`ExceptionalCharacterBurgess` refines this to precisely the sieve prefixes
`⌊(2Z-1)/d⌋` and records the source-shaped explicit target with saving
`0.0163`, a fixed lower cutoff, and range `q≤H^3.1`. It now also defines the
literal cube-free condition, proves the squarefree downstream moduli satisfy
it, and encodes the cited `r=7` estimate as
`A H^(6/7)q^(2/49+ε')`. Taking `ε'=1/2000000`, an exact kernel-checked
exponent calculation proves this two-factor estimate implies the decimal
target on the whole range. The primitive-to-imprimitive arithmetic is now
closed as well. Changed-level character values are expressed by an exact
coprimality indicator, Möbius inversion turns every ambient prefix into a
divisor sum of primitive prefixes of lengths `H/d`, and the frozen pointwise
divisor-epsilon theorem absorbs their number after splitting epsilon in half.
Thus the remaining source theorem can be restricted to primitive cube-free
characters with `ε'=1/4000000`; Lean derives the all-character form required
by the quotient-character consumer. This primitive theorem no longer needs
to be supplied on all prefix lengths. The exact complete-period sum is zero,
every prefix equals the prefix of length `H % q`, and the trivial estimate
`|S(H)|≤H` handles the complementary lower range. The remaining analytic
core is precisely `q^(2/7+7ε')<H<q` (equivalently
`q^(2/49+ε')<H^(1/7)`), with a constant at least one. The 1962
prime-modulus precursor and its Lemmas 2--4 proof architecture are pinned
locally. The PDF and TeX source of the modern explicit cube-free treatment
arXiv `2511.17778v2` are now pinned as auxiliary evidence: its Theorem 1.3
isolates the shifted moment, Lemma 2.1 isolates the complete Weil-type sum,
and Lemmas 2.3--2.4 supply the finite gcd-tuple bounds. The essential 1963
composite cube-free source is still not locally retrievable, and the modern
paper is not treated as a substitute proof.
`BurgessMoment` now formalizes the finite front end identified by that source.
The complete shifted `2r`-moment is expanded exactly over ordered tuple pairs;
each term is a complete quotient-character correlation, including at
nonunits. The diagonal set is defined by at most `r` distinct shifts, and an
injective value/label encoding proves its cardinality is at most
`r^(2r)B^r`. Thus a uniform nondegenerate bound `W` yields the standard
two-term moment majorant `r^(2r)B^r q+B^(2r)W`, with `r=7` specialized
literally. The next Burgess task is the composite Weil bound for the
nondegenerate correlations.
The coefficient boundary is now source-literal. `burgessTupleShiftInt`
enumerates the two tagged blocks in `{1,…,B}` and
`burgessTupleDifferenceProduct` is exactly
`A_j=∏_{i≠j}(b_i-b_j)`. Summing the cardinalities of all value fibers proves
that more than `r` values among `2r` positions forces a singleton fiber, so a
nondegenerate tuple always has `A_j≠0`. The relaxed gcd weight, the
`(4r)^ω(q)√q` factor, and `TaoPrimitiveCubefreeBurgessCompleteWeilBound` are
now explicit, and the general and `r=7` moment reductions consume them. The
source gcd-weight sum is now also closed: divisor-multiple counting gives
`∑_{n≤H}gcd(n,q)≤Hτ(q)`, and exact coordinate factorization gives
`∑_uv burgessTupleGcdWeight q uv≤2rB(2Bτ(q))^(2r-1)`. Both moment reductions
now include this bound. The remaining analytic task at this stage is solely
the composite complete Weil estimate itself.
The arithmetic losses have now been converted to the source's analytic
epsilon notation as well. The fixed-base prime-factor theorem absorbs
`28^ω(q)` into `q^(ε/2)`, and the divisor-epsilon theorem absorbs `τ(q)^13`
into the other `q^(ε/2)`. Consequently, for every `ε>0`, the composite Weil
predicate alone implies
`moment≤7^14B^7q+C_εB^14q^(1/2+ε)` for some positive constant `C_ε`.
`BurgessWeilCRT` now closes the exact multiplicative reduction inside the
remaining Weil predicate. A character modulo coprime `mn` factors into
canonical CRT-coordinate characters; the tuple numerator, denominator, and
complete correlation factor accordingly. The factor `(4r)^ω(q)√q` and each
fixed `gcd(|A_j|,q)` contribution are multiplicative, so two local estimates
with the same witness `j` assemble into the relaxed global gcd-weight bound.
Primitivity now descends as well. The changed-level local characters multiply
exactly to the global character; a factorization of one local character
through `d` therefore induces a global factorization through `dn` or `md`.
For a primitive global character, conductor equality and natural-number
cancellation force the local conductor to be the entire local level.
`BurgessWeilIteration` now completes the cube-free recursion. The least-prime
factorization splits a nontrivial cube-free `q` as `p^k n` with `k∈{1,2}`,
coprime factors, and `n<q`. A strong induction keeps one fixed nonzero `A_j`
through all splits, and the final insertion into the relaxed weight proves
the full composite predicate from one local proposition. The next Burgess
task is therefore sharply local: prove the fixed-coefficient complete-sum
estimate for primitive characters modulo `p` and `p^2`. The
coefficient-divisible branch is now closed at both levels by the trivial
modulus bound and the available gcd factor. Consequently the nontrivial
boundary splits into separately stated prime and prime-square estimates when
`gcd(|A_j|,p)=1`.
The prime-square input is now complete. `BurgessWeilPrimeSquare` decomposes
`ZMod (p^2)` into the fibers
`a+pt`, removes singular fibers, and proves that the restriction of a
primitive character to the principal units `1+pt` is a nontrivial additive
character. Writing the reduced numerator and denominator as `F` and `G`, the
stationary polynomial `F'G-FG'` has degree at most `2r`. Exact first-order
product identities turn every nonsingular fiber into an additive-character
sum at frequency `F'/F-G'/G`, which vanishes unless the stationary polynomial
vanishes. The selected coefficient's coprimality makes its tagged root simple
in exactly one of `F,G`, proving that polynomial nonzero. Its at most `2r`
roots give the required `4rp` bound. The prime-modulus Weil estimate is now
the sole local algebraic-geometry boundary.
`BurgessWeilPrime` makes that boundary exact and library-independent. It
rewrites the complete Burgess correlation over `ZMod p` as one multiplicative
character on a product of `r` tagged linear factors times its inverse on a
second such product. The `A_j` coprimality hypothesis gives a unique tagged
root modulo `p`, and primitive prime-level characters are proved nontrivial.
The single proposition `TaoPrimeLinearQuotientWeilBound` requests the bound
`4r√p` for precisely this finite-field sum; checked bridges carry it through
the prime, prime-square, CRT, and cube-free layers. The next analytic task is
therefore to prove this proposition, with no conductor or composite-modulus
bookkeeping left in its statement.
`BurgessWeilPrimePolynomial` now verifies the complete algebraic hypothesis
of the classical theorem. The inverse denominator character is replaced by
the denominator polynomial to exponent `orderOf χ-1`, without changing any
summand. The unique tagged root has multiplicity `1` or `orderOf χ-1`, hence
is not divisible by the character order and rules out an order-th power.
The polynomial splits and its distinct-root finset has cardinality at most
`2r`. `BurgessWeilPrimeLowRoots` now proves this estimate when the polynomial
has one or two distinct roots. Root-multiplicity grouping makes the one-root
sum vanish; an affine reindexing identifies the two-root sum with a Jacobi
sum, whose norm is at most `√p` by the Gauss--Jacobi identities. The remaining
boundary is sharpened further in `BurgessWeilPrimeActiveRoots`. Roots with
multiplicity divisible by `orderOf χ` contribute one off their own zero and
zero at it. The exact active/inactive partition reduces the full sum to the
active-root sum with finitely many deleted inputs; their total norm cost is
absorbed by the original `2 #roots √p` allowance. The remaining task is exactly
`TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore`, restricted to at
least three root multiplicities nonzero modulo the character order.
For the actual cleared Burgess polynomial, `BurgessWeilPrimeThreeRoots`
sharpens this once more. Its degree is exactly `r * orderOf χ`, hence the
active multiplicity sum is divisible by the character order. A formal
fractional-linear equivalence sends one of three active roots to infinity;
degree divisibility cancels the denominator character and reduces the sum to
a two-root Jacobi sum with one deleted input. The `√p+1` estimate and all
inactive corrections fit inside the existing target. The remaining analytic
task is therefore `TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore`, for
degree-divisible split polynomials with at least four active roots.
`BurgessWeilPrimeLargeCharacteristic` removes the finite-characteristic
fringe as well: the trivial complete-sum bound is `p`, and this is within the
target whenever `p ≤ 4D²`, with `D` the distinct-root count. Thus the minimal
remaining contract may simultaneously assume at least four active roots,
degree divisibility, and `4D² < p`.
`BurgessWeilPrimeFourRoots` now isolates the four-root geometry exactly. Its
fractional-linear reindexing reduces that case to a canonical three-point
hypergeometric sum, with one deleted value and no remaining polynomial-root
bookkeeping. The open prime input is therefore the canonical `2√p`
hypergeometric estimate together with the generic degree-divisible case of at
least five active roots in the range `4D² < p`.
`BurgessWeilPrimeSourceResidual` sharpens the latter statement to the exact
cleared family `primeLinearOrderPolynomial p r χ b`; no arbitrary split
polynomial remains on the production route. The same bridge also observes
that the four-root large-characteristic branch forces `p > 64`, so the
canonical hypergeometric input is restricted to that range.
That canonical input is now source-shaped as well: all three finite local
characters are powers of the single ambient `χ`, and their exponents are
normalized to the finite range below `orderOf χ`. The exact modulo-order
transport is complete; only the resulting finite-parameter Weil estimate is
analytic.
The remaining geometry is normalized to Legendre form as well: scaling sends
`(0,λ,μ,∞)` to `(0,1,t,∞)` and costs only a unit-bounded character factor.
Thus the four-root analytic task has one cross-ratio parameter `t ≠ 0,1`.
`BurgessWeilPrimeKummer` now consolidates both residual branches into the
sharp classical theorem: a split polynomial outside the shape
`C(c)*Q^(orderOf χ)`, with `c≠0`, has complete character sum at most
`(t-1)√p`. The tagged nondivisible root multiplicity is proved to exclude
that scalar-power shape, and checked bridges carry this one statement through
the split-polynomial, quotient, and composite contracts. The remaining prime
task is therefore the canonical Kummer finite-field estimate itself; the
Legendre and source-polynomial residuals remain useful lower-dimensional
specializations rather than independent production assumptions.
`ExceptionalCharacterScales` takes `R=⌊Z^0.0001⌋` and proves uniformly that all
requested prefixes eventually exceed the cutoff and meet the period range;
Bertrand proves band nonemptiness. Thus only the published analytic `r=7`
Burgess estimate for primitive cube-free characters in that core range remains
at this boundary.
`ExceptionalCharacterNormalization` identifies the exact
half-open band cardinality with `π′(2Z)-π′(Z)`, transfers the pinned PNT to
strict counting, proves the asymptotic `Z/log Z`, and records the eventual
lower bound `Z/(2 log Z)`. `ExceptionalCharacterAbsorption` now proves the
two diagonal pieces are `O(Z/log Z)` and, under `J≤A Z^(2/125)`, combines the
three exact exponents into `1-1/5000` and obtains an `o(Z/log Z)` off-diagonal
term. The normalized moment constant is independent of `A`; truncation at
`⌊A Z^(2/125)⌋` and the exceptional threshold therefore close the
self-improving argument. Both `J≪Z^(2/125)` and the bounded squared moment now
follow conditional only on explicit Burgess. The analytic Burgess proof
remains.
`ExceptionalCharacterFixedLevel` supplies the downstream consumer bridge.
With `q₂=1`, literal exceptional primitive characters of level `q` form a
separated heterogeneous family, and both its cardinality and squared sum are
preserved exactly. The resulting varying-conductor theorem gives the literal
`J≪Z^0.016`, bounded moment, and general `O(λ⁻²)` tail conclusions conditional
only on explicit Burgess.
`ExceptionalCharacterAggregate` strengthens this to the actual multi-conductor
shape needed downstream. Primitive characters agreeing after lcm lift are
proved to have equal levels and equal original characters. The dependent
sigma over any admissible finite conductor set is therefore one separated
family, with exact total-cardinality and double-moment identities; explicit
Burgess yields a single constant uniform over the entire set. This is the
uniform family input needed by the divisor sets generated from the
small-prime tuple moduli.
`SmallPrimeExceptionalConductors` now performs that finite instantiation. It
unions the nontrivial divisor sets of every actual tuple modulus, proves the
lcm and every member squarefree, and obtains the uniform bound
`d≤taoSmallAntiSievePrimeCutoff(x)^50`. The rounded exponent comparison
`cutoff^50<⌊z^(9/10)⌋` is now proved eventually, so every source selector
above the lower distinguished-prime scale lies in the Lemma 5.1 square-root
range. A maximal finite universe of all admissible squarefree conductors gives
one eventual Burgess-conditional moment constant simultaneously for every
admissible subset and all 1001 selectors. The literal exceptional outer sum
is bounded by that constant times the completed Mertens coefficient and then
absorbed into the principal majorant. The same scale inequality proves
`P_j⁻⁸ cutoff⁵⁰≤1`, so the explicit totient error is absorbed as well. Thus
the entire source-facing small-prime fiftieth moment has a fixed elementary
majorant conditional on analytic Burgess. The large-prime branch now has a
literal unweighted contribution and exact finite mean, second-moment,
variance, and double-covariance identities. Its diagonal is bounded by the
mean; under `H≤lowerPrime`, joint divisibility at two distinct shifts carrying
the same prime is impossible, so all such covariances are nonpositive. The
variance therefore reduces exactly to the mean plus distinct-prime
covariances. The crude/improved estimates of Propositions 6.7--6.8, their
literal dyadic aggregation, the exact source mean/variance bounds, and the
final Markov/Chebyshev normalization are now complete conditional on explicit
Burgess. The deterministic squarefree-log partition places every typical
tuple in the resulting three-branch union and gives the source-shaped
probability bound. Only the analytic Burgess input remains for unconditional
Proposition 6.6 closure.

The character-algebra entry to those propositions is now also compiled. A
single large-prime event is empty or one primitive residue fiber modulo `p`;
a joint event at distinct primes is empty or one primitive residue fiber
modulo `pp'`. Both probability bounds reduce to the existing all-character
1000th-power dyadic prime-average expression.

The exceptional counting itself is now closed conditional on analytic
Burgess. For Proposition 6.7, the number of prime conductors supporting an
exceptional character is bounded by the total character count, with exponent
`2/125`. For Proposition 6.8, a dependent common-factor family retains `p`
  and varies `p'`; the self-improving Lemma 5.1 cardinal proof now exposes one
  constant independent of the family, and selector diagonalization makes the
  bound eventually pointwise uniform in `p`.

The principal part of the probability error is now explicit. The character
sum is split before weak AM--GM, so its main term occurs exactly once. The
principal expectation equals the probability that the tuple product is
coprime to the modulus. If `m'` is coprime to `p` or `pp'`, failure forces a
coordinate collision with one of those primes; uniformity of each coordinate
and primality of the dyadic band give a reciprocal-cardinality bound, followed
by a finite union bound. The one-prime nonprincipal conversion is now
complete: every nonprincipal character modulo a prime is primitive, and away
from the union of exceptional conductors over all ordinary tuple coordinates
the complete moment is bounded by `φ(p) ∑_{j≠0} P_j^(-8)`. This is substituted
directly into the collision estimate to bound deviation from `1/φ(p)`.
For the product modulus, exact conductor regrouping is now complete under the
explicit assumption that every ordinary coordinate band is coprime to `pp'`.
The totient divisor identity then bounds the whole nonprincipal contribution
by `pp' ∑_{j≠0} P_j^(-8)` and supplies the corresponding direct deviation
theorem. That band-separation assumption is now removed. The noncoprime part of a
band is contained in `{p,p'}`, so the ambient and primitive normalized averages
differ by at most `4/card`. Coprimality-free primitive conductor regrouping and
1000th-power convexity yield the explicit correction `(4/card)^1000`, and the
final product-modulus deviation theorem no longer assumes band separation.
The remaining work in Propositions 6.7--6.8 is Burgess-cardinality insertion
and dyadic aggregation of the now source-normalized crude and improved
estimates.
The first direct-counting input is exact:
the primes in `[Z,2Z)` lying in one residue class modulo positive `q` number
at most `⌊2Z/q⌋+1`. The next step is to combine this normalized fiber bound
with frozen tuple coordinates.
The product probability measure is now also converted exactly to finite
counting: its Cartesian prime-band support has measure one, every supported
tuple has the same inverse-product atom mass, and an arbitrary event's
probability equals its supported cardinality times this mass. The
frozen-coordinate bridge is now compiled too: its support has the exact
full-support/missing-band cardinality, a uniform coordinate fiber bound divides
by the exact band size, and pairwise residue rigidity inserts the
`⌊2P/q⌋+1` progression count. Factoring the source product by any ordinary
coordinate and cancelling its coprime complementary cofactor gives the core
single- and joint-divisibility bounds. A coprime/noncoprime event split now
combines this with the proved collision unions, yielding unconditional crude
bounds with respectively one and two explicit collision sums.
The paper's stronger source freezing step is compiled as well. Arbitrary finite
sets of coordinates have an exact support-cardinality cancellation law, and a
general theorem counts selected products lying in one residue class with any
specified representation multiplicity. Unique factorization gives multiplicity
at most `2` for two sampled primes and at most `6` for three. Freezing two
coordinates therefore proves the exact finite Proposition 6.7(i) ratio with
numerator `2(⌊4P₁P₂/p⌋+1)`; freezing three proves the Proposition 6.8(i) ratio
with numerator `6(⌊8P₁P₂P₃/(pp')⌋+1)`. The divisibility events and nonzero
shifts automatically supply the complementary-cofactor coprimality.
The exact ratios are also normalized abstractly. If every selected scale obeys
`P_j≤L·#band(P_j)` and the modulus lies below the selected product range, the
floor-plus-one term is absorbed and the coordinate scales cancel, giving
`16L²/p` in Proposition 6.7(i) and `96L³/(pp')` in Proposition 6.8(i).
The next source specialization derives one common logarithmic loss from the
PNT and the anatomy-scale hypotheses.
That common PNT specialization is now compiled under the precise structure
`TaoPrimeTupleSourceScaleFamily`: all bands are eventually nonempty and obey
`P_j≤4log(z)#band(P_j)` simultaneously. Hence the eventual source bounds are
`256log²(z)/p` and `6144log³(z)/(pp')`. The remaining work here is the exact
modulus/product scale discharge and finite dyadic mean/covariance aggregation.
The improved estimates now reach the literal probability space as well.
Coprimality removes the empty single-event branch and gives the absolute
deviation from `1/φ(p)`; the one- and two-prime upper bounds cover empty events.
Exact multiplicativity of the totient main term and a separate covariance
algebra lemma then give the distinct-prime covariance error needed by the
second-moment sum. The remaining work is its finite dyadic aggregation and
source-scale discharge.
That finite partition is now compiled on the literal anti-sieve indices.
Single conductors and ordered distinct-prime pairs are each separated into
improved and exceptional pieces; all shift multiplicities are preserved, and
the exceptional pieces retain explicit crude majorants. The partition is
inserted into the existing diagonal variance reduction. What remains is the
analytic cardinality and source-scale summation of those finite expressions.
The product exceptional predicate is now reduced to the counted Lemma 5.1
families: the only nontrivial divisors of `pp'` are `p`, `p'`, and `pp'`.
Thus a bad pair lies over an exceptional endpoint prime or in the common-factor
exceptional-partner union. The union over all ordinary coordinate scales has
both its exact sum-cardinality bound and the fixed factor-1000 consequence.
The first-moment block summation is also compiled. The anti-sieve interval is
identified with the source half-open dyadic band, its reciprocal-totient main
sum is eventually at most `4/log R` by PNT, and the remaining improved and
exceptional contributions are kept as explicit uniform-error and
cardinality-times-crude terms. The exact two-band covariance block is now
compiled as well: it preserves the ordered distinct-prime restriction and
literal `(H-1)^2` shift multiplicity, and separates the full band-product
uniform improved error from the exceptional ordered-pair cardinality times a
crude joint bound. That exceptional pair cardinality is now reduced exactly
to exceptional first endpoints, exceptional second endpoints, and the sum of
common-factor partner fibers. The three coordinate aggregates in the
improved errors also have explicit uniform source envelopes from
`P_j=z^(1+o(1))` and PNT, which are composed into the literal one-prime,
joint, and covariance errors. Fixed log-power absorption and source-range
dyadic selector comparisons now give the direct literal bounds
`3R^-1.001` and `C R^-1.001 S^-1`, including the ordered covariance form.
For the exceptional endpoints, the fixed `P_j^0.016` count cannot be
uniformly rewritten as `R^0.02` at the bottom of the modulus range. The new
adaptive threshold `max(P_j^-0.008,R^-0.01)` fixes that mismatch: it remains
inside the fixed exceptional family, and the uniform squared moment plus
Chebyshev gives the required `O(R^0.02)` count after the 1000-coordinate
union. The cofactor embedding now also preserves its complete squared moment;
the moment bound is pointwise uniform in the fixed prime and cofactor set, and
the same adaptive argument gives `O(S^0.02)` partners. These sets now feed the
actual character expansions: adaptive emptiness gives the exact 1000th-moment
tail `P_j^-8+R^-10`, the one-prime error is bounded by
`1003R^-1.001`, and the uniform adaptive joint/covariance errors retain the
ordered `R^-1.001 S^-1` scale. The product partition also keeps the necessary
mixed thresholds—`R` for conductor `p`, `S` for `p'` and `pp'`—and is covered
exactly by the two endpoint sets and the adaptive partner set. The mixed
product moment and literal joint-probability bound compile, and direct
normalization gives the same ordered source power for its joint and covariance
errors. The adaptive one-band probability and two-band covariance consumers
are now compiled with literal shift multiplicities. Their exceptional pair
finset is bounded by the two adaptive endpoint counts plus the pointwise
adaptive partner fibers. These bounds are now composed with explicit Burgess:
the exceptional pair count has source shape
`R^0.02·#band(S)+#band(R)·S^0.02`, and both finite block sums consume this
cardinality together with their normalized improved errors. Uniform crude
specialization and conductor geometry are now inserted automatically. The
literal source range is an exact disjoint union of retained dyadic slices;
one Burgess constant works simultaneously on the whole grid, whose cardinality
is at most `4 log z`. Summing gives `mean ≤ 2000000 H`, off-diagonal covariance
`≤ H`, and `variance ≤ 2000001 H`. This closes the large-prime branch
conditional on the still-open analytic Burgess theorem.

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
and proved nonzero, nonnegative, `C∞`, periodic, and correctly supported. The
contradiction growth
hypothesis already supplies `ε25=3/2-(2/3+η)⁻¹>0` and `K=1`; the cutoff has a
fixed positive inner-rectangle minimum; its integral is real and nonnegative;
and its norm lower bound is reduced to the measure of an explicit good set in
`(H,2H)`, whose reciprocal membership transport is exact. Both source changes
of variables and their Jacobian comparisons are now formalized. The quadratic
fractional band has exact period mass `43/50`; uniformly for `N/H²≥1/2`, its
slice has measure at least `N/(8H²)` and the quadratic reciprocal preimage has
measure at least `H/32`. A finite disjoint unit-cell covering with endpoint
trimming and slow variation now inserts the first fractional coordinate and
gives inner prime-scale measure at least `H/400` for `H≥200`. The fixed
cutoff and Theorem 2.5 constants are now coordinated uniformly, and two
logarithmic powers close the full eventual contradiction conditional on the
specialized Theorem 2.5 conclusion. The arithmetic scale no
 longer depends on unrestricted Sylvester--Schur: the frozen PNT and exact
 binomial-factorization bounds now prove the required large prime uniformly for
 every start at all sufficiently large `H`, hence in particular in the
 quadratic failure window, giving eventual
`N/H²≥1/2` and the final geometric measure bound. The
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
boundary is Theorem 2.5; its Lemma 3.1 consumer is now conditionally complete.

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
callback is complete as well. The exact outer-sum/Cauchy--Schwarz bridge now
identifies the literal product-restricted convolution double block with this
consumer. Bounded product support is enlarged to the canonical Vaughan block,
the actual beta/gamma envelopes contribute `1` and `log(2B)`, and the resulting
conditional theorem bounds the norm square of the literal source Type II
block. A separate triangle theorem reduces the full product convolution norm
to the sum of square roots of arbitrary double-block majorants. The remaining
local assembly problem is therefore the source regime split and asymptotic
summation/simplification across every Type I/II block. The
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

## Historical Burgess amplification frontier (release 2.57)

The exact interval/affine layer is now formalized in
`BurgessAmplification.lean`. In particular, the prefix-to-translate error is
reduced to two boundary intervals, unit multiplication is eliminated exactly,
and the additive average is exchanged into the `burgessShiftSum` appearing in
the proved complete fourteenth-moment estimate.
The coprime multiplier-pair residue map and its multiplicity are now explicit;
the first multiplicity moment and the exact weighted regrouping identity are
proved.

The next bounded research package is the second-moment collision estimate for
the multiplicity of residues `(N+n)/a`. It should feed a finite Hölder
inequality together with
`burgess_shift_fourteenth_moment_le_standard`; only after that should the
`r = 7` choices of `A` and `B` be optimized into
`TaoPrimitiveCubefreeBurgessRSevenCoreBound`.

## Collision-to-Hölder status (release 2.58)

The multiplicity second moment has now been converted exactly into an ordered
collision cardinality, and unit cancellation exposes the cross-multiplied
congruence used by the cited proof. Hölder is no longer an open architectural
edge: its exact powered inequality is compiled for both the multiplicity-
weighted character sum and the original affine Burgess average.

The next target is arithmetic rather than functional analytic: prove the
fixed-`a,c` collision fiber has cardinality at most
`1 + H*gcd(a,c)/max(a,c)` in the source range, then formalize the totient/
divisor summation used to bound the complete collision count.

## Collision-fiber arithmetic status (release 2.59)

The fixed-`a,c` target is now closed in its stronger natural-number form.
Integer determinant divisibility, the `2*A*H <= q` no-wrap argument, and
reduced-multiplier spacing give
`card <= H / (max a c / gcd a c) + 1`. An exact fiberwise decomposition of
the global ordered collision family then yields the sum of these local
majorants over coprime multiplier pairs.

The next bounded package is the elementary gcd/divisor summation converting
that explicit finite sum into the aggregate second-moment bound used by the
pinned Burgess proof. After that, combine it with the compiled Hölder and
fourteenth-moment estimates, control the translation boundary recursively,
and optimize `A` and `B` for `r = 7`.

## Summatory collision status (release 2.60)

The elementary gcd/divisor package is complete. Divisor incidence bounds the
fixed-`c` quotient sum by `H*tau(c)`, the summatory divisor function is
identified with `sum floor(A/d)`, and its real cast is at most
`A*harmonic(A)`. The global collision theorem therefore has an explicit
diagonal term plus `2*H*A*harmonic(A)`, which has the required
`O(A*H*log A)` scale.

The next bounded package is the actual Burgess recursion: average the affine
translations, insert the compiled Hölder estimate and complete fourteenth
moment, and use the `2ab` boundary comparison to shorten the original
interval. The subsequent package is exact `r = 7` parameter selection and
conversion to `TaoPrimitiveCubefreeBurgessRSevenCoreBound`.

## Pre-Hölder recursion status (release 2.61)

The exact averaging equation is now formalized with an arbitrary inductive
majorant `E`. Both shorter endpoint intervals are retained explicitly, and
the affine averages are bounded by the real multiplicity-weighted main term.
Thus the finite structural content of source equation (28) is complete under
the natural condition `A*B <= H`.

The next bounded package is the scalar boundary calculation for
`E(K)=C*K^(1-1/r)*q^((r+1)/(4r^2)+epsilon)` (with the project’s precise
cube-free factor), including the finite `b^(1-1/r)` sum. It should then be
combined with the compiled powered Hölder inequality and moment/collision
bounds before selecting the exact natural parameters for `r=7`.

## Normalized power-boundary status (release 2.62)

The scalar boundary package now compiles in a general form. For every
nonnegative exponent and constants, monotonicity and endpoint comparison give
the required finite boundary estimate, and the positive affine-average
denominator is cancelled explicitly. The recursion now exposes only the
normalized main term `M/(#A*B)` plus
`2*C*(A*B)^alpha*Q`.

The next bounded package is the main term: extract the `2r`-th root from the
powered Hölder inequality and monotonically replace its collision and moment
factors by the existing harmonic and complete-moment upper bounds. Only then
should the proof specialize to `r=7` and commit to floor/ceiling definitions
of `A` and `B`.

## Rooted main-term status (release 2.63)

The powered Hölder estimate has been rooted without loss, and abstract
monotonicity permits direct insertion of the collision and moment bounds. At
`r=7`, the complete normalized recurrence now exposes every scalar factor:
the exact coprime-pair count, the diagonal-plus-harmonic collision term, and
the two-term complete moment beneath a `1/14` power, divided by `#A*B`, plus
the normalized inductive boundary.

The next bounded package is quantitative coprime counting. A source-compatible
lower bound such as `#\{a<=A:(a,q)=1\} >= A*phi(q)/q - 2^(omega(q)-1)` must be
formalized or replaced by a slightly coarser explicit bound that remains
strong enough after cube-free divisor losses. That theorem should feed a
dedicated scalar optimization file rather than further enlarging the finite
amplification module.

## Coprime multiplier status (release 2.64)

The dedicated scalar file now starts with exact Möbius inversion. It proves
the short coprime count is at least its totient-density main term minus
`tau(q)`, and packages the half-density consequence under a transparent
dominance hypothesis. This coarser discrepancy is mathematically sufficient
provided the existing divisor-`epsilon` estimate is paired with a lower bound
for `phi(q)/q`. That pairing is now elementary: the divisor-sum identity for
the totient proves `q/phi(q) <= tau(q)`, so `2*tau(q)^2 <= A` suffices.

The next bounded package should use the existing divisor-`epsilon` estimate to
prove `2*tau(q)^2 <= A` for the intended power-sized `A`. After that, define
the rounded Burgess parameters in this scalar file and
prove `1<=A`, `1<=B`, `A*B<=H`, and `2*A*H<=q` before simplifying the rooted
recurrence.

## Rounded Burgess optimization status (release 2.65)

That bounded package is now compiled. The divisor-square error is eventually
below every floor-rounded positive power. With
`B=floor(q^(1/14))` and `A=H/(K*B)`, explicit lower and upper interval-range
hypotheses yield `1<=A`, `1<=B`, `A*B<=H`, `A<=H`, `2*A*H<=q`, and
`2*tau(q)^2<=A`. The rooted recurrence is cardinality-free, and its collision
bracket has been compressed to `3*H*A*harmonic(A)`.

The next bounded package should absorb `harmonic(A)` and `q/phi(q)` by small
powers of `q`, normalize the two complete-moment summands at
`B asymp q^(1/14)`, and prove the resulting `H^(6/7) q^(2/49+epsilon)` main
term. The inductive boundary must then be made strictly contractive by the
safety factor `K`.

## Burgess exponent status (release 2.66)

Harmonic, reciprocal-totient, and complete-moment losses now have separate
compiled epsilon-power bounds. Exact root algebra yields the main factor
`A^(13/14)*H^(13/14)*q^(3/28+epsilon/14+delta/14)` before division by
`A*B`, while the denominator is exactly normalized to expose that division.
The next package is now pure substitution: use the existing rounded lower
bounds for `A` and `B` to turn these exponents into `H^(6/7)` and `q^(2/49)`,
then choose the safety factor to contract the boundary.

## Rounded substitution status (release 2.67)

The pure substitution package is now compiled. Exact quotient/floor geometry
and real-power identities reduce the normalized parameter factor to
`2*K^(1/14)*H^(6/7)/q^(13/196)`. Combined with the previously rooted moment,
this gives the target main exponent
`H^(6/7)*q^(2/49+epsilon/14+delta/14)` with an explicit constant.

The next bounded package should multiply in `q/phi(q)`, select the three small
loss parameters inside the requested epsilon budget, and expose a single
final main-term constant. Independently, export the stronger rounded geometry
`K*A*B<=H` and use a sufficiently large fixed `K` to make the normalized
boundary coefficient contractive.

## Epsilon allocation and contraction status (release 2.68)

The reciprocal-totient factor is now part of the main estimate, and the
allocation `6*eta/14 + eta/14 + eta/2 = eta` produces the exact conductor
power `q^(2/49+eta)`. Exact integer division also exposes the previously
latent `K*A*B<=H`; at induction exponent `6/7`, any `K` with
`K^(6/7)>=4` makes the affine boundary at most one half, and `K=128` is a
compiled concrete choice.

The next package should instantiate the scalar recurrence with these two
bounds and the complete fourteenth-moment estimate. This will isolate the
remaining analytic complete-Weil theorem from the now-closed parameter and
inductive arithmetic.

## Rounded strong-induction status (release 2.69)

The scalar recurrence now consumes the compiled main and boundary estimates
directly. A uniform coefficient closes under strong induction because every
`a*b` is strictly smaller than `H`; recursive sublengths below the core
threshold are discharged by the trivial character-sum estimate. For all
sufficiently large conductors this proves the primitive Burgess bound on the
whole quadratic no-wrap range
`2*H^2<=128*q*floor(q^(1/14))`.

The next bounded package is the large-length Pólya--Vinogradov bridge. Its
natural formal route is finite Fourier inversion on `ZMod q`, Mathlib's
primitive-character Gauss-sum transform, an exact geometric-sum estimate for
the interval indicator, and a harmonic bound for the nonzero frequencies.
That bridge will extend the medium result to the all-prefix primitive
contract; the prime finite-field complete-Weil theorem remains independent.

## Pólya--Vinogradov completion status (release 2.70)

The proposed Fourier route is now fully compiled. A DFT-squared calculation
establishes the exact Gauss-sum norm for primitive characters at arbitrary
nonzero conductors. Pointwise Fourier inversion, the affine geometric-sum
bound, and a symmetric separated-set integral test give
`|S(N,H)| <= 10*sqrt(q)*(1+harmonic(q))` for `H<q`.

After harmonic absorption, failure of
`2*H^2<=128*q*floor(q^(1/14))` supplies precisely the missing
`q^(45/98)` factor. The large and medium branches therefore have the same
`H^(6/7)*q^(2/49+eta)` endpoint. Finite conductors are absorbed explicitly,
and the proof now reaches the primitive all-prefix, imprimitive cubefree, and
decimal sieve-facing contracts.

The next bounded package is solely the remaining prime finite-field
complete-Weil residual. Once it is discharged, Lemma 5.2 becomes
unconditional and can be inserted into the already compiled exceptional
character and bad-interval consumers.

## Sharp Kummer boundary status (release 2.71)

The prime residual now has a single exact interface,
`TaoPrimeKummerPolynomialWeilBound`. Its coefficient is the sharp
`(t-1)*sqrt(p)`, and its exceptional case includes the nonzero scalar factor
required by the classical theorem. The existing tagged root supplies a
kernel-checked contradiction to that exceptional case via root
multiplicities. Consequently this one estimate implies every complete-Weil
and Burgess consumer already in the graph.

The next analytic package is a proof of this Kummer estimate over `ZMod p`.
No general multiplicative-character Weil theorem is present in the pinned
Mathlib closure; the existing local Stepanov development is specialized to
quadratic/Kloosterman curves and does not by itself discharge arbitrary
character order.

## Small Sylvester--Schur lengths (release 2.72)

`SylvesterSchurSmallLengths` combines monotone binomial-growth propagation
with finite prime certificates. It proves `SylvesterSchurBelow 49`, uniformly
in the unbounded start. The coarse threshold handles lengths through four;
verified small baselines cover lengths five through ten; and the uniform
baseline `T=3H` plus one finite-type certificate closes `11<=H<=48`.

The next useful arithmetic increment should continue beyond length forty-eight
or package a more structural middle-length argument. The unrestricted residual
is now the finite rectangle intersected with `H>=101`.

## Eventual start-uniform Sylvester--Schur (release 2.73)

`SylvesterSchurEventual` proves a stronger result in the direction actually
needed asymptotically: there is one `M` such that every interval with positive
length and start at least `M` has a prime divisor larger than its length. The
proof takes the existing uniform large-length cutoff `B`; lengths at least `B`
use that theorem, while every smaller length satisfies `H^H <= B^B` and hence
uses the fixed-length threshold at start `B^B+1`.

Admissible interval starts satisfy `x <= 4N+1`, so they eventually exceed this
single cutoff. Scale-local variants now carry the resulting large-prime witness
through normalization, maximal transfer, recombination, window bounds, tail
summation, and finite-prefix absorption. The exact endpoint
`taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess` therefore has
only the critical smooth saddle asymptotic and analytic Burgess as hypotheses.

The highest-value next work for Theorem 1.7 is consequently the Kummer/Weil
endpoint in the Burgess stack or the uniform critical smooth-number saddle
asymptotic—not further enumeration of the independent Sylvester--Schur
rectangle.

## Distinct-root Kummer trace (release 2.74)

The Kummer boundary is now in literal trace normal form. For every split
polynomial, `primePolynomialCharacterCorrelation_eq_kummerRootCorrelation` rewrites the
correlation as the leading-character value times a sum of products indexed by
the distinct roots, with exact root-multiplicity exponents.

The converse exceptional-shape algebra is also complete. Dividing every
divisible root multiplicity by `orderOf χ` constructs
`kummerRootPowerBase`; the split factorization proves that the original
polynomial is a nonzero scalar multiple of this base to the character order.
Thus Kummer nondegeneracy is equivalent to the existence of one root whose
multiplicity is not divisible by that order.

`TaoPrimeKummerRootProductWeilBound` is proved equivalent to the prior sharp
polynomial endpoint. The next step is genuinely the finite-field trace bound
`(t-1)*sqrt(p)` itself; the pinned Mathlib closure and local dependencies do
not contain a reusable general multiplicative-character Weil theorem.

## Three-or-more-root Kummer residual (release 2.75)

The sharp distinct-root trace theorem is now unconditional for at most two
roots. A single root gives a translated nontrivial character sum and hence
zero. Two roots reduce by an affine bijection to the already formalized Jacobi
sum, giving exactly `sqrt(p)`, which is the coefficient `(t-1)*sqrt(p)` at
`t=2`.

`TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore` isolates the remaining
case and is proved equivalent to the full polynomial Kummer theorem. Future
Burgess work should therefore target only nondegenerate traces with at least
three distinct roots; redoing splitting or low-root algebra cannot reduce the
remaining dependency further.

## Degree-divisible three-root closure (release 2.76)

The Kummer trace bound is now sharp for every three-root split polynomial
whose degree is divisible by the character order. Exact active/inactive-root
separation leaves either two active characters, handled by the Jacobi-sum
bound plus one deleted point, or three active characters with trivial total
product, handled by the projective two-root reduction plus one deleted point.
Both give at most `sqrt(p)+1 <= 2*sqrt(p)`.

Consequently the full Kummer theorem is equivalent to
`TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible`.
For the degree-divisible cleared polynomials occurring in Burgess, the prime
trace problem therefore begins at four distinct roots. In the unrestricted
generic formulation, only the degree-nondivisible three-root hypergeometric
case joins that four-or-more-root residual.

## Hypergeometric/large-root split (release 2.77)

The converse active-root congruence is now exact: for a split polynomial, the
character order divides the total degree exactly when it divides the sum of
the active-root multiplicities. Therefore a three-active-root,
degree-nondivisible trace has three nontrivial local characters whose product
is nontrivial. Translation sends its roots to `0`, `v-u`, and `w-u`, giving
precisely `TaoPrimeThreePointHypergeometricWeilBoundAt`.

The remaining inactive-root configurations are elementary after at most two
deleted points; characteristics at most four follow from the trivial complete
sum bound. Consequently, under the three-point hypergeometric theorem, the
general sharp Kummer endpoint is equivalent to the pure
`TaoPrimeKummerRootProductWeilBoundFourRootsOrMore` residual. This identifies
two genuine geometric trace inputs and leaves no unresolved three-root
normalization or exceptional-point bookkeeping.

## Degree-divisible four-root closure (release 2.78)

Assuming `TaoPrimeThreePointHypergeometricWeilBoundAt`, the sharp Kummer bound
is now proved for every four-root split polynomial of character-order-divisible
degree. Two active roots cost at most `sqrt(p)+2`; three active roots cost at
most `sqrt(p)+2`; and four active roots cost at most `2*sqrt(p)+1`. Each is at
most the sharp four-root allowance `3*sqrt(p)`.

This gives the equivalent residual
`TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible`. Thus the
degree-divisible Burgess family has no remaining trace case below five roots.
The unrestricted four-root degree-nondivisible case is a genuinely different
geometric trace, while the source-shaped route retains the three-point
hypergeometric theorem and the five-active-root large-characteristic input.

## Four-point normalization and pure five-root residual (release 2.79)

The complementary four-root case is now normalized exactly. If all four
roots are active and the degree is not divisible by the character order,
translation sends them to four distinct finite points
`0`, `v-u`, `w-u`, and `z-u`; the four local characters and their product
are nontrivial. This is precisely
`TaoPrimeFourPointHypergeometricWeilBoundAt`. A reusable deletion theorem
then handles inactive roots, with the worst one-active configuration covered
because four distinct elements imply `p >= 4`.

Thus, conditional on the explicit three- and four-point endpoints, the full
sharp Kummer theorem is equivalent to the pure five-or-more-root predicate
`TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore`. The next finite-field
work is now cleanly separated into proving the two named lower-point
endpoints and the residual trace theorem beginning at five distinct roots.

## Degree-divisible five-root closure (release 2.80)

The five-root projective identity is now formalized. With local characters
of trivial total product, the same Möbius equivalence sends one marked root
to infinity; denominator characters cancel, and the complete sum becomes a
four-point trace minus one value. The four-point endpoint therefore gives
`3*sqrt(p)+1`, which fits the sharp five-root allowance `4*sqrt(p)` after all
inactive-root configurations are included.

The unrestricted exact residual is
`TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible`. The
source-facing improvement is stronger: because
`primeLinearOrderPolynomial` has degree divisible by the character order,
`TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic`
is now sufficient, together with the existing reduced three-point input and
the four-point endpoint, for the entire composite Burgess chain. The next
source-specific geometric trace problem begins at six active roots.

## Source-shaped four-point endpoint (release 2.81)

The five-active-root branch now preserves the fact that every local character
is a power of the single Burgess character. Four exponents are reduced modulo
`orderOf χ`, and scaling one nonzero marked point gives the precise normal
form with finite points `0`, `1`, `t`, and `u`. The resulting open statement
is `TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour`, not the
global endpoint for four unrelated characters.

Together with the existing one-parameter three-point input, this reduced
two-parameter statement discharges exactly five active roots. The other
finite-field task is now the source-specific six-active-root trace residual;
both are clean analytic boundaries with all algebraic normalization and
small-characteristic routing proved internally.

## Six-root reduction and five-point boundary (release 2.82)

Degree divisibility also closes the algebra at six active roots. The verified
Möbius identity sends one root to infinity, cancels the total denominator
character, and expresses the complete sum as a five-point trace minus one
value. The finite trace has five powers of one Burgess character and is
normalized to the three-parameter configuration `0,1,t,u,v`, with all
exponents reduced modulo the character order.

Thus the exact production residual is now
`TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic`.
Proving the three reduced lower-point trace estimates would discharge every
source case through six active roots; the remaining higher-root task begins
at seven active roots.

## Fixed fourteenth-moment source boundary (release 2.83)

Tao's optimization never varies the moment order: it uses `r = 7` throughout.
The production interfaces now reflect that fact. The fixed complete-Weil
predicate is consumed directly by the fourteenth moment and every subsequent
Burgess theorem, while a separate fixed-`Fin 7` local iteration carries the
prime and prime-square estimates through cube-free CRT factorization.

At prime level, `TaoPrimeLinearQuotientWeilBoundRSeven` is supplied by the
three reduced lower-point endpoints and
`TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven`.
Consequently the outstanding higher-root trace problem is no longer
quantified over irrelevant moment orders. The stronger all-orders interfaces
remain available for reuse but are not assumptions of the exact Tao path.

## Seven-root reduction and six-point boundary (release 2.84)

The degree-balanced projective reduction now also covers exactly seven active
roots. Sending one root to infinity cancels the seven local denominator
characters and leaves six finite powers of the ambient Burgess character,
together with one deleted projective value. A `5*sqrt(p)` estimate for that
finite trace therefore fits the required split-polynomial coefficient.

Exponent reduction and scaling produce the four-parameter normal form
`0,1,t,u,v,w` above characteristic `64`. The exact fixed-order production
residual is now
`TaoPrimeLinearOrderPolynomialWeilBoundEightActiveRootsLargeCharacteristicRSeven`.
Thus four reduced lower-point trace endpoints cover every source case through
seven active roots, and the remaining higher-root task begins at eight.

## Finite fixed-order root window (release 2.85)

The `r=7` source polynomial has at most `2r=14` distinct roots. Since the
active-root finset is a subset of the full root finset, the outstanding source
trace theorem is now stated only on the finite cardinality window from eight
through fourteen. The proof is threaded through the fixed prime quotient and
cube-free composite interfaces.

This makes the remaining algebraic reduction plan finite: exact active-root
counts `8,9,10,11,12,13,14` may be treated successively, while no assertion
for a larger root set is relevant to Tao's fourteenth moment.

## Eight-root reduction and seven-point boundary (release 2.86)

The degree-balanced projective calculation now covers exactly eight active
roots. Sending one root to infinity cancels eight denominator characters and
leaves seven finite powers of the Burgess character. The complete sum is a
seven-point trace minus one deleted value, so a `6*sqrt(p)` trace bound gives
the required `6*sqrt(p)+1` active-root estimate and closes the corresponding
split-polynomial case.

Reducing exponents modulo the character order and scaling the first nonzero
point yields the five-parameter normal form `0,1,t,u,v,w,z` for `p > 64`.
The literal `r=7` source residual is therefore the exact finite window
`9..14`; exact cardinality nine is the next algebraic branch.

## Nine-root reduction and eight-point boundary (release 2.87)

The degree-balanced projective calculation now covers exactly nine active
roots. Sending one root to infinity cancels nine denominator characters and
leaves eight finite character powers. The complete sum is an eight-point
trace minus one deleted value, so a `7*sqrt(p)` trace estimate yields the
required `7*sqrt(p)+1` active-root bound and closes the split-polynomial case.

Modulo-order exponent reduction and scaling produce the six-parameter normal
form `0,1,t,u,v,w,z,r₀` above characteristic `64`. The literal `r=7` residual
is now exactly `10..14`; cardinality ten is the next algebraic branch.

## Ten-root reduction and nine-point boundary (release 2.88)

The degree-balanced projective calculation now covers exactly ten active
roots. Sending one root to infinity cancels ten denominator characters and
leaves nine finite character powers. The complete sum is a nine-point trace
minus one deleted value, so an `8*sqrt(p)` trace estimate yields the required
`8*sqrt(p)+1` active-root bound and closes the split-polynomial case.

Modulo-order exponent reduction and scaling produce the seven-parameter normal
form `0,1,t,u,v,w,z,r₀,s₀` above characteristic `64`. The literal `r=7`
residual is now exactly `11..14`; cardinality eleven is the next algebraic
branch.

## Eleven-root reduction and ten-point boundary (release 2.89)

The degree-balanced projective calculation now covers exactly eleven active
roots. Sending one root to infinity cancels eleven denominator characters and
leaves ten finite character powers. The complete sum is a ten-point trace
minus one deleted value, so a `9*sqrt(p)` trace estimate yields the required
`9*sqrt(p)+1` active-root bound and closes the split-polynomial case.

Modulo-order exponent reduction and scaling produce the eight-parameter normal
form `0,1,t,u,v,w,z,r₀,s₀,a₀` above characteristic `64`. The literal `r=7`
residual is now exactly `12..14`; cardinality twelve is the next algebraic
branch.

## Twelve-root reduction and eleven-point boundary (release 2.90)

The degree-balanced projective calculation now covers exactly twelve active
roots. Sending one root to infinity cancels twelve denominator characters and
leaves eleven finite character powers. The complete sum is an eleven-point
trace minus one deleted value, so a `10*sqrt(p)` trace estimate yields the
required `10*sqrt(p)+1` active-root bound and closes the split-polynomial case.

Modulo-order exponent reduction and scaling produce the nine-parameter normal
form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀` above characteristic `64`. The literal `r=7`
residual is now exactly `13..14`; cardinality thirteen is the next algebraic
branch.

## Thirteen-root reduction and twelve-point boundary (release 2.91)

The degree-balanced projective calculation covers exactly thirteen active
roots. Its complete sum is a twelve-point trace minus one deleted value, so an
`11*sqrt(p)` trace estimate yields the required `11*sqrt(p)+1` active-root
bound. Modulo-order reduction and scaling produce the ten-parameter normal
form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀` above characteristic `64`. The literal
fixed-order residual is thereby reduced to exact cardinality fourteen.

## Fourteen-root reduction and thirteen-point boundary (release 2.92)

The final degree-balanced projective calculation covers exactly fourteen
active roots. Its complete sum is a thirteen-point trace minus one deleted
value, so a `12*sqrt(p)` trace estimate yields the required
`12*sqrt(p)+1` active-root bound. Modulo-order reduction and scaling produce
the eleven-parameter normal form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀` above
characteristic `64`.

The structural `2r=14` root cap now eliminates the literal fixed-`r=7`
source-cardinality residual. The remaining Burgess work is analytic: prove the
reduced trace endpoints through thirteen points, then discharge their existing
prime-quotient, composite, amplification, and optimization consumers.

## Erdős--Selfridge source-Theorem-2 bridge (release 2.93)

The stronger theorem used inside the 1975 Erdős--Selfridge proof is now an
exact Lean contract: once `N+H` reaches the least prime `p^(H) >= H`, some
prime at least `H` has product valuation not divisible by the proposed power
exponent. The interval representation, construction and minimality of
`p^(H)`, and the automatic endpoint hypothesis in `H<N` are all proved.

At exponent two, a hypothetical square makes every factorization coordinate
even, so the source witness yields the residual square contradiction. This is
compiled through the full square proposition and both direct Theorem 1.10
consumers. The remaining work is the arithmetic proof of the source
prime-multiplicity theorem itself (or a direct proof of its weaker square
corollary); no online candidate inspected so far supplies a completed Lean
proof.

## Erdős--Selfridge equation (3) (release 2.94)

The counterexample setup is now internal. The canonical `l`-power-free part
of a natural is defined by reducing every factorization coordinate modulo
`l`; the complementary quotient coordinates reconstruct an exact `l`-th
power. Both reconstructed naturals are nonzero, their factorizations are
proved exactly, and the coefficient valuations are all below `l`.

Prime uniqueness has also been sharpened from `H<p` to the source boundary
`H<=p`. Under a Theorem-2 counterexample this localizes every large-prime
product valuation to its unique factor, so all coefficient primes are `<H`.
The resulting simultaneous interval theorem is precisely source equation (3).
The next proof obligation is Lemma 1's distinctness of products of fewer than
`l` coefficients; after that comes the deletion/divisibility Lemma 2.

## Erdős--Selfridge Lemma 1 (release 2.95)

The first combinatorial lemma of the 1975 proof is now complete. A
Sylvester--Schur prime in the counterexample interval forces source equation
(2), `H^l<N`. Gcd bounds for two equal-cardinality interval subproducts then
give equation (4), while explicit binomial and geometric estimates bound the
largest possible interval-product gap.

For the stronger assertion, a putative positive-rational `l`-th-power ratio
is reduced by gcd cancellation to coprime numerator and denominator. The
resulting lower power-gap estimate contradicts the strict interval upper
bound. Multiplying equation (3) over each selected subfamily transports the
contradiction to products of the canonical power-free coefficients. Thus
`erdosSelfridgeLemmaOne_of_failure` exposes the complete source Lemma 1 from
the already named Sylvester--Schur contract. The next internal source task is
Lemma 2's maximal-valuation deletion/factorial-divisibility step, followed by
the paper's remaining case and counting arguments.

## Erdős--Selfridge Lemma 2 and equation (21) (release 2.96)

The maximal-valuation deletion argument is now formalized at the source's
exact finite cardinality. For every prime below `H`, Lean selects a position
whose interval element has maximal valuation. At every other position the
canonical coefficient valuation is bounded by that of the position distance.
The exact identity for all such distances is
`m!*(H-1-m)!`, and the standard binomial divisibility places it in
`(H-1)!`.

The image of prime choices can be smaller than `π(H-1)` when choices collide.
It is therefore extended inside the interval index set to an exact deletion
set of that cardinality. The surviving coefficient product proves equation
(9), and its survivor count is exactly `H-π(H-1)`. Specializing to exponent
two bounds the one removed valuation per prime by one and proves equation
(21): the full squarefree-coefficient product divides `(H-1)!` times the
product of primes below `H`. The next source task is Section 3.1's
large-length comparison, equations (22)--(23), followed by the explicitly
finite small-length cases.

## Erdős--Selfridge squarefree density (release 2.97)

The first combinatorial input to equation (22) is now exact. The theorem
`card_filter_dvd_Ioc_add_of_dvd` counts multiples of a divisor of the block
length in every translated interval. Inclusion--exclusion then proves that
the multiples of `4` or `9` have cardinality twelve in `(N,N+36]`.

Since squarefree naturals are divisible by neither `2²` nor `3²`,
`card_erdosSelfridgeSquarefreeBlock_le` proves the cited upper bound 24.
`card_filter_squarefree_interval_offsets_le` supplies the same statement in
the established `N+(i+1)` indexing. Next, order the distinct squarefree
coefficients and combine this density estimate with the finite base range to
derive the cleared-denominator form of equation (22); after that come the
2- and 3-adic ledger of equation (23) and the finite residual cases.

## Erdős--Selfridge equation (22) (release 2.98)

The product lower bound is now complete. The 36-block recurrence and a finite
small-prime-square base prove `3*Q(M)≤2*M` from `M=44` onward. The first 64
squarefree values are exactly the naturals at most 103 avoiding the squares
of `2`, `3`, `5`, and `7`; Lean verifies their cardinality and strict product
inequality by kernel reduction, without `native_decide`.

Prefix-cardinality identities for `Finset.orderEmbOfFin` prove this product is
minimal among all 64-element positive squarefree sets. Maximum deletion plus
the cumulative density bound propagates
`3^H*H! < 2^H*∏a` to every `H≥64`. Source Lemma 1 supplies distinctness of the
canonical coefficients, so `powerFreePart_two_equation22_of_failure` is the
exact counterexample-facing endpoint. The next task is equation (23): compare
the 2- and 3-adic valuations in equation (21), then insert the explicit
primorial bound.

## Erdős--Selfridge pre-equation-(23) ledger (release 2.99)

`ErdosSelfridgeSquareValuations.lean` performs the exact algebraic part of the
next source line. The primorial factorization is one at each prime below `H`;
equation (21) can therefore be sharpened by extracting all powers of `2` and
`3` on both sides. The resulting divisibility theorem is combined with the
strict equation-(22) endpoint to obtain
`powerFreePart_two_preEquation23_of_failure`.

The next proof task is now sharply isolated: bound the factorial valuations
from below and the coefficient-product valuations from above, then transport
those natural bounds to the paper's real exponents and constant `14/3`.
After the primorial estimate rules out `H≥71`, Section 3.2's finite residual
cases remain.

## Erdős--Selfridge valuation bounds (release 3.00)

`binary_digits_sum_cast_le_logb_succ` and
`ternary_digits_sum_cast_div_two_le_logb_succ` provide the exact digit-sum
inputs to Legendre's formula. They yield
`factorization_factorial_two_source_lower` and
`factorization_factorial_three_source_lower`.

For the coefficient side, `card_oddTwoValuationInterval_rec` and
`card_oddThreeValuationInterval_rec` recursively count interval elements with
odd local valuation. Their discrepancy theorems give the source bounds for
`γ` and `δ`, after exact identification with the factorization of the
canonical coefficient product.

The complete chain is assembled in
`powerFreePart_two_preEquation23_logarithmic_of_failure`. The next task is now
only the real-power simplification from that theorem to
`(3/2)^H 2^(2H/3) 3^(H/4) < (14/3) H^2 ∏_{p<H} p`, followed by the primorial
estimate and the residual finite lengths.

## Erdős--Selfridge equation (23) (release 3.01)

`two_logarithmic_power_eq` and `three_logarithmic_power_eq` evaluate the
logarithmic losses exactly. `erdosSelfridge_equation23_root_factor_le` proves
the remaining root factor is at most `4H²`, which is absorbed by `14H²/3`.
The public endpoint `erdosSelfridge_equation23_of_failure` is therefore the
literal displayed inequality from the paper.

Next: formalize the cited primorial upper bound strongly enough to contradict
equation (23) in the large-length range, then enter Section 3.2's finite
residual cases.

## Erdős--Selfridge eventual primorial contradiction (release 3.02)

`ErdosSelfridgePrimorial.lean` connects the local prime product to Mathlib's
primorial and transfers the frozen Chebyshev asymptotic to the eventual bound
`prod_{p<H} p <= 3^H`. Exact rational comparisons show that the left side of
equation (23) is `B^H` for a base `B>3`; a standard little-o theorem then
absorbs `(14/3)H^2`.

The endpoint `exists_erdosSelfridgeSquareLargeLengthThreshold` excludes the
square-case failure above an extracted threshold. The remaining source work
is effectiveness: formalize the explicit primorial estimate used for the
paper's cutoff, then discharge the finite residual lengths in Section 3.2.

## Erdős--Selfridge finite lengths three through five (release 3.03)

`ErdosSelfridgeFinite.lean` supplies the reusable finite-candidate theorem
`length_le_card_erdosSelfridgeSquareCoefficientCandidates_of_failure`.
Distinctness from Lemma 1 and prime support from equation (3) place all
canonical coefficients among the divisors of the prime product below `H`.

Exact candidate counts exclude `H=3` and `H=5`. For `H=4`, the candidates
are exhausted, their product is `36`, and equation (3) reduces failure to a
square product of four consecutive integers. The next task is the source's
`H=6` exceptional modulo-`5` case, followed by the small-prime counts through
`H=70`.

## Erdős--Selfridge length six (release 3.04)

The source's exceptional `H=6` split is complete. The nonexceptional branch
uses an exact modulo-five enumeration to produce five coefficients supported
on `2,3`, too many for the four candidates. In the class `5 | N+1`, the
middle four positions avoid five, exhaust those candidates, and have square
coefficient product; their equation-(3) decompositions contradict the
four-consecutive theorem.

`not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_six`
packages all finite lengths completed so far. The next source boundary is the
small-prime counting argument beginning at length seven.

## Erdős--Selfridge length seven (release 3.05)

An exact enumeration of `N mod 5` proves that at least five of the seven
positions avoid the prime five. Equation (3) then places the associated
canonical coefficients among the four squarefree products supported on
`2,3`, while Lemma 1 makes them distinct. This closes `H=7`.

`not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seven`
packages the completed range `3 <= H <= 7`. The next source boundary is
`H=8`, where the ordinary five-coefficient count has the exceptional class
`7 | N+1` and `5 | N+2`.

## Erdős--Selfridge length eight (release 3.06)

The source's exceptional `H=8` split is complete. Divisibility by `5` and
`7` is reduced to `N mod 35`, and all closed residue computations are checked
by the kernel. Outside `7 | N+1` and `5 | N+2`, at least five coefficients
are supported on `2,3`, contradicting their four possible values.

Inside the exceptional class, the terms `N+3` through `N+6` avoid both large
primes and exhaust `1,2,3,6`. Their canonical decompositions force a square
product of four consecutive integers. The combined endpoint now reaches
`H=8`; the next ordinary small-prime count begins at `H=9`.

## Erdős--Selfridge lengths nine through thirteen (release 3.07)

The source's five-coefficient count is now formalized in two prime-stable
blocks. Reduction modulo `35` handles the first nine positions and persists
through length eleven. Reduction modulo `385` handles the first twelve
positions and persists through length thirteen.

After removing the relevant primes above three, all surviving coefficients
divide six; five distinct values therefore cannot occur. The combined finite
endpoint reaches `H=13`. The next task is the `H=14` count, where the prime
`13` joins the excluded support and a direct union bound should replace a
large modulus enumeration.

## Erdős--Selfridge lengths fourteen through seventeen (release 3.08)

`ErdosSelfridgeFiniteCounts.lean` introduces the scalable counting layer.
The union of positions divisible by `5,7,11,13` has cardinality at most the
sum of the four individual interval-multiple counts. Exact counts at lengths
fourteen and fifteen remove the one-unit slack needed at the boundary.

Five terms remain for every `14 <= H <= 17`, and their coefficients inject
into `1,2,3,6`. The next boundary is `H=18`, requiring the same construction
with prime `17` added.

## Erdős--Selfridge lengths eighteen through twenty (release 3.09)

The sharp ceiling sum over arbitrary excluded-prime sets supplies five usable
terms throughout `18..20`. A generic transfer theorem proves their canonical
coefficients are coprime to the excluded-prime product and therefore divide
six. Distinctness gives the five-to-four contradiction. The next finite source
range begins at `H=21`.

## Complete finite square range (release 3.10)

The arbitrary-prime-set framework closes all `21 <= H <= 70` at once.
Kernel computation checks the fifty ceiling-sum inequalities and prime-product
factorizations; nine distinct coefficients must lie among the eight divisors
of `30`. Together with earlier releases, Section 3.2 is complete for
`3 <= H < 71`. The remaining square-case task is the paper's explicit
Section 3.1 cutoff for `H >= 71`.

## Explicit Section 3.1 split (release 3.11)

The actual prime products for all 226 lengths `71..296` now satisfy a closed
integer certificate strong enough to reverse equation (23). Above that range,
the rational base `31335/10000` and a ratio induction give the paper's exact
growth cutoff `H=297`. The finite and large branches are assembled into the
square conclusion under the sole remaining proposition
`ErdosSelfridgeThreePrimorialConclusion`; proving this elementary `3^H`
primorial bound is the next boundary.

## Hanson three-primorial theorem (release 3.12)

`ErdosSelfridgeHanson.lean` closes that boundary.  Hanson's Sylvester sequence
gives a factorial denominator whose quotient is divisible by every prime below
the target length.  A source-aligned finite truncation at `2,3,7,43` is made
quantitative with the integer weights `903,602,258,42,1`; clearing the common
denominator `1806` converts the entropy comparison into natural-number
arithmetic.

The remainder primorial is absorbed by strong induction.  Exact base and
initial-gap certificates handle every length at least `1400`, while twenty-five
monotone endpoint computations cover the finite prefix.  The resulting theorem
`erdosSelfridgeThreePrimorialConclusion_hanson` supplies the previously named
contract unconditionally.  The Erdős--Selfridge square branch now has only the
independent unrestricted `SylvesterSchurConclusion` boundary left.

## Factorial Sylvester--Schur cutoff (release 3.13)

The remaining global contract now uses a substantially sharper finite
reduction.  `SylvesterSchurFactorialThreshold.lean` compares the ascending
factorial lower bound `(N+1)^H` with the existing small-prime envelope for
`choose (N+H) H`.  Since `N+H <= 2(N+1)`, the gap
`H! 2^r < (N+1)^(H-r)` forces a prime factor larger than `H`.

At the exact exponent `r=pi(H)`, every start at or above
`H! 2^pi(H)+1` is closed.  The weaker but familiar `H! 2^(H-1)+1` threshold
is also exported.  Combining the exact cutoff with the existing large-length
tail reduces `SylvesterSchurConclusion` to a smaller finite rectangle; the
next task is to layer stronger central/large-upper-index inequalities over
the remaining lengths `49` and above.

## Sylvester--Schur through one hundred (release 3.14)

The existing `3H` propagation mechanism remains effective for the next
fifty-two lengths.  `SylvesterSchurHundred.lean` checks the baseline inequality
at `3H` for every `49<=H<=100` and verifies every start with `N+H<3H` in one
bounded certificate.  The resulting `sylvesterSchurBelow_oneHundredOne`
theorem is uniform over all starts.

The exact-prime-count factorial rectangle now begins at `H=101`.  Further
brute-force enlargement remains possible but grows quadratically; the next
scalable boundary is a stronger large-upper-index or central-range inequality.

## Square-root central envelope (release 3.15)

`SylvesterSchurSqrtEnvelope.lean` supplies that scalable boundary in exact
arithmetic form.  Splitting at `sqrt n` bounds the low-prime factorization by
`n^sqrt(n)`.  Above the split, binomial valuations are at most one.  Under the
contradiction hypothesis that no prime divisor exceeds `k`, the central
assumption `2k<=n` and the three-multiple valuation lemma eliminate every
supported prime in `(n/3,k]`.

After applying Hanson's primorial bound, the contradiction reduces to the
single explicit inequality
`k * (n^sqrt(n) * 3^(n/3+1)) < 4^k`.
The next step is an exact logarithmic or monotonicity proof of this inequality
on a sufficiently large central region, followed by a finite bridge down to
the current `H=101` frontier and combination with the large-start cutoff.

## Explicit central tail (release 3.16)

The numerical gap is now unconditional on the full central strip.  The proof
avoids an existential analytic cutoff: elementary block induction gives
`x<=2^(sqrt(x)/16)` for `sqrt(x)>=320`, and hence
`(3H)^sqrt(3H)<=2^(H/4)` for `H>=34134`.  Writing `H=4q+r`, another induction
shows that the remaining polynomial factor times `162^q` is smaller than
`256^q`.  Monotonicity then handles every `2H<=n<=3H` simultaneously.

The next scalable region is `n>3H`, where the `n/3` support cutoff no longer
improves on the no-large-prime cutoff `H`.  The natural next layer is a
sublinear square-root envelope on a growing noncentral range, followed by the
factorial large-start criterion; the bounded bridge remains
`101<=H<34134`.

## Effective all-start tail (release 3.17)

The noncentral large-length region is now closed.  At upper index `1024H`,
Mathlib's explicit Chebyshev inequality and exact decimal-free rational
margins prove the full small-prime binomial-growth inequality.  The local
growth monotonicity lemma propagates it to every larger index.  Below that
baseline, the square-root/Hanson envelope is controlled using
`log H<=sqrt(H)/1000`, itself obtained from the antitonicity of
`log x/sqrt x` at the explicit cutoff `4^101`.

This replaces the earlier ineffective PNT length endpoint by the concrete
tail `H>=4^101`.  The exact remaining problem is now a genuinely explicit
finite rectangle: `101<=H<4^101` and starts below the prime-count factorial
cutoff.  Further work should reduce that enormous length endpoint sharply
before kernel certification, using tighter explicit prime-count margins and
additional interval decompositions.

## Sharpened effective all-start tail (release 3.18)

The proposed tightening has now reduced the effective tail from `4^101` to
`250000`.  The transition point is `64H`: below it,
`log H<=sqrt(H)/40` absorbs the square-root/Hanson term, while the explicit
Chebyshev estimate establishes binomial growth at the endpoint and
monotonicity handles all larger starts.

The outstanding unrestricted Sylvester--Schur task is now the finite
rectangle `101<=H<250000` below the exact prime-count factorial start cutoff.
The next useful step is a kernel-checkable length-block certification or a
further analytic split that reduces this remaining length range.

## Prime-counted effective all-start tail (release 3.19)

The square-root split now retains the exact number of low primes, replacing
the exponent `sqrt(n)` by `pi(sqrt(n))`.  A finite endpoint certificate plus
reduced-residue counting modulo `210` proves `pi(m)<=m/4` for all `m>=120`.
This reduces the near-branch logarithmic cost enough to close every upper
index through `64H` from `H=10000`.  The corresponding bound
`pi(H)<=H/4` also supplies the far-branch baseline at `64H`, with release
3.18 covering lengths at least `250000`.

The outstanding unrestricted Sylvester--Schur task is therefore the finite
rectangle `101<=H<10000` below the exact prime-count factorial start cutoff.
A length-block certificate or another arithmetic refinement must discharge
that rectangle; unrestricted Sylvester--Schur is still not claimed.

## Bounded prime-count bridge (release 3.20)

The exact kernel certificate `6*pi(m)<=m+84` on `100<=m<800` matches the
square-root range for `6000<=H<10000` below the transition `n=64H`.
Together with `log H<=13*sqrt(H)/100`, it closes that near branch.  The far
baseline already works from `H>=2200`, so every start is now closed once
`H>=6000`.

The outstanding unrestricted Sylvester--Schur task is the finite rectangle
`101<=H<6000` below the exact prime-count factorial start cutoff.  Further
work needs either a sharper bounded envelope, a smaller transition, or direct
length-block certification.

## Adaptive-transition tail (release 3.21)

The bounded prime-count estimate is sharpened to `4*pi(m)<=m+12` for
`60<=m<400`.  Rather than retain one transition across the bridge, the proof
uses `16H` on `2200<=H<3000` and `20H` on `3000<=H<6000`.  This balances the
near square-root cost against the far condition `H<C^3` and closes both
regions exactly.

The outstanding unrestricted Sylvester--Schur task is now the finite
rectangle `101<=H<2200` below the exact prime-count factorial start cutoff.
The adaptive method can plausibly be iterated, but direct length-block
certificates become increasingly competitive at this scale.

## Finite prime-count tail to 512 (release 3.22)

The adaptive split is refined to transition `5H` on `512<=H<625`, `6H` on
`625<=H<1134`, and `5H` on `1134<=H<2200`.  Sparse exact prime-count
certificates prove `pi(H)<=H/5` and `pi(H)<=H/6`; after the anchor
`pi(1906)=291`, four exact counts of residues coprime to `210` cover the rest
of the upper band without costly larger prime-count evaluations.  The matching
near logarithmic estimates and far binomial baselines close every start.

The outstanding unrestricted Sylvester--Schur task is now the finite
rectangle `101<=H<512` below the exact prime-count factorial start cutoff.
At this scale, direct length-block certification is the natural next route.

## Central finite bridge to 121 (release 3.23)

Direct bounded certification shows that the central binomial baseline
`(2H)^pi(H)<choose(2H,H)` already holds throughout `121<=H<512` except at
five isolated lengths.  For `139,140`, the near square-root envelope reaches
the exact baseline `n=281`; for `199,200,201`, it reaches `n=403`.
Monotonicity propagates each baseline to every later start.

The outstanding unrestricted Sylvester--Schur task is now only the twenty
length rows `101<=H<121` below their exact prime-count factorial cutoffs.
These rows require a stronger local certificate because the present
prime-counted envelope already fails at their first admissible upper index.

## Unrestricted Sylvester--Schur and square Erdős--Selfridge (release 3.24)

The remaining twenty length rows are now closed.  A single exact central
baseline at upper index `243` works for every `101<=H<121`, and one bounded
kernel certificate verifies every one of the 420 admissible earlier starts.
Together with release 3.23, this proves the unrestricted
`SylvesterSchurConclusion` with no residual rectangle.

The square specialization of Erdős--Selfridge needed by Tao's Theorem 1.10
is then an unconditional consequence of this Sylvester--Schur theorem and
the already formalized Hanson input.  It is no longer an external hypothesis
of the Theorem 1.10 assembly.  The remaining boundary for Theorem 1.10 is
Tao's Theorem 2.5 together with Proposition 2.3(ii), the Baker--Harman--Pintz
short-interval prime input.

## Literal Type II convolution bridge (release 3.25)

The analytic Type II endpoint is no longer detached from the source
convolution.  The literal Vaughan double block is rewritten exactly as a
product-restricted outer sum; Cauchy--Schwarz passes to the squared inner sum;
the bounded support is enlarged without loss; and the actual beta and gamma
coefficients are inserted with bounds `1` and `log(2B)`.  Composing this with
the mixed Weyl--Vinogradov estimate gives the conditional source-block norm
square bound.  Exact double-block decomposition and the triangle inequality
also reduce the full convolution norm to the square-root sum of block
majorants.

Next, prove the named Vinogradov proposition and close the small/large block
regime splits strongly enough to sum those majorants with the required
logarithmic saving.  The Type I estimates and finite Fourier assembly must then
be combined with the completed Type II block interface.

## Complete finite Type II family split (release 3.26)

The small-band cases are now eliminated at the arithmetic coefficient level.
When the outer dyadic scale is below the common subdivision budget, the
Möbius-tail restriction is zero provided `2*budget≤U`; the inner divisor tail
vanishes analogously under `2*budget≤V`.  Hence the conditional source theorem
is only invoked for large--large pairs, exactly where its block geometry is
available.

The resulting piecewise block majorant is summed over the entire canonical
double family in one public theorem.  Since that family has exactly
`(log₂ B+1)^102` members in each coordinate, a uniform square majorant incurs
the explicit factor `(log₂ B+1)^204` after square-root summation.  The next
Type II task is no longer finite bookkeeping: it is the uniform comparison of
the source choices `U,V≈P^(1/3)`, the block scales, and the displayed majorant,
followed by logarithmic exponent absorption.  The Vinogradov proposition
itself remains the analytic boundary.

## Canonical cube-root Type II cutoffs (release 3.27)

That source-parameter comparison is now formalized.  The natural cutoff is
fixed to `⌊B^(1/3)⌋₊`; logarithmic little-o estimates show that it eventually
contains twice the full `(log₂ B+1)^101` subdivision budget, while the strict
gap `1/4<1/3` absorbs floor rounding and yields the outer lower scale whenever
`P≤B`.

The finite family argument now follows actual coefficient support.  Dyadic
bands wholly below either cutoff vanish, blocks whose filtered product support
is empty vanish, and a witness in every remaining block gives product scale
at most `2B`.  Hence the global phase hypothesis
`2B*(log B)^d≤|N|` implies the blockwise reciprocal-phase hypothesis.  The
canonical public theorem fixes both cutoffs and has no quantified block-scale
assumptions.  The next Type II task is purely analytic: establish
`VinogradovExponentialSumEstimate` and collapse the explicit square-root sum
to the requested logarithmic saving.

## Canonical Type II geometry and majorant compression (release 3.28)

The remaining finite choices and first layer of asymptotic geometry are now
removed.  The derivative orders are fixed to `{5,6}`.  Every surviving outer
endpoint exceeds `B^(1/4)`, every surviving doubled inner dyadic scale exceeds
`2B^(1/4)`, and each canonical block length is at most
`B/(log B)^100`.  The exact outer block cardinality and component logarithm
are consequently replaced by their geometric bounds.

The resulting `vaughanTypeIICanonicalGeometricBlockMajorant` is proved to
dominate the exact source block majorant, with the component-count factor
compressed to an absolute constant times `log B*K`.  The next step is to use
the product-scale and quarter-power inequalities to control its reciprocal
phase and inverse-endpoint powers, then absorb the square root and the
`(log₂ B+1)^204` family factor.  This remains conditional on proving the named
Vinogradov estimate.

## Scale-local Type II exponent ledger (release 3.29)

The common-width fallback is no longer the sharp path.  The production
majorant retains widths `2^s/(log B)^100` and `2^t/(log B)^100`.  Exact product
support bounds the underlying dyadic product by `B` and both analytic
endpoint monomials by `B²`.  Expanding the expression in Lean gives the
literal denominator exponents `298`, `197`, and `297`.

The diagonal term also uses survival beyond the inner cutoff: its cubic
monomial is at most `B²/B^(1/4)`, giving a genuine power saving before any
family count.  This power-saved majorant now bounds every exact source block
and is propagated through the full conditional convolution.  Next, convert
the phase factor using `(log B)^d≤F`, convert the inverse endpoint using the
quarter-power lower bound, and perform the square-root family summation.  The
high-scale Vinogradov proposition remains the analytic input to this chain.

## Block-independent Type II decay ledger (release 3.30)

Those three comparisons are now formalized.  On every surviving nonempty
block, the global phase inequality gives
`F^(-1/1024)≤(log B)^(-d/1024)`, while the outer cutoff gives
`K^(-1/1024)≤B^(-1/4096)`.  Cutoff and empty-support branches remain exactly
zero, so one block-independent majorant controls the complete family.

The nested powers are flattened in Lean and the diagonal quotient is exactly
`B^(7/4)`.  Consequently the full conditional Type II convolution is at
most `(3 log B)^204` times the square root of one explicit ledger containing
only `B`, `P`, `d`, and `T`.  The next algebraic step is to add the source
upper comparison `B≤2P`, choose `d` and `T` from the target exponent, and
absorb the fixed power savings and constants into `B/(log P)^A`.  This
remains conditional on the named high-scale Vinogradov estimate.

## Arbitrary Type II logarithmic saving (release 3.31)

The remaining absorption is now complete.  A generic real-power lemma proves
that every fixed negative power of `P` eventually dominates any prescribed
negative power of `log P`.  Under `P≤B≤2P`, this controls both fixed-power
terms and gives `log B≤2log P`.  The phase and source-error terms are combined
with their denominators by exact rpow arithmetic.

For a target saving `S`, the squared-block exponent is `E=2S+408`: the factor
two comes from square-root extraction and `408=2*204` pays for the full
double-family count.  The explicit choices
`d=2048S+216064`, `T=2S+111`, and Vinogradov parameter
`(2S+113)/3` satisfy every ledger inequality exactly.  The complete canonical
Type II convolution is therefore `O(B/(log P)^S)` for arbitrary `S≥0`,
conditional on `VinogradovExponentialSumEstimate`.  The Type II algebraic
branch is finished; the next Theorem 2.5 work is the analytic Vinogradov
proposition, quantitative Type I, and Fourier recombination.

## Literal Type I convolution bridge (release 3.32)

The finite Type I reduction is now attached to the actual source convolution,
rather than remaining a generic rescaling lemma.  One canonical outer
Vaughan block is rewritten exactly as a product-restricted weighted Type I
outer sum.  When the source interval is `[a,b)` and `m>0`, its inner support
is exactly `[⌈a/m⌉,⌈b/m⌉)`; the phase parameters become
`N/m` and `M/m^j` with no rounding approximation.

Both source coefficient systems are inserted.  The Möbius cutoff costs one,
the convolved cutoff costs `log(2B)`, and triangle reassembly covers the
complete canonical outer family.  The logarithmically weighted inner sum is
fed directly into the proved `2 log` Abel bound.  The next bounded Type I
task is therefore analytic: derive a uniform logarithmic saving for every
exposed unweighted initial subinterval from the high-scale reciprocal-phase
estimate, then absorb the single outer-family count and coefficient losses.

## Cutoff-active Type I family loss (release 3.33)

The provisional Type I bound no longer estimates indices where the outer
coefficient is zero. Active first-term indices obey `mâ‰¤U`, and active
second-term indices obey `mâ‰¤UV`, directly from the two Vaughan support
theorems.

## High-frequency exterior geometry (release 3.61)

The stationary estimate now covers every subinterval when the stationary
point lies in the ambient dyadic block, and the exterior-left range
`0 <= s <= P/2` has a source-scale first-derivative bound. For `M=N`, the
identity `s=-2q₂/q₁` makes this exterior-left condition eventual uniformly
on each fixed Fourier box. Same-sign modes are now controlled by the total
phase scale even when the quadratic coefficient dominates.

The next bounded task is to encode the finite sign/axis/high/low partition and
absorb its finitely many modewise constants into the target logarithmic
saving.

## Specialized all-mode partition (release 3.62)

The finite sign/axis/high/low case split is now encoded modewise for `M=N`,
`j=2`. It yields arbitrary logarithmic saving uniformly for every retained
mode on a natural half-open dyadic subinterval. The fixed Fourier-box radius
is absorbed into the eventual threshold, so the opposite-sign stationary
point always lies in the exterior-left chamber.

The next bounded task is finite Fourier-box summation, followed by the exact
endpoint comparison between an arbitrary real order-convex interval and its
natural `Ico` core. The quantitative PNT and Vinogradov propositions remain
explicit analytic inputs.

## Specialized finite Fourier assembly (release 3.63)

The retained Fourier box is now summed exactly, with its fixed coefficient
`ℓ¹` norm absorbed into the target logarithmic saving. The next bounded task
is the arbitrary-real-interval bridge: identify the natural `Ico` core of an
order-convex subset of `[P,2P]`, compare prime sums exactly, and bound the two
short integral endpoint pieces.

## Arbitrary-interval natural core (release 3.64)

The natural core and exact prime-sum identity are now formalized, together
with the sharp two-unit symmetric-difference volume bound for a nonempty
core. Next: prove the generic set-integral difference estimate, discharge the
empty-core geometry, and absorb both endpoint errors into the arbitrary
logarithmic saving.

## Arbitrary-interval finite Fourier closure (release 3.65)

The generic set-integral comparison, capped core, composite top-endpoint
case, and empty-core unit-cell geometry are complete. The resulting theorem
gives every fixed finite Fourier polynomial an arbitrary logarithmic saving
uniformly over measurable order-convex real dyadic intervals.

The next bounded task is the quantitative reconstruction step for a general
smooth periodic weight. The existing coefficient decay and uniform Fourier
convergence are qualitative; the proof must retain a `P/(log P)^A` rate while
the truncation radius varies, or instead sum a frequency-dependent mode
majorant directly. The two analytic propositions remain explicit inputs.

## Exact smooth Fourier-tail reconstruction (release 3.66)

The reconstruction remainder is now isolated exactly. A smooth periodic
weight differs from its retained Fourier box by no more than the discarded
coefficient `l1` mass, which is bounded by `27 * taoC3Norm W` times the
universal radial cubic-envelope tail. This bound has been carried through the
full arbitrary-real-interval discrepancy.

Next: prove a concrete inverse-power bound for the radial tail, choose a
polylogarithmic radius that absorbs it into `P/(log P)^A`, and generalize the
mode partition from a fixed box to that growing box by spending frequency
growth inside the available stretched-log parameter margin.

## Quantitative growing-box reconstruction (release 3.67)

That task is complete. The cubic radial tail is bounded by a universal
summable `5/2` mass times `(R+1)^(-1/2)`. At
`R(P)=ceil((log P)^B)`, every retained frequency fits a fixed Vinogradov
constant at epsilon/2. The resulting mode theorem, coefficient-normalized
finite assembly, arbitrary-interval reduction, and smooth reconstruction are
uniform in all data quantified after the eventual natural-scale threshold.

Next: pass this eventual natural-scale estimate to the literal all-real-scale
specialized contract, including the bounded initial range. Independently, the
named quantitative PNT and Vinogradov propositions remain the genuine
analytic hypotheses to discharge.

## Real-scale specialized contract closure (release 3.68)

The real-scale and bounded-initial-range task is complete.
`SpecializedRealScale.lean` proves exact prime-set preservation at
`Q=ceil(P)`, a unit endpoint-strip integral error, monotone transfer of the
Vinogradov range, real-exponent logarithmic normalization, and a compact-range
crude estimate. These combine in
`taoTheorem25Specialized_of_analyticInputs :
ClassicalMangoldtDiscrepancyLogSaving → VinogradovExponentialSumEstimate →
TaoTheorem25SpecializedConclusion`.

Next: discharge the two named analytic propositions. The scale, interval,
Fourier reconstruction, and bounded-range parts of the specialized Theorem
2.5 contract are no longer open.

Block cardinalities now compress every uniform callback `Q`. Summing the
exact canonical family gives losses `(logâ‚‚ B+1)^102 U Q` and
`(logâ‚‚ B+1)^102 log(2B) UV Q`. The next analytic package should instantiate
`Q` uniformly for active `m`, using Abel summation for the logarithmic inner
and the reciprocal-phase estimate directly for the other inner.

## Type I scale and ceiling transfer (release 3.34)

The source-to-inner scale bookkeeping is now exact.  Rescaling by an active
outer index preserves `reciprocalPhaseScale` at the real scale `P/m`, while
rounding up to `ceil(P/m)` can only decrease it.  Ceiling division also sends
every source subinterval of `[P,2P)` into the rounded dyadic interval
`[ceil(P/m),2ceil(P/m))`.

Consequently the source upper condition `F(P) <= (P/m)^4` implies the
fourth-power low-scale condition at the rounded Type I scale.  The next
bounded task is not further rescaling: it is an endpoint subdivision or
wrapper that supplies the four-step differencing margin and effective-error
premise on each resulting fiber piece.

## Quadratic Type I Weyl subdivision (release 3.35)

That endpoint wrapper and subdivision are now formalized.  Ten
ceiling-rounded blocks suffice once the inner dyadic scale is at least ten.
The exact short-interval sum identity reconstructs the original dyadic sum,
and every nonempty block automatically has room for its interval plus four
optimized differencing ranges.

The local effective error is also reduced to one source-scale inequality.
Across `[D,2D]`, the quadratic reciprocal-phase scale is between one quarter
of its value at `D` and that value; this controls both the high-scale and
inverse-scale terms.  The remaining task is a uniform comparison of the local
two-term widths with a source expression, followed by the finite ten-block
sum and insertion into the Type I active-support estimates.

## Uniform quadratic Type I subintervals (release 3.36)

The local-width comparison and finite summation are now complete. Both terms
in the local Weyl width are controlled at the dyadic source scale: the
high-scale quotient decreases, while the inverse scale loses at most the
factor four isolated in release 3.35. One uniform block majorant therefore
sums with the exact factor ten.

The argument is generalized from the whole band to arbitrary subintervals,
supplying precisely the prefix theorem required by the logarithmically
weighted Type I term. Next, instantiate it at `D=ceil(P/m)` with parameters
`(N/m,M/m^2)`, propagate source budgets over active `m`, and feed the resulting
`Q` into both Type I family theorems.

## Rescaled active Type I callbacks (release 3.37)

The literal substitution and callback insertion are now complete. At each
active `m`, the rounded dyadic geometry and fourth-power transfer feed the
uniform ten-block estimate. Its arbitrary-subinterval form supplies every
prefix required by finite Abel summation, so both unweighted and logarithmic
inner fibers have explicit rescaled bounds.

The complete Vaughan families now consume those bounds with the exact active
support losses from release 3.33. The remaining quantitative Type I problem
is a source-parameter simplification: prove the named admissibility predicate
for every active `m`, dominate the displayed rescaled majorants by a common
logarithmically saving `Q`, and absorb the `U`, `UV`, coefficient, and family
factors. No convolution or endpoint reconstruction remains in that step.

## Exact Type I high/low regime split (release 3.38)

The source does not place every Type I fiber in the low-scale Weyl range.
This is now reflected exactly: transformed scale below `D^4` enters the
ten-block Weyl theorem, while transformed scale above `D^4` enters the
Vinogradov component estimate. The common maximum majorant is uniform over
all subintervals, so the unweighted, logarithmic, and complete-family layers
need no further regime bookkeeping.

The high branch is also connected to the existing source-parameter
arithmetic. Its derivative cutoff and `10^-3` smallness premise follow
eventually from the exponential frequency bound once `D` retains a fixed
positive power of the ambient scale. The next task is therefore sharply
localized: prove the low-branch effective-error budget for canonical active
indices and bound the two explicit majorants strongly enough to absorb the
active-family losses.

## Automatic Type I source admissibility (release 3.39)

The low-branch budget is now closed by a direct numerical reduction: under
`F(D) <= D^4`, its high-order contribution is `O(1/D)`, its subdivision term
is fixed, and its inverse-scale term is controlled by the source lower bound.
The ceiling comparison loses only an absolute factor four.

Canonical Vaughan active support also supplies the missing geometry. The
cube-root source cutoff is at most twice `ceil(P/m)`, so every active fiber
has rounded length at least `B^(1/4)` eventually. This simultaneously gives
the absolute threshold and the positive logarithmic fraction needed in the
two hybrid branches. Both Type I families therefore obtain admissibility
directly from global source frequency hypotheses. The next target is no
longer a regime or support argument: it is the explicit logarithmic
absorption and weighted summation of the hybrid majorants.

## Reciprocal-weighted Type I family summation (release 3.40)

The formerly uniform family callback discarded the decisive dependence of a
fiber on its outer index: `D=ceil(P/m)`. The new aggregation layer retains a
bound proportional to `P/m`. Exact active-support containment then converts
the outer sum to `harmonic U` in the first Type I family and `harmonic (UV)`
in the second, before the already exact short-interval family count is paid.

This removes an apparent polynomial loss and leaves only logarithmic factors.
The next analytic task is now well posed: give separate absorbed bounds for
the low Weyl and high Vinogradov envelopes, each proportional to `P/m`, and
dispatch them through the new harmonic family theorems. A branch-sensitive
envelope is preferable to the current maximum, since the unused Weyl formula
need not be small on a high-scale fiber.

## Complete quantitative Type I closure (release 3.41)

The branch-sensitive envelope is now implemented. High fibers are bounded by
the existing source Vinogradov component estimate, and low fibers reduce to
the explicit width `(1/D + 16/(log B)^d)^(1/1024)`. Active support supplies
`D>=B^(1/4)`, so both branches have a uniform reciprocal-weighted bound.

The two complete canonical Type I families consume this estimate with only
harmonic outer losses. The exact logarithmic ledger costs 104 powers, and
the final exported theorems give every requested saving `S` under
`S+106<=3A` and `1024*(S+105)+1<=d`. The next bounded task is no longer Type
I analysis: combine this result with the completed Type II family theorem and
the exact Vaughan decomposition to obtain the corresponding Mangoldt
reciprocal-phase estimate, before prime and Fourier transfer.

## Quadratic Mangoldt Vaughan assembly (release 3.42)

The completed Type I and Type II estimates now meet in the exact Vaughan
identity. The canonical cutoff term vanishes above the cube-root cutoff, and
the remaining log-Type-I, prime-Type-I, and Type-II convolution sums are
combined with their literal signs and supports. Choosing the Type II phase
exponent `2048*S+216064` also satisfies the Type I budget, so one theorem
delivers arbitrary logarithmic saving for the full quadratic Mangoldt phase
sum.

The next bounded task is interface normalization. The combined theorem still
states the Type I reciprocal-phase-scale inequalities and the Type II
absolute-frequency inequalities separately. These should be derived from one
source-facing range for `N`; after that, the established prime partial-
summation and Fourier machinery can consume the Mangoldt estimate.

## Unified quadratic source range (release 3.43)

That normalization is now complete. At positive natural scale,
`F(N,N,2,P)<=2|N|`; conversely, the source lower bound on `|N|` yields both
the logarithmic phase-scale lower bound and `64<=F`. The final quadratic
Mangoldt theorem therefore exposes only the source's lower and upper
absolute-frequency bounds.

The next bounded task is the prime transfer: convert the logarithmically
weighted Mangoldt phase estimate into the unweighted prime exponential sum,
control prime powers, and feed the resulting mode estimate into the existing
smooth-periodic Fourier layer.

## Quadratic Mangoldt-to-prime transfer (release 3.44)

That prime transfer is now complete. Exact endpoint arithmetic places every
half-open prefix into the existing prime-power-tail interface. The explicit
tail has a fixed quarter-power saving, hence is eventually smaller than any
prescribed negative logarithmic power. Subtracting it from the uniform
Mangoldt prefix estimate gives the logarithmically weighted prime estimate;
reverse Abel summation then removes `log p`.

The exported high-frequency quadratic prime bound uses precisely the unified
source range from release 3.43. The next bounded task is Fourier completion:
control the logarithmic integral for each nonzero mode, sum those modes, and
combine them with the low-frequency and zero-mode contributions.

## Diagonal Fourier bridge (release 3.45)

The diagonal `(1,1)` mode now reaches the literal Fourier discrepancy. The
prime sum is definitionally transported to the completed `(N,N)` reciprocal
phase estimate, while a genuine integration-by-parts argument bounds the
logarithmic integral by `6*P^2/(|N|*log P)`. Their triangle-inequality
combination is exported under the same unified source frequency range.

This exposes the next analytic task precisely. A general Fourier mode uses
the unequal coefficients `(q1*N,q2*N)`, whereas the present Vaughan source
chain is diagonal. The exact general-mode identity and derivative are now
formalized, including nonstationarity for same-sign coefficients; opposite
signs can create a stationary point. The next bounded release should
generalize the Type II, Type I, Mangoldt, and prime endpoints to the unequal
parameters and split the integral analysis by this stationary geometry before
attempting mode summation. Low-frequency and zero-mode estimates remain a
separate final branch.

## Unequal Type II high-pair bridge (release 3.46)

The high-scale half of the Type II split now retains independent reciprocal
coefficients. The exact transformed phase, fixed Vinogradov envelope,
eventual logarithmic absorption, decay-kernel callback, and canonical
Vaughan-block specialization all compile with `(N,M)`. Separate exponential
upper bounds yield the same factor-five transformed-scale budget.

The next bounded task is the complementary low-scale half. Its present
distance-kernel proof controls the full source scale through the linear term
by using `N=M`. For independent coefficients, the quadratic transformed term
must be included using the inner band lower bound. Once that comparison is
formalized, the existing near/far aggregation can be generalized and the
result propagated through the complete Type II family.

## Unequal Type II low-pair bridge (release 3.47)

The quadratic transformed coefficient now supplies the missing lower bound on
the source phase scale whenever both inner variables lie in the positive
dyadic band. Together with the transformed linear coefficient, this removes
the `N=M` dependence from the low-scale Weyl distance kernel.

The near/far and low/high splits have been generalized and instantiated on a
canonical Vaughan inner block; the convolution bridge then yields the actual
weighted double-block estimate. The next bounded task is to generalize the
finite double-family summation and its majorant-compression chain. Once that
is complete, the already-general Type I estimates can be recombined with Type
II to obtain unequal Mangoldt and prime estimates for nonzero Fourier modes.

## Unequal prime source closure (release 3.48)

The complete Type II block family, its compressed majorants, and arbitrary
logarithmic saving now retain independent coefficients. An exact synthetic
diagonalization at each block reuses the established scalar compression
ledger while preserving the unequal phase scale. Combining this with both
Type I families gives the full unequal Mangoldt estimate under one lower
condition at scale `4*P`; prime-power removal and reverse Abel summation then
give the unweighted prime estimate whenever the quadratic coefficient is
nonzero.

The next bounded task is the Fourier split. Modes with zero quadratic
coefficient need a linear-phase source estimate, while nonzero modes need
their logarithmic integrals bounded according to same-sign nonstationary and
opposite-sign stationary geometry. Only after those branches are available
should the low-frequency, zero-mode, and finite Fourier sums be assembled.

## Same-sign unequal Fourier modes (release 3.49)

Both same-sign chambers now reach the literal Fourier discrepancy. The
positive chamber uses the reciprocal derivative factor `A*t+2*B` to define
an exact integration-by-parts amplitude; its derivative is nonnegative for
`t>=2`. Endpoint and total-variation control give a dyadic bound inversely
proportional to the linear coefficient. Complex conjugation proves the
negative chamber without duplicating the analytic calculation.

The next bounded task is the opposite-sign split at the possible stationary
point `t=-2*B/A`. Away from that point the same integration-by-parts weight
can be used on subintervals with a quantitative derivative lower bound; a
short neighborhood of the point needs a length estimate. Coordinate-axis
modes, especially the zero quadratic coefficient excluded by Type II, remain
a separate branch.

## Stationary near/far geometry (release 3.50)

The critical point and near/far split are now exact. The derivative numerator
is `A*(t-t0)`, and an interior critical point converts the source phase scale
into `|A| >= (16/5) P L`. Consequently points at distance at least `δ` have
derivative magnitude at least `(2/5)Lδ/P^2`. The central interval has the
sharp elementary length cost `2δ/log P`, and the original integral is exactly
the sum of the two far pieces and this central piece.

The next bounded task is a formal first-derivative cancellation lemma adapted
to each far piece. The reciprocal derivative need not be globally monotone,
so the proof should split at the single turning point of the phase derivative
or establish bounded variation directly. Balancing that estimate against the
central length term will select `δ` and close the opposite-sign chamber.

## Optimized interior stationary cancellation (release 3.51)

That far-piece task is complete. The amplitude derivative is nonpositive on
the left and on the right up to `3t0/2`; the remaining right tail satisfies a
uniform pointwise derivative bound and is integrated explicitly. The full
interior split is at most
`64P^3/(Aδ log P) + 2δ/log P + 160P^2/(A log P)`. Inserting the source-scale
lower bound for `A` and choosing `δ=P/sqrt L` gives
`50P/(sqrt L log P)` for `L>=4`.

The next bounded task is to replace the wholly interior neighborhood by its
intersection with the source interval, treating the one-sided and fully
clipped cases. Then conjugation can close the other opposite-sign chamber.
Coordinate-axis modes remain separate.

## Complete nonzero stationary chamber (release 3.52)

Endpoint clipping and sign conjugation are complete. The same optimized bound
holds whenever the critical point lies anywhere in the source interval, even
within `P/sqrt L` of an endpoint. The deterministic result is transported to
the literal Fourier mode and combined with the unequal prime estimate while
keeping `L` explicit for later logarithmic specialization.

The coordinate-axis split began with the pure quadratic axis. It has a
nonstationary logarithmic integral and can reuse the nonzero-quadratic prime
theorem. The pure linear axis requires a separate Type II path because its
transformed quadratic coefficient vanishes.

## Pure quadratic coordinate axis (release 3.53)

The pure quadratic axis is complete. Its amplitude derivative is positive,
the two-endpoint variation estimate gives `16P^3/(|B|log P)`, and the exact
identity `F=|B|/(16P^2)` converts this to `P/(L log P)`. The unequal prime
estimate then supplies the full axis discrepancy.

The next bounded analytic task was the pure linear Type II branch. Its
correlation has a nonzero transformed linear coefficient but vanishing
quadratic coefficient, so it requires linear specializations of both the Weyl
and Vinogradov paths.

## Pure-linear Type II pointwise chamber (release 3.54)

The pure-linear integral estimate and the two pointwise Type II branches are
complete. The derivative critical sets vanish identically. Consequently the
high-scale conditional Vinogradov estimate applies on the full interval, while
the low-scale internal four-step Weyl estimate bypasses critical-component
decomposition. The latter includes the exact short-block geometry, far-pair
inverse-scale bound, effective-error estimate, and four-kernel decay theorem.

The next bounded task is to aggregate these pointwise bounds through the Type
II double-block family, then reuse the existing Vaughan source-block,
Mangoldt, prime, and Fourier layers. This propagation is required before the
pure-linear coordinate axis can be declared complete. Low modes and final
Fourier assembly remain separate tasks.

## Complete pure-linear Type II source family (release 3.55)

The pointwise bounds are now aggregated through arbitrary short double
blocks, canonical Vaughan dyadic blocks, and literal weighted-convolution
double blocks. The finite family sum, decay absorption, and explicit
arbitrary-log-saving compression are complete in
`LinearAxisTypeIISourceBlock.lean`.

The next bounded analytic task is the pure-linear Type I path. Both the
log-weighted and prime-coefficient Vaughan families currently use the
nonzero-quadratic Type I bridge. They need the same zero-critical-set
specialization already established for Type II. Once those two estimates are
available, the existing exact Vaughan assembly can be reused for Mangoldt and
prime propagation.

## Complete pure-linear coordinate axis (release 3.56)

The pure-linear Type I path is complete. The low branch specializes the
four-step Weyl estimate to the empty critical set, the high branch specializes
the conditional Vinogradov estimate, and the existing Type I rescaling and
finite-family majorants yield both logarithmic-saving Vaughan families.

Those families combine with the release-3.55 Type II theorem in the exact
Vaughan decomposition. Prime-power removal and reverse Abel summation produce
the unweighted prime estimate, and the existing pure-linear integral theorem
then gives the literal prime-minus-integral Fourier discrepancy. The next
bounded task is the low-frequency/zero-mode partition and final finite Fourier
assembly.

## Low-frequency discrete-to-continuous bridge (release 3.57)

The elementary bridge is complete. The logarithmically weighted reciprocal
character is uniformly Lipschitz on a positive dyadic interval, every sample
is compared with its unit-cell integral, and exact telescoping gives the
full-interval error `2*pi*(j+1)*F/log(P) + 1/log(P)^2`.

The next bounded analytic task is to formalize a classical quantitative PNT
input with arbitrary logarithmic saving for Mangoldt partial-sum discrepancy,
then transfer it through Abel summation and prime-power removal to this
integer/integral comparison. After that, the zero mode and the finite
high/low Fourier partition can be assembled.

## Quantitative-PNT consumer (release 3.58)

The complete weighted Abel consumer is now formalized. A uniform bound `B`
for ordinary Mangoldt discrepancy partial sums yields an explicit bound for
the Mangoldt/log sum minus the logarithmic integral. The missing classical
PNT is stated independently as a global prefix estimate with every integral
logarithmic saving, and that proposition implies the required uniform dyadic
bound.

The next bounded task is higher-prime-power removal for the `Lambda/log`
normalization, giving the literal unweighted prime sum. Then the zero mode and
the finite high/low Fourier partition can be completed. The quantitative PNT
contract itself remains an external analytic obligation.

## Low-frequency prime endpoint (release 3.59)

Higher-prime-power removal for `Lambda/log` is complete. The literal
unweighted prime sum is now compared with the logarithmic integral under the
single global quantitative-PNT contract, and the result has been transported
to every integer Fourier mode. The zero mode is an explicit specialization.

The next bounded task is to absorb the displayed polylogarithmic factors into
an arbitrary target saving under the low-frequency phase-scale cutoff. That
uniform statement can then be joined to the completed high-frequency chambers
inside the finite Fourier box.

## Low-frequency absorption complete (release 3.60)

The displayed polylogarithmic factors are now absorbed rigorously. Under the
global quantitative-PNT contract, every mode with phase scale at most
`(log P)^D` satisfies any prescribed `P/(log P)^S` bound, uniformly on the
dyadic interval.

The next bounded task is the finite high/low partition. Before assembly, the
opposite-sign, nonzero-coefficient chamber with stationary point outside the
summation interval must be checked against the existing nonstationary source
theorems.

## Quantitative-PNT source bridge (release 3.69)

The low-frequency hypothesis is now connected exactly to the conventional
classical theorem statement. `QuantitativePNTBridge.lean` converts an eventual
de la Vallée Poussin bound for `Chebyshev.psi` into the half-open complex
Mangoldt discrepancy used throughout node 73. The conversion accounts for
the endpoint `Λ(k)` and proves stretched-exponential-to-logarithmic absorption
for every natural exponent.

Next: prove `ClassicalChebyshevPsiDeLaValleePoussin` by completing a
quantitative PNT contour/zero-free argument, and prove
`VinogradovBilinearPolynomialNontrivialEstimate` (which already implies the
named Vinogradov proposition with the compiled constant shifts). The frozen
dependency supplies sharp Perron approximation and a qualitative PNT, but no
terminal quantitative `ψ` estimate, so neither obligation is silently
discharged by that dependency.

## Unconditional quantitative PNT (release 3.70)

The quantitative-PNT task above is now complete.
`ClassicalQuantitativePNT.lean` uses the frozen sharp Perron theorem, Ford's
proved asymptotic zero-free region after its finite-low-zero rectangle patch,
and the frozen global Jensen count. The zero sum is controlled with a finite
low-zero reciprocal constant and a coarse quadratic multiplicity count; the
square-root-logarithmic Perron height supplies the classical stretched-
exponential error.

Next: close `VinogradovBilinearPolynomialNontrivialEstimate`. The remaining
source-facing gap is the degree-uniform critical-VMVT coefficient-growth
bound isolated in `VinogradovOptimalWooley.lean`; the explicit Ford moment
route is formally known to be weaker than the fixed `2^-18` target.

## Effective-degree Vinogradov completion (release 3.71)

The preceding agenda item is closed after correcting its degree choice. The
source applies Taylor with a large remainder cutoff but applies the
mean-value theorem only to `k=floor(4 log F/log X)`. At this effective degree,
the quarter-block saving dominates the fixed `2^-18` target. Ford handles the
large-degree tail and a finite maximum handles all smaller critical degrees.

The specialized Theorem 2.5 and Theorem 1.8 are now unconditional. The next
public-endpoint analytic boundaries are independent: the sharp critical
smooth-number dilation asymptotic and the prime finite-field Weil input for
Theorem 1.7, and Proposition 2.3(ii)/Baker--Harman--Pintz for Theorems 1.9 and
1.10.

## Tilted saddle distribution (release 3.72)

`SmoothNumberSaddleTilt` now constructs the normalized tilted mass on the
positive `y`-smooth integers and proves that its total mass is one. Its
log-partition function is exactly `phiZero`; its first and second derivatives
are `-phiOne` and `phiTwo`. The finite count has the exact factorization
`Psi(X,y) = exp(phase) * cutoffFactor`, with `cutoffFactor` in `[0,1]`.

`SmoothNumberSaddleLocalLimit` proves that the existing critical saddle
asymptotic is equivalent to the explicit local-limit target
`cutoffFactor * saddleGaussianScale -> 1`. Thus the smooth-number side of
Theorem 1.7 is now reduced to a concrete Gaussian local-limit estimate for a
kernel-normalized distribution; that estimate remains open, as does analytic
Burgess.

## Probability characteristic function (release 3.73)

`SmoothNumberSaddleProbability` realizes the tilted weights as a probability
measure on logarithmic size and evaluates its characteristic function as the
absolutely convergent series of those masses. At the saddle, the existing
log-partition derivative identities give exact center `log X` and positive
variance `phiTwo`. The centered, variance-normalized characteristic function
now has a checked Fourier expansion with atoms
`(log n - log X) / sqrt(phiTwo)`.

The next smooth-number task is no longer to construct the probabilistic
object: it is to bound this explicit series on small, intermediate, and large
frequencies and feed those estimates through a local-limit inversion theorem.

## Prime-local Fourier product (release 3.74)

`SmoothNumberSaddleEulerCharacteristic` now provides the exact finite Euler
product for the complex smooth Dirichlet series and hence for the tilted
characteristic function. The local normalized factor is precisely
`(1-a)/(1-a exp(i theta))`, with `a=p^(-sigma)` and `theta=t log p`.

Its squared norm is formally reduced to
`(1-a)^2 / ((1-a)^2 + 2a(1-cos theta))`, and these factors multiply exactly
for the centered variance-normalized saddle law. The next analytic step is to
turn elementary lower bounds for `1-cos theta` into uniform product decay,
with a Taylor expansion on the central frequency window and an integrable
minor-arc bound outside it.

## Central Gaussian envelope (release 3.75)

`SmoothNumberSaddleFrequency` proves the first uniform estimate on the exact
prime product. The principal-period inequality
`1-cos(theta) ≥ 2theta^2/pi^2` supplies a rational local contraction, and a
central-window estimate converts this to a Gaussian exponential. The exponent
coefficient is proved equal to `smoothSaddleSecondPrimeTerm`, so the global
coefficient is exactly `phiTwo`, not a comparison surrogate.

At the saddle, normalization by `sqrt(phiTwo)` gives
`|characteristic(t)| ≤ exp(-t^2/pi^2)` whenever
`|t| log y / sqrt(phiTwo)` is below the explicit two-prime margin. The next
step is an asymptotic lower bound on `phiTwo` strong enough to make this window
grow, followed by a minor-arc product estimate.

## Explicit central radius (release 3.76)

`SmoothNumberSaddleCentralWindow` defines the exact radius
`pi/2*(1-2^(-sigma))*sqrt(phiTwo)/log y`. It proves positivity, exact
equivalence between `|t|` lying below this radius and the local phase condition,
and the squared and unsquared Gaussian envelopes on the resulting interval.

The asymptotic interface is now precise: the already proved saddle limit
`sigma → 1`, together with `log y/sqrt(phiTwo) → 0`, implies that the radius
tends to infinity. Thus the next central-frequency task is a curvature lower
bound strong enough to prove that ratio limit. Minor-arc product decay and
Fourier inversion follow as separate tasks.

## Critical curvature lower bound (release 3.77)

The central-radius growth problem is complete. At the moving comparison point
`1-8 log(u)/log(y)`, the endpoint prime-counting bound makes `phiOne` exceed
`log X`, so this point lies below the exact saddle. The second saddle sum is
proved antitone, and the exact secant identity between the saddle and one
therefore gives
`phiTwo/log(y)^2 ≥ u/(16 log u)` eventually.

It follows that `log(y)/sqrt(phiTwo) → 0`, the explicit central radius tends
to infinity, and every fixed normalized frequency is eventually governed by
the universal Gaussian envelope. The next tasks are product decay on the
complementary frequency ranges and a checked Fourier inversion argument.

## Gaussian finite-product transfer (release 3.78)

The global fixed-frequency central-limit step is now compiled. The exact
center `log X` distributes over the prime-local means, so the normalized
characteristic is a finite product of centered prime factors. Their curvature
shares are nonnegative and sum to one. A telescoping contraction estimate,
combined with `|exp(-x)-(1-x)| <= x^2`, proves convergence to the Gaussian
product whenever the summed local quadratic remainder vanishes and the
largest share tends to zero.

The latter condition is unconditional: on `sigma >= 1/2`, one prime
contributes at most `20 log(y)^2`, hence its normalized share is at most
`20 log(y)^2/phiTwo -> 0`. The immediate next task is therefore the explicit
third-order estimate for the centered geometric prime factor. After that,
complementary-frequency decay and Fourier inversion remain.

## Prime-local Taylor closure (release 3.79)

The centered geometric exponent law now has exact mean zero and variance
`a/(1-a)^2`, together with a uniform third absolute centered moment bound
`<= 4000a` on `a <= 4/5`. A global cubic bound for the pure-imaginary
exponential gives local quadratic error `<= 16000 |u|^3 a`.

The geometric characteristic is proved equal to the centered saddle Euler
factor. Summing over source primes costs at most
`16000 |t|^3 log(y)/sqrt(phiTwo)`, which vanishes in the critical regime.
Thus fixed-frequency convergence to the standard Gaussian characteristic is
unconditional. The next analytic task is uniform decay outside the expanding
central range, followed by a checked Fourier inversion/local-limit argument.

## One-sided Laplace target (release 3.80)

The cutoff factor is now exactly a one-sided Laplace moment of the centered
normalized logarithmic law. Its rate is `sigma*sqrt(phiTwo)`, the full
Gaussian prefactor is `sqrt(2*pi)` times that rate, and the rate diverges in
the critical regime. The critical saddle theorem is equivalent to this
normalized moment tending to one. The remaining task is thus a genuine
shrinking-scale local limit: complementary-frequency estimates must be strong
enough to justify inversion at this diverging rate.

## Central saddle integral (release 3.81)

`SmoothNumberSaddleCentralIntegral.lean` now carries out the complete
central-frequency limit. The exact normalized kernel
`lambda/(lambda-i*t)` has norm at
most one and tends to one at every fixed frequency. After restriction to the
explicit expanding central interval, the full integrand is dominated by the
integrable envelope `exp(-t^2/pi^2)` and converges pointwise to the standard
Gaussian characteristic function. Dominated convergence and the checked
Gaussian integral give mass `sqrt(2*pi)`; after normalization, the central
contribution tends to one.

The next analytic task is the part Granville summarizes as the small error
outside the segment `|t| <= 1/log y`: formalize a smooth-number Perron
truncation at the exact saddle, identify its normalized central segment with
this integral, and prove the complementary error is negligible.

## Exact normalized Perron line (release 3.82)

`SmoothNumberSaddlePerronLine.lean` now matches the probability-side central
integral to the source-side vertical line without an implicit Fourier
convention. It proves the exact identity
between the twisted Dirichlet-series integrand with
`sigma/(sigma+i*t)` and the centered characteristic/Laplace integrand at
frequency `-t*sqrt(phiTwo)`. The central Perron height rescales exactly to the
explicit radius, and the interval change of variables identifies the two
normalized central contributions.

The next task is no longer a normalization or sign issue. It is the genuine
sharp Perron estimate: compare the complete finite-height vertical line with
the literal smooth cutoff, then show the part outside the central height is
negligible on the Gaussian main-term scale.

## Smooth sharp-Perron cutoff (release 3.83)

The finite-height comparison is now formalized. Absolute convergence passes
the smooth Dirichlet series through the vertical integral, giving exactly the
sum of frozen coefficient-free Perron kernels. The inclusive cutoff series is
`psiNat`, so subtraction is a summable termwise kernel error.

The immediate analytic task is to aggregate the inherited logarithmic bounds
below and above `X`, retain the uniform endpoint estimate, and choose the
height so both the cutoff error and frequencies outside the central segment
are negligible after saddle normalization.

## Symmetric Perron inversion limit (release 3.84)

The infinite-height endpoint convention is now exact. Each kernel converges
to the symmetric cutoff value, and a summable height-independent envelope
permits passage through the full smooth-number sum. The resulting limit is
`psiNat X y` minus the possible endpoint half-mass, with norm at most `1/2`.

The next analytic target is therefore sharper than the former cutoff problem:
at the finite saddle height, bound the portion of the vertical line outside
the expanding central window by `o` of the Gaussian main term. Combined with
the compiled central contribution, this will supply the critical smooth-number
saddle asymptotic.

## Complementary Perron interface (release 3.85)

The full normalization and subtraction ledger is now closed. The normalized
finite line is the full kernel sum over the saddle main term, and after
removing the evaluated central interval the remainder is exactly the two
vertical-line tails. Its height limit is the endpoint-corrected saddle ratio
minus the central term, so critical corrected-ratio convergence is equivalent
to decay of one named infinite complement.

Two quantitative tasks remain: prove `smoothSaddleMainTerm` tends to infinity
in every critical regime, disposing of the correction bounded by one half;
and prove the complementary Perron line tends to zero using the finite Euler
product away from the central frequency window.

## Saddle main-term growth (release 3.86)

The first of those two tasks is complete. A uniform comparison of the second
and first saddle prime terms proves `phiTwo <= 7*log(y)*phiOne` on the critical
half-plane. At the exact saddle this supplies a concrete
`sqrt(X)/(sqrt(14*pi)*log(X))` lower bound for the Gaussian main term. The main
term diverges in every critical regime, and the bounded endpoint disappears
after normalization.

The remaining smooth-number target is now singular and exact: prove
`smoothSaddleInfiniteComplementaryPerronLine (X n) (y n) -> 0` for every
critical regime. No endpoint, normalization, or main-term-growth side
condition remains.

## Wide-frequency annular decay (release 3.87)

The prime-factor contraction now holds across the full principal phase range,
not merely the local Taylor window. After variance normalization it supplies
the integrable bound `exp(-t^2/(48*pi^2))` up to radius
`pi*standardDeviation/log(y)`. Since the old central radius diverges, the
indicator of the intervening annulus tends pointwise to zero; dominated
convergence proves that annular contribution is negligible.

The next target is the outer-frequency estimate beginning at physical height
`pi/log(y)`. This is the only part of the named infinite complementary Perron
line not covered by the central and wide-frequency integral theorems.

## Physical principal-phase interface (release 3.88)

The normalized annulus is now matched exactly to the source-side Perron
contour. Its outer endpoint is physical height `pi/log(y)`, and the signed
standard-deviation substitution proves that the normalized sum of the two
intervening vertical-line integrals tends to zero.

The remaining target is a direct estimate of the two outer tails starting at
`pi/log(y)`, uniformly through the height limit defining
`smoothSaddleInfiniteComplementaryPerronLine`.

## Named outer-tail target (release 3.89)

The two tails beyond `pi/log(y)` are now a literal finite Perron-line object,
with an exact infinite-height limit. Algebraic interval splitting proves that
the former complementary line is the already negligible annulus plus this
outer line. Consequently every remaining formulation of the critical saddle
asymptotic reduces to
`smoothSaddleInfiniteOuterPerronLine (X n) (y n) -> 0`.

The next work is genuinely analytic: obtain uniform finite-Euler-product
decay or an equivalent oscillatory estimate on these nonprincipal tails.

## Global phase-loss envelope (release 3.90)

The exact Euler-factor modulus formula now yields a range-free contraction.
After multiplication, both the tilted characteristic and the physical Perron
integrand are controlled by the exponential of the explicit weighted cosine
loss over primes. The estimate includes all resonant and nonresonant
frequencies; no principal-cell hypothesis remains in the bound itself.

The next analytic task is sharply isolated: lower-bound this cosine loss on
suitable outer-frequency blocks, using prime distribution and phase
variation, strongly enough to integrate through the Perron height limit.

## First outer-frequency shell (release 3.91)

The first block after the principal phase boundary is now quantitative. On
`[pi/log(y), 4*pi/(3*log(y))]`, primes in `(y/2,y]` all lie in the
cosine-negative half-circle. A reusable cardinality consequence of the
Chebyshev–PNT dyadic-block estimate and monotonicity of `p^(-sigma)` produce
the loss `y^(1-sigma)/(16*log(y))` in factored form.

The next step is a shell construction that shifts the contributing prime
band as `t` grows, followed by summation of the resulting integrable
envelopes.

## Adaptive outer-frequency shell (release 3.92)

The contributing block now shifts with frequency at
`N(t)=ceil(exp(pi/t))`. Ceiling control proves its lower and upper phase
inequalities, the outer cutoff puts it below `y`, and a sufficiently large
Chebyshev–PNT threshold supplies its prime population. The resulting bound
is `N(t)^(1-sigma)/(16*log(N(t)))` in factored form.

The next analytic step is to control the frequencies above this
small-frequency regime, where one movable block gives only bounded loss, by
combining multiple prime bands or a suitable phase-distribution estimate;
the resulting bound must then be integrated uniformly to infinite height.

## Accumulated first-shell loss (release 3.93)

The first outer shell now uses every retained CEP dyadic block. The cutoff
remains within an `exp(-16)` factor after raising to `1-sigma`, while the
saddle equation supplies `y^(1-sigma) ≫ u`; combined with reciprocal mass
`≫1/log(u)`, the cosine loss is `≫u/log(u)` and diverges. The corresponding
Perron integrand has a uniform vanishing envelope.

Next, absorb the saddle-standard-deviation prefactor to make this shell's
normalized integral vanish, then reproduce an accumulating phase window for
the later outer ranges.

## Integrated first outer shell (release 3.94)

The complete symmetric first-shell Perron contribution is now a named exact
integral and tends to zero. Its total physical width contributes `1/log(y)`,
curvature bounds the remaining standard-deviation factor by `sqrt(7*u)`, and
the accumulated `exp(-c*u/log(u))` decay absorbs this square-root growth.

The next analytic step is no longer integration of the first shell. It is to
construct accumulated phase loss beyond `4*pi/(3*log(y))`, cover all later
outer-frequency ranges, and pass the resulting estimates to
`smoothSaddleInfiniteOuterPerronLine`.

## Eighth-root fourth shell (release 4.00)

The third iterated square-root alphabet now gives accumulated loss throughout
the physical band from `6*pi/log(y)` to `12*pi/log(y)`. Its retained
logarithmic support lies between exponents `1/12` and `1/8`.

Next, convert this loss to a divergent Rankin-ratio power and integrate the
fourth shell. The repeated construction should then be abstracted into an
indexed family suitable for infinite outer-line assembly.

## Integrated eighth-root shell (release 4.01)

The fourth-shell loss is now the divergent scale `u^(1/9)/log(u)`, and its
exact normalized symmetric contribution through `12*pi/log(y)` vanishes.
The next step is an indexed shell construction and aggregate tail estimate.

## Indexed shell infrastructure (release 4.02)

All iterated square-root alphabets now share one recursive definition with
closed-form logarithmic envelopes, and their physical endpoints form an
exact doubling sequence. Next, prove a uniform indexed phase-loss theorem
and sum the resulting normalized shell bounds.

## Uniform indexed phase loss (release 4.03)

The full CEP loss theorem now holds uniformly for any indexed shell whose
iterated-root scale retains four fifths of its ideal logarithmic size. Next,
verify that condition over a growing index range and sum the shell envelopes.

## Indexed scale range (release 4.04)

The four-fifths hypothesis now follows from terminal noncollapse and the
explicit inequality `10*(2^k-1)*log(2) <= log(y)`. Next, construct a growing
terminal index satisfying these conditions and estimate the residual tail.

## Fourth-root third shell (release 3.98)

The next resonant endpoint is crossed with the iterated square-root prime
scale. Its retained CEP support lies between logarithmic exponents `1/6` and
`1/4`, giving accumulated cosine loss throughout the complete physical band
from `3*pi/log(y)` to `6*pi/log(y)`.

Next, compare its cofactor power with a positive power of the Rankin ratio,
prove exponential absorption of the saddle normalization, and integrate the
third shell before iterating the construction further.

## Integrated fourth-root shell (release 3.99)

The third-shell loss is now a divergent `u^(1/5)/log(u)` scale. Its
exponential absorbs the saddle prefactor, proving that the exact normalized
symmetric contribution through physical height `6*pi/log(y)` tends to zero.

Next, the rescaled-alphabet construction must be iterated or abstracted to
cover all subsequent bands uniformly and pass their aggregate to
`smoothSaddleInfiniteOuterPerronLine`.

## Extended first-shell band (release 3.95)

The accumulated CEP alphabet remains in the nonpositive-cosine window up to
`3*pi/(2*log(y))`, not merely `4*pi/(3*log(y))`. The exact newly exposed
symmetric band has been integrated with a reusable shell lemma, and its
normalized contribution tends to zero.

Next, move or repartition the prime alphabet after the phase reaches
`3*pi/2`. The proof must recover divergent accumulated loss across the
resulting resonant region and ultimately cover the entire infinite outer
Perron line.

## Square-root second shell (release 3.96)

The first resonant boundary is now crossed by replacing the top alphabet with
the full CEP alphabet below `floor(sqrt(y))`. Its exact logarithmic support
keeps every selected phase in the negative-cosine half-circle through height
`3*pi/log(y)`, and the critical regime satisfies the required PNT and cofactor
range conditions. The resulting cosine loss is explicit on the whole second
shell.

Next, compare the square-root cofactor power with a positive power of the
Rankin ratio, prove the resulting loss tends to infinity fast enough to absorb
the saddle normalization, and integrate this second shell.

## Integrated square-root second shell (release 3.97)

The square-root-alphabet loss has now been converted to the divergent scale
`u^(2/5)/log(u)`. Its exponential envelope absorbs the square-root saddle
prefactor, so the exact normalized symmetric contribution through physical
height `3*pi/log(y)` tends to zero in every critical regime.

The next analytic step is to repartition the prime alphabet after this
second resonant endpoint, obtain summable control over all subsequent
frequency bands, and pass those bounds to
`smoothSaddleInfiniteOuterPerronLine`.

## Fixed-depth indexed admissibility (release 4.05)

Every fixed number of iterated-root shells is now eventually available. The
terminal scale survives exactly when `4^(2^k) <= y`, and the logarithmic
rounding condition is eventually automatic for fixed `k`. The next task is
genuinely diagonal: define an integer depth tending to infinity slowly enough
that both inequalities hold pointwise, then obtain a uniform summable shell
envelope through that depth and control the remaining infinite tail.

## Fixed-index indexed loss (release 4.06)

For each fixed `k >= 2`, the critical Rankin ratio now fits the CEP cofactor
range and the full indexed cosine-loss theorem applies on the corresponding
shell. The next proof must avoid merely intersecting infinitely many eventual
sets: choose an explicit or slow diagonal depth, establish all range
inequalities uniformly below it, convert each loss into an integrable
normalized envelope, and sum the resulting finite family before treating the
frequencies beyond its terminal endpoint.

## Growing indexed diagonal (release 4.07)

The slow depth selector now tends to infinity and controls all preceding
indexed shells simultaneously. The next module should formulate an
index-dependent lower envelope for the CEP cutoff power, convert the global
Euler-product loss to a symmetric-shell norm estimate, and find a summable
majorant uniform for `k <= K(n)`. Only after that finite moving sum vanishes
can the terminal-height residual be attacked.

## Explicit indexed loss scale (release 4.08)

The fixed-index loss is now
`exp(-16)*(u/(15 log 4))^((4/5)2^(-k))/(16 log 2 log u)` and diverges for
every fixed `k`. Next combine its exponential with the indexed shell width
and the `sqrt(u)` saddle normalization. Once every fixed contribution tends
to zero, diagonalize a finite-prefix norm bound with a prescribed vanishing
threshold; this avoids requiring a false uniform-in-all-`k` power estimate.

## Fixed indexed shell integrals (release 4.09)

Every fixed indexed shell contribution now tends to zero, with its exact
doubling width accounted for. The next construction should apply the
countable diagonal theorem to predicates asserting both analytic shell
admissibility and a small bound on the norm of the finite prefix sum, for
example `<=1/(K+1)`. Since each fixed finite sum tends to zero, the resulting
moving sum will vanish automatically as `K(n)->infinity`.

## Vanishing growing indexed prefix (release 4.10)

The moving finite sum now vanishes at a depth tending to infinity, with all
shellwise estimates retained. Next prove a finite telescoping lemma for the
positive and negative interval integrals, including the common saddle
normalization, so this sum becomes the symmetric Perron contribution from
indexed height one to height `K`. Then compare its terminal truncation with
the named infinite outer line; that final comparison is the remaining
smooth-saddle tail problem.

## Telescoped indexed segment (release 4.11)

The indexed prefix is now exactly one contiguous symmetric Perron segment,
and its moving upper endpoint crosses arbitrarily many shell boundaries while
the contribution vanishes. The remaining task is no longer finite-shell
assembly: prove that the named infinite outer line differs from this segment
by a post-terminal tail tending to zero. This likely requires a second
frequency mechanism once the iterated prime scale approaches the CEP
cofactor floor, rather than further fixed-depth diagonalization alone.

## Exact post-terminal reduction (release 4.12)

The first three outer pieces now concatenate to one pre-indexed segment and
their existing convergence theorems prove that segment vanishes. Removing it
and the vanishing moving indexed segment from the infinite outer line defines
one exact post-terminal remainder. The critical smooth-saddle asymptotic is
equivalent to decay of this remainder along the already selected diagonal.

Further iterated-root diagonalization cannot by itself solve this obligation:
the terminal index may diverge while its physical endpoint remains bounded
when PNT admissibility forces the terminal prime scale away from the CEP
floor. The next analytic task must therefore use a genuinely high-frequency
estimate—such as a uniform finite-Euler-product minor-arc bound or an
equivalent oscillatory Perron-tail argument.

## Indexed physical-height ceiling (release 4.13)

The limitation anticipated above is now a theorem. Terminal scale survival
is exactly `4^(2^k) <= y`; logarithmic monotonicity and the indexed endpoint
formula give the absolute ceiling `3*pi/(2*log 4)`. Any growing admissible
depth therefore has eventually bounded physical height and cannot tend to
infinity. Research on the post-terminal remainder should now focus entirely
on a global minor-arc or oscillatory inversion estimate.

## Hildebrand--Tenenbaum minor-arc interface (release 4.14)

The original global mechanism is now represented exactly. The HT loss
`u*t^2/((1-sigma)^2+t^2)` is radially monotone, and their Lemma 8(ii)
characteristic estimate has a source-facing proposition. Assuming it, the
literal normalized Perron integrand obeys the same exponential envelope and
every finite symmetric shell is bounded by its left-endpoint loss times its
width and saddle normalization.

The next source steps are now unambiguous: formalize the Mangoldt cosine-sum
lower bound behind equation (3.16), then reproduce Lemma 9's smoothed
short-interval estimate and Lemma 10's finite Perron-height selection.

## HT Mangoldt-transform subtraction (release 4.15)

The finite complex transform and weighted cosine sum in Lemma 6 are now
literal Lean definitions. Real-part subtraction gives the cosine sum exactly,
and two complex approximation errors bounded by `E` give the corollary with
error `2E`. Next combine the native quantitative PNT with complex Abel
summation to prove this transform approximation uniformly in the HT range.

## Exact HT Lemma 6 interface (release 4.16)

The target range is now fixed exactly at
`exp((log y)^(3/2-epsilon))`, together with equation (3.10)'s error scale.
The main term has checked Cartesian and norm formulas, and the uniform
transform proposition feeds the cosine corollary without further analytic
loss. A naive Abel transfer from the unshifted de la Vallée Poussin estimate
costs `|t|` and cannot reach this ceiling. The next proof must therefore use
shifted Perron inversion and the Vinogradov zero-free region directly.

## HT prime-power bridge (release 4.17)

The Mangoldt cosine sum now splits exactly into a logarithmically weighted
prime sum and a non-prime remainder. Monotonicity of `log` bounds the first
by `log y` times the literal Euler-product cosine loss, and `1-cos<=2`
bounds the second. Combining these facts with release 4.16 gives the exact
source-shaped lower bound needed in Lemma 8(ii). Next reproduce HT Lemma 5
at weight `n^(-sigma)`, then prove that the cosine main term dominates both
that remainder and the Lemma-6 error in the required saddle ranges.

## HT Lemma 5 in the saddle range (release 4.18)

The non-prime Mangoldt remainder now has an exact exponent decomposition.
For `sigma>=1/2`, the `k`th slice is at most
`2^(-(k-2)/2)` times the weighted prime logarithm sum; a checked truncated
geometric-series estimate and Chebyshev's bound therefore give an explicit
`O(log y)` theorem. This closes the higher-prime-power term in the proof of
HT Lemma 8(ii). The next bounded task is to lower-bound the elementary
cosine main term strongly enough to absorb this logarithmic remainder and
the equation-(3.10) error, still conditional on the Lemma-6 transform
proposition.

## HT cosine main term (release 4.19)

Cauchy--Schwarz applied to the Cartesian phase gives the checked bound
`M >= y^beta*t^2/(2*beta*(beta^2+t^2))`, uniformly in `t log y`. This is now
inserted into the Euler-product loss inequality together with the explicit
`O(log y)` prime-power remainder. The next bounded arithmetic task is a
source-strength upper bound for `smoothSaddlePhiOne`, yielding
`y^(1-sigma)/((1-sigma) log y) >= c*u` at the saddle. The independent
analytic task remains the shifted-Perron proof of HT Lemma 6.

## HT saddle comparison (release 4.20)

The existing canonical finite Abel estimate now bounds `smoothSaddlePhiOne`
by an explicit constant times `y^(1-sigma)/(1-sigma)`. At the exact saddle
this proves that the HT main coefficient controls a fixed multiple of `u`,
and hence that the cosine main term divided by `log y` dominates the exact
rational loss in Lemma 8(ii). The finite theorem assumes
`2*smoothSaddleDivisor y sigma <= sqrt y`. Parameter inspection shows that
this cutoff is not expected in the critical regime, so the theorem is kept
only as a conditional intermediate result.

## Uniform HT saddle comparison (release 4.21)

Abel summation against Chebyshev's theta function now directly bounds the
logarithmically weighted prime sum by
`log(4)y^(1-sigma)/(1-sigma)`. This gives
`smoothSaddlePhiOne <= 5 log(4)y^(1-sigma)/(1-sigma)` and closes the
Rankin-ratio/main-coefficient comparison without a cutoff. The remaining
task in this chain is the shifted-Perron/zero-free-region proof of the named
HT Lemma 6 transform proposition.

## HT shifted-Perron normalization (release 4.22)

The remaining transform is now written literally as
`sum_{n<=y} Lambda(n)n^(-s)` with `s=1-beta+i*t`; its source main term is
literally `y^(1-s)/(1-s)`. This shifted-Perron estimate is equivalent to the
previous contract. The exact psi-Abel formula is also available and confirms
where an unshifted discrepancy estimate incurs frequency variation. The next
bounded analytic task is to connect the truncated Mangoldt Dirichlet sum to
the zeta logarithmic derivative on the initial Perron line before shifting
through the frozen zero-free rectangle.

## HT shifted-Perron initial line (release 4.23)

That initial-line connection is now exact. Absolute convergence on
`1<Re(s)+c` permits termwise integration of the shifted von Mangoldt series,
and the normalized integral is the source coefficient times the existing
finite-height sharp-Perron kernel. The sharp cutoff recovers the finite
source Dirichlet sum, producing an exact error series at
`s=1-beta+i*t` whenever `beta<c`. The next bounded task is the rectangle
identity that moves this line left across the pole at `z=1-s`; after that,
the horizontal and left-edge integrals require the frozen zero-free bounds.

## HT shifted-Perron rectangle (release 4.24)

The rectangle identity and pole extraction are now compiled. On a rectangle
with positive left edge and `left<beta<right`, the translated surrogate is
holomorphic away from `z=beta-i*t` provided it is zero-free throughout the
rectangle. The residue is the exact source main term, and the initial line
equals that term plus the two horizontal and one left vertical integrals.
The next bounded task is to choose the left displacement and height from the
native Vinogradov--Korobov zero-free theorem, then establish a uniform bound
for the literal translated logarithmic derivative on those three edges.

## HT shifted zero-free rectangle (release 4.25)

The rectangle's nonvanishing is now derived from the frozen native
Vinogradov--Korobov theorem. The exact sufficient condition is
`eta <= c / VKDenominator(|t|+T)` with `eta<=1`; no new source proposition is
introduced. The native Ford theorem supplies positive `c` and a starting
height. The next bounded task is parameter arithmetic: choose a positive
`eta<beta` and `T>|t|` satisfying that width throughout the HT frequency
range, then establish logarithmic-derivative bounds on the resulting left
and horizontal edges.

## HT contour parameters and error assembly (release 4.26)

The rectangle now uses the concrete source-compatible choices
`eta=2*(log y)^(epsilon/2-1)`, `T=2Y_epsilon(y)`, and
`right=beta+1/log y`. Their positivity, pole geometry, full-frequency height
coverage, exact left-edge decay, and constant right-line power cost are all
proved. The initial-line sharp-Perron identity and the zero-free contour
identity combine exactly, reducing the transform error to a named sum of
three contour edges minus a named truncation series. The next bounded task is
to prove `eta <= c/VKDenominator(3Y_epsilon(y))` eventually, use monotonicity
to discharge the literal width condition, and then bound the two remainders;
the range `beta<=eta` should be closed separately by the `1/beta` allowance.

## HT selected-contour VK width (release 4.27)

The exact VK comparison is now closed. After unfolding the source ceiling,
the selected shift times the denominator is a fixed log-log factor times
`(log y)^(-epsilon/6)`, so log-versus-power decay makes it smaller than the
native Ford constant. The frozen denominator scaling theorem controls
height `3Y`, and monotonicity covers each actual height `|t|+2Y`. Native
constants therefore yield the exact error decomposition eventually and
uniformly in frequency whenever `beta>eta`. The next bounded task is to
estimate the sharp-Perron truncation series (using its frozen kernel bounds)
and the three zero-free contour edges; separately, `beta<=eta` should follow
from a crude transform/main-term bound absorbed by the existing `1/beta`
term.

## HT sharp-Perron truncation majorant (release 4.28)

The source-weighted finite-height cutoff error is now controlled term by
term. Its coefficient/right-line powers cancel exactly to the frozen
optimized Perron exponent, leaving the common factor `y^(beta-1)`. The
strict lower range, endpoint, and strict upper range are combined into a
nonnegative majorant whose far tail is summable by comparison with the
von Mangoldt Dirichlet series at `1+1/log y`. The full complex `tsum` is
bounded by this scalar `tsum`. The next bounded task is its explicit
arithmetic estimate—finite near-diagonal harmonic mass plus the far
Dirichlet tail—at `T=2Y_epsilon(y)`; this should make the truncation term
negligible compared with the equation-(3.10) allowance.

## HT sharp-Perron arithmetic estimate (release 4.29)

The majorant sum is now explicit. Integrality of the cutoff means every
nonendpoint additive distance is at least one, so a deliberately coarse
`y+1` bound replaces the near-diagonal harmonic decomposition. After the
exact power factorization, every such term belongs to one positive von
Mangoldt Dirichlet series at the optimized abscissa. The frozen series bound
and `y^(1+1/log y)=exp(1)y` yield the endpoint plus
`(y+1)exp(1)y(log y+C)/(pi*T)`, and this is transferred to the full complex
HT truncation remainder at `T=2Y_epsilon(y)`. The next bounded task is to
prove its eventual absorption into the target exponential allowance; the
other analytic task is the quantitative bound for the three contour edges.

## HT harmonic-strength Perron arithmetic (release 4.30)

The coarse all-distance factor has been replaced by the required harmonic
summation. The near range compares to a half-integral reciprocal-distance
kernel with mass at most `8*harmonic(y+1)`; the far range costs only two
times the optimized positive von Mangoldt series. Thus the explicit
source-height error has the schematic size
`y^(beta-1)*(Lambda(y)+y*polylog(y)/Y_epsilon(y))`.
The height-decay exponent `3/2-epsilon` exceeds the target exponent
`epsilon/2` exactly when `epsilon<1`, so the next bounded task is the formal
eventual absorption of these displayed terms. Quantitative contour-edge
bounds and the small-beta branch remain afterward.

## HT Perron-truncation absorption (release 4.31)

The sharp-Perron remainder is now closed at the source scale. The strict gap
between height exponent `3/2-epsilon` and decay exponent `epsilon/2` absorbs
all fixed constants and logarithmic powers. Endpoint, near, and far pieces
each consume one third of the scalar target, yielding the complete complex
bound `y^beta*exp(-(log y)^(epsilon/2))`, uniformly in the frequency. This is
formally below the HT Lemma-6 allowance for every `0<beta<1`. The next
bounded task is now purely the displaced rectangle: bound its two horizontal
edges and left vertical edge, then close `beta<=eta` separately.

## HT contour-edge geometry (release 4.32)

The normalized contour geometry is now closed. Generic pointwise sup bounds
control `HIntegral'` and `VIntegral'` by exact edge lengths, and the HT
specialization combines both horizontal edges and the left vertical edge
into one named scalar majorant. The horizontal length is exactly
`eta+1/log y`; the vertical length is `2T`. The next bounded analytic task is
therefore to prove uniform pointwise estimates for the translated zeta
logarithmic derivative on those three zero-free boundary segments and absorb
the resulting majorant. The `beta<=eta` branch remains independent.

## HT weighted left edge (release 4.33)

The vertical geometry is now at the correct source scale. Keeping `1/|z|`
inside the left-edge integral gives the elementary bound
`1/|a+iu| <= 2/(a+|u|)`, whose symmetric mass is logarithmic rather than
linear in the contour height. The shifted integrand norm has also been
reduced exactly to the translated zeta logarithmic derivative times
`y^Re(z)/|z|`. The next bounded task is consequently a genuine analytic one:
prove a uniform logarithmic-derivative estimate throughout the selected
zero-free strip, instantiate the weighted majorant, and absorb its fixed
logarithmic losses. The small-beta branch remains independent.

## HT VK-separated logarithmic derivative (release 4.34)

The analytic input behind the edge bound is now available without selecting
a special ordinate. Twice the HT shift fits eventually inside the native VK
width, so every local sharp-Landau zero is horizontally separated from the
evaluation point by the contour shift. The resulting reciprocal-distance
bound controls the full finite zero sum, and the frozen Landau
partial-fraction theorem yields a physical `zeta'/zeta` estimate throughout
each admissible positive-height unit interval. The next bounded task is to
instantiate this theorem on the two horizontal edges and the positive half
of the left edge, use conjugation for negative heights, and absorb the
resulting logarithmic factors. The small-beta branch remains independent.

## HT sign-uniform logarithmic derivative (release 4.35)

Conjugation now gives the same VK-separated Landau estimate at negative
height, and a single absolute-ordinate theorem covers both signs without an
auxiliary selected interval. Frozen zero-mass control reduces its size to
`O((1+1/eta)*log |R|)`. This is already the pointwise estimate needed on the
two horizontal edges. The vertical edge crosses ordinate zero, where the
zeta pole contributes a separate reciprocal-distance term, so the next task
is a fixed-height surrogate-logarithmic-derivative bound plus that explicit
pole term, followed by high/low vertical assembly.

## HT compact low-height pole control (release 4.36)

The vertical edge's central segment is now controlled. A fixed half-VK
compact rectangle is free of zeros of the entire surrogate `(s-1)zeta(s)`;
compactness supplies its uniform logarithmic-derivative bound. Returning to
zeta costs exactly `1/eta` on `Re(s)=1-eta`. Together with release 4.35 this
covers every ordinate. The next bounded task is to prove the enlarged
nine-frequency VK comparison needed by the high part, split the weighted
vertical integral at height eight, assemble the horizontal estimates, and
absorb the resulting logarithmic factors.

## HT literal contour pointwise bounds (release 4.37)

Pointwise physical `zeta'/zeta` control is now specialized to every literal
HT edge. The nine-frequency VK comparison covers the factor-three Landau
height enlargement, the horizontal ordinates and real parts satisfy the
required ranges exactly, and the vertical high/low split is recombined by a
single max majorant. The next bounded task is algebraic rather than analytic:
prove surrogate nonvanishing supplies the zeta nonzero hypotheses, retain
the Perron denominator on all three edges, instantiate the weighted contour
majorant, and absorb its logarithmic losses.

## HT weighted analytic contour edge (release 4.38)

The three physical logarithmic-derivative estimates now control the literal
shifted Perron integrand. Both horizontal edges gain the full reciprocal
contour height, the left edge retains its reciprocal Perron denominator, and
the translated surrogate-zero-free rectangle proves all required zeta
nonvanishing assertions. The prepared weighted integration theorem therefore
gives one explicit complete edge majorant. The next bounded task is to absorb
that scalar majorant into the Lemma 6 allowance; the complementary
`beta<=eta` branch remains separate.

## HT large-beta contour absorption (release 4.39)

The weighted edge majorant is now absorbed uniformly when `2*eta<=beta`.
Both logarithmic-derivative envelopes cost only `O((log y)^3)`, and the
vertical reciprocal-distance integral costs `O((log y)^2)`. The corrected
factor-two contour displacement gives the spare stretched exponential needed
to remove these powers while retaining the exact equation-(3.10) decay.
The next bounded task is the complementary small-beta estimate, after which
the contour and already-complete truncation bounds can be recombined.
