# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `prime-equidistribution-1.56`. It
reproduces the source identities, pinned build environment, initial source
definitions, frozen Gafni--Tao theorem closure, and Tao's Proposition
2.3(i),(iii). It is not a main-theorem release manifest.

## Pinned source

- Paper: Terence Tao, *Products of consecutive integers with unusual anatomy*.
- arXiv identifier: `2603.27990v2`.
- PDF and TeX archive hashes: `Sources/SHA256SUMS.txt`.
- Provenance and download URLs: `Sources/PINS.md`.
- Baker--Harman--Pintz 2001 PDF: pinned by SHA-256 with DOI, mirror origin,
  and theorem/page locators; this is source provenance, not a formal proof.
- Erdős--Selfridge 1975 PDF: pinned by SHA-256 with archival origin and exact
  theorem locator; this is source provenance, not yet a formal proof.
- Granville 2008 smooth-number survey: pinned by SHA-256 from the author's
  site with exact equation and page locators for Tao's Proposition 2.1; this
  is source provenance, not a formal proof.
- Canfield--Erdős--Pomerance 1983 primary smooth-number paper: pinned by
  SHA-256 from the author's archive, with Theorem 3.1 and equations
  (3.5), (3.10), (3.11), and (3.15) as exact proof locators; this is source
  provenance, not a formal proof.
- Matomäki--Radziwiłł--Shao--Tao--Teräväinen 2021/2022 PDF and TeX archive:
  pinned by SHA-256 with arXiv and DOI provenance and an exact Proposition
  1.12 proof locator; this is the cited input behind Tao's Theorem 2.5, not yet
  a formal proof.
- A public Lean proof of the standard Sylvester--Schur theorem is pinned by
  commit, path, byte size, and raw-file SHA-256 in `Sources/PINS.md`. It is a
  provenance-only reference and is not vendored because the pinned proof source
  has no explicit license. The local binomial-to-interval bridge is independent.

## Lean package

- Package directory: `Extension/`.
- Package/library name: `Tao2026`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Production modules: `Anatomy`, `Intervals`, `Asymptotics`, `BadIntervals`, `BadIntervalMaximal`, `NormalizedBadIntervals`, `TypicalBadIntervals`, `NonTypicalBadIntervals`, `BadIntervalSourceScales`, `BadIntervalLongSieve`, `BadIntervalCofactorSieve`, `BadIntervalLongOptimization`, `BadIntervalLongSaddle`, `BadIntervalLongSum`, `BadIntervalLargePrimeSum`, `BadIntervalLargeLength`, `Counting`,
  `CoefficientBounds`, `CoefficientProduct`, `CoefficientSelection`, `CriticalIntervals`,
  `FactorialAsymptotics`, `FactorialCoefficientBounds`, `FactorialEquidistribution`, `FactorialFibers`, `FactorialIntervals`, `FactorialOneTerm`, `FactorialOneTermAsymptotics`, `FactorialShortIntervals`, `FourierAssembly`, `FourierApproximation`, `FourierDecay`, `FourierIntegrationByParts`, `FourierRadial`, `FourierSlices`,
  `IntervalMultiples`, `PrimeIntervals`, `PrimeEquidistribution`,
  `PrimePowerReduction`, `PartialSummation`, `PhaseVariation`, `LowFrequency`, `PowerfulAsymptotics`, `PowerfulExtraction`,
  `PowerfulLimit`, `PowerfulNumbers`,
  `PowerfulRelations`, `PowerfulRelationCounting`, `SquareRelations`, `ConvolutionRearrangement`,
  `QuadraticIdealDivisors`, `QuadraticSolutionCount`, `QuadraticUnits`, `ShortIntervalDecomposition`, `SmoothNumbers`, `SmoothNumberBounds`, `SmoothNumberRankin`, `SmoothNumberPrimeSum`, `SmoothNumberSourceRegimes`, `SmoothNumberPolylogRegimes`, `SmoothNumberLowerBound`, `SmoothNumberHildebrand`, `SmoothNumberCriticalLower`, `SmoothNumberCEPPacket`, `SmoothNumberCEPRecurrence`, `SmoothNumberCEPIntervals`, `SmoothNumberCEPWeights`, `SmoothNumberCEPSource`, `SmoothNumberCEPSize`, `SmoothNumberCEPPrimeMass`, `SmoothNumberCEPBootstrap`, `SmoothNumberCEPCoarse`, `SmoothNumberSaddlePoint`, `SmoothNumberSaddleRegimes`, `SmoothNumberSaddlePhase`, `SmoothNumberStability`, `SmoothNumberSaddleCurvature`, `BadOneTermAsymptotics`,
  `PublicStatements`, `TypeIReduction`, `TypeIIReduction`, `TypeIIArithmetic`, `TypeIIKernel`, `VeryBadIntervals`, `VeryBadEquidistribution`,
  `TorusFourier`, `VinogradovPhase`, `Vinogradov`, `VinogradovSharp`,
  `VinogradovMeanValue`, `VinogradovUniform`, `VinogradovFord`,
  `VinogradovWooleyCoefficient`, `VinogradovFiniteDegree`,
  `VinogradovOptimalWooley`, `VaughanCoefficients`, `VaughanIdentity`, and `Audit`.
- Frozen theorem dependency: the exact 1,339-module import closure of
  `GafniTao.Theorem11`, with 965 `GafniTao`, 291 `RiemannZeta`, and 83
  `PrimeNumberTheoremAnd` source modules.
- Proved content: Proposition 2.3(i) from Mathlib's Bertrand theorem;
  definition-interface lemmas; the uniform discrepancy result
  `exists_uniform_dyadic_exceptional_power_guthMaynard`; exact control of the
  higher-prime-power tail; and
  `exists_dyadic_primeFree_power_guthMaynard`, which gives a nonnegative
  exponent strictly below one for the genuine variable-length dyadic
  prime-free endpoint measure; the finite dyadic assembly; the monotonicity
  treatment of `theta >= 1`; and `taoProposition23iii_guthMaynard`, which has
  the full source range and quantified `O(X^(1-c+o(1)))` conclusion. Exact
  proposition-valued conclusion contracts for Theorems 1.7--1.10 compile,
  but none is proved. The exact inclusive smoothness bridge, unique `p²m`
  representation of `B¹`, and finite identity
  `badOneTermCount_eq_sum_psiNat` are also proved and audited. All four
  quantified estimates of Proposition 2.1 and all of Lemma 1.6(i) are proved.
  `SmoothNumberStability` fixes the literal cutoff `floor(cX)`, proves its
  ratio and logarithmic limits, proves preservation of
  `IsTaoCriticalSmoothRegime`, and records both monotone halves. It also
  separates Granville (3.24)'s quotient-limit target from its `IsTheta`
  consequence without assuming either one. The analytic quotient-limit and
  hence Lemma 1.6(ii) remain open. `SmoothNumberSaddlePoint` now defines the
  exact finite sums `phiOne` and `phiTwo`, proves positivity, continuity,
  strict decrease, both endpoint limits, existence and uniqueness of the
  positive solution `phiOne(y,sigma)=log X`, and the derivative identity
  `phiOne'=-phiTwo`. Its exact mean-value secant theorem converts
  `log X2-log X1` into `phiTwo` times the change of saddle parameter.
  `SmoothNumberSaddleRegimes` proves explicit upper and lower finite-prime
  estimates and deduces that this exact saddle tends to `1` in every critical
  regime. The remaining step is the uniform saddle-point asymptotic, not
  construction, calculus, or critical-regime location of the saddle. The analytic route
  now starts from a proved exact Dirichlet-series identity: for every
  `sigma>0`, the series over positive `(y+1)`-smooth naturals is summable and
  equals the finite Euler product over primes `p≤y`. The finite Rankin
  inequality `Ψ(X,y)≤X^sigma∏_{p≤y}(1-p^(-sigma))⁻¹` is proved in the literal
  source-inclusive convention and audited. Each Euler factor is then bounded
  by its exponential geometric tail, uniformly reduced through the factor at
  two to `∑_{p≤y}p^(-sigma)`, and combined with the exact identity for
  `X^sigma` to expose the complete Rankin saddle exponent. Exact finite Abel
  summation rewrites the remaining weighted prime sum through
  `Nat.primeCounting`; its backward differences are nonnegative, so Mathlib's
  explicit Chebyshev estimate applies termwise. The resulting unconditional
  finite majorant is substituted into the source-facing Rankin exponent. Its
  square-root remainder is also absorbed into the global explicit majorant
  `(2 log 4+2)n/log n`, and that cleaner finite difference bound is propagated
  to a second source-facing Rankin exponent. Bernoulli's inequality then proves
  the sharp discrete estimate
  `n^(-sigma)-(n+1)^(-sigma) ≤ sigma n^(-sigma)/n` for `0≤sigma≤1`,
  reducing the entire weighted prime contribution to an explicit endpoint
  plus a constant multiple of `sum_{2≤n<y} n^(-sigma)/log n`. A second
  Bernoulli argument proves the finite integral comparison
  `sum n^(-sigma)≤y^(1-sigma)/(1-sigma)`; using `log n≥log 2` gives a
  completely sum-free, kernel-checked baseline Rankin exponent. A general
  cutoff `2≤k≤y` now splits the power-log sum into the exact scales
  `k^(1-sigma)/((1-sigma)log 2)` and
  `y^(1-sigma)/((1-sigma)log k)`. Under the two elementary cutoff comparisons
  `k^(1-sigma)log y≤y^(1-sigma)` and `log y≤L log k`, this is normalized
  to the correct growing `log y` scale. The concrete divisor
  `R=(log y)^(1/(1-sigma))` is now constructed with cutoff `floor(y/R)`;
  its power comparison is exact before flooring, and for `y≥4` the single
  condition `2R≤sqrt y` supplies the floor-size and `L=2` logarithmic
  comparisons. The resulting power-log, weighted-prime, and source-facing
  Rankin estimates are kernel-checked and audited. The source-regime
  saddle variables `u=log X/log y` and `sigma=1-log u/log y` are explicit;
  their range criteria and exact identities `y^(1-sigma)=u` and
  `-(1-sigma)log X=-u log u` are also proved and audited. The square-root
  separation fits the polylogarithmic regime, while the critical
  `y=z^(alpha+o(1))` regime requires a finer multi-scale estimate. Those
  finite multi-scale argument is now compiled: every `[a,b)` retains the
  exact difference of endpoint powers over `(1-sigma)log a`, monotone cutoff
  chains reassemble exactly, and the corresponding local majorants sum
  termwise. The concrete saturated dyadic chain has exact depth
  `clog 2 y - 1`; a block-cardinality bound reduces it to the scalar
  exponential-harmonic sum `∑ 2^(j delta)/j`. The arbitrary-cutoff and
  midpoint estimates sum the tail geometrically, retain the denominator
  `2^delta-1`, lower-bound it by `delta log 2`, and produce the terminal scale
  `2^(m delta)/(m delta)` plus a half-exponential harmonic prefix. The named
  chain majorants propagate through the weighted-prime sum and full
  source-facing Rankin exponent. Exact depth/logarithm comparisons convert the
  terminal term to `2(2y)^delta/(delta log y)` and at the standard saddle to
  `2*2^delta*u/log u`. The midpoint exponential is bounded by the square root
  of the terminal source scale, so the prefix becomes
  `sqrt(2^delta*u) * (1+log(floor(m/2)))`. The explicit finite condition
  `2(1+log(floor(m/2)))log u <= sqrt u` now absorbs that prefix and yields the
  full scalar bound `5u/log u`. The natural dyadic factor is bounded by
  `1+log(log(2y)/log 2)`; together with `log u <= 4u^(1/4)`, this reduces the
  finite obligation to `8(1+log(log(2y)/log 2)) <= u^(1/4)`, and the resulting
  continuous-log wrapper is compiled. Its quadratic-depth consequence and
  positive-term optimization are verified in both exact source regimes;
  both matching lower bounds are also verified.
  The critical source regime is now encoded exactly by
  `log X/log x -> 1` and `log y/log z(x) -> alpha`, with `alpha` fixed before
  the limit. The exact identity `log x/log z=u₀`, the divergence `u₀->∞`, and
  the consequences `u/u₀->1/alpha` and `u->∞` for fixed positive `alpha` are
  proved. The generic eventual scalar consumer now reduces this regime to the
  single quadratic depth envelope `log(2y)/log 2<=u²` plus the elementary
  saddle-range hypotheses.
  The critical integral-depth bridge is now audited.  For
  `k=Nat.log y X`, one has `k/u₀ -> 1/alpha`,
  `log k/log₂x -> 1/2`, and `k log k/log z -> 1/alpha`.  The frozen PNT gives
  `log(primeCounting y)/log z -> alpha`, the logarithmic gap from `k` tends
  to infinity, and consequently `2k<=primeCounting y` eventually.  The
  full finite exponent simplex is now compiled as well.  Prime multisets of
  every total degree at most `k` are evaluated injectively by unique
  factorization, stars and bars gives the exact cardinality
  `choose(k+primeCounting y,primeCounting y)`, and `y^k<=X` embeds this family
  into `psiNat X y`.  Independently, a largest-prime-factor/cofactor bijection
  proves the exact recurrence
  `psiNat X y=1+sum_{p<=min(X,y)}psiNat(X/p,p)` for `X>=1`.  The weighted
  arithmetic bridge is now exact too: multiplication by every
  admissible prime power bijects smooth cofactors with divisible smooth
  numbers, total prime multiplicity is the sum of the resulting `psiNat`
  counts, and the logarithmic factorization formula gives the finite
  Chebyshev--Hildebrand identity with an explicit nonnegative boundary defect.
  Its first-prime-power consequence
  `sum_{p<=y}log(p)psiNat(X/p,y)<=psiNat(X,y)log X` is also verified.  The
  inequality is iterated exactly through every depth `d` satisfying `y^d<=X`,
  proving `theta(y)^d<=psiNat(X,y)log(X)^d` and its quotient form.  At the
  canonical depth, the residual `b=floor(X/y^d)` satisfies `1<=b<y` and is
  retained through the refined bound
  `theta(b)theta(y)^d<=psiNat(X,y)log(X)^(d+1)`.  A thresholded endpoint factor
  combines this with a pinned-PNT threshold above which `theta(b)>=b/2`; when
  inactive, `b` is bounded by that fixed threshold.  The exact loss of this
  route is now audited rather than hidden: it proves
  `X/(B*2^d*(log X)^(d+1))<=psiNat(X,y)`, the normalized logarithm of this
  denominator tends to `2/alpha`, and hence
  `X/z^(2/alpha+epsilon)<=psiNat(X,y)` for every positive `epsilon`.  The
  sharp asymptotic conversion has also been isolated and verified:
  `HasCriticalSmoothLowerSaddle X y E`, together with `E/log z -> 0`, implies
  `X/z^(1/alpha+epsilon)<=psiNat(X,y)`.  The concrete CEP-sized error
  `E=C*u*log(log u)` is proved to satisfy that normalized limit for every
  fixed `C`.  Moreover `log u/log y -> 0`, so the critical regime eventually
  lies in the fixed source-uniform range `u<=y^(1/2)`. The primary CEP
  construction has an exact finite combinatorial core: multinomial expansion and the bound on
  multiset permutation counts prove equation (3.11) for every finite prime
  packet. Finite distributivity lifts this to an arbitrary family of prime
  bands. Unique factorization proves that pairwise disjoint bands give an
  injective combined-product map, so the full product is a reciprocal sum over
  distinct integers; every target is certified `y`-smooth and bounded by `y`
  to the total selected multiplicity. The exact counting step (3.5) is now
  compiled too: high-prime packet multipliers paired with all `w`-smooth
  cofactors inject into the ambient `y`-smooth finset, giving
  `sum_m psiNat (X/m) w <= psiNat X y`. A uniform cofactor density converts
  this to equation (3.10), and composition with the collision-free packet
  inequality gives the exact finite (3.10)--(3.11) lower-bound bridge. The
  source specialization is now exact as well: the open--closed intervals use
  CEP's reversed exponents, are proved pairwise disjoint, the normalized
  exponential weights satisfy `sum_j alpha_j=1`, and the multiplicities are
  exactly `floor(alpha_j*u)`.  Their combined packet specializes (3.11) and
  (3.10), with the lowest band endpoint discharging the high-prime premise.
  The exact reverse weighted moment and its closed geometric expression are
  proved, flooring errors give the finite multiplier-size inequality (3.6),
  and every generated multiplier satisfies that lower power bound.  A
  source-band cardinality is now identified exactly with the difference of
  `Nat.primeCounting` at its floored endpoints. A
  cardinality-to-reciprocal-mass lemma therefore reduces the bandwise analytic
  input to that literal prime-count difference; any such verified estimate now
  propagates through the displayed source (3.11)--(3.10) packet.  The
  canonical cofactor cutoff is the floor of the lowest band endpoint, and
  `X^(1/(log X/log y))=y` identifies the canonical source cutoff exactly with
  the original natural `y`; thus the packet now feeds directly into
  `psiNat X y` without a rounding loss. The new coarse CEP specialization uses
  fixed dyadic PNT blocks instead of shrinking bands. It proves endpoint
  reciprocal mass at least `1/(16 log 2 log u)`, chooses multiplicity
  `floor(u-2u/log u)`, bounds cofactor depth by `10u/log u`, and bounds total
  secondary loss by `60u log(log u)`. The theorem
  `IsTaoCriticalSmoothRegime.hasCriticalSmoothLowerSaddle_coarseCEP` constructs
  the concrete saddle packet, and
  `IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat` gives the
  sharp critical lower half unconditionally. Therefore the quantified upper
  and lower conclusions in both parts of Proposition 2.1 are compiled and
  axiom-audited. The exact shrinking-band construction remains documented as
  an optional source-faithful alternative. Uniform diagonalization over the
  fixed block `z<p<3z`, its reciprocal-prime mass, and the exact `B¹` sum now
  prove `x/z^(2+epsilon) <= badOneTermCount x` eventually. The upper proof
  combines the rounded square-root range, a finite exponent grid through
  `z²`, and the reciprocal-square tail. Hence
  `badOneTermCount_quotientPowerScale` proves Lemma 1.6(i).
  `TaoLemma16iiConclusion` is the exact natural-cutoff statement of part
  (ii), and cutoff monotonicity proves its automatic direction for both
  contractions and expansions. The missing direction is precisely the
  reverse analytic comparison supplied in the source by Granville (3.24).
  The exact saddle parameter underlying that formula is now constructed and
  proved unique and tends to `1` in every critical regime. Its curvature is
  at least `log(2) log(X)` and hence diverges, while an exact secant bound
  controls cutoff sensitivity; fixed dilations change the saddle by
  `o(1/log y)`.
  `SmoothNumberSaddlePhase` defines the literal logarithmic Euler-product
  phase and Gaussian main term, proves `phase'=log(X)-phiOne`, recovers the
  exact Euler product by exponentiation, evaluates Rankin's inequality at the
  saddle, and proves that saddle is the unique positive global phase minimum.
  The two minimum phases are squeezed between the old and new saddles times
  the logarithmic cutoff increment; hence fixed dilation changes the minimum
  phase by `log(c)`. `SmoothNumberSaddleCurvature` proves a uniform
  prime-local logarithmic derivative bound, the `phiTwo` quotient limit `1`,
  and the complete Gaussian main-term quotient limit `c`. The uniform
  asymptotic evaluation of `Psi`
  remains the missing analytic comparison.
  The polylogarithmic source regime is encoded by `log X/log x -> 1` and
  `log y/log₂x -> A` for fixed `A>1`. The natural scale
  `taoPolylogUZero=log x/log₂x` diverges, `u/taoPolylogUZero -> 1/A`, and
  `sigma -> 1-1/A`. The quadratic depth envelope, full scalar estimate, and
  finite Rankin insertion follow. The normalized saving tends to `1/A`, the
  positive dyadic error is `o(log x)`, and the audited conclusion is
  `Psi(X,y) <= X/x^(1/A-epsilon)` for every fixed positive `epsilon`.
  The matching polylogarithmic lower bound is audited.  The exact integral
  depth `k=Nat.log y X` satisfies `y^k<=X` and has normalized limit `1/A`;
  its logarithm has limit `1` on the `log₂x` scale.  The frozen PNT gives
  `log(primeCounting y)/log₂x -> A`, hence eventually `2k<=primeCounting y`.
  Products of `k`-element prime subsets form an injective family of smooth
  naturals below `X`, and the integral binomial entropy inequality yields
  `x^(1-1/A-epsilon) <= psiNat X y` for every fixed positive `epsilon`.
  The Section 6 bad-interval pipeline now includes the corrected normalization
  and maximal transfer, the condition-(ii) exceptional-square bound, and the
  source-faithful condition-(i) cofactor sieve. For the latter, both endpoint
  orientations give exact affine restrictions on `m≤⌊2x/p₀²⌋`, Corollary 2.9
  yields the factor-`16` fixed-fiber estimate, and the PNT supplies the base
  `H/(8k log(2p₀))`. The floor-defined degree has proved strict maximality,
  giving `2x<(2p₀)^(2k+4)` and `log(2x)/log(2p₀)<2k+4`. On `k≥4` the valid
  quarter-bound and a stronger large-`H` absorption produce the explicit
  `H^(-0.9(k-1))` decay and canonical exponential fiber estimate. The literal
  long-interval cutoff now discharges the denominator comparison eventually.
  Exact AM--GM optimization in the prime scale then proves that the saddle
  numerator is at least `(9/2) log x log₂ x` and bounds the canonical `k≥4`
  fixed fiber by `128x/(p₀ z(x)^6)` eventually, subject only to the displayed
  PNT/cardinality, large-budget, and degree side conditions.
  The source's printed quarter comparison is repaired on its full `k≥2`
  range by the valid eighth-comparison. A `22/25` absorption and the resulting
  `11/100` saddle coefficient still give `128x/(p₀ z(x)^4)`. On the exact
  source upper range `p₀^20≤x^3`, nonempty fibers supply `p₀²≤2x`, degree two
  follows eventually, and the literal long range itself discharges the PNT
  and large-budget hypotheses.
  The exact finite dyadic-length and moderate-prime aggregation bounds the
  reciprocal-prime sum by the harmonic number. Its two logarithmic losses are
  absorbed by one factor of `z(x)`, so the actual long moderate-prime
  normalized failure union satisfies `#union≤x/z(x)^3` eventually.
  The preliminary large-`p₀` branch is also finite and audited on the exact
  ceiling-rounded `H<x^(7/50)` range. The unsieved cofactor cover contributes
  `8Hx/p₀²` per fiber, and the dyadic-length plus reciprocal-square sums yield
  `#union≤x^(199/200)` eventually. Exact natural-power bridges connect
  `H^50<x^7` and `p₀^20>x^3` to the two finite cutoffs.
  The complementary preliminary large-length branch is finite and audited on
  the exact range `H≥x^(7/50)`. At the fixed spare exponent `41/300`, which
  lies strictly between `2/15` and `7/50`, the prime-free length at outer
  scale `2x` is eventually at most `H/2`. A single greedy disjoint selection
  across every length gives the exact incidence bound
  `#union≤6 primeFreeEndpointMeasure(2x,41/300)`; Proposition 2.3(iii) then
  supplies an existential fixed power saving for the actual normalized
  failure union.
  The complementary `k<4` branch forces `2x<(2p₀)^10`; the unsieved cofactor
  cover converts this into the uniform power saving `4096x^(9/10)` per fiber.
  The positive powerful-
  number `a²b³` parameterization with squarefree `b`, including uniqueness,
  is proved and audited as elementary infrastructure for Corollary 2.11. It
  also yields the exact finite squarefree-cube sum for `VB¹`. Dominated
  convergence, the unique square-times-squarefree reindexing, and Mathlib's
  Dirichlet-series formula for Riemann zeta prove the exact
  `ζ(3/2)/ζ(3) √x` asymptotic. All interval predicates now carry the source's
  `H≥1` convention, and the exact type-`F₃`/factorial-square endpoint
  correspondence is proved and audited. On finite ranges, largest-index
  projection is proved to have image exactly `F₃∩[1,x]`, giving the audited
  inequality `factorialThreeCount x ≤ factorialSquareTripleCount x`. The
  one-term set is characterized by square multiples of `s(a!)`; the square
  subfamily gives audited `⌊√x⌋-1` lower bounds for endpoints and triples and
  the full reverse-big-O half of their `x^(1/2+o(1))` scale contracts.
  The exact reduction from repeated factorial squarefree components to a
  square consecutive product is also proved. Bertrand's postulate now rules
  out every such square when `N≤H` and `2≤N+H`; the full square proposition is
  also proved directly at length two and is therefore equivalent to only its
  residual arithmetic core `3≤H<N`. The exact
  Erdős--Selfridge square proposition has a proved finite
  consequence bounding every factorial squarefree-component fiber by two;
  proving its residual short-range arithmetic core remains the explicit,
  source-pinned dependency. The exact counting key
  `(a₃,a₃-a₂-1,a₁ mod 2)` is proved injective under this proposition, and a
  uniform gap bound `a₃-a₂≤g` now gives Tao's literal finite upper transfer
  `#triples(x)≤2g #F₃(x)`. This has also been lifted through the quantified
  asymptotic API: a subpolynomial natural gap budget, the total power-scale
  half of Theorem 1.9, and ES imply the literal `TaoTheorem110Conclusion`,
  with the square family supplying its lower half. Lemma 4.2 is now connected
  to this API by the explicit budget `⌈exp((log x)^(3/4))⌉`; it bounds all
  triple tail gaps, including bounded middle indices, and is proved to be
  `x^o(1)`. Thus no unformalized counting, gap-transfer, or asymptotic
  bookkeeping remains between Theorem 1.9, Lemma 4.2, ES, and Theorem 1.10.
  Tao's complete Lemma 4.1 (`abound`) is now unconditional:
  every type-`F₃` interval satisfies `H<N`. Its exact triple specialization
  `a₃-a₂<a₂` is also proved, as is the resulting fact that no member of such
  an interval is prime. For its quantitative conclusion, the product of the
  primes in `(a/2,a]` is proved to divide the interval product, giving the
  exact inequality `θ(a)-θ(⌊a/2⌋)≤H log(N+H)`. The pinned PNT supplies an
  eventual lower bound by `a/4`, and the finite exceptional range is absorbed
  into one uniform positive constant, proving `a ≪ H log N` literally.
  The common arithmetic spine of Lemma 4.2 is also complete. At Tao's exact
  scale `P=H log²N`, Lemma 4.1 puts `a<P` eventually. Equality of squarefree
  components then forces every prime `p>P` to have even interval-product
  valuation, concentrated in a unique interval element because `p>H`. In the
  large-`P` branch `√(2N)<P<p`, the resulting `p²` divisor is larger than the
  endpoint, proving that `p` cannot divide the product. The normalized
  large-`P` cutoff has a uniform `O(log^12 N)` `C³` bound; its reciprocal-mass
  sandwich and final logarithmic contradiction are complete. The exact
  proposition-valued Proposition 2.3(ii) interface supplies `4P≤N`, closing
  this branch conditional on that interface and Theorem 2.5. In the low-`P`
  branch, the explicit two-coordinate cutoff is smooth and periodic, its
  support gives an exact arithmetic zero sum, its `C³` cost is
  `O(log^12 N)`, and Theorem 2.5 gives the uniform upper bound. Exact
  reciprocal and quadratic substitutions, endpoint trimming, occupied-cell
  insertion, and the positive quadratic-bump minimum give the matching
  `H/1920` set-measure and integral lower bounds. The final contradiction and
  low/high case split are compiled. The remaining Lemma 4.2 input is the
  analytic BHP proof behind Proposition 2.3(ii). The source-shaped backward
  interval theorem is separately declared and proved to imply the exact Tao
  interface: the `N+2N^(21/40)` sampling shift handles endpoint orientation,
  and Bertrand absorbs the finite initial range into one uniform constant.
  Lemma 4.3 is now reproducible in full finite form. Canonical square
  decomposition gives positive squarefree coefficients supported on primes
  at most `P=max(a,H)`. Their interval product divides the exact envelope
  `∏_{p≤P}p^(H/p+1)`, whose logarithm is bounded by
  `log 4·H(2+log P)+log 4·P`. Two-half averaging produces ordered terms and
  the relation `c₁n₁²+h=c₂n₂²`, `0<h<H`, with each coefficient bounded by
  `exp(3 log 4(2+log P+P/H))`.
  The subsequent exact finite Theorem 1.9 reduction is also reproducible.
  Nontrivial endpoint values map to length-at-least-two interval witnesses;
  each chosen Lemma 4.3 certificate, interval length, and selected-element
  offset form an injective interval code. For arbitrary bounds `A,C,G`, the
  endpoint subfamily is bounded by `A·C²·G³` times a rounded uniform Lemma
  2.10 relation count. In the bounded-length refinement, the two coefficient
  intervals are replaced by the exact smooth-number pair finset of cardinality
  `psiNat x P ^ 2`; the resulting endpoint count is bounded by
  `A·psiNat(x,P)²·G³` times the same relation budget. The required logarithmic
  smooth-number specialization is proved directly: iterated retained-smooth
  square decomposition plus Chebyshev gives
  `psiNat(x,⌈C log(x+2)⌉)=x^o(1)`. Lemma 4.1 places the actual `H≤B` family in
  this range, proving its endpoint count is `x^o(1)` for every fixed `B`.
  The small-`a` regime is also complete: at
  `a ≤ H log(x+2)/100`, Lemma 4.3 gives coefficient exponent `1/10`, and the
  exact interval code gives endpoint exponent `1/4` after Lemma 4.2. The full
  quantified Proposition 2.1 bounds are now available; this branch still uses
  the direct logarithmic specialization. The complementary large-sieve
  estimate is completed below without needing the stronger critical input.
  The complementary regime now has an exact finite sieve interface: every
  upper-half prime removes at least `p-H` start residues, fixed `(a,H)` fibers
  inject into the resulting survivor set, and budgeted fibers reassemble with
  an `A·G` loss. Lemmas 4.1 and 4.2 place all such intervals in explicit
  subpolynomial parameter boxes. Pairwise coprimality, the `a^k` product
  condition, the PNT lower count of upper-half primes, the `[-k]` deletion
  loss, and the source-scale lower bound for the literal removed/allowed
  ratio are compiled. Native cyclic DFT Parseval, one- and two-modulus
  Montgomery uncertainty, arbitrary finite tensor uncertainty,
  pairwise-coprime iterated additive CRT, and the finite-support
  simultaneous-residue specialization are also compiled and axiom-audited.
  Tensor characters are injectively reindexed into one cyclic denominator,
  their Fourier energies agree exactly, and Parseval plus exact interval
  residue-fiber counting supplies the upper inequality and survivor bound for
  one product denominator. The finite Schur Gram bound, exact
  analysis/synthesis identities, and Bombieri duality are also compiled and
  audited, including direct transfer from synthesis energy. The exact
  circle-character Dirichlet-kernel Gram formula and diagonal are compiled in
  a separate arithmetic layer. An injective `L`-fold shift-pair embedding,
  exact difference-synthesis identity, squared-Dirichlet Fejér Gram identity,
  Schur synthesis estimate, and operator duality reduce the circle large sieve
  without loss to Fejér row/column bounds. `LargeSieveSeparated` proves the
  separated-circle row-sum estimate by centered representatives and radial
  bins, giving an explicit `8L` analysis bound for every finite
  `1/L`-separated family. The rational, fixed-selection, and aggregation
  layers compute the CRT numerator, prove nondivisibility and exclusive-modulus
  cross-denominator distinctness, identify the circle and tensor energies,
  and derive the finite global Corollary 2.8 survivor inequality without a
  subset-count loss. The exact fixed-cardinality selection count, binomial
  lower bound, elementary-symmetric denominator, literal factorial residue
  restrictions and ratio product, survivor transport, and source-scale
  Corollary 2.9 fixed-fiber estimate are now compiled and audited. The
  maximal-degree specialization, uniform fiber estimate, nonempty-fiber
  reassembly, and absorption of the subpolynomial budgets are compiled and
  audited as well. Together with the `O(log x)·⌊√x⌋` cover for the literal
  one-term family, this proves `TaoTheorem19Conclusion` from Lemma 4.2 and
  reduces it exactly to Theorem 2.5 plus the prime-gap input.
  All three source-facing total counts are proved to decompose exactly into
  their nontrivial and one-term value counts.
  The `b=1` powerful-number family gives audited `⌊√x⌋` lower bounds for
  `VB¹` and `VB`, together with their reverse-big-O square-root lower halves.
  Termwise domination of the exact `VB¹` sum by the convergent `b⁻³ᐟ²`
  p-series gives the summable majorant used in the audited normalized limit;
  its squarefree p-series constant is proved equal to the public zeta ratio.
  The complete finite and asymptotic Theorem 1.8 assembly is proved
  conditional on Lemma 3.1, hence conditional only on Theorem 2.5. Every
  nontrivial value below `x` lies in a bounded witness interval; each interval
  injects into a chosen Lemma 3.2 certificate together with its length and one
  offset. Explicit subpolynomial natural length and coefficient budgets reduce
  the count to `A²G⁴` times one uniform Corollary 2.11 fiber, proving the
  nontrivial `x^(2/5+o(1))` bound and then the literal zeta-ratio endpoint.
  The exact-once prime divisor lemma and the positive-start `H<N` conclusion
  of Tao's Lemma 3.1 are also proved; the documented `{1}` edge case prevents
  claiming the unrestricted wording verbatim.
  The arithmetic and Theorem 2.5 interface for the stronger clause now also
  compile: a prime `H<p≤2H` dividing an interval element must divide it twice;
  the exact source rectangle `{N/p}≥0.9`, `{N/p²}<0.9` contradicts this; every
  supported periodic weight therefore has zero prime sum. The explicit
  sine/flat-exponential cutoff is proved nonzero, nonnegative, `C∞`,
  `ℤ²`-periodic, and supported in this rectangle; the specialized Theorem 2.5
  contract yields its integral upper bound. The contradiction growth
  hypothesis supplies the exact positive source exponent with multiplier one.
  The cutoff has a fixed positive minimum on the inner rectangle, the integral
  is real and nonnegative, and its norm lower bound is reduced to the measure
  of the explicit inner prime-scale good set; reciprocal membership is
  transported exactly. Both source substitutions and their Jacobians compile.
  The quadratic band has exact period mass `43/50`; its uniform slice lower
  bound implies quadratic reciprocal-set measure at least `H/32` under
  `N/H²≥1/2`. The finite disjoint unit-cell argument, endpoint trimming, and
  reciprocal Jacobian give the complete geometric lower bound `H/400`. The
  standard binomial Sylvester--Schur contract and the exact interval-product
  contract are stated, and their bridge is proved. More importantly, the
  frozen PNT and exact factorization/binomial bounds prove the large prime
  uniformly in the sufficient quadratic window for all large `H`. Thus
  `N/H²≥1/2` and the `H/400` measure bound are unconditional eventually; the
  unrestricted classical contract is no longer a release dependency. A fixed
  cutoff constant and the fixed specialized-Theorem-2.5 constant are selected
  before the eventual quantifiers; the audited two-logarithm comparison then
  proves the complete eventual Lemma 3.1 contradiction and exact corrected
  fixed-slack `TaoLemma31Conclusion` conditional on
  `TaoTheorem25SpecializedConclusion`.
  Combining this contract with the proved certificate encoding and uniform
  Corollary 2.11 gives audited endpoints
  `taoTheorem18_of_taoTheorem25Specialized` and
  `taoTheorem18_of_taoTheorem25`; no further Section 3 bookkeeping remains.
  Theorem 2.5 and Fourier hypotheses use Mathlib's genuine
  `C∞` index `∞`; `⊤` in this toolchain denotes analytic regularity and would
  incorrectly exclude every nonzero compactly supported cutoff.
  Lemma 3.2's canonical exponent-one coefficient/powerful-core split, its
  small-prime support, factorial divisibility, and exact two-position linear
  relation are proved. The exact coefficient-product divisibility, finite
  Abel/Chebyshev envelope estimate, two-half averaging, fixed-power coefficient
  bounds, and final nonzero-shift powerful relation complete the lemma.
  The finite powerful-pair count used in Corollary 2.11 is also reindexed
  bijectively by the unique square-times-squarefree-cube parameters, with its
  exact cardinality preserved. For Lemma 2.10, the coefficient product now has
  an audited squarefree-discriminant decomposition and every square-discriminant
  solution for any nonzero integer shift injects into the signed divisors of
  `a*h`; the resulting divisor-epsilon bound is proved. The literal
  `bm+cn√D` norm point is injective, and norm-one
  Pell solutions are proved to act on each fixed-norm fiber of `ℤ[√D]`. The
  fundamental unit's powers have a proved exponential coordinate lower bound,
  giving exactly `2 log₂(B)+1` candidate powers under a coordinate bound `B`.
  On every nonzero fixed-norm fiber, equality of generated principal ideals is
  proved equivalent to membership in the same norm-one Pell orbit. Each such
  principal ideal is also proved to divide `(N)`, so the ideal-divisor map has
  exactly the Pell orbits as its fibers. The Galois fundamental identity is
  specialized abstractly to prove that a prime has at most two primes above it
  in any Dedekind Galois extension with group order two. The concrete
  `ℚ[X]/(X²-D)` field is proved irreducible and quadratic, its square root is
  proved integral, and `ℤ[√D]` embeds injectively into the actual maximal order.
  Fixed-norm points generate members of a constructed finite set of ideal
  divisors of `(N)` there, with fibers exactly the maximal-order association
  classes, and the two-primes-above bound is instantiated for this concrete
  order. The field is proved totally real of signature `(2,0)`, so Mathlib's
  Dirichlet theorem gives unit rank one; the torsion subgroup is proved to be
  exactly `{±1}` and every unit has a unique torsion-times-power
  representation. An oriented generator has a selected real-place growth
  base `λ_D>1`, and a `B log λ_D` cutoff leaves at most `2(2B+1)` explicit
  unit candidates. The sharp `d(|N|)^2` ideal-divisor cardinal bound, the
  transfer from boxed norm-point coordinates to that place cutoff, and a
  uniform lower bound for `λ_D` are proved, closing Lemma 2.10 for nonzero
  signed shifts and polynomially bounded parameter families. Corollary 2.11
  is also complete: exact dyadic fibers, both coordinate bounds, the Lemma
  2.10 cube-base fiber, `2/5,2/5,1/5` interpolation, logarithmic absorption,
  negative-shift symmetry, and the uniform `a,b,|h|≪ x` family theorem are
  all kernel-checked and axiom-audited.
  The exact complex-valued finite prime sum, logarithmic integral,
  `ℤ²`-periodicity and sum-of-orders `C³` convention for Theorem 2.5 are now
  compiled. Its `M=N,j=2` consumer is
  formally derived from the full contract. The reciprocal phase and additive
  character are defined, and the exact all-orders derivative identity,
  including the source's binomial `M_r` coefficient and normalized absolute
  form (expint1), is proved and audited. The source bounds
  `1 ≤ binom(r+j-1,j-1) ≤ (r+j)^r`, the corresponding absolute coefficient
  bounds, and upper/reverse-triangle/dominant-term derivative inequalities
  are proved as well. The Type I product rescaling and exact Type II
  conjugate correlation phase displayed in the source are proved too. The
  exact arithmetic-function cutoffs
  and four-term Vaughan identity are also proved, both pointwise as nested
  finite divisor sums and after complex weighting by the reciprocal phase.
  `VaughanCoefficients` reassociates this identity into the source's two Type I
  pairs and one Type II pair. Its four canonical coefficients satisfy the
  absolute bounds `1`, `log P`, `1`, `log P` on positive arguments at most
  `P`; their cutoff/tail support statements and the literal product-restricted
  weighted identity are proved as well.
  The Type II inner sum times its conjugate is expanded into the exact double
  coefficient-correlation sum, with every phase rewritten to the displayed
  `X_{n,n'}` reciprocal phase. Summing over the outer support gives the exact
  rearranged correlation sum, and finite Cauchy--Schwarz bounds the bilinear
  outer sum with an explicit coefficient envelope and support cardinality.
  The diagonal is evaluated as `#K`, split exactly from the off-diagonal
  correlations, and bounded by `#K·#S·L²`; the residual estimate contains only
  explicit off-diagonal `X_{n,n'}` norms. A uniform bound for those norms is
  propagated over the exact ordered-pair envelope `#S(#S-1)`.
  Both transformed Type II reciprocal coefficients are proved nonzero off the
  diagonal under the source's positive-index and nonzero-coefficient
  hypotheses.
  Their exact absolute values and quantitative support bounds are proved,
  including the mean-value factor `|n'-n|·j·B^(j-1)` and positive-lower-support
  denominator estimates. The combined scale is normalized at `KR` to expose
  the source factor `|n'-n|/R`, with higher loss `j(B/R)^(j-1)` and dyadic
  factor `j·2^(j-1)`. The literal product-restricted inner sum is also
  rearranged into correlations on `K ∩ (1/n)I ∩ (1/n')I`; its diagonal is
  evaluated exactly and bounded by `#K`. The restricted expression is split
  into diagonal and off-diagonal pieces, and a uniform off-diagonal bound is
  propagated through `#S(#S-1)` to the final real squared-inner-sum estimate.
  The Type I inner and outer sums are likewise defined with variable inner
  supports; their exact `N/m, M/m^j` rescaling and coefficient-envelope
  triangle reduction are proved.
  The normalized derivative is identified exactly with `1/t` times the
  source's critical expression `N+M_r/t^(j-1)`. Its two-point sublevel
  inequality, power-difference lower bound, quotient diameter estimate, and
  one-interval cover are proved. Under `t^(j-1) ≤ 2X^(j-1)`, each derivative
  order is covered by an interval of length at most `16Xq`; the corresponding
  single-order and finite-union Lebesgue-measure bounds are also proved.
  The corresponding lattice-point bounds `16Xq+1` and
  `#orders·(16Xq+1)` prove the discrete deletion bookkeeping.
  The weighted Mangoldt sum is split exactly into the prime-logarithm phase
  sum and its non-prime tail; unit modulus bounds that tail by the frozen
  explicit local higher-prime-power estimate.
  Exact finite Abel summation and an explicit `2 log b` norm bound reduce the
  logarithm-weighted alternate Type I form to uniform unweighted prefix-sum
  estimates. Conversely, prime-log prefix bounds control the unweighted prime
  reciprocal-phase sum with the exact factor `1/log a`.
  The low-frequency phase branch has the explicit pointwise derivative bound
  `(j+1)F/X`, additive-character Lipschitz and total-variation bounds, and an
  exact complex Abel reduction. Consequently the Mangoldt phase sum differs
  from the integer phase sum by at most `(1+2π(j+1)F)B` whenever `B` bounds
  all initial-subinterval partial sums of `Λ-1`. The frozen `WeakPNT` is now
  connected to this reduction: global discrepancy is `o(k)`, uniformly every
  subinterval of `[P,2P]` has discrepancy `o(P)`, and every fixed bounded
  reciprocal-phase scale gives an `o(P)` Mangoldt-to-integer phase
  comparison. The stronger quantitative PNT estimate needed when the scale
  grows polylogarithmically remains open.
  Finite two-dimensional Fourier polynomials are evaluated exactly as
  reciprocal phases with integer-rescaled parameters. Their prime sums and
  logarithmic integrals are interchanged with the finite mode sum, and the
  total discrepancy is bounded by the coefficient-weighted mode errors (or
  the coefficient `ℓ¹` norm times a uniform mode error). Integer frequency
  rescaling is also propagated through the explicit Vinogradov parameter
  bound. The source interval assumptions now discharge mode integrability,
  and the retained square box has exact cardinality `(2R+1)²`, yielding the
  explicit mode-count × coefficient-envelope × error bound. Fourier
  modes in that box inherit both Vinogradov parameter bounds uniformly with
  positive enlarged constant `(R+1)K`. Uniform approximation by a continuous
  Fourier polynomial now transfers to the full weight with explicit errors
  `(2P+1)δ` in the prime sum and `Pδ/log P` in the integral; continuous
  source weights are proved integrable automatically. Fourier coefficient
  tails between nested finite mode sets are bounded uniformly by their exact
  discarded `ℓ¹` norm and propagated through the full discrepancy. The
  source's cubic envelope `(1+|n|+|m|)^(-3)` is proved summable on `ℤ²`; the
  square frequency boxes exhaust `ℤ²`, their outer `ℓ¹` tail tends to zero,
  and coefficients under this envelope generate uniformly convergent finite
  square Fourier polynomials. A continuous `ℤ²`-periodic plane weight is now
  descended through the open quotient `ℝ² → (ℝ/ℤ)²`; Mathlib's torus
  characters are identified with the source's `fourierMode2D`, and its
  Fourier coefficients are identified with their literal fundamental-square
  integrals. Mathlib's reconstruction theorem proves that coefficients satisfying the
  cubic envelope give square partial sums converging uniformly to the
  original `W`. The exact unit-interval integration-by-parts identity is now
  iterated three times and gives a cubic frequency bound by the norm of the
  third derivative. Fubini factorization of the actual two-torus coefficient
  is proved in both coordinate orders, the torus slices are identified with
  unit-interval coefficients, and the cubic derivative bound is propagated
  to either nonzero coordinate frequency. The zero mode and directional bounds
  are combined into the source radial envelope with constant `27`. Iterated
  derivatives inherit periodicity, their norm ranges are bounded on the compact
  fundamental square, and automatically constructed pure coordinate chains
  give the unconditional `taoC3Norm` coefficient estimate.
  The `j=1` phase and its finite prime sums are proved exactly equal to the
  `j=2, M=0` case after absorbing `M` into `N`.
  The finite core of the shorter-than-dyadic decomposition is proved: exact
  quotient-block regrouping, ceiling control of the block count, and strict
  within-block diameter. Every coefficient sequence supported on the original
  interval is also decomposed exactly, pointwise and in arbitrary finite
  weighted sums, into block restrictions that preserve uniform norm bounds.
  The canonical shorter family over `[1,B]` has budget
  `(log₂ B+1)^101`, exact cardinality `(log₂ B+1)^102`, and covers every
  positive coefficient index. Exact weighted coefficient decomposition and
  the final one-family Type I/two-family Type II identity are proved, with
  `m*n∈I` retained. The real-log comparison and extra subdivision power absorb
  ceiling rounding and prove literal support width
  `(1+log(B)^(-100))M`, including singleton small bands. The monotonic `P≤B`
  transfer gives the paper's literal
  `(1+log(P)^(-100))M` form. Vinogradov/Weyl cancellation and the resulting
  quantitative Type I/II estimates remain open.
  Independently, every finite weighted divisor-antidiagonal convolution is
  reindexed exactly into a bounded product box with the literal condition
  `m*n∈I`. Reassociation of the nested terms puts all three convolution terms
  of the reciprocal-phase Vaughan identity into this product-restricted form.
  Each bounded product sum then decomposes exactly into quotient blocks of its
  outer coefficient, and into double quotient blocks of both coefficients,
  while retaining the product restriction. The counted canonical family, its
  exact Type I/II decomposition, and its literal real-log width bridge are
  proved. The coefficient envelope is also complete.
  For an interval prime support and a quotient outer block, the filtered
  Type II correlation support is identified with one explicit half-open
  interval using exact ceiling-divided endpoints. Its length is at most the
  outer block length, and the canonical Vaughan correlation is rewritten
  exactly as `reciprocalPhaseSum` on that interval.
  The unconditional analytic engine now starts in `WeylDifferencing`: exact
  shifted-pair fibers prove the `H`-fold averaging identity and its finite
  Cauchy--Schwarz inequality, followed by an exact expansion and regrouping
  of window squares under `n+h=n'+h'`. Both shift orders reduce to truncated
  forward correlations or their conjugates; natural-distance regrouping then
  supplies a real and divided finite van der Corput inequality with strict
  lag range. The zero lag, uniform recursive majorant, translated source
  reciprocal phase, appended-lag rule, sampling identity, and positive-ray
  derivative commutation are proved. The exact terminal affine geometric-sum
  identity and its nonresonant `min(N, 2 / ‖e(alpha)-1‖)` estimate are proved
  as well. Its denominator is identified as `2|sin(π alpha)|`, bounded below
  by four times the canonical nearest-integer distance, and converted into
  the standard `min(N, 1/(2 dist(alpha,ℤ)))` form. Uniform bounds at any finite
  difference depth now propagate to the root through an explicit recursive
  square-root majorant, and a source-facing theorem instantiates exactly four
  rounds for the cited `k=5` branch. A one-step real finite difference is also
  exactly an interval integral of its derivative, with proved absolute upper
  and signed lower derivative-separation bounds. On the positive ray these
  bounds now localize to the exact evaluation interval
  `[x, x + sum(lags)]` and iterate through any lag list with its exact lag
  product. Direct reciprocal-phase specializations give both the raw upper
  bound and the critical-regular normalized lower bound; continuity and the
  intermediate value theorem supply the constant sign needed for the latter
  from an absolute derivative separation hypothesis. The derivative of every
terminal iterated phase is identified with the corresponding difference of
the next original derivative and has a uniform critical-regular two-sided
window frozen at `X` and `2X`; four lags therefore consume the fifth source
derivative exactly. The frozen radian-normalized Kusmin--Landau estimate is now
adapted exactly to `exp(2πix)`. Mean-value and second-derivative sign bridges
convert absolute terminal derivative windows into monotone increments, and the
resulting source-facing theorem proves the nonlinear critical-regular terminal
  sum bound under explicit expanded-interval and upper-one-period hypotheses.
  Admissible lag sums and products are bounded by `rH` and `H^r`, giving a
  uniform terminal theorem for all admissible lag lists and truncated lengths
  on one expanded regular interval and a direct composition through the
  recursive majorant. Its literal four-round form uses derivative orders five
  and six and one worst-case `H^4` upper-smallness condition.
  An exact lag-sensitive Weyl tree additionally retains the accumulated lag
  list and boundary-truncated length at every node. The reciprocal-phase
  terminal estimate feeds it with the leaf profile
  `min(L, 1/(prod(lags)*scale))`; the innermost lag sum is bounded by the exact
  harmonic factor `harmonic H`, and the corresponding one-level square-root
  bound is proved. Every successive outer lag sum is then collapsed by a
  general induction to the closed scalar envelope `weylLagClosedMajorant`,
  whose length and scale coefficients contain exact generalized harmonic
  factors bounded by `H`. Successive Cauchy--Schwarz estimates additionally
  retain their sharp product `H^11 * harmonic(H)^4`, producing the terminal
  sixteenth-power bound
  `(6L)^15 * harmonic(H)^4 / (H+1)^4 / scale` and a source-readable global
  wrapper with `harmonic(H) <= 1 + log H`. Its four-round source
  specialization is proved, and
  the fourfold scale square root is verified by an exact sixteenth-power
  identity. Replacing those factors by `H` gives a coarse scale recurrence
  whose four-round coefficient has exact sixteenth power `(QH)^15`; including
  the terminal inverse scale gives `(QH)^15/scale`. This coarse source-facing
  majorant is proved. The length recurrence is split into four explicit
  nonnegative terms with exact sixteenth powers `D^8`, `E^8 D^4`, `E^12 D^2`,
  and `E^14 D`; exact step-factor bounds convert these to powered denominator
  estimates with exponents `8,4,2,1`. These and the coarse scale estimate are
  extracted as sixteenth roots and rewritten exactly as real `1/16` powers in
  a source-facing five-term majorant with no hidden recurrence.
  The canonical floor-rounded range `floor((2U)^(-1/4))` is defined for the
  explicit upper scale `U`, proved to satisfy the exact upper-smallness
  condition, and installed in root and rpow source wrappers. Starts whose
  `4H+1` windows meet a critical set are deleted with the exact finite-order
  bound `orders.card*(16Xq+4H+2)`. Their per-order integer interval hulls obey
  the same bound, and their endpoint cut set has size at most
  `2*orders.card`; consequently the regular multiplier is exactly
  `2*orders.card+1`. Real expanded-interval regularity is recovered off these
  hulls, and a global arbitrary-upper-small-range source envelope handles both
  long and short components. Its adaptive specialization uses
  `min(L, floor((2U)^(-1/4)))`, which automatically fits the interval and
  preserves upper-smallness. The exact inequality
  `(H+1)^(-4) <= 2U+(L+1)^(-4)` combines its two branches in one effective
  majorant. A further audited wrapper chooses critical width equal to the
  `1/128` power of `2U+(L+1)^(-4)+1/F`, normalized exactly to
  `240(5+j)^5 F/X^5+(L+1)^(-4)+1/F` and bounded by the derivative-order factor
  times this source-shaped error.
  The further optimized range `min(floor(L*q), canonicalRange)` inherits
  upper-smallness, and its cast, expanded margin, and logarithm are bounded by
  `Lq`, `4Lq+1`, and `log L`, respectively. The global component theorem is
  instantiated at this range with those penalties substituted explicitly.
  Its terminal denominator is bounded by `2U+(Lq)^(-4)` and propagated through
  a fully explicit optimized terminal root. The four diagonal roots are then
  bounded by `72Lq`, the terminal root by
  `100((5+j)^5+1)(1+log L)Xq`, and the full optimized majorant by the analogous
  constant `172`. Both the global fixed-power component theorem and its
  explicit source-normalized `1/128`-power form compile and are audited. The
  additive endpoint is also absorbed, yielding one explicit coefficient times
  `X` and that source power. Under `F≤X^4`, an exact short/long dichotomy removes
  the interval-length term on arbitrary subintervals and gives the explicit
  two-term width `(F/X^5+1/F)^(1/1024)`.
  For the subsequent Type II decay-kernel summation, fixed natural-distance
  fibers are proved to have cardinality at most two, sums are regrouped
  exactly by distance, and nonnegative kernels incur only this factor two.
  The source real-power decay kernel is defined and proved nonnegative,
  normalized to one at distance zero, and antitone under `R>0`, `F≥0`, and
  `c≥0`. The discrete distance sum is bounded by one plus the corresponding
  real integral, which is evaluated exactly using a proved affine-rpow
  antiderivative, yielding a closed-form finite-sum bound. The bound is
  normalized exactly to `N_r F^{-c}`. The all-support theorem correctly
  retains `1 + O(N_r F^{-c})`, and its distance-zero lower bound shows why.
  In the actual off-diagonal use the center is erased first; the zero-distance
  fiber is proved empty, so the positive-distance sum is bounded directly by
  the integral and has a pure `N_r F^{-c}` bound with no endpoint condition.
  This strengthened estimate is propagated through the complete
  product-restricted squared-inner-sum reduction, its actual short-block
  specialization, and the exact Vaughan outer/inner double blocks.
  A pointwise restricted-correlation estimate of the exact source shape
  `Q(A·kernel(|n-n'|)+E)` is now summed over the ordered off-diagonal pairs,
  preserving the decay and counting the additive error exactly. This estimate
  is substituted into the product-restricted Cauchy--Schwarz rearrangement to
  give the corresponding real squared-inner-sum inequality.
  The result is specialized first to an actual shorter-than-dyadic coefficient
  block, whose diameter theorem supplies the distance bound, and then to the
  exact outer/inner double blocks produced by the product-box Vaughan
  decomposition. Since those blocks begin at one, membership also supplies
  every nonzero reciprocal-phase index required by the rearrangement.
  Each quotient block is proved to have cardinality at most its chosen length.
  Both support cardinalities are then eliminated from both the conservative
  and endpoint-free double-block estimates in favor of the explicit lengths
  `qouter` and `qinner`; the source-facing endpoint-free theorem contains no
  artificial additive `1`.
  The analytic and finite Type II layers are now connected in the equal-phase
  specialization used by Tao. The transformed scale has a proved lower bound
  by natural distance times half the original phase scale. Consequently the
  two-term Weyl width is bounded uniformly by
  `E^(1/1024)+4(1+distance*F/B)^(-1/1024)`. The varying correlation-interval
  logarithm is dominated by the fixed outer block length, and this pointwise
  estimate is substituted into the endpoint-free kernel theorem to obtain the
  exact Vaughan double-block squared-sum bound. A further wrapper discharges
  the pairwise `F'/K^5≤E` estimates uniformly: the named
  `typeIIShortIntervalScaleError` uses the block left endpoint for reciprocal
  support and its length for separation. In the quadratic wrapper, one
  outer-block expansion margin supplies the interval endpoints and the linear
  power-evaluation bound automatically. The transformed-scale condition also
  follows algebraically when the uniform block error is at most `1/K`. In the
  quadratic case this comparison is now derived on large inner bands from
  `10F≤K^4(log Bcap)^100`: logarithmic block width gives `10qF≤K^4R`, and the
  reciprocal-phase scale estimate then obtains
  the former monomial condition `5q|N|≤K^5R^2` internally. The
  endpoint-free kernel and Weyl propagation are generalized to arbitrary
  positive endpoints and then specialized to the exact named dyadic Vaughan
  blocks. Pairwise effective errors are bounded by the named scalar
  `typeIIShortIntervalEffectiveErrorBound`; its `1/128` power controls the
  optimized range. The logarithmic block-width theorem proves `5q≤K` on bands
  above the subdivision budget, automatically closing the expansion margin.
  Consequently the canonical dyadic theorem exposes the low-frequency
  source-scale condition rather than an abstract block-error or derived
  monomial hypothesis. It now splits pairs at
  `distance·F/B=3`: nearby correlations are bounded trivially and absorbed by
  the kernel lower bound `1/4`, while far pairs have inverse transformed scale
  at most `2/3` and consume the explicit `1/4` upper-scale budget. That budget
  follows from the pair-local `F'/K^5≤1/K`; the standing `2≤log Bcap` assumption proves the common
  subdivision budget is at least `4·(240·7^5)`, so no second monomial or
  threshold hypothesis remains. The
  generic and canonical `..._norm_sq_le_weylVinogradov_quadratic_additiveError`
  wrappers now perform the source's scale split on every far pair. The
  `F'≤K^4` branch is proved by four-step Weyl with a pair-local effective-error
  budget and contributes `E^(1/1024)`; only the target correlation bound for
  `K^4<F'`, carrying an independent nonnegative error `V`, remains as an
  analytic argument. The
  source inequalities and logarithmic consequences needed to absorb the
  retained uniform block-error term, and that high-scale Vinogradov bound
  itself, remain pending. The small inner singleton-band branch is closed by
  an exact diagonal-only theorem.
  The high-frequency logarithmic arithmetic is formalized exactly: if
  `ℓ≥1`, `ℓ^d≤F`, and `b+t≤dc`, then `ℓ^b F^(-c)≤ℓ^(-t)`. Direct corollaries
  use `ℓ=log P`, the explicit threshold `P≥e`, and the source's strict
  `log^d P<F` hypothesis.
  Independently, `eventually_exp_neg_log_rpow_le_log_rpow_neg` and its
  polynomial-prefactor variant prove that every source-shaped factor
  `log(P)^b exp(-c log(P)^ρ)` with `c,ρ>0` is eventually at most
  `log(P)^(-A)`. Thus the logarithmic absorption after the pending Vinogradov
  estimate is already exact. The source parameter bound
  `log F≤C(log P)^(3/2-ε)` is also converted exactly to the lower exponent
  `(log P)^3/(log F)^2≥C⁻²(log P)^(2ε)` and combined with that absorption in
  `eventually_log_rpow_mul_vinogradovExp_le_log_rpow_neg`. The source's more
  primitive parameter hypothesis `F≤C exp((log P)^(3/2-ε))` is converted to
  this logarithmic form, with its multiplier retained explicitly, by
  `eventually_log_rpow_mul_vinogradovExp_of_parameterBound`. The source choices
  `α=(log P)^(4A)` and `q=(log P)^(-3A)` discharge the coefficient conditions
  for the full regular-component derivative window, and
  `eventually_vinogradov_alpha_condition_of_parameterBound` proves the
  numerical `10^-3` condition whenever `log X≥c log P`.
  `vinogradovDerivativeCutoff` is the literal source cutoff
  `10⌈log F/log X⌉+1`; its primitive eventual budget theorem includes the
  shifted demand `R+j≤log P` for `j≤(log P)^(1/2)`. The production
  `Vinogradov` module combines this budget with critical deletion and the
  logarithmic coefficient parameters to produce the complete source-cutoff
  derivative window on a regular interval.
  `norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope` consumes a
  local analytic bound stated from precisely that window and propagates it to
  the full interval with the proved regular-component count and explicit
  deletion error.
  `VinogradovExponentialSumEstimate` records the pinned source lemma with one
  absolute constant, the hypotheses `X≥2`, `F≥X^4`, pointwise neighborhood
  smoothness, the numerical condition, and the exact decay
  `αX exp(-2^-18(log X)^3/(log F)^2)`. Its formal Taylor front end identifies
  the literal ordinary-derivative polynomial `F_n(q)`, proves the Lagrange
  remainder and normalized factorial cancellation, and controls the integral
  shift by its exact boundary cardinality. Product shifts are indexed by pairs,
  retaining multiplicities with proved cardinality `V²`; their Taylor errors
  are summed into a uniform envelope, and an exact averaging lemma reduces the
  original sum to a `V²`-normalized Taylor-polynomial pair-sum estimate. That
  reduction also covers intervals shorter than a shift. At the floor-rounded
  source choice `V=⌊X^(1/4)⌋`, the envelope is bounded by `√X` plus the exact
  normalized top-derivative remainder. The literal cutoff, `F≥X⁴`, and the
  `10^-3` condition prove its two displayed factors at most one; `√X+2π` is
  then absorbed into nine copies of the target decay scale. The interval pair
  sum is also split into complete local product sums and a right-boundary strip
  bounded exactly by `V⁴`. Each complete sum is rewritten as a generic
  coefficient-only bilinear polynomial sum after its unit constant phase is
  removed. The exact trivial `V²` bound handles normalized targets at least
  one. Therefore the smallest open residual is
  `VinogradovBilinearPolynomialNontrivialEstimate`; it implies the full named
  exponential-sum proposition with an explicit total constant shift of
  eighteen. The coefficient window is converted to logarithmic form, its
  cubic distortion is controlled by the nontrivial-scale hypothesis, and the
  explicit block `[(4/3)(log F/log X),(7/4)(log F/log X)]` is proved to contain
  at least `R/128` medium coefficients with `c₀=1/128`. The subsequent
  polynomial mean-value argument is now formalized through both Hölder steps:
  `∑ν=V^ℓ`, `∑ν²=J`, the exact equal-power-sum solution count, and the
  unnormalized equation-(16) estimate are proved. The signed power-sum
  difference support is finite, has total multiplicity `(V^ℓ)²`, and is
  contained coordinatewise in `|d_j|≤ℓV^(j+1)`. The conjugate-pair moment
  expansion is regrouped exactly over that support, and the proved bound
  `μ(d)≤J` yields equation (18). Full symmetric-box enlargement and exact
  coordinate factorization are also compiled. The geometric-series reduction,
  capped reciprocal kernel, separated nearest-integer fibers, image count, and
  explicit harmonic integral-test coordinate estimate in Lemma 12 compile as
  well. Its medium coefficients now satisfy a coefficient-free normalized
  logarithmic saving, with the reciprocal cancellation preserved. The scalar
  factors are bounded by fixed negative powers, reindexed over the actual
  medium degrees, and the source block proves the quadratic coordinate-product
  initial saving `V^(-R^2/307200)` times the trivial box square. The scalar-growth
  discharge, native frozen Wooley VMVT, and exact Ford/local count bridge now
  compile. The squared coordinate-box product is now bounded by
  `(3ℓ)^(2R)V^(R(R+1))`; the critical positive exponent is exactly `4ℓ²`, and
  its real-power normalization yields the compiled abstract assembly
  `|B|^(2ℓ²) ≤ C² A V^(4ℓ²+2ε-δ)`. The sharper `c₀=1/4` block now has
  floor-rounded weighted mass `R²/193`; after the `1/1024` scalar cost it gives
  `V^(-255R²/197632)`. Native VMVT loss `ε=δ/128`, exact critical-root
  extraction, the ceiling-sensitive comparison with `4·2⁻¹⁸/s²`, and the
  floor-rounded conversion to twice the exact source exponential decay all
  compile. The exact Section-12 passage now retains the native p-adic data
  `(p,C,B₀)` and produces the critical coefficient `C·(p^(B₀+1)κ_R)^ε`; a
  uniform rooted bound for it implies the established critical coefficient
  contract, while native existence of all other fields is proved. The explicit
  supercritical Ford multiplier `3R+⌊R/5⌋`, loss `3R²/2800`, and `57R³`
  coefficient exponent also compile. At `R≥10000`, the maximal recurrence
  multiplier `4R` is now proved to lie in Ford's source range and gives the
  sharper loss `3R²/8000`. Equation (18) has been reassembled for an arbitrary
  supercritical moment, proving exact cancellation of the main VMVT exponent;
  its cubic coefficient growth is absorbed by the `32R⁴` root into the
  existing absolute `fordUniversalRootCoefficient`, and the full-range Ford
  moment therefore yields an unconditional uniform positive rooted power
  saving. The formal comparison
  `vinogradovFordFull_root_saving_lt_sourceTarget` proves that its extraction
  root is nevertheless too large for Tao's fixed `2^-18` decay, confirming
  that this route cannot replace quantitative control at the critical moment.
  The optimal critical VMVT coefficient is defined
  as the supremum of the normalized counts; it supplies the mean-value bound
  and lies below every other valid witness. Coefficients below any cutoff are
  absorbed into one literal finite sum envelope. At cutoff `1000`, the theorem
  `vinogradovCriticalRootCoefficientBoundAt_of_from1000` glues a rooted bound
  restricted to `R≥1000` to this finite envelope, and
  `vinogradovBilinearPolynomialNontrivialEstimateAt_of_from1000` supplies the
  existing source-facing consumer. The two directions between the witness tail
  contract and uniform scalar boundedness of the optimal rooted coefficient
  are proved, so no stronger choice-dependent hypothesis has been introduced.
  `VinogradovOptimalWooley` further proves directly that the retained p-adic
  data bound both the optimal coefficient and its rooted form by the exact
  Section-12 expression, and maps the Wooley data contract to the optimal
  scalar contract. Bertrand's theorem is used to choose the concentration
  prime in the controlled range `R<p≤2R`; the corresponding bounded-prime tail
  contract already implies the source-facing bilinear estimate. The open
  frontier is therefore exactly the uniform infinite-degree control of the
  concentration constant and starting depth in that displayed expression.
  The coordinate-box factor is separately proved to contribute a critical
  root between `1` and `3`; hence uniform boundedness of the full optimal root
  is equivalent, up to this absolute factor, to boundedness of the VMVT
  coefficient root alone. Its coefficient-only tail condition already implies
  the source-facing bilinear estimate. More precisely, that root is proved
  equal to `C_R^(1/κ_R²)`, and its bound by a fixed `A≥1` is equivalent to the
  unrooted growth condition `C_R≤A^(κ_R²)`. This exact growth condition also
  has a direct source-facing bilinear consumer. At the p-adic level, the single
  root-free residual
  `C·(p^(B₀+1)κ_R)^ε≤A^(κ_R²)` is now a named bounded-prime contract;
  it implies optimal coefficient growth and the final bilinear consumer.
  `exists_norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope`
  proves its complete global reciprocal-phase consumer.
  The intrinsic low-scale theorem uses `F'≤K^4` directly to replace the former
  global block error by `(1/K)^(1/1024)`; this is propagated through the generic
  and canonical mixed Weyl--Vinogradov Type II estimates. Consequently the
  upper source-scale inequality is no longer an input to that hybrid.
  `exists_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov`
  rewrites each actual high-scale correlation to the exact quotient interval
  and applies the source contract with explicit critical-deletion cost.
  The companion logarithmic-envelope theorems replace the exact component
  multiplicities by `log P` and prove that the entire normalized
  principal-plus-deletion expression is eventually at most
  `3(log P)^(-T)` whenever `T+2≤3A`.
  The fixed-constant interfaces preserve one absolute Vinogradov constant
  through all pairs and produce the exact hybrid callback
  `Q(4·kernel+3(log P)^(-T))`; the Vaughan-inner-block specialization derives
  the required transformed-scale upper bound with multiplier `5`.
  `eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov`
  consumes this callback in the intrinsic-error canonical double-block
  theorem, removing the abstract high-pair hypothesis entirely.
  `reciprocalPhaseScale_typeIICorrelation_le_exp_of_dyadicBlock` proves that
  passing to a Type II correlation preserves the same exponential parameter
  class; in the canonical equal-parameter quadratic block the explicit loss
  is exactly the fixed factor `5`.

## Reproduction command

From this node directory:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The command verifies:

1. required project files;
2. all eight pinned source artifact hashes (Tao PDF and TeX archive,
   Baker--Harman--Pintz PDF, Erdős--Selfridge PDF, Granville and
   Canfield--Erdős--Pomerance smooth-number PDFs, and the Singmaster PDF and
   TeX archive);
3. all 1,339 frozen dependency hashes and the exact frozen source file set;
4. the raw-only Mermaid architecture contract;
5. the exact Lean, Mathlib, and imported package pins;
6. direct production-root import coverage and forbidden-shortcut absence in
   production and frozen source; and
7. the warning-free `Tao2026` build and executable axiom audit.

The runner emits no persistent log. Console success is evidence only for the
checkout on which it was run.

## Not yet reproducible

The source crosswalk records the initial definitions, main targets, and proved
Proposition 2.3(i),(iii). There is no proved public endpoint for Theorems
1.7--1.10 and no main-theorem proof release to reproduce. The present
axiom audit covers every current Tao production theorem but is not a substitute
for the eventual public-endpoint release audit.
