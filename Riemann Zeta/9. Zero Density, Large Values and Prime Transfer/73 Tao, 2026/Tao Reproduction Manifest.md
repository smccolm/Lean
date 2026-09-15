# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `prime-equidistribution-2.90`. It
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
- Burgess 1962 prime-modulus precursor: the MathNet archival translation is
  pinned by SHA-256 with theorem and Lemmas 2--4 proof locators. It records
  the moment/amplification architecture but is not the still-needed 1963
  composite cube-free theorem.
- Hasanalizade--Lin--Martin--Luna Martínez--Treviño 2026 explicit cube-free
  Burgess paper: version `2511.17778v2` PDF and TeX source are pinned by
  SHA-256 under CC BY 4.0. Theorem 1.3 and Lemmas 2.1, 2.3, and 2.4 locate the
  moment expansion, complete Weil-type input, and gcd-tuple combinatorics.
  This is auxiliary proof architecture, not a silently imported theorem.
- A public Lean proof of the standard Sylvester--Schur theorem is pinned by
  commit, path, byte size, and raw-file SHA-256 in `Sources/PINS.md`. It is a
  provenance-only reference and is not vendored because the pinned proof source
  has no explicit license. The local development is independent: beyond the
  binomial-to-interval bridge, it proves the theorem uniformly for all starts
  at every sufficiently large interval length, proves monotone propagation in
  the start from the explicit threshold `H^H+1`, and reduces the remaining
  unrestricted theorem to a genuinely finite rectangle. The independent
  local proof now also discharges every start for lengths `H < 49`.

## Lean package

- Package directory: `Extension/`.
- Package/library name: `Tao2026`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Production modules: `Anatomy`, `Intervals`, `Asymptotics`, `BadIntervals`, `BadIntervalMaximal`, `NormalizedBadIntervals`, `TypicalBadIntervals`, `NonTypicalBadIntervals`, `BadIntervalSourceScales`, `BadIntervalLongSieve`, `BadIntervalCofactorSieve`, `BadIntervalLongOptimization`, `BadIntervalLongSaddle`, `BadIntervalLongSum`, `BadIntervalLargePrimeSum`, `BadIntervalSmoothBranches`, `BadIntervalLargeLength`, `Counting`,
  `CoefficientBounds`, `CoefficientProduct`, `CoefficientSelection`, `CriticalIntervals`,
  `FactorialAsymptotics`, `FactorialCoefficientBounds`, `FactorialEquidistribution`, `FactorialFibers`, `FactorialIntervals`, `FactorialOneTerm`, `FactorialOneTermAsymptotics`, `FactorialShortIntervals`, `FourierAssembly`, `FourierApproximation`, `FourierDecay`, `FourierIntegrationByParts`, `FourierRadial`, `FourierSlices`,
  `IntervalMultiples`, `PrimeIntervals`, `PrimeEquidistribution`,
  `PrimePowerReduction`, `PartialSummation`, `PhaseVariation`, `LowFrequency`, `PowerfulAsymptotics`, `PowerfulExtraction`,
  `PowerfulLimit`, `PowerfulNumbers`,
  `PowerfulRelations`, `PowerfulRelationCounting`, `SquareRelations`, `ConvolutionRearrangement`,
  `QuadraticIdealDivisors`, `QuadraticSolutionCount`, `QuadraticUnits`, `ShortIntervalDecomposition`, `SmoothNumbers`, `SmoothNumberBounds`, `SmoothNumberRankin`, `SmoothNumberPrimeSum`, `SmoothNumberSourceRegimes`, `SmoothNumberPolylogRegimes`, `SmoothNumberLowerBound`, `SmoothNumberHildebrand`, `SmoothNumberCriticalLower`, `SmoothNumberCEPPacket`, `SmoothNumberCEPRecurrence`, `SmoothNumberCEPIntervals`, `SmoothNumberCEPWeights`, `SmoothNumberCEPSource`, `SmoothNumberCEPSize`, `SmoothNumberCEPPrimeMass`, `SmoothNumberCEPBootstrap`, `SmoothNumberCEPCoarse`, `SmoothNumberSaddlePoint`, `SmoothNumberSaddleRegimes`, `SmoothNumberSaddlePhase`, `SmoothNumberStability`, `SmoothNumberSaddleCurvature`, `BadOneTermAsymptotics`,
  `PublicStatements`, `TypeIReduction`, `TypeIIReduction`, `TypeIIArithmetic`, `TypeIIKernel`, `VeryBadIntervals`, `SylvesterSchurSmallLengths`, `SylvesterSchurEventual`, `VeryBadEquidistribution`,
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
  consequence without assuming either one. The analytic quotient-limit
  remains open, but `BadOneTermRegularVariation` now derives the complete
  Lemma 1.6(ii) contract from that same limit. `SmoothNumberSaddlePoint` now defines the
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
  contractions and expansions. `BadOneTermRegularVariation` derives the
  reverse directions from `B¹(x/2)/B¹(x)->1/2`: an eventual factor-four
  inequality is iterated through fixed powers of two, and exact floor
  bracketing handles every fixed `c>0`. Thus part (ii) follows from the same
  sharp critical dilation limit used for the adjacent dyadic ratio.
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
  and the complete Gaussian main-term quotient limit `c`. The remaining
  uniform `Psi/mainTerm -> 1` statement is an exact proposition-valued
  contract, and is proved to imply both Granville's quotient limit and Tao's
  `IsTheta` stability clause. Its analytic proof
  remains the missing analytic comparison.
  The first smooth-number disposal in Proposition 6.5 is now instantiated on
  the actual normalized interval union. Membership with distinguished
  `p₀≤y` implies containment in the `y`-smooth naturals up to `2x`; the exact
  floored cutoff `⌊z(x)^β⌋` preserves the critical exponent. The resulting
  cardinal bound is `2x/z(x)^(1/β-ε)` for every fixed positive `β,ε`, with
  the audited specialization `2x/z(x)^(12/5)` at `β=2/5`, `ε=1/10`.
  For each later fixed `(p₀,H)` fiber, the two square-endpoint orientations
  are also covered by smooth cofactors, giving the exact finite reduction
  `#fiber≤2H Ψ(⌊2x/p₀²⌋,p₀)`. The actual short normalized union is then
  assembled over all dyadic lengths and a concrete 60-cell exponent grid.
  On the fixed range from `z(2x)^(6/5)` through `z(2x)^3`, every cell keeps
  exponent at least `2+1/200`; the logarithmic length factor and dilation
  losses are absorbed to give the source-scale bound
  `#union≤x/z(x)^(2+1/800)`.
  The exact limit `log z(2x)/log z(x)→1` transfers the literal source range
  `z(x)^(5/4)<p₀≤⌈z(x)^3⌉` into the grid, so this bound now applies to
  the corresponding source-defined actual normalized interval union.
  The exact converse behind condition (iii) is also proved. If a `p₀`-smooth
  cofactor has at least 1000 prime factors above a supplied lower cutoff,
  counted with multiplicity, the construction selects the 1000 largest in
  nonincreasing order, factors them off, and proves the remainder smooth
  below the last selected prime. Thus a remaining non-typical interval has
  fewer than 1000 such factors once the length and square failures are absent.
  Its canonical filtered prime-factor list is packaged as an exact
  `DeficientPrimeFactorization`: `m=p₁⋯pⱼ m'`, `j<1000`, every listed
  factor lies between the lower cutoff and `p₀`, and `m'` is lower-cutoff
  smooth, with multiplicities retained.
  The deficient packets are converted into a finite product/remainder cover.
  Two endpoint orientations, fixed-fiber counting, and the exact dyadic-length
  sum reduce the actual short, square-avoiding condition-(iii) union to
  `4L ∑_{p₀}∑_a Ψ((2x/p₀²)/a,y)`, where `a` ranges over products of fewer than
  1000 primes in `[y,p₀]`. For the concrete source threshold
  `y=⌊z(x)^(9/10)⌋`, selector diagonalization proves the smooth-number bound
  uniformly in `p₀` and every factor list while retaining the exact reciprocal
  weight `1/(p₀²∏q)`. The outer reciprocal-square tail contributes
  `1/(y-1)`, the list mass is at most
  `1000(1+log⌈z(x)^3⌉)^999`, and all fixed logarithmic losses are absorbed.
  Consequently both the high source subrange and, crucially, the central
  range `z(x)^(9/10)<p₀≤z(x)^(11/10)` of actual deficient condition-(iii)
  intervals are eventually at most `x/z(x)^(2+1/200)`.
  A 600-cell fixed exponent mesh now also covers the two complementary
  windows `z(x)^(2/5)<p₀≤z(x)^(9/10)` and
  `z(x)^(11/10)<p₀≤z(x)^(5/4)`. Exact cutoff transfer from `x` to `2x`,
  finite dyadic aggregation, and arbitrary fixed polylogarithmic absorption
  give the actual short normalized union bound
  `#union≤x/z(x)^(2+1/1000)`. Thus all fixed exponent bands from `2/5`
  through `5/4` are quantitatively covered.
  The finite failure-union assembly is now also compiled for these concrete
  cutoffs. The actual fixed non-typical family is partitioned exhaustively
  into the large-length, large-prime, long-moderate, large-square, small-prime,
  outside-central, central-deficient, and high-smooth unions. Fixed powers of
  `x` are converted using `log z/log x→0`, all eight estimates are normalized,
  and their finite sum is absorbed, proving
  `#fixedNonTypicalUnion≤x/z(x)^(2+1/4000)` eventually.
  `BadIntervalSlowCutoff.lean` completes the source cutoff diagonal. For row
  denominator `d=n+10`, it uses the exact lower floor
  `⌊z(x)^(1-2/d)⌋` and upper ceiling `⌈z(x)^(1+2/d)⌉`; moving low and high
  meshes plus the full intervening deficient range yield the eight-branch
  bound `#union≤x/z(x)^(2+1/(128d²))`. A countable diagonal selects one
  `q(x)→∞`. Separate floor and ceiling limit theorems prove both selected
  cutoff logarithms divided by `log z(x)` tend to one, and the selected actual
  non-typical union is eventually bounded by `x/z(x)^2`. This is the compiled
  source-facing Proposition 6.5 contract.
  `BadIntervalSlowCutoffLogSaving.lean` retains the quantitative margin hidden
  by that weaker display. Its exponent is `1-1/(n+10)`, and after paying for
  Lemma 1.6(i)'s lower bound it proves the fixed-row estimate relative to the
  actual `badOneTermCount x`. One diagonal selector therefore works for every
  fixed `epsilon>0` and gives
  `#nonTypical <= badOneTermCount(x)/log(x)^(1-epsilon)` eventually.
  `BadIntervalRandomModel.lean` begins Proposition 6.6 without an informal
  random-choice surrogate. It defines the exact half-open dyadic prime bands,
  the product probability measure on 1001 natural-valued coordinates, and the
  uniform coordinate measures. The coordinate pushforward laws, probability
  normalization, almost-sure prime-band support, and mutual independence are
  proved. The exact tuple product `p₀²p₁⋯p₁₀₀₀m'`, divisibility indicators,
  typical normalized interval event, and event probability are now production
  definitions. `BadIntervalAntiSieve.lean` disposes of the exceptional
  `p∣l` branch pointwise: its complete weight is at most `H log H`, hence at
  most `H log z(x)` eventually for every source-admissible `H`; the associated
  event is empty and has exactly zero probability. The small-prime branch is
  now literal in `BadIntervalSmallPrimeMoment.lean`: it uses the exact cutoff
  `⌊z(x)^(1/100)⌋`, removes `p∣l`, retains moment `50`, and expands the real
  expectation exactly as a finite ordered-50-tuple sum of logarithmic weights
  times joint divisibility probabilities. For each tuple, its prime lcm is
  explicit, two realizations are proved congruent modulo that lcm, its residue
  is proved coprime to the lcm, and the joint event is proved either empty or
  exactly one primitive residue-class fiber. `BadIntervalLargePrimeMoment.lean`
  defines the unweighted large-prime contribution on the literal shift/prime
  index set and proves exact finite identities for its mean, second moment,
  variance, and covariance matrix. When `H≤lowerPrime`, a common prime cannot
  divide the two translated products at distinct shifts; that joint event is
  empty, its covariance is nonpositive, and the variance reduces to the mean
  plus the ordered distinct-prime covariance sum. The analytic estimates for
  that surviving sum are not claimed. `BadIntervalLargePrimeCharacter.lean`
  proves that each single event is empty or a primitive residue fiber modulo
  `p`, while each distinct-prime joint event is empty or a primitive residue
  fiber modulo `pp'`. Both literal probabilities are bounded by the existing
  all-character 1000th-moment expression at the exact corresponding modulus.
  `BadIntervalLargePrimeExceptional.lean` turns the aggregate exceptional
  character count into the Proposition 6.7 exceptional-prime count with the
  exact exponent `2/125`. `ExceptionalCharacterCofactorAggregate.lean` forms
  the dependent family of characters of conductor `q₁q₂` for fixed `q₁`.
  `ExceptionalCharacterUniformCard.lean` exposes the self-improving bound with
  one constant independent of that family, and
  `ExceptionalCharacterCofactorUniform.lean` diagonalizes selectors to obtain
  one eventual pointwise bound for every admissible `q₁` and cofactor set.
  `BadIntervalLargePrimePairs.lean` specializes this to prime products `pp'`,
  proving the uniform exceptional-partner count required by Proposition 6.8,
  conditional only on analytic Burgess.
  `BadIntervalPrincipalCharacter.lean` separates the unique principal
  character before weak AM--GM, so the main term is charged once rather than
  1000 times. It identifies the principal tuple expectation exactly with a
  coprimality probability. For one prime, and for a product of two primes, the
  coprimality deficit is bounded by the union of coordinate collisions; each
  coordinate costs at most the reciprocal of its exact dyadic-band
  cardinality. The remaining probability error is therefore purely the
  nonprincipal moment plus this explicit collision majorant.
  `BadIntervalLargePrimeNonprincipal.lean` closes that nonprincipal moment
  for a prime modulus: every nonprincipal character modulo `p` is primitive,
  and outside the union of exceptional conductors over the 1000 ordinary
  coordinate scales its complete moment is at most
  `φ(p) * ∑_{j≠0} P_j^(-8)`. The exceptional union costs at most the sum of
  the coordinate-wise counts, hence only a fixed factor 1000 under a uniform
  bound. Substitution gives a direct deviation estimate from `1/φ(p)`.
  `BadIntervalLargePrimeProductNonprincipal.lean` proves the analogous exact
  conductor reduction for an ambient product modulus when its prime bands are
  coprime to that modulus. If every nontrivial divisor conductor is
  unexceptional, the totient divisor identity gives the full error `q Z^(-8)`;
  for `q=pp'`, coordinate summation and substitution yield the corresponding
  direct deviation theorem. Charging the possible sampled points `p,p'` to
  collision error is completed in
  `BadIntervalLargePrimeProductCollision.lean`: the ambient and primitive
  averages differ by at most four reciprocal band cardinalities, because only
  the two modulus primes can contribute. A coprimality-free primitive
  conductor regrouping and 1000th-power convexity give an explicit
  `(4/card)^1000` correction and remove band separation from the final
  product-modulus deviation theorem.
  `BadIntervalLargePrimeCrude.lean` begins the direct finite fallback count.
  The literal fiber of dyadic-band primes in one residue class modulo positive
  `q` has cardinality at most `⌊2Z/q⌋+1`, with its normalized real form proved
  for subsequent frozen-coordinate probability estimates.
  `BadIntervalPrimeTupleUniform.lean` proves that the product law is exactly
  uniform on the finite Cartesian product of all 1001 prime bands. The support
  has measure one, each supported tuple has atom mass equal to the inverse
  product of the exact band cardinalities, and every event probability is its
  supported tuple count times that common mass.
  `BadIntervalPrimeTupleFiber.lean` now performs the finite conditioning step.
  Freezing an ordinary coordinate gives an exact 1000-coordinate support, and
  its cardinality times the missing band cardinality equals the full support
  cardinality. A uniform fiber bound `M` therefore gives probability at most
  `M/card`; pairwise congruence modulo `q` inserts the exact
  `⌊2P/q⌋+1` residue-fiber bound. The source product is factored into the
  chosen coordinate and its complementary cofactor. Splitting off noncoprime
  source products and invoking the existing coordinate-collision union bounds
  removes that premise: the final single-prime crude bound adds one collision
  sum, while the joint two-prime bound adds two. The stronger source
  multi-coordinate ratios and their normalization are recorded next.
  `BadIntervalPrimeTupleMultiFiber.lean` implements the paper's literal
  multi-coordinate freezing step. For every finite set of coordinates it
  proves exact support-cardinality cancellation and a general product-residue
  probability bound with a supplied representation multiplicity. Products of
  two prime coordinates have multiplicity at most `2`; products of three have
  multiplicity at most `6`. Consequently the finite form of Proposition
  6.7(i) has numerator `2(⌊4P₁P₂/p⌋+1)`, while the finite form of Proposition
  6.8(i) has numerator `6(⌊8P₁P₂P₃/(pp')⌋+1)`, over the exact products of the
  corresponding band cardinalities. The nonzero-shift hypotheses discharge
  the complementary-cofactor coprimality conditions. Source-scale
  normalization and dyadic aggregation remain.
  `BadIntervalLargePrimeCrudeNormalize.lean` cancels the remaining coordinate
  scales. Under the common exact band hypothesis
  `P_j≤L·#taoDyadicPrimeBand(P_j)`, and the explicit condition that the modulus
  does not exceed the selected product range, the preceding ratios become
  `16L²/p` and `96L³/(pp')`. Thus the crude clauses now have precisely the
  source logarithmic shape; the following module supplies the PNT/anatomy
  scale instantiation.
  `BadIntervalLargePrimeCrudeSource.lean` now supplies that PNT specialization.
  The structure `TaoPrimeTupleSourceScaleFamily` records coordinatewise
  divergence and `log(P_j)/log(z)→1`. Finiteness of `Fin 1001` makes the PNT
  lower bound uniform, giving simultaneously
  `P_j≤4log(z)·#taoDyadicPrimeBand(P_j)` and nonempty bands. The resulting
  eventual crude bounds are `256log²(z)/p` and `6144log³(z)/(pp')`, retaining
  only the explicit modulus-below-selected-product comparisons. Dyadic mean
  and covariance aggregation remains.
  `BadIntervalLargePrimeProbabilityBounds.lean` transfers the improved
  character estimates to the literal divisibility events. Coprimality of the
  fixed remainder constructs a witness and removes the empty branch, giving
  the full absolute error about `1/φ(p)`; unconditional upper halves are
  recorded for one and two primes. An audited real-algebra lemma then combines
  these marginal errors with the `pp'` joint error, using
  `φ(pp')=φ(p)φ(p')`, to give the explicit distinct-prime covariance bound.
  The later aggregation modules below complete the finite dyadic sum.
  `BadIntervalLargePrimeAggregation.lean` performs the exact finite
  anti-sieve partition. The literal shift-prime index set is split between
  improved and exceptional conductors, and the ordered distinct-prime
  covariance sum is split between improved and exceptional pairs. Combining
  these with the diagonal variance reduction retains every shift multiplicity
  and leaves only explicit supplied crude majorants on exceptional terms.
  Analytic cardinality and source-scale summation remain.
  `BadIntervalLargePrimeExceptionalPartition.lean` identifies the only
  nontrivial divisors of `pp'` as `p`, `p'`, and `pp'`. Consequently every
  exceptional product pair is covered by an exceptional first prime, an
  exceptional second prime, or the common-factor exceptional-partner union.
  The latter is formed over all 1000 ordinary coordinate scales and carries
  exact sum-cardinality and factor-1000 bounds. Weighted source-scale
  summation remains.
  `BadIntervalLargePrimeBlockSum.lean` compiles the finite dyadic first-moment
  block. It identifies `(R-1,2R-1]` with the source band `[R,2R)`, proves
  `1/φ(p)≤2/R`, and uses the PNT to obtain the eventual main-term sum
  `≤4/log R`. The complete shift-prime block is bounded by this main term,
  the uniform improved error, and exceptional cardinality times a supplied
  crude estimate. Burgess-cardinality insertion and scale summation remain.
  `BadIntervalLargePrimeCovarianceBlockSum.lean` compiles the exact finite
  two-band covariance consumer. The ordered distinct-prime sum over bands
  `R,S` is bounded with its literal `(H-1)^2` shift multiplicity by the full
  band-product cardinality times a uniform improved covariance error plus the
  exceptional ordered-pair cardinality times a supplied crude joint bound.
  Burgess-cardinality insertion and summation over dyadic scales remain.
  `BadIntervalLargePrimeExceptionalPairCard.lean` bounds that exact ordered
  exceptional-pair finset by the three conductor families in the source:
  exceptional first endpoints, exceptional second endpoints, and
  common-factor exceptional partners. Both the exact natural-cardinality
  inequality and a real-valued uniform interface for Burgess bounds compile.
  `BadIntervalLargePrimeErrorNormalize.lean` and
  `BadIntervalLargePrimeErrorSource.lean` expose the reciprocal-band,
  eighth-power, and change-level collision aggregates. From the simultaneous
  contract `P_j=z^(1+o(1))` and the dyadic PNT they derive explicit source
  envelopes and insert them into the literal one-prime, joint, and covariance
  errors. `BadIntervalLargePrimeErrorPower.lean` absorbs arbitrary fixed
  logarithmic powers against a positive `z`-power gap and converts these
  envelopes and literal errors to `3R^-1.001` and explicit-constant
  `R^-1.001 S^-1` joint/ordered-covariance forms. Burgess cardinality insertion
  and dyadic scale summation remain.
  `BadIntervalLargePrimeAdaptiveExceptional.lean` begins the exact insertion
  with the threshold `max(P_j^-0.008,R^-0.01)`. Its character finsets stay
  inside the fixed exceptional family, while the uniform aggregate squared
  moment, finite Chebyshev inequality, and union over the 1000 ordinary
  coordinates give one Burgess-conditional endpoint count `O(R^0.02)`. This
  quantifier order is necessary at the smallest source modulus bands; the
  fixed `O(P_j^0.016)` count alone does not imply it. The corresponding
  cofactor-family embedding has an exact squared-moment identity and one
  eventual bound pointwise uniform in the fixed prime and cofactor set. Thus
  the adaptive threshold at the second band also gives `O(S^0.02)` partners
  uniformly. `BadIntervalLargePrimeAdaptiveError.lean` proves the finite
  consumer chain: adaptive emptiness bounds every primitive 1000th moment,
  gives the one-prime probability error with explicit additional
  `1000R^-10`, transports the threshold through product conductor fibers,
  and retains explicit `R^-1.001` and ordered `R^-1.001 S^-1` source powers
  for the adaptive one-prime, joint, and covariance errors.
  `BadIntervalLargePrimeAdaptivePartition.lean` then records the necessary
  mixed conductor scales exactly: `p` uses `R`, while `p'` and `pp'` use
  `S`. Excluding the two endpoint sets and the adaptive partner set implies
  this predicate, and the resulting mixed product moment and literal joint
  probability bound compile. The mixed joint and covariance errors also have
  explicit ordered `R^-1.001 S^-1` source bounds.
  `BadIntervalLargePrimeAdaptiveBlockSum.lean` inserts the exact adaptive
  endpoint/pair predicates into the finite Proposition 6.7 and 6.8 consumers.
  It preserves the literal shift multiplicities, and reduces the adaptive
  exceptional-pair finset to the two endpoint counts plus the pointwise
  adaptive partner fibers. `BadIntervalLargePrimeAdaptiveSource.lean`
  composes those endpoint and partner estimates with explicit Burgess and
  obtains the exact source pair-count shape
  `R^0.02·#band(S)+#band(R)·S^0.02`. It also inserts these cardinalities and
  the normalized adaptive one-/two-band improved errors into the complete
  block sums. `BadIntervalLargePrimeAdaptiveGeometry.lean` proves the common
  conductor and partner ranges automatically under the fixed source margin
  `R,S≤z^1.01`, and supplies uniform crude estimates on whole bands.
  `BadIntervalLargePrimeAdaptiveComplete.lean` inserts both into the complete
  source blocks. The exact zero contribution from primes dividing `m'` also
  removes the previous whole-band coprimality assumption.
  `BadIntervalLargePrimeDyadicScales.lean` partitions the literal source
  prime range into disjoint exact dyadic slices, proves a `4 log z` scale
  count and the required lower/upper scale margins.
  `BadIntervalLargePrimeAdaptiveUniform.lean` uniformizes the Burgess
  constants over that finite grid, sums the block majorants, and proves the
  literal source mean bound `2000000 H`, distinct-prime covariance bound
  `H`, and variance bound `2000001 H`, conditional on explicit Burgess.
  `BadIntervalProbabilityNormalization.lean` converts the completed source
  moments into literal event bounds. Markov at moment 50 gives the small-prime
  tail at threshold `H log(z)^2/(8 log₂(x))`; Chebyshev and the exact variance
  identity give the large-prime tail above its mean at threshold
  `H log(z)/(8 log₂(x))`. Their union with the zero-measure exceptional branch
  is bounded by
  `A(8 log₂(x))^50/log(z)^50 + 2000001(8 log₂(x))^2/(H log(z)^2)`.
  `BadIntervalTypicalAntiSieve.lean` proves the complementary deterministic
  statement: square avoidance and the source scale force enough logarithmic
  mass in the squarefree component, every such prime is partitioned with its
  exact logarithmic weight among the exceptional, small, and large branches,
  and the one-eighth scalar allocation makes every typical tuple lie in that
  union eventually. The final probability theorem absorbs the fiftieth-moment
  tail and gives one `B>0` with
  `Pr(typical) ≤ B(8 log₂(x))^50/(H log(z)^2)` eventually, conditional only on
  `TaoExplicitCubefreeBurgessBound`. This is the compiled source meaning of
  `O(1/(H log(z)^(2-o(1))))` in Proposition 6.6.
  `BadIntervalProbabilityUniform.lean` corrects the endpoint's quantifier
  order for the subsequent source sum: one Burgess-dependent constant is
  chosen before the eventual `x`, and the estimate then holds simultaneously
  for every positive admissible `H` and every remainder `m'`. It defines the
  finite typical support, proves the exact identity between its cardinality
  ratio and the typical-event probability, and derives the uniform supported
  tuple-count estimate. `BadIntervalTypicalCounting.lean` then uses the exact
  lower-endpoint product budget and last-band smoothness cutoff to sum over all
  finite smooth remainders, restoring the literal `Psi` factor. It sums every
  power-of-two length with `sum 2^(-r) ≤ 2`, maps the resulting fixed-prime-
  scale family into `B¹ ∩ [1,2x]`, and reduces its domain cardinality to the
  literal one-term count times a uniform evaluation-fiber bound.
  `BadIntervalTypicalScales.lean` supplies the moving dyadic grid and all
  ordered 1001-coordinate scale choices. `BadIntervalTypicalEnlargement.lean`
  implements the source enlarged bands, and
  `BadIntervalTypicalMultiplicity.lean` proves the absolute fixed-scale fiber
  bound `1000^1000`. `BadIntervalTypicalGlobal.lean` proves that canonical
  largest-prime-factor recovery preserves that bound after adjoining every
  scale choice. `BadIntervalTypicalAssembly.lean` uses PNT to compare each
  original band to its enlarged band with factor eight, sums the simultaneous
  Proposition 6.6 estimates, proves the resulting assembly factor tends to
  zero, and derives little-o of `badOneTermCount` at the fixed enlarged
  endpoint, conditional on explicit Burgess.
  `BadIntervalTypicalWeighted.lean` inserts the actual interval-length weight
  into this global count. The `2^r` weight cancels the inverse-length factor,
  the number of admissible dyadic exponents is at most `50 iteratedLog x`, and
  the resulting weighted assembly factor tends to zero. It follows that the
  full global length-weighted tuple count is little-o of the same fixed-
  dilation one-term count, conditional on explicit Burgess.
  `BadIntervalTypicalUnion.lean` canonically chooses the distinguished prime,
  cofactor, and anatomy of each forward typical interval, proves exact tuple
  start `N+1` and length `H`, and gives an injective map into the weighted
  global family. The reflected modules
  `BadIntervalBackwardSmallPrime.lean`,
  `BadIntervalBackwardLargePrime.lean`,
  `BadIntervalBackwardLargePrimeAdaptiveBlockSum.lean`,
  `BadIntervalBackwardLargePrimeAdaptiveUniform.lean`,
  `BadIntervalBackwardProbabilityNormalization.lean`, and
  `BadIntervalBackwardTypicalAntiSieve.lean` prove the symmetric `v-l`
  small-prime moment, exact source mean/variance, Markov--Chebyshev tail,
  deterministic typical-event inclusion, and uniform probability/support
  count. `BadIntervalBackwardTypicalWeighted.lean` performs the same global
  length-weighted assembly, and `BadIntervalBackwardTypicalUnion.lean`
  canonically records tuple start `N+H` and length `H`, proves injectivity, and
  combines the two endpoint orientations. Thus the full actual typical union
  is little-o of the fixed-dilation one-term count conditional on Burgess.
  `BadIntervalTypicalWeighted.lean` and
  `BadIntervalBackwardTypicalUnion.lean` also retain a fixed logarithmic saving
  in this estimate. `BadIntervalRecombination.lean` partitions the normalized
  family exactly into typical and non-typical parts and applies the factor-30
  maximal transfer. Its scale-local form uses the proved eventual
  start-uniform Sylvester--Schur theorem, so conditional only on explicit
  Burgess and Lemma 1.6(ii), it yields a logarithmically saving bound for every
  sufficiently large nontrivial dyadic window. The same module proves an exact finite
  power-of-two cover of all nontrivial bad numbers up to `x` and bounds the
  global count by the sum of those window cardinalities.
  `BadIntervalDyadicSummation.lean` isolates the exact adjacent-dyadic
  regular-variation input for `badOneTermCount`, proves that every fixed
  logarithmic weighting retains ratio `1/2`, obtains an eventual geometric
  contraction, sums all late scales, and absorbs the finite prefix. The last
  endpoint is trapped between `x` and `2x`; Lemma 1.6(ii) transfers it back to
  `x`. `BadOneTermRegularVariation.lean` then derives the adjacent ratio rather
  than assuming it: a slowly widening central prime packet carries
  asymptotically all of the exact `B¹` sum, the four complementary ranges have
  a fixed-row power saving and hence diagonal `o(B¹(x))` mass, and the sharp
  critical smooth-number dilation limit halves the central packet. Thus
  `badOneTermCount(x/2)/badOneTermCount(x)->1/2`, and the dyadic specialization
  follows. The same module derives this dilation input from the existing
  Gaussian saddle-asymptotic target. The half-ratio also proves the complete
  Lemma 1.6(ii) contract by finite power-of-two iteration and exact floor
  bracketing. This proves the exact `TaoTheorem17Conclusion` conditional on
  that saddle asymptotic and analytic Burgess; unrestricted
  Sylvester--Schur is no longer a Theorem 1.7 hypothesis.
  `BadIntervalCharacterExpansion`
  proves exact normalized orthogonality over all Dirichlet characters, the
  integrated fiber-probability identity, and exact factorization of the full
  tuple expectation through the independent coordinate laws. Each coordinate
  expectation is computed as its normalized finite dyadic prime-character
  average. The residual and distinguished squared coordinate have norm at
  most one, and finite weak AM--GM gives the source reduction to the
  all-character sum of 1000th powers of the remaining prime averages. The
  tuple modulus satisfies `lcm≤2^50 φ(lcm)`, yielding the explicit
  `2^50/lcm` coefficient. This estimate is inserted into the complete
  ordered fiftieth-moment expansion, the finite tuple/character/coordinate
  sums are reordered exactly, and one of the 1000 tail coordinates is
  selected with factor `1000`. `PrimeCharacterSums.lean` defines the exact
  normalized sum `s_Z(χ)` and threshold `Z^(-1/125)=Z^(-0.008)`, including
  the identity `(Z^(-1/125))^1000=Z^(-8)`. Primitive nonprincipal characters
  are partitioned into exceptional and unexceptional sets; the latter's
  1000th moment is at most `φ(q)Z^(-8)`, while the former's 1000th moment is
  bounded by its squared moment. Exact scale separation proves that every
  prime in the later dyadic band is coprime to the 50-prime tuple lcm, so each
  ambient character sum equals its primitive counterpart. The principal term
  is exactly one. The nonprincipal sum is partitioned over the positive
  divisors `d≠1` of the modulus; each fixed-conductor fiber injects into the
  primitive nonprincipal characters at level `d`. Consequently the complete
  ambient moment is bounded by one plus the divisor sum of exceptional squared
  moments and `φ(d)Z^(-8)` errors. This conductor-reduced estimate is inserted
  termwise into the ordered tuple expression, and the earlier factor-1000
  pigeonhole now controls the complete fiftieth moment by that explicit finite
  sum. `SmallPrimeMertens.lean` identifies the tuple lcm exactly with the
  product of its distinct prime support, records support multiplicities summing
  to 50, and factors the logarithmic coefficient into one `log p/p` per
  distinct prime and the repeated logarithms. The latter cost exactly
  `log(cutoff)^(50-#support)`; the distinct factors are bounded using the proved
  finite estimate `weightedPrimeLogSum Y ≤ log 4 * (2 + log Y)`. Fixed ordered
  prime tuples have at most `H^50` admissible shift tuples, and a generic
  fiberwise summation theorem removes all shifts at that cost. Ordered tuples
  are regrouped by exact support; each support fiber costs at most `50^50`, and
  its elementary-symmetric weight is bounded by a power of the full weighted-
  prime sum. This yields an explicit `H^50 O(log(cutoff)^50)` coefficient
  bound. The conductor expression is split exactly into principal,
  exceptional-square, and totient-error portions. The principal part satisfies
  the Mertens bound, while `∑_{d∣q}φ(d)=q` cancels the lcm denominator in
  the unexceptional part and Chebyshev theta bounds its remaining tuple sum.
  `ExceptionalCharacterBHM.lean` proves Lemma 5.3 in the exact finite weighted
  form used by the source. Hermitian Gram symmetry supplies the row-only form;
  the sieve-weighted prime indicator recovers the dyadic prime sum exactly and
  has energy equal to the band cardinality; and every Gram row is split into
  one diagonal term plus `J-1` off-diagonal terms. Division by the exact band
  cardinality now yields the normalized `s_Z` estimate, and the exact finite
  Markov step proves `J Z^(-2/125) ≤ ∑|s_Z|²`. Thus the sole
  non-elementary small-prime term is the exceptional squared-moment tuple sum.
  The later Selberg alternative and self-improving family theorem reduce this
  term to the still-open analytic Burgess estimate. Conditional on that same
  explicit Burgess hypothesis, the large-prime mean/variance branches, exact
  probability normalization, deterministic typical-event inclusion, and the
  source-shaped Proposition 6.6 probability bound are now closed, uniformly
  in every admissible length and remainder at each sufficiently large ambient
  scale. Its exact probability-to-support-cardinality conversion is also
  closed. The smooth-remainder and dyadic-length summations, all ordered
  prime-scale choices, enlarged-band comparison, fixed/global
  `1000^1000` representation-fiber bounds, and the global little-o estimate at
  one fixed dilation are closed for both endpoint orientations. The explicit
  logarithmic saving, Proposition 6.5 recombination, factor-30 maximal
  transfer, conditional local dyadic-window estimate, and exact finite global
  dyadic cover are also closed. The dyadic summation and exact conditional
  public Theorem 1.7 endpoint are now closed from the adjacent ratio
  `B¹(2^r)/B¹(2^(r+1))->1/2`. `BadOneTermRegularVariation.lean` proves that
  ratio from `TaoCriticalSmoothDilationLimitConclusion`, and the completed
  saddle-main-term stability reduces the latter to
  `TaoCriticalSmoothSaddleAsymptoticConclusion`. The half-ratio now also
  supplies Lemma 1.6(ii)'s reverse fixed-dilation comparison by exact finite
  power-of-two bracketing. `SylvesterSchurEventual.lean` proves that all
  Sylvester--Schur failures have bounded start: large lengths use the existing
  uniform length tail, while bounded lengths use the fixed-length threshold
  `H^H+1`. Admissible interval starts tend to infinity with the dyadic scale,
  so this eventual theorem supplies the local large prime at every
  sufficiently large scale. Proving the sharp saddle asymptotic and removing
  the Burgess hypothesis are the two remaining analytic inputs to Theorem 1.7.
  `FundamentalSieveWeights.lean` also fixes the literal truncated divisor-sum
  weight from Lemma 5.4, proves it equals one on all dyadic primes above the
  sieve level when `λ₁=1`, proves its exact floor-weighted mass expansion, and
  bounds the coefficient `ℓ¹` mass by `R` under `|λ_d|≤1`. It now also proves
  the quantitative floor error
  `|Σ_{n≤X}ν(n)-X Σ_{d≤R}λ_d/d|≤R`, its direct upper-bound form, and transfer
  of any coefficient main-mass bound to `Σν≤XB+R`. The remaining sieve input
  is precisely the construction of coefficients with squarefree support,
  nonnegative weight, and `O(1/log R)` main mass.
  `SelbergPrimeWeights.lean` supplies a proved, unconditional real-valued
  alternative sufficient for the same diagonal role. It instantiates the
  frozen Selberg sieve at density `1/d`; the coefficients are supported on
  `d≤R` and the primorial, have coefficient one at `d=1`, and satisfy the
  upper-Möbius inequality. The resulting literal divisor weight is
  nonnegative and equals one on primes above `R`. Selberg diagonalization and
  its bounding-sum theorem give main mass at most `2/log R`, while
  `|λ_d|≤3^ω(d)` gives the explicit finite estimate
  `Σ_{n≤X}ν(n)≤2X/log R+R(1+log R)^3`. This is recorded as a representation
  delta, not as proof that the coefficients lie in `{−1,0,1}`.
  `ExceptionalCharacterSelberg.lean` connects this weight to Lemma 5.3
  end-to-end. It removes the zero coordinate exactly, expands every weighted
  correlation over the supported divisors, reindexes a divisor restriction as
  the ordinary prefix `m≤⌊(2Z-1)/d⌋`, and uses multiplicativity to extract the
  value at `d` with norm cost at most one. The diagonal is discharged by the
  explicit Selberg mass estimate. The final normalized BHM theorem therefore
  leaves precisely a uniform unshifted prefix bound for
  `χ_j(m) conjugate(χ_k(m))`, the remaining Burgess input.
  `ExceptionalCharacterFamilies.lean` now supplies the source family
  bookkeeping: dependent primitive levels `q₁q₂`, coprimality and squarefree
  hypotheses, exact lcm identity `lcm(q₁q₂,j,q₁q₂,k)=q₁lcm(q₂,j,q₂,k)`,
  squarefreeness of that pair level, and its bound by `Z^3.09`. It proves on
  every natural input, including nonunits, that the raw pair correlation is
  exactly one quotient Dirichlet character at the lcm level. The resulting
  normalized BHM theorem consumes only the named uniform cubefree Burgess
  prefix-bound predicate; no Burgess estimate is postulated as a theorem. The
  exact exponent ledger `0.016+0.0001+(1-0.0163)=1-0.0002` and the strict
  period-range comparison `3.09<3.1(1-0.0001)` are also compiled.
  `ExceptionalCharacterBurgess.lean` replaces the convenient all-prefix
  interface by the exact sieve prefixes `floor((2Z-1)/d)` and gives the
  source-shaped proposition-valued target with saving `0.0163`, fixed lower
  cutoff, and period range `q≤H^3.1`. It additionally defines cube-free by
  exclusion of prime cubes, proves squarefree implies cube-free, and records
  the cited `r=7` estimate in the literal form
  `A H^(6/7)q^(2/49+ε')`. The choice `ε'=1/2000000` and the complete rational
  exponent conversion to `H^(1-0.0163)` are kernel-checked. It also proves the
  exact primitive-to-imprimitive reduction: changed-level prefixes have a
  finite Möbius expansion into primitive prefixes of lengths `H/d`, and the
  divisor-count loss is absorbed by reserving half of `ε'`. Consequently it
  suffices to formalize the published two-factor estimate for primitive
  cube-free characters; the all-character form used downstream is derived.
  The primitive target is further reduced exactly to its genuine core range.
  Complete character periods sum to zero, so every prefix is its `H % q`
  prefix. The triangle inequality gives `|S(H)|≤H`, and exact real-power
  arithmetic shows this already implies the desired estimate outside
  `q^(2/49+ε') < H^(1/7)`, equivalently
  `q^(2/7+7ε') < H`. Therefore a constant `A≥1` need only be proved for
  primitive cube-free characters in the finite range
  `q^(2/7+7ε') < H < q`.
  `BurgessMoment.lean` now compiles the exact finite algebra at the front of
  this core proof. It expands the complete shifted `2r`-moment over ordered
  pairs of shift tuples, rewrites every summand as one complete quotient-
  character correlation, splits tuples by whether at most `r` distinct shifts
  occur, and proves the coding bound `#degenerate ≤ r^(2r) B^r`. Consequently
  a uniform nondegenerate complete-sum bound `W` gives
  `moment ≤ r^(2r) B^r q + B^(2r) W`; the literal fourteenth-moment `r=7`
  specialization is audited. The composite Weil estimate remains analytic
  work.
  The source coefficient is now literal as well:
  `burgessTupleDifferenceProduct uv j = ∏_{i≠j}(b_i-b_j)` over the two tagged
  `r`-tuples. A fiber-cardinality argument proves every nondegenerate tuple
  has a uniquely occurring shift and hence some nonzero `A_j`. The relaxed
  source weight `∑_{A_j≠0} gcd(|A_j|,q)` and factor
  `(4r)^ω(q)√q` define `TaoPrimitiveCubefreeBurgessCompleteWeilBound`, and
  `burgess_shift_fourteenth_moment_le_of_completeWeil` reduces the literal
  `r=7` moment to this complete Weil input plus the visible finite gcd sum.
  The finite gcd sum is now proved unconditionally. Counting multiples of
  each divisor gives `∑_{n≤H}gcd(n,q)≤H τ(q)`; splitting around a fixed shift,
  gcd submultiplicativity, and exact independent-coordinate factorization
  then give
  `∑_uv burgessTupleGcdWeight q uv ≤
  2r B (2B τ(q))^(2r-1)`. The general and literal `r=7` complete-moment
  consumers now incorporate this bound. Thus the composite complete Weil
  predicate is the sole missing Burgess moment input.
  The remaining elementary arithmetic losses are also absorbed. The proved
  divisor-epsilon estimate controls `τ(q)^13`, while the fixed-base
  prime-factor estimate controls `28^ω(q)`. Splitting any positive `ε` evenly
  between these factors yields a positive `C_ε` such that, conditional only
  on the composite Weil predicate,
  `∑_x |burgessShiftSum B χ x|^14 ≤ 7^14 B^7 q +
  C_ε B^14 q^(1/2+ε)`.
  `BurgessWeilCRT.lean` now proves the exact multiplicative layer of that
  remaining predicate. For coprime `m,n`, canonical left and right CRT
  characters factor every global character value, the tuple numerator and
  denominator commute with both projections, and the complete correlation
  modulo `mn` is exactly the product of its two local correlations. The
  factor `(4r)^ω(q)√q` and every fixed coefficient contribution
  `gcd(|A_j|,q)` are multiplicative across the same split. Consequently local
  bounds using one common coefficient witness assemble into the relaxed
  global gcd-weight bound. What remains here is transport of primitivity to
  these canonical local characters, iteration over a cube-free factorization,
  and the prime and prime-square local complete-sum estimates. The first of
  these is now closed too: the global character is exactly the product of the
  two local characters changed back to level `mn`. If (say) the left local
  character factored through `d`, this identity would make the global
  character factor through `dn`. Equality of conductor and level for the
  primitive global character then gives `mn ∣ dn`, so cancellation and
  `d ∣ m` force `d=m`. The symmetric proof handles the right factor. Thus
  both canonical local characters are primitive.
  `BurgessWeilIteration.lean` closes the cube-free iteration. Every
  nontrivial cube-free `q` is split canonically as `p^k n`, with `k=1` or
  `k=2`, coprime factors, and `n<q`. Strong induction preserves a fixed
  nonzero `A_j` through every CRT split and proves the corresponding
  fixed-gcd bound; selecting one nonzero coefficient of a nondegenerate tuple
  and inserting it into the relaxed weight yields the full composite Weil
  predicate. Thus the sole remaining input in this layer is the local
  fixed-coefficient complete-sum estimate for primitive characters modulo
  `p` and `p^2`. This boundary is now tightened further. If `p ∣ |A_j|`,
  the trivial complete-correlation bound by the modulus already implies the
  required fixed-gcd estimate at both levels. Hence only the complementary
  case `gcd(|A_j|,p)=1` is the nontrivial branch. Separate prime and
  prime-square coprime-coefficient predicates recombine exactly into that
  local input and hence into the full composite Weil predicate.
  `BurgessWeilPrimeSquare.lean` closes the prime-square side.
  It gives an exact base-`p` fiber decomposition of the complete correlation,
  proves that singular base fibers vanish, and bounds their base set by
  `2r`. On the principal-unit kernel it constructs the induced additive
  character and proves that primitivity modulo `p^2` makes this character
  nontrivial. The numerator, denominator, and logarithmic stationary
  polynomial are explicit over `ZMod p`; the latter has degree at most `2r`.
  The first-order product identity identifies every nonsingular fiber with a
  fixed scalar times that additive character at `(F'/F-G'/G)t`, so every
  nonstationary fiber cancels. Coprimality of `A_j` with `p` makes the tagged
  root simple in exactly one of `F,G`, proving `F'G-FG'` nonzero. Its at most
  `2r` roots therefore support the complete sum and give the unconditional
  local bound `‖correlation‖ ≤ 4rp`. The sole remaining local analytic input
  is now the primitive prime-modulus Weil estimate.
  `BurgessWeilPrime.lean` normalizes that final local input to a standalone
  finite-field statement. The Burgess correlation is definitionally the
  complete sum of a nontrivial multiplicative character on one product of
  linear factors times the inverse character on the other product.
  Coprimality of the selected `A_j` proves that its tagged root remains unique
  after reduction modulo `p`, while prime-level primitivity proves the
  character is nontrivial. The proposition
  `TaoPrimeLinearQuotientWeilBound` asks exactly for the resulting
  `4r√p` estimate and is proved to imply both the remaining primitive-prime
  predicate and the full cube-free composite Weil predicate. Proving this
  normalized finite-field Weil theorem remains the genuine analytic boundary.
  `BurgessWeilPrimePolynomial.lean` reduces this once more to the standard
  split-polynomial formulation. Raising the denominator product to
  `orderOf χ - 1` preserves the character sum exactly. At the uniquely
  tagged root, the resulting polynomial has multiplicity `1` on the
  numerator side or `orderOf χ - 1` on the denominator side, so this
  multiplicity is not divisible by `orderOf χ` and the polynomial cannot be
  an `orderOf χ`-th power. The polynomial splits over `ZMod p` and its
  distinct roots are contained in the `2r` tagged roots. Consequently the
  proposition `TaoPrimeSplitPolynomialWeilBound`, with bound twice the
  distinct-root count times `√p`, implies the linear-quotient theorem and
  the full composite predicate.
  `BurgessWeilPrimeLowRoots.lean` proves the one- and two-distinct-root cases
  of this bound. The one-root sum vanishes by translation and nontriviality;
  the two-root sum is transformed exactly into a Jacobi sum and bounded by
  `√p` using the Gauss--Jacobi identities. The checked proposition
  `TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore` implies both the full
  split-polynomial boundary and the composite Weil predicate. Thus only the
  classical split-polynomial Weil estimate with at least three distinct roots
  remains.
  `BurgessWeilPrimeActiveRoots.lean` sharpens this residual. It partitions the
  roots according to whether their multiplicity is divisible by `orderOf χ`.
  An inactive root contributes one away from itself and zero at itself, so the
  full sum is exactly the active-root sum with the inactive inputs deleted.
  Their total correction is at most the inactive-root count and is absorbed by
  the existing `2 #roots √p` target. Consequently the sole remaining contract
  is `TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore`, restricted to at
  least three multiplicities nonzero modulo the character order.
  `BurgessWeilPrimeThreeRoots.lean` closes the exactly-three-active-root case
  for the cleared Burgess polynomial. Its degree is proved to be exactly
  `r * orderOf χ`, so the active multiplicity sum is divisible by the
  character order. A verified fractional-linear equivalence sends one active
  root to infinity; the common denominator character cancels, leaving a
  two-root Jacobi sum with one deleted point. The resulting `√p+1` estimate,
  together with the inactive-root correction, is absorbed by the original
  target. Thus the actual remaining Burgess contract is
  `TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore`: at least four
  active roots, under the degree-divisibility property already proved for the
  cleared polynomial.
  `BurgessWeilPrimeLargeCharacteristic.lean` also removes every small-prime
  case. The triangle inequality gives the unconditional trivial bound `p` for
  a complete polynomial-character sum. If `D` is the distinct-root count and
  `p ≤ 4D²`, then `p ≤ 2D√p`, exactly the required target. The remaining
  four-active-root contract may therefore assume the strict large-
  characteristic condition `4D² < p`.
  `BurgessWeilPrimeFourRoots.lean` normalizes the exactly-four-active-root
  case. A checked Möbius reindexing sends one root to infinity, cancels the
  total denominator character using degree divisibility, and identifies the
  sum with a canonical three-point hypergeometric character sum minus one
  deleted value. A `2√p` bound for that canonical sum gives `2√p+1` before
  inactive-root correction and implies the original polynomial target.
  Consequently the large-characteristic residual is now the conjunction of
  `TaoPrimeThreePointHypergeometricWeilBound` and
  `TaoPrimeSplitPolynomialWeilBoundFiveActiveRootsLargeCharacteristic`; no
  four-root coordinate bookkeeping remains in the generic residual.
  `BurgessWeilPrimeSourceResidual.lean` removes the remaining arbitrary-
  polynomial generality from the production path. The higher-root predicate
  now ranges only over `primeLinearOrderPolynomial p r χ b`, with the tagged
  unique root and `r ≥ 2` already present in the source quotient. Its bridge
  internally dispatches the small-characteristic and zero-through-four-root
  cases and reaches the composite cube-free endpoint. In this exact path the
  canonical hypergeometric estimate is needed only for `p > 64`.
  The four-root contract is sharpened further to
  `TaoPrimeReducedPowerThreePointHypergeometricWeilBoundAboveSixtyFour`.
  Its three finite local characters must be powers of the one ambient
  Burgess character, and their exponents lie strictly below `orderOf χ`.
  Exact `pow_mod_orderOf` identities prove that this normalized finite-range
  statement covers every root multiplicity occurring in the cleared
  polynomial.
  Finally, `threePointMulCharSum_eq_legendreForm` scales the two nonzero
  finite marked points from `(λ, μ)` to `(1, t)` with `t=μ/λ`, extracting a
  character-valued constant of norm at most one. The production input is now
  the one-parameter predicate
  `TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour`, with
  `t ≠ 0,1`.
  `ExceptionalCharacterScales.lean`
  defines `R=floor(Z^0.0001)` and proves uniformly over supported divisors
  that these prefixes eventually exceed the cutoff and satisfy the period
  range. Bertrand supplies dyadic-band nonemptiness. Consequently an explicit
  Burgess proof now enters the normalized family estimate with no residual
  scale hypotheses.
  `ExceptionalCharacterNormalization.lean` identifies the exact half-open
  band cardinality with `π′(2Z)-π′(Z)`, transfers the pinned PNT from inclusive
  to strict prime counting, and proves this cardinality is asymptotic to
  `Z/log Z`. In particular, the exact BHM denominator is eventually at least
  `Z/(2 log Z)`.
  `ExceptionalCharacterAbsorption.lean` completes the remaining non-Burgess
  asymptotics and bootstrap in this chain. The two Selberg diagonal terms are
  `O(Z/log Z)`. Under the preliminary envelope `J≤A Z^(2/125)`, the exact
  exponent ledger makes the off-diagonal term
  `Z^(1-1/5000) log^3 Z=o(Z/log Z)`. Thus the normalized moment constant is
  independent of `A`. An arbitrary finite family is truncated at
  `⌊A Z^(2/125)⌋`; the exceptional threshold and that uniform moment bound
  force the truncation below its cap, yielding both `J≪Z^(2/125)` and the
  complete bounded second moment conditional only on the explicit cubefree
  Burgess target. The analytic Burgess proof is the remaining Lemma 5.1 step.
  `ExceptionalCharacterFixedLevel.lean` now connects this family theorem to
  the literal fixed-conductor finsets used by Section 6.  Taking `q₂=1`, it
  embeds every exceptional primitive character of level `q` into the
  heterogeneous datum type, proves pairwise separation, and preserves both
  cardinality and the squared prime sum exactly.  Consequently, for any
  varying squarefree `q≤Z^3.09`, explicit Burgess implies the literal
  `#Exceptional(q,Z)≪Z^0.016`, bounded squared-moment, and `O(λ⁻²)` tail
  conclusions.  No provisional family envelope remains.
  `ExceptionalCharacterAggregate.lean` proves that equality of primitive
  lcm-level lifts forces equality of the original levels and characters.
  Hence the dependent sigma of all literal exceptional characters over any
  admissible finite conductor set embeds as one automatically separated
  `q₁=1` family. Its total cardinality and complete double squared-moment
  sum are preserved exactly. Conditional on explicit Burgess, a single
  uniform Lemma 5.1 application bounds that entire conductor union, matching
  the family shape of the Section 6 exceptional divisor sum.
  `SmallPrimeExceptionalConductors.lean` constructs that exact conductor
  universe as the finite union of all nontrivial divisors of the ordered
  tuple moduli. It proves the tuple lcms and their divisors squarefree and
  bounds every conductor by the literal small-prime cutoff to the fiftieth
  power. The exact rounded inequality `cutoff^50<⌊z^(9/10)⌋` is now proved
  eventually, and every character scale above that lower prime scale satisfies
  the square-root Burgess range. Applying Lemma 5.1 once to the maximal finite
  set of admissible squarefree conductors yields one eventual constant valid
  pointwise for every admissible conductor subset and every one of the 1001
  scale selectors. Exact subset insertion and the completed Mertens sum absorb
  the exceptional term into a fixed multiple of the principal majorant. The
  explicit inequality `P_j^{-8} cutoff^50≤1` then absorbs the totient error
  as well. The resulting source-facing theorem bounds the entire literal
  small-prime fiftieth moment by a fixed multiple of the elementary principal
  majorant, conditional only on analytic Burgess.
  A recursive finite universe enumerates exactly all admissible factor lists
  of length below 1000; the distinct-product sum is bounded by the resulting
  literal list sum, preserving multiplicity and exposing the factor-count split.
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
  uniformly for every start `N>H` for all sufficiently large `H`; the former
  quadratic-window theorem is retained as a corollary. For every fixed positive
  `H`, Bernoulli monotonicity propagates the binomial inequality above the
  explicit threshold `H^H+1`. Consequently the unrestricted theorem is reduced
  to a bounded rectangle in `(H,N)`, which remains to be discharged. Thus
  `N/H²≥1/2` and the `H/400` measure bound are unconditional eventually; the
  unrestricted classical contract is no longer a Lemma 3.1 dependency. A fixed
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

## Release delta: prime-equidistribution-2.57

The production inventory now includes `BurgessAmplification.lean`. The new
module is imported by `Tao2026.lean` and `Audit.lean`; its declarations are
covered by explicit `#print axioms` commands. It certifies the finite interval
shift, unit affine reindexing, norm comparison, and sum-exchange layer needed
before the existing fourteenth-moment bound can be applied. It also certifies
the coprime multiplier-pair residue map, its exact first multiplicity moment,
and the weighted regrouping of the complete affine average.

This delta does not certify the still-missing second-moment collision bound,
Hölder estimate, parameter optimization, primitive Burgess core estimate,
or any theorem numbered 1.7--1.10.

## Release delta: prime-equidistribution-2.58

`BurgessAmplification.lean` now proves that the second moment of the residue
multiplicity is exactly the cardinality of its ordered collision family. For
unit multipliers, residue equality is proved equivalent to the source's
cross-multiplied congruence, and fixed-multiplier collision fibers expose that
congruence directly. The exact three-factor finite Hölder inequality is then
instantiated with the multiplicity: the first moment, collision count, and
complete `2r` character moment appear literally. Both the weighted complex
sum and the original coprime affine average receive this powered bound.

The numerical upper bound for the collision cardinality (the source's
`1 + H*gcd(a,c)/max(a,c)` estimate and its divisor-sum consequence), the
inductive boundary-error estimate, and parameter optimization remain open.

## Release delta: prime-equidistribution-2.59

`BurgessAmplification.lean` now proves the arithmetic fixed-multiplier
collision estimate. Residue collision is expressed as divisibility of an
integer determinant; under `2*A*H <= q`, the determinant difference is too
small for a nonzero multiple of `q`. Dividing the resulting exact relation by
`gcd(a,c)` gives reduced-multiplier spacing and the symmetric natural bound
`card <= H / (max a c / gcd a c) + 1`.

The global ordered collision set is decomposed exactly by multiplier pair.
Forgetting the fixed multiplier coordinates injects every global fiber into
the corresponding local fiber, so the full collision cardinality is bounded
by the explicit finite sum of those `max/gcd` majorants. The subsequent
elementary divisor-sum estimate, Burgess induction and boundary absorption,
and `r = 7` parameter optimization remain open. No theorem numbered
1.7--1.10 is proved unconditionally by this delta.

## Release delta: prime-equidistribution-2.60

The elementary summation following the local collision estimate is now
compiled. For a fixed upper multiplier `c`, each gcd quotient is majorized by
a divisor of `c`; counting its positive multiples shows that each divisor
costs at most `H`. Double-counting divisor incidences proves
`sum_{c<=A} tau(c) = sum_{d<=A} floor(A/d)`, and comparison with the harmonic
sum gives the real bound `A * harmonic A`.

Consequently the full residue-collision cardinality is at most the square of
the coprime multiplier count plus `2*H*sum_{c<=A} tau(c)`, and hence at most
that diagonal term plus `2*H*A*harmonic A` after casting to `ℝ`. This is a
slightly coarser constant than the asymptotically sharpened source display but
has the required `O(A*H*log A)` shape. The Burgess induction and translation-
boundary absorption, followed by the `r = 7` choices of `A` and `B`, remain
open. No theorem numbered 1.7--1.10 is proved unconditionally by this delta.

## Release delta: prime-equidistribution-2.61

The exact pre-Hölder Burgess recursion is now compiled. The affine `b`-sum is
first bounded pointwise in its `a`-coordinate and then regrouped as the real
multiplicity-weighted shifted-character sum. For an arbitrary shorter-
interval majorant `E`, the exact interval-shift identity controls both boundary
pieces at starts `N` and `N+H`. Summing over coprime multipliers proves the
source equation
`#A*B*|S(N,H)| <= sum_x v_A(x)|W_B(x)| + 2*sum_{a,b} E(ab)`
whenever `A*B <= H`.

This delta is unconditional finite algebra and introduces no analytic
hypothesis. The next step is to specialize `E` to the inductive Burgess power,
bound its finite `a,b` sum, and combine the result with the audited Hölder,
collision, and complete fourteenth-moment estimates. The `r = 7` parameter
optimization and Theorems 1.7--1.10 remain open.

## Release delta: prime-equidistribution-2.62

The shorter-interval error in the Burgess recursion is now specialized and
normalized. Monotonicity first replaces every coprime multiplier `a <= A` by
the common endpoint `A`. For a nonnegative power majorant
`E(K)=C*K^alpha*Q`, the remaining `b`-sum is at most
`B*C*(A*B)^alpha*Q`. Dividing equation (28) by the positive coprime-
multiplier count times `B` gives the source-facing bound
`|S(N,H)| <= M/(#A*B) + 2*C*(A*B)^alpha*Q`, where
`M=sum_x v_A(x)|W_B(x)|`.

This closes the scalar affine-boundary calculation at a deliberately coarse
endpoint constant. The next step is to extract the `2r`-th root from the
compiled powered Hölder estimate, insert the harmonic collision and complete
moment estimates, and choose the natural `r = 7` parameters. No theorem
numbered 1.7--1.10 is proved unconditionally by this delta.

## Release delta: prime-equidistribution-2.63

The Burgess main term is now closed through its analytic insertions. The
powered Hölder estimate is converted to an actual `1/(2r)` real-power bound
using positivity. A monotone interface replaces the collision and complete-
moment factors by arbitrary majorants; at `r=7`, this inserts the proved
diagonal-plus-`2*H*A*harmonic(A)` collision estimate and the compiled
diagonal-plus-`C*B^14*q^(1/2+epsilon)` complete-moment estimate.

The final theorem of this delta combines those estimates with the normalized
power-boundary recursion. It is the complete pre-optimization recurrence: the
main term is one explicit `1/14` power divided by `#A*B`, and the inductive
translation error is `2*C₂*(A*B)^alpha*Q`. The remaining Burgess work is now
scalar but substantial: prove a usable lower bound for the coprime multiplier
count, choose integer `A` and `B`, verify every range condition, and absorb the
boundary term. The composite complete-Weil estimate remains a visible
hypothesis. No theorem numbered 1.7--1.10 is proved unconditionally here.

## Release delta: prime-equidistribution-2.64

The first scalar denominator estimate is now compiled in the new
`BurgessOptimization` module. Exact integer Möbius inversion identifies the
number of positive `a <= A` coprime to `q` with
`sum_{d|q} mu(d)*floor(A/d)`. Evaluating the same identity over a full period
recovers `sum_{d|q} mu(d)/d = phi(q)/q`. Since replacing each real quotient by
natural division costs at most one, the short multiplier count satisfies
`A*phi(q)/q - tau(q) <= #A`.

This is coarser than the source's `2^(omega(q)-1)` discrepancy but remains
compatible with the existing divisor-`epsilon` estimates. A half-density
corollary is available whenever `2*tau(q) <= A*phi(q)/q`. The remaining
optimization is simplified by the additional elementary bound
`q/phi(q) <= tau(q)`, proved from `sum_{d|q} phi(d)=q`. Consequently the
single natural condition `2*tau(q)^2 <= A` guarantees half of the expected
coprime density. It remains to establish that condition for the rounded
choice of `A`, control the harmonic factor, choose `B`, and absorb the
inductive boundary. No theorem numbered 1.7--1.10 is proved by this delta.

## Release delta: prime-equidistribution-2.65

`BurgessOptimization` now proves that `2*tau(q)^2` is eventually bounded by
every floor-rounded positive power of `q`. Consequently any multiplier
length above that power has the required half-totient-density denominator.
The remaining multiplier-pair cardinalities in the rooted Holder term are
bounded by their scalar rectangles, and the collision bracket is compressed
under `A <= H` to `3*H*A*harmonic(A)`. This yields a fully scalar normalized
fourteenth-moment recurrence, including a complete-Weil specialization.

The actual integer parameters are now defined by
`B = floor(q^(1/14))` and `A = H/(K*B)`. Their floor losses are explicit:
eventually `q^(1/14)/2 <= B <= q^(1/14)`, while two complete denominator
blocks give `H/(2*K*B) <= A`. A single quadratic upper-range hypothesis
implies `2*A*H <= q`; the lower range `K*q^(1/14+eta) <= H` eventually
implies `2*tau(q)^2 <= A`. The combined admissibility theorem also proves
`1<=A`, `1<=B`, `A*B<=H`, and `A<=H`. Harmonic epsilon absorption, final
power algebra, and inductive boundary absorption remain. No theorem numbered
1.7--1.10 is proved by this delta.

## Release delta: prime-equidistribution-2.66

The first exponent-normalization layer is compiled. For `A<=q`, the harmonic
factor is bounded by `(1+delta^-1)*q^delta`; independently,
`q/phi(q)` is bounded by the frozen divisor-epsilon constant times `q^delta`.
The half-density denominator is rewritten exactly as
`2*S*(q/phi(q))/(A*B)`.

At `B<=q^(1/14)`, the two complete fourteenth-moment summands are bounded by
`(7^14+C)*q^(3/2+epsilon)`, and the fourteenth-root form has exact exponent
`q^(3/28+epsilon/14)`. An exact root factorization of the compressed
collision monomial is also proved. Combining it with the harmonic and moment
bounds yields the pre-substitution main factor
`A^(13/14)*H^(13/14)*q^(3/28+epsilon/14+delta/14)` with an explicit constant.
The remaining scalar step is to insert the proved lower bounds for rounded
`A,B`, account for the totient loss, and obtain
`H^(6/7)*q^(2/49+epsilon)` before boundary contraction. No theorem numbered
1.7--1.10 is proved by this delta.

## Release delta: prime-equidistribution-2.67

The rounded-parameter substitution is now compiled. From the exact quotient
geometry and the lower floor bound for `B`, the module proves
`H^13/(A*B^14) <= 2^14*K*H^12/q^(13/14)`. Exact real-power algebra then turns
the normalized `A,H` factor into the fourteenth root of this quotient and
bounds it by `2*K^(1/14)*H^(6/7)/q^(13/196)`.

Combining that estimate with the release-2.66 rooted collision/moment bound
proves the post-substitution main term with the exact conductor exponent
`2/49 + epsilon/14 + delta/14`. The reciprocal-totient factor has not yet
been multiplied into this theorem, and the normalized affine boundary has
not yet been made contractive. The complete-Weil estimate also remains an
explicit analytic hypothesis. No theorem numbered 1.7--1.10 is proved
unconditionally by this delta.

## Release delta: prime-equidistribution-2.68

The reciprocal-totient loss is now multiplied into the rounded main term.
The general theorem retains the separate exponent
`2/49 + epsilon/14 + delta/14 + deltat`; a specialization chooses moment,
harmonic, and totient losses `6*eta`, `eta`, and `eta/2`, respectively, and
therefore proves the exact target exponent `2/49+eta` with one explicit
constant.

The affine boundary is now quantitatively contractive as well. Exact natural
division gives `K*A*B<=H`, hence
`(A*B)^(6/7)<=H^(6/7)/K^(6/7)`. Whenever `K^(6/7)>=4`, the normalized
boundary is at most half the induction majorant; the concrete choice `K=128`
is proved to satisfy this condition. The next step is to combine these scalar
bounds with the compiled recurrence and its complete-Weil hypothesis. No
theorem numbered 1.7--1.10 is proved unconditionally by this delta.

## Release delta: prime-equidistribution-2.69

The rounded main and boundary estimates are now assembled inside the actual
complete-Weil scalar recurrence. The selected moment constant is uniform;
doubling the main coefficient leaves one copy for the main term and one for
the half-sized affine boundary. Exact `K*A*B<=H` proves that every translated
length is strictly smaller, so a strong-induction wrapper supplies both
endpoint intervals without an external callback.

For `K=128`, the core lower inequality eventually supplies every rounded
admissibility condition. The induction recursively handles shorter lengths
that remain in the core and uses the trivial interval estimate below it.
Consequently the primitive estimate
`H^(6/7)*q^(2/49+eta)` is compiled throughout the eventual medium range
`2*H^2 <= 128*q*floor(q^(1/14))`. Extending beyond that quadratic range is
the Pólya--Vinogradov completion step used in the pinned Burgess proof. The
prime finite-field complete-Weil residual also remains analytic input. No
theorem numbered 1.7--1.10 is proved unconditionally by this delta.

## Release delta: prime-equidistribution-2.70

The large-length Pólya--Vinogradov bridge is now compiled. Finite Fourier
inversion on `ZMod q` is proved from the primitive-character transform, and
a DFT-squared argument proves the exact composite-modulus Gauss-sum norm
`|tau(chi)|=sqrt(q)`. The interval Fourier kernel is reduced to the existing
geometric-series majorant; symmetric integral-test summation gives the
explicit estimate `10*sqrt(q)*(1+harmonic(q))`.

The harmonic loss is absorbed into `q^eta`. Failure of the quadratic
no-wrap condition gives exactly
`q^(45/98)<=H^(6/7)`, so the large-length estimate matches
`H^(6/7)*q^(2/49+eta)`. Combining this branch with the medium strong
induction proves the full eventual primitive core, and a finite-conductor
absorption removes the eventual qualifier. The file exports the primitive
all-prefix, imprimitive cubefree, and exact decimal Burgess contracts,
conditional only on `TaoPrimitiveCubefreeBurgessCompleteWeilBound`.

Thus the Burgess recurrence, Pólya--Vinogradov completion, and all
small-conductor bookkeeping are closed. The source-specific prime
finite-field complete-Weil residual remains the analytic input, so no theorem
numbered 1.7--1.10 is proved unconditionally by this delta.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` on the current checkout; the isolated production graph
contained 10036 jobs, including the root and axiom audit.

## Release delta: prime-equidistribution-2.71

`BurgessWeilPrimeKummer.lean` now states the remaining prime input in the
sharp classical form. For a split polynomial not equal to a nonzero scalar
multiple of an `orderOf χ`-th power, its complete character sum is bounded by
`(t-1)*sqrt(p)`, where `t` is the number of distinct geometric roots.

The exceptional power shape is defined explicitly. A checked root-
multiplicity argument proves that the tagged Burgess root, whose multiplicity
is not divisible by `orderOf χ`, excludes that shape even in the presence of
an arbitrary nonzero scalar. The sharp Kummer statement then implies the
coarser split-polynomial, linear-quotient, and cube-free composite contracts.

This consolidates the former four-root hypergeometric and five-or-more-root
source-specific assumptions into one canonical finite-field theorem. The
Kummer estimate itself remains the analytic input, so this delta does not
claim Lemma 5.2 or Theorems 1.7--1.10 unconditionally.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10037 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.72

`SylvesterSchurSmallLengths.lean` discharges the first forty-eight interval lengths
of the unrestricted Sylvester--Schur residual, uniformly over every start
`N > H`. Lengths one and two lie beyond the existing canonical fixed-length
threshold automatically. Lengths three and four use that threshold plus
bounded certificates. For lengths five through ten, much smaller verified
binomial-growth baselines propagate to every later start and leave only tiny
finite ranges, again closed by kernel-checked prime certificates. For
`11<=H<=48`, the uniform baseline `T=3H` and one bounded `Fin` certificate
close all remaining starts below that baseline.

Thus `sylvesterSchurBelow_eleven : SylvesterSchurBelow 11` is unconditional.
The stronger `sylvesterSchurBelow_fortyNine : SylvesterSchurBelow 49` then
combines it with the uniform finite-type certificate. Together with the
pre-existing finite-rectangle reduction, the still-open Sylvester--Schur
rectangle can be restricted to lengths `H >= 49`. This is a
strict reduction of the Theorem 1.7 arithmetic input; it does not yet prove
the full contract or any of Theorems 1.7--1.10 unconditionally.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10038 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.73

`SylvesterSchurEventual.lean` combines the uniform large-length theorem with
the threshold `H^H+1` for each of the finitely many smaller lengths. It proves
`exists_sylvesterSchurAboveStart`: there is one start cutoff beyond which the
Sylvester--Schur conclusion holds for every positive length.

`BadIntervals.lean` turns that start-uniform result into
`eventually_admissibleSylvesterSchurAtScale`. The equality boundary `H=N` is
still handled directly by Bertrand. Scale-local large-prime hypotheses are
then threaded through normalization, maximal transfer, recombination, local
dyadic windows, tail summation, and finite-prefix absorption. The packaged
endpoint `taoTheorem17_of_explicitBurgess` proves the exact Theorem 1.7
contract from explicit Burgess, Lemma 1.6(ii), and the adjacent one-term ratio,
without unrestricted Sylvester--Schur. Finally,
`taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess` reduces the
remaining Theorem 1.7 work to precisely the analytic Burgess estimate and the
critical smooth-number saddle asymptotic.

The unrestricted global Sylvester--Schur contract remains documented and its
small-length proof remains useful independently, but its still-open finite
rectangle is no longer on the Theorem 1.7 dependency path. This delta does not
claim Theorem 1.7 unconditionally, and it does not change the open inputs for
Theorems 1.8--1.10.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.74

`BurgessWeilPrimeKummer.lean` now rewrites every split polynomial correlation
as the literal distinct-root trace
`χ(lc(P)) * ∑_x ∏_a χ(x-a)^(rootMultiplicity a P)`. It also constructs the
canonical root-factor polynomial obtained by dividing all multiplicities by
`orderOf χ` and proves the converse exceptional-shape theorem: for a nonzero
split polynomial, all root multiplicities are divisible by the character
order if and only if the polynomial is a nonzero scalar multiple of an
order-th power.

Consequently `TaoPrimeKummerPolynomialWeilBound` is proved equivalent to
`TaoPrimeKummerRootProductWeilBound`, whose hypotheses and summand contain only
the distinct roots, their multiplicities, and one certified nondivisible
multiplicity. The Kummer estimate itself remains the analytic input; this
delta removes its remaining polynomial-factorization bookkeeping but does not
claim Burgess or Theorem 1.7 unconditionally.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.75

`primeKummerRootCorrelation_le_of_card_roots_le_two` proves the sharp Kummer
trace estimate for every polynomial with at most two distinct roots. The
one-root trace vanishes by character orthogonality; the two-root trace is the
already formalized Jacobi sum and has norm at most `sqrt(p)`.

The new predicate
`TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore` is therefore equivalent
to the full polynomial Kummer endpoint. Its direct composite bridge feeds the
entire Burgess chain. The remaining analytic input is now restricted to
nondegenerate Kummer traces with at least three distinct roots; this delta
does not prove that estimate or claim Theorem 1.7 unconditionally.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.76

`primePolynomialCharacterCorrelation_le_two_mul_sqrt_of_card_roots_eq_three_of_degree_dvd`
proves the sharp `2*sqrt(p)` Kummer bound when a split polynomial has exactly
three distinct roots and the character order divides its degree. After exact
active/inactive-root separation, two active roots give a Jacobi sum with one
deleted point; three active roots have trivial total character and the
projective Jacobi reduction applies. In either case the deleted-point cost is
absorbed by `sqrt(p) >= 1`.

The equivalent residual
`TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible` now
contains only traces with at least four roots or exactly three roots whose
degree is not divisible by the character order. It has a direct bridge to the
composite Burgess estimate. The residual trace estimate remains unproved, so
no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.77

`orderOf_dvd_natDegree_iff_dvd_sum_primeActiveRoots_count` proves both
directions of the active-root degree congruence. The new translation identity
then puts every three-active-root sum with nondivisible total degree into the
literal `TaoPrimeThreePointHypergeometricWeilBoundAt` form. Inactive-root
cases are controlled by the existing Jacobi estimate plus deleted points, and
the trivial complete-sum estimate covers the small characteristics.

Thus, assuming the already isolated three-point hypergeometric estimate, the
full polynomial Kummer theorem is equivalent to
`TaoPrimeKummerRootProductWeilBoundFourRootsOrMore`. Its direct composite
bridge leaves a pure four-or-more-root trace theorem as the other finite-field
input. Neither analytic trace estimate is claimed here, so Burgess and Theorem
1.7 remain conditional.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.78

`primeKummerRootCorrelation_le_of_card_roots_eq_four_of_degree_dvd` proves the
sharp `3*sqrt(p)` Kummer bound for every split four-root polynomial whose
degree is divisible by the character order, conditional only on the already
isolated three-point hypergeometric estimate. Exact active-root cardinalities
two, three, and four are handled by the Jacobi, projective-Jacobi, and
four-root Möbius reductions, respectively; inactive deleted points fit inside
the three available square-root units.

Accordingly, under the three-point endpoint, the full polynomial Kummer
theorem is equivalent to
`TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible`. For
Tao's degree-divisible cleared Burgess polynomials, the remaining trace input
now begins at five roots. The analytic hypergeometric and higher-root bounds
remain unproved.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.79

`TaoPrimeFourPointHypergeometricWeilBoundAt` isolates the exact geometric
input for four nontrivial finite local characters whose product is
nontrivial. `fourRootMulCharSum_eq_fourPointTranslate` and
`norm_primeActiveRootCharacterSum_le_three_mul_sqrt_of_card_eq_four_degree_not_dvd`
prove that a degree-nondivisible four-active-root Kummer trace is literally
an instance of this endpoint. The remaining active/inactive configurations
are discharged by the existing one-, two-, and three-point bounds plus exact
deleted-point accounting; four distinct roots force `p >= 4`, which absorbs
the worst three deleted points.

Consequently, under the three- and four-point endpoints, the full polynomial
Kummer theorem is equivalent to the pure
`TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore` residual. Its direct
composite bridge leaves no unresolved Kummer trace with fewer than five
distinct roots. Neither hypergeometric endpoint nor the five-or-more-root
trace bound is claimed as proved, so Burgess and Theorem 1.7 remain
conditional.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.80

`fiveRootMobius_term` and `fiveRootMulCharSum_eq_fourPointSum_sub` formalize
the projective reduction of five local characters whose product is trivial.
Sending one root to infinity cancels all denominator characters and leaves a
four-point sum plus one deleted value. Consequently
`norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree`
and `primeKummerRootCorrelation_le_of_card_roots_eq_five_of_degree_dvd` prove
the sharp degree-divisible five-root Kummer bound from the four-point
endpoint, including every active/inactive split.

The exact generic residual is now
`TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible`. More
importantly, the actual cleared Burgess family has the source-specific
residual
`TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic`;
its direct linear-quotient and composite bridges require only the documented
three-point input, the four-point endpoint, and at least six active roots.
The geometric endpoints and higher-root residual remain analytic inputs, so
no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.81

The four-point input used by the exactly-five-active-root Burgess branch is
now source-shaped. `TaoPrimePowerFourPointHypergeometricWeilBoundAt` records
that all four finite local characters are powers of the one Burgess
character. Exponent reduction modulo `orderOf χ` is proved exactly, and
`fourPointMulCharSum_eq_legendreForm` scales the marked points to
`0`, `1`, `t`, and `u`. Thus the final analytic input for this branch is the
finite-exponent, two-parameter proposition
`TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour`.

The power-specific five-root, active-root, and split-polynomial reductions
are all formalized and audited. Consequently the direct bridge from
`TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic`
no longer assumes the global endpoint for four unrelated characters at all
primes. It uses only the existing reduced one-parameter three-point input,
the reduced two-parameter four-point power input above `64`, and the exact
six-active-root source residual. These analytic inputs remain unproved, so
this delta does not claim Burgess or Theorem 1.7 unconditionally.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10039 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.82

`sixRootMobius_term` and `sixRootMulCharSum_eq_fivePointSum_sub` formalize the
next projective reduction on the exact degree-balanced Burgess path. Sending
one of six active roots to infinity cancels the six denominator characters
and leaves five finite powers of the single source character plus one deleted
value. The new active-root and split-polynomial theorems therefore close the
exactly-six-active-root branch from a sharp `4*sqrt(p)` five-point estimate.

The analytic input is normalized completely: exponents are reduced modulo
`orderOf χ`, scaling places the five finite points at `0`, `1`, `t`, `u`, and
`v`, and only `p > 64` is required. Consequently
`TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristic`
is now the source residual, with direct linear-quotient and composite bridges
from the reduced one-, two-, and three-parameter lower-point endpoints. Those
endpoints and the seven-active-root trace residual remain unproved, so no
unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10040 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.83

The analytic Burgess chain is now typed at the only moment order used by
Tao. `TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven` is propagated
through the fourteenth moment, amplification, rounded optimization,
Pólya--Vinogradov completion, and the explicit cubefree Burgess endpoint.
The former all-`r` complete-Weil proposition still exists as a reusable
stronger interface, but is no longer required by this production route.

This specialization is also proved below the composite boundary rather than
obtained only by specializing an all-orders result. Fixed-`Fin 7` local
prime-power predicates, strong cube-free CRT iteration, the prime quotient
interface, and
`TaoPrimeLinearOrderPolynomialWeilBoundSevenActiveRootsLargeCharacteristicRSeven`
connect the exact source residual directly to the fixed complete-sum input.
The unconditional prime-square stationary-phase theorem is reused unchanged.
Thus the remaining source trace assumption is literal at `r = 7`; the three
reduced lower-point endpoints and that seven-active-root residual remain
unproved, so no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10040 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.84

`sevenRootMobius_term` and `sevenRootMulCharSum_eq_sixPointSum_sub`
formalize the next degree-balanced projective reduction. One of seven active
roots is sent to infinity, the seven denominator characters cancel, and the
complete sum becomes a six-point power-character trace minus one deleted
value. The resulting `5*sqrt(p)+1` estimate fits the existing split-polynomial
allowance and closes the exactly-seven-active-root branch.

The six-point analytic input is source-normalized: its six exponents are
reduced modulo `orderOf χ`, scaling places its marked points at
`0,1,t,u,v,w`, and only `p > 64` is required. Both the reusable all-order and
literal fixed-`r=7` paths now end at an eight-active-root source residual.
The reduced one-, two-, three-, and four-parameter endpoints and that fixed
eight-active-root trace residual remain unproved, so no unconditional Burgess
or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10041 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.85

The literal fixed-`r=7` higher-root residual now records its complete finite
support. `card_roots_primeLinearOrderPolynomial_le` bounds the cleared
polynomial by `2*7=14` distinct roots, and active roots form a subset of those
roots. Therefore
`TaoPrimeLinearOrderPolynomialWeilBoundEightToFourteenActiveRootsLargeCharacteristicRSeven`
is sufficient for the fixed prime quotient and composite complete-sum
endpoints; no character-sum assertion above fourteen roots is assumed.

This leaves exactly the active-root cardinalities `8,9,10,11,12,13,14`, plus
the four reduced lower-point endpoints already exposed. These analytic inputs
remain unproved, so no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10041 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.86

Exactly eight degree-balanced active roots now reduce projectively to a
seven-point power-character trace and one deleted value. The new
`BurgessWeilPrimeEightRoots` module proves the pointwise Möbius identity, the
complete-sum formula, the `6*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Exponent reduction and scaling isolate the remaining
five-parameter normal form `0,1,t,u,v,w,z` above characteristic `64`.

Consequently the literal fixed-`r=7` higher-root residual is narrowed from
`8..14` to `9..14`. The new finite-window predicate has direct bridges through
the fixed prime quotient and cube-free composite endpoint. The five reduced
trace endpoints through seven points remain unproved, so no unconditional
Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10042 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.87

Exactly nine degree-balanced active roots now reduce to an eight-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeNineRoots` module proves the pointwise Möbius identity, the
complete-sum formula, the `7*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Exponent reduction and scaling isolate the remaining
six-parameter normal form `0,1,t,u,v,w,z,r₀` above characteristic `64`.

The literal fixed-`r=7` higher-root residual is consequently narrowed from
`9..14` to `10..14`, with direct fixed prime-quotient and cube-free composite
bridges. The reduced trace endpoints remain unproved, so no unconditional
Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10043 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.88

Exactly ten degree-balanced active roots now reduce to a nine-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeTenRoots` module proves the pointwise Möbius identity, the
complete-sum formula, the `8*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Exponent reduction and scaling isolate the remaining
seven-parameter normal form `0,1,t,u,v,w,z,r₀,s₀` above characteristic `64`.

The literal fixed-`r=7` higher-root residual is consequently narrowed from
`10..14` to `11..14`, with direct fixed prime-quotient and cube-free composite
bridges. The reduced trace endpoints remain unproved, so no unconditional
Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10044 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.89

Exactly eleven degree-balanced active roots now reduce to a ten-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeElevenRoots` module proves the pointwise Möbius identity, the
complete-sum formula, the `9*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Exponent reduction and scaling isolate the remaining
eight-parameter normal form `0,1,t,u,v,w,z,r₀,s₀,a₀` above characteristic
`64`.

The literal fixed-`r=7` higher-root residual is consequently narrowed from
`11..14` to `12..14`, with direct generic and fixed prime-quotient and
cube-free composite bridges. The reduced trace endpoints remain unproved, so
no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10045 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.90

Exactly twelve degree-balanced active roots now reduce to an eleven-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeTwelveRoots` module proves the pointwise Möbius identity, the
complete-sum formula, the `10*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Exponent reduction and scaling isolate the remaining
nine-parameter normal form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀` above characteristic
`64`.

The literal fixed-`r=7` higher-root residual is consequently narrowed from
`12..14` to `13..14`, with direct generic and fixed prime-quotient and
cube-free composite bridges. The reduced trace endpoints remain unproved, so
no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10046 jobs, including the root and dependency audit.
