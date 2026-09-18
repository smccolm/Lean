# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `prime-equidistribution-4.72`. It
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
  `QuadraticIdealDivisors`, `QuadraticSolutionCount`, `QuadraticUnits`, `ShortIntervalDecomposition`, `SmoothNumbers`, `SmoothNumberBounds`, `SmoothNumberRankin`, `SmoothNumberPrimeSum`, `SmoothNumberSourceRegimes`, `SmoothNumberPolylogRegimes`, `SmoothNumberLowerBound`, `SmoothNumberHildebrand`, `SmoothNumberCriticalLower`, `SmoothNumberCEPPacket`, `SmoothNumberCEPRecurrence`, `SmoothNumberCEPIntervals`, `SmoothNumberCEPWeights`, `SmoothNumberCEPSource`, `SmoothNumberCEPSize`, `SmoothNumberCEPPrimeMass`, `SmoothNumberCEPBootstrap`, `SmoothNumberCEPCoarse`, `SmoothNumberSaddlePoint`, `SmoothNumberSaddleRegimes`, `SmoothNumberSaddlePhase`, `SmoothNumberSaddleTilt`, `SmoothNumberSaddleProbability`, `SmoothNumberSaddleEulerCharacteristic`, `SmoothNumberSaddleFrequency`, `SmoothNumberSaddleCentralWindow`, `SmoothNumberSaddleCurvatureLower`, `SmoothNumberSaddleGaussianProduct`, `SmoothNumberStability`, `SmoothNumberSaddleCurvature`, `SmoothNumberSaddleLocalLimit`, `BadOneTermAsymptotics`,
  `PublicStatements`, `TypeIReduction`, `TypeIConvolutionBridge`, `TypeIWeylBridge`, `TypeISourceBlock`,
  `TypeIIReduction`, `TypeIIArithmetic`, `TypeIIKernel`, `TypeIIConvolutionBridge`,
  `TypeIISourceBlock`, `VeryBadIntervals`, `SylvesterSchurSmallLengths`, `SylvesterSchurEventual`, `VeryBadEquidistribution`,
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

## Current reproducibility boundary

The source crosswalk records the definitions, main targets, and proved
Proposition 2.3(i),(iii). Release 3.71 includes the first unconditional public
endpoint, Theorem 1.8. Theorems 1.7, 1.9, and 1.10 are not yet unconditional,
so the combined four-theorem proof release is not yet reproducible.

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

## Release delta: prime-equidistribution-2.91

Exactly thirteen degree-balanced active roots now reduce to a twelve-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeThirteenRoots` module proves the pointwise Möbius identity,
the complete-sum formula, the `11*sqrt(p)+1` active-root estimate, and the
exact split-polynomial bridge. Exponent reduction and scaling isolate the
remaining ten-parameter normal form `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀` above
characteristic `64`.

The literal fixed-`r=7` higher-root residual is consequently narrowed from
`13..14` to the exact active-root case `14`, with direct generic and fixed
prime-quotient and cube-free composite bridges. The reduced trace endpoints
remain unproved, so no unconditional Burgess or Theorem 1.7 claim is made.

On 2026-09-14, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10047 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.92

Exactly fourteen degree-balanced active roots now reduce to a thirteen-point
power-character trace and one deleted projective value. The new
`BurgessWeilPrimeFourteenRoots` module proves the pointwise Möbius identity,
the complete-sum formula, the `12*sqrt(p)+1` active-root estimate, and the
exact split-polynomial bridge. Exponent reduction and scaling isolate the
remaining eleven-parameter normal form
`0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀` above characteristic `64`.

The structural fourteen-root cap for the literal `r=7` polynomial converts
the final lower bound on active-root cardinality into equality. The fixed prime
quotient and cube-free composite bridges therefore no longer assume a source-
cardinality residual; they depend on the reduced trace endpoints through
thirteen points. Those endpoints remain unproved, so no unconditional Burgess
or Theorem 1.7 claim is made.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10048 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.93

`ErdosSelfridgeSource.lean` adds the source-facing Theorem 2 boundary from the
pinned 1975 Erdős--Selfridge paper. It proves that `consecutiveProduct N H` is
the source product over `[N+1,N+H]`, constructs the least prime `p^(H)`, proves
its minimality, and uses Bertrand to obtain `p^(H)<=N+H` in the exact residual
range `H<N`.

The exponent-two specialization is then fully internal: a hypothetical square
has every prime valuation divisible by two, contradicting Theorem 2's witness.
This proves bridges to `ErdosSelfridgeSquareCoreConclusion`, the full square
proposition, the Lemma 4.2 Theorem 1.10 consumer, and the direct Theorem 2.5
plus Baker--Harman--Pintz consumer. The prime-multiplicity proposition itself
remains unproved, so no unconditional Erdős--Selfridge or Theorem 1.10 claim is
made. The `erdos137` candidate was re-audited and not imported: it does not
contain this theorem, while its relevant elementary facts are already
subsumed by node 73.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10049 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.94

`ErdosSelfridgePowerFree.lean` formalizes the first internal step of the
pinned 1975 proof. The canonical factorization remainder and quotient modulo
`l` reconstruct every positive natural exactly as `a*x^l`, and every prime
valuation of `a` is strictly below `l`.

For a source-Theorem-2 counterexample, a new uniqueness theorem valid at the
closed boundary `H<=p` identifies each large-prime valuation of the interval
product with the valuation of its unique divisible factor. Divisibility by
`l` therefore removes all primes `p>=H` from the canonical coefficient. The
simultaneous counterexample theorem yields precisely equation (3) for every
factor in `[N+1,N+H]`. Source Lemma 1 and the subsequent deletion/counting
argument remain unproved, so the public Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10050 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.95

`ErdosSelfridgeProductSeparation.lean` continues the pinned 1975 proof from
equation (3). Failure of source Theorem 2 plus the named Sylvester--Schur
contract gives equation (2), `H^l<N`. Product-gcd control proves equation (4)
for distinct equal-cardinality subfamilies of `[N+1,N+H]`.

The complete stronger Lemma 1 is also compiled. After cancelling an arbitrary
positive numerator/denominator gcd, a lower gap between coprime rational
`l`-th powers contradicts the strict powered interval-gap upper bound.
Equation (3) transports this exclusion, and hence product injectivity, to the
canonical power-free coefficients. Lemma 2 and the remaining source
deletion/counting argument remain open, so the public Theorem 1.10 status is
unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10051 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.96

`ErdosSelfridgeDeletion.lean` formalizes the maximal-valuation deletion
argument of source Lemma 2. For each prime below `H`, its chosen interval
position dominates every other valuation. The retained coefficient valuation
is bounded by the corresponding distance valuation; the exact distance
product `m!*(H-1-m)!` divides `(H-1)!`.

The image of the prime choices is extended to exactly `primeCounting (H-1)`
deleted positions, proving both the source survivor cardinality and equation
(9). At exponent two, every canonical coefficient valuation is at most one,
so the same ledger proves equation (21): the product of all coefficients
divides `(H-1)!` times the product of primes below `H`. The subsequent
large-length inequalities and finite square cases remain open, so the public
Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10052 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.97

`ErdosSelfridgeSquareDensity.lean` begins Section 3.1 of the pinned 1975
proof. A general translated-interval theorem counts exactly `L/d` multiples
of `d` whenever `d∣L`. At length 36, inclusion--exclusion for `4`, `9`, and
`36` proves that exactly twelve entries are divisible by `4` or `9`.

The prime-square characterization of squarefreeness then gives at most 24
squarefree entries in any such block. The equivalent source-offset theorem
for the values `N+(i+1)`, `i<36`, is included. All four main endpoints are in
the dependency audit. The product inequality (22), equation (23), and finite
residual lengths remain open, so the public Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10053 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.98

`ErdosSelfridgeSquareDensity.lean` now completes source equation (22). The
36-term density theorem is iterated from an explicit finite base to obtain
`3*Q(M)≤2*M` for all `M≥44`. The first 64 squarefree values are identified
exactly through the prime squares at most 103, and their strict product bound
is checked by kernel reduction without forbidden evaluators.

Increasing finset enumerations prove first-64 minimality; deleting a maximum
then propagates `3^H*H! < 2^H*∏a` for every `H≥64`. Lemma 1 makes the canonical
counterexample coefficient map injective, so the source-facing equation (22)
is fully instantiated. All new endpoints are dependency-audited. Equation
(23) and the finite residual square cases remain open, so the public Theorem
1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10053 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-2.99

`ErdosSelfridgeSquareValuations.lean` formalizes the exact valuation algebra
between equations (21), (22), and (23). The primorial has factorization one
at each prime below `H`; extracting the full powers of `2` and `3` from the
equation-(21) divisibility gives an exact natural-number ledger.

That ledger is combined with the canonical strict equation-(22) theorem to
produce the source-facing pre-equation-(23) inequality. All four public
endpoints are dependency-audited. The four explicit logarithmic valuation
bounds, displayed equation (23), primorial contradiction, and finite square
cases remain open, so the public Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10054 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.00

`ErdosSelfridgeSquareValuations.lean` now proves the four valuation estimates
used by Erdős--Selfridge before equation (23). Legendre digit-sum identities
give the factorial lower bounds; exact halving/thirding recurrences and
two-sided discrepancies for odd interval valuations give the coefficient
product upper bounds.

The release also provides factorial-cancelled real, ratio, and `rpow` forms of
the pre-(23) ledger. `powerFreePart_two_preEquation23_logarithmic_of_failure`
inserts all four estimates into the exact counterexample inequality. All new
public endpoints are dependency-audited and use only the standard logical
axioms. The final simplification to the displayed constant `14/3`, the
primorial contradiction, and finite square cases remain open; public Theorem
1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10054 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.01

`ErdosSelfridgeSquareValuations.lean` now proves displayed equation (23).
Exact `rpow`/`logb` identities evaluate both logarithmic loss factors, while
`erdosSelfridge_equation23_root_factor_le` bounds the residual root expression
by `4H²`, safely within the printed `(14/3)H²` constant. The resulting public
theorem `erdosSelfridge_equation23_of_failure` has the literal source shape.

Both new endpoints are dependency-audited and use only the standard logical
axioms. The explicit primorial contradiction and finite residual square cases
remain open; public Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10054 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.02

`ErdosSelfridgePrimorial.lean` proves the exact identification of the local
prime product with `primorial (H-1)` and derives the eventual estimate
`prod_{p<H} p <= 3^H` from the frozen prime number theorem. The left side of
equation (23) is regrouped as `B^H`; exact rational root estimates prove
`B>3`, and polynomial-versus-exponential growth absorbs `(14/3)H^2`.

The public endpoints exclude square-case multiplicity failure for every
sufficiently large `H` and expose an existential natural threshold. All new
endpoints are dependency-audited and use only the standard logical axioms.
The source's explicit cutoff and finite residual square cases remain open, so
the public Theorem 1.10 status is unchanged.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10055 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.03

`ErdosSelfridgeFinite.lean` begins the finite Section 3.2 proof. It embeds the
`H` distinct canonical coefficients into the positive divisors of
`prod_{p<H} p`. Exact kernel-reduced candidate counts exclude `H=3` and
`H=5`.

For `H=4`, the image exhausts `1,2,3,6`, so its product is `36`. Multiplying
the canonical equation-(3) decompositions makes the interval product a
square, while the source difference-of-squares identity proves that four
consecutive positive integers never have square product. The combined public
endpoint excludes every failure with `3<=H<=5`. All new endpoints are audited
and use only the standard logical axioms. The explicit large cutoff and finite
lengths from six onward remain open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10056 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.04

`ErdosSelfridgeFinite.lean` now proves the exact length-six residue split.
Outside `5 | N+1`, a kernel-checked modulo-five enumeration leaves five
positions whose coefficients belong to the four candidates supported on
`2,3`. In the exceptional class, the middle four positions avoid five, their
coefficients exhaust `1,2,3,6`, and equation (3) forces a square product of
four consecutive integers.

The combined public endpoint now excludes every square-case failure with
`3<=H<=6`. All new endpoints are dependency-audited and use only the standard
logical axioms. The explicit large cutoff and finite lengths from seven onward
remain open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10056 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.05

`ErdosSelfridgeFinite.lean` now closes length seven. A kernel-checked
enumeration of the five residue classes of `N` proves that at least five of
the seven interval positions avoid divisibility by five. Their canonical
coefficients are distinct by Lemma 1 but belong to the four-element set
`1,2,3,6`, contradicting cardinality.

The combined public endpoint now excludes every square-case failure with
`3<=H<=7`; the release-3.04 endpoint is retained as a compatibility theorem.
All new endpoints are dependency-audited and use only the standard logical
axioms. The explicit large cutoff and finite lengths from eight onward remain
open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10056 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.06

`ErdosSelfridgeFinite.lean` now proves the full length-eight split. A reusable
modulo-35 reduction and closed enumeration leave at least five positions
avoiding both five and seven outside the source exception. Their distinct
coefficients cannot fit among the four products supported on `2,3`.

In the exceptional class `7 | N+1`, `5 | N+2`, the middle four terms avoid
both primes. Their coefficients exhaust `1,2,3,6`; equation (3) therefore
forces a square product of four consecutive integers, contradicting the exact
identity already formalized. The combined public endpoint covers
`3<=H<=8`. All new endpoints are dependency-audited and use only the standard
logical axioms. The explicit large cutoff and finite lengths from nine onward
remain open.

The cumulative canonical verification recorded for release 3.07 includes and
audits this entire delta.

## Release delta: prime-equidistribution-3.07

`ErdosSelfridgeFinite.lean` now closes lengths nine through thirteen. A
kernel-checked modulo-35 count supplies five positions avoiding `5,7` in
every length at least nine, closing the prime-stable block through eleven. A
second modulo-385 count supplies five positions avoiding `5,7,11` from length
twelve, closing the block through thirteen.

In both blocks, Lemma 1 makes the coefficients distinct and equation (3)
places them among the four divisors `1,2,3,6`. The combined public endpoint
now covers `3<=H<=13`. All new endpoints are dependency-audited and use only
the standard logical axioms. The explicit large cutoff and finite lengths
from fourteen onward remain open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10056 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.08

`ErdosSelfridgeFiniteCounts.lean` introduces a reusable union bound for the
positions divisible by `5,7,11,13`. Combining the general interval-multiple
bound with exact divisible-block counts leaves at least five positions for
every `14<=H<=17`. Their canonical coefficients are distinct and divide six,
so the four available values give the contradiction.

The combined public endpoint now covers `3<=H<=17`. All new endpoints are
dependency-audited and use only the standard logical axioms. The explicit
large cutoff and finite lengths from eighteen onward remain open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10057 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.09

`ErdosSelfridgePrimeUnion.lean` proves the sharp ceiling bound for one prime
and its arbitrary finite-union complement theorem. The explicit prime sets
through `17` and `19` leave five survivors at every length `18..20`.
`ErdosSelfridgeFiniteTwenty.lean` then transfers interval avoidance to
coefficient coprimality and divisibility by six.

The combined public endpoint now covers `3<=H<=20`. All new endpoints are
dependency-audited and use only the standard logical axioms. The explicit
large cutoff and finite lengths from twenty-one onward remain open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10059 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.10

`ErdosSelfridgeFiniteSeventy.lean` generalizes the survivor lower bound and
coefficient transfer to base `30`. Exact kernel computation verifies every
length `21<=H<=70`: at least nine coefficients avoid all primes from seven
upward, but only eight positive divisors of `30` are available.

The combined public endpoint now excludes every square-case failure with
`3<=H<=70`, completing Section 3.2. All new endpoints are dependency-audited
and use only the standard logical axioms. The explicit Section 3.1 cutoff for
`H>=71` remains open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10060 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.11

`ErdosSelfridgeLargeGrowth.lean` proves a strict rational lower bound
`31335/10000` for the effective equation-(23) base. An exact base calculation
at `H=297` and ratio induction establish dominance over `(14/3)H^2 3^H` for
every larger length. A closed natural-number certificate separately verifies
the actual prime-product inequality for every `71<=H<=296`.

These branches now assemble with the complete finite proof through seventy
and feed `ErdosSelfridgeSquareConclusion` conditional on the explicitly named
`ErdosSelfridgeThreePrimorialConclusion`. The only remaining Section 3.1
arithmetic is a Lean proof of the elementary bound `prod_{p<H} p<=3^H`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10061 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.12

`ErdosSelfridgeHanson.lean` formalizes Hanson's elementary primorial method.
The Sylvester-sequence reciprocal identity proves a strict floor-sum margin,
and factorial valuations show that every prime below `n` divides Hanson's
coefficient.  A fixed five-part multinomial with denominators `2,3,7,43` and
weights `903,602,258,42,1` supplies the quantitative upper bound entirely in
natural-number arithmetic.

Exact base-gap and initial-absorption inequalities close the strong-induction
step from `n=1400`; twenty-five monotone block certificates cover the finite
prefix.  Therefore `erdosSelfridgeThreePrimorialConclusion_hanson` proves the
named all-length `3^H` primorial contract, and
`erdosSelfridgeSquareConclusion_of_sylvesterSchur` leaves only the independent
`SylvesterSchurConclusion` assumption.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10062 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.13

`SylvesterSchurFactorialThreshold.lean` proves a sharper fixed-length
large-start criterion.  The ascending-factorial lower bound and the existing
small-prime binomial envelope show that
`H! * 2^r < (N+1)^(H-r)` forces a prime above `H`, for every exponent `r`
between the exact prime count and `H-1`.

The specialization `r=pi(H)` gives the audited cutoff
`sylvesterSchurPrimeCountFactorialThreshold H = H! * 2^pi(H) + 1`.
The classical `H! * 2^(H-1) + 1` cutoff is retained as a corollary.  The
unrestricted `SylvesterSchurConclusion` is now reduced to the smaller
`SylvesterSchurPrimeCountFactorialFiniteRectangle`; that rectangle, restricted
already to lengths at least `49`, remains open.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10063 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.14

`SylvesterSchurHundred.lean` extends the unconditional bounded-length theorem
from `H<49` to `H<101`.  Exact kernel evaluation verifies the `3H`
binomial-growth inequality for all lengths `49..100` and supplies a prime
witness for every start below the propagation baseline.

`sylvesterSchurBelow_oneHundredOne` combines that block with the earlier
small-length theorem and is uniform over all starts.  The remaining
exact-prime-count factorial rectangle is therefore restricted to `H>=101`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10064 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.15

`SylvesterSchurSqrtEnvelope.lean` proves a generic square-root factorization
split for binomial coefficients.  Low primes contribute at most
`n^sqrt(n)` and high primes occur with exponent at most one.  Under the
no-prime-above-`k` hypothesis, their contribution is bounded by `primorial k`.

For `2k<=n`, the checked three-multiple valuation lemma eliminates supported
high primes in `(n/3,k]`, improving the factor to `primorial (n/3)`.
The release-3.12 Hanson theorem converts both bounds to explicit powers of
three.  Audited binomial and consecutive-product endpoints now show that the
corresponding gap against `4^k/k` forces a prime divisor above `k`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10065 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.16

`SylvesterSchurCentralTail.lean` discharges the release-3.15 square-root/Hanson
gap on an explicit two-dimensional region.  Checked block induction proves
`x<=2^(sqrt(x)/16)` for `sqrt(x)>=320`, which yields
`(3H)^sqrt(3H)<=2^(H/4)` from `H>=34134`.  A second induction compares the
remaining polynomial multiple of `162^q` with `256^q`, where `q=H/4`.

Monotonicity extends the endpoint calculation to every `2H<=n<=3H`.
The audited binomial and consecutive-product endpoints therefore close every
start `H<N<=2H` for `H>=34134`, without an asymptotic or floating-point
threshold.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10066 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.17

`SylvesterSchurExplicitTail.lean` proves an effective all-start tail.  For
upper index at most `1024H`, certified logarithmic estimates discharge the
square-root/Hanson gap.  At `1024H`, Mathlib's explicit Chebyshev prime-count
bound proves the complete small-prime binomial-growth inequality; monotonicity
propagates it to every larger upper index.

Thus every start `H<N` is closed once `H>=4^101`.  Combining this theorem with
`sylvesterSchurBelow_oneHundredOne` and the exact prime-count factorial cutoff
defines `SylvesterSchurExplicitResidualRectangle`, with concrete bounds
`101<=H<4^101` and `N+1 < H! * 2^pi(H)+1`.  A checked assembly theorem shows
that this rectangle implies unrestricted `SylvesterSchurConclusion`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10067 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.18

`SylvesterSchurExplicitTail.lean` now proves the same all-start conclusion
from the substantially smaller cutoff `H>=250000`.  The certified inequality
`log H<=sqrt(H)/40`, anchored at the exact square `250000=500^2`, controls the
square-root/Hanson branch through upper index `64H`.  At `64H`, Mathlib's
explicit Chebyshev prime-count estimate gives the strict binomial-growth
margin, and the existing monotonicity theorem propagates it thereafter.

The checked residual proposition is therefore the concrete finite rectangle
`101<=H<250000` and `N+1 < H! * 2^pi(H)+1`.  No theorem statement outside the
explicit-tail quantitative boundary changed.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10067 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.19

`SylvesterSchurPrimeCountEnvelope.lean` sharpens the square-root split by
retaining the exact low-prime exponent `pi(sqrt(n))`.  Its consecutive-product
gap theorem remains purely integral, and an elementary residue count modulo
`30` supplies an auxiliary `pi(m)<=m/3` estimate.

`SylvesterSchurPrimeCountTail.lean` proves `pi(m)<=m/4` from `m=120`, using a
finite kernel endpoint certificate below `690` and reduced-residue counting
modulo `210` thereafter.  Together with `log H<=sqrt(H)/10`, this closes the
near branch through `64H` from `H=10000`.  The same prime-count saving proves
the far binomial-growth baseline on `10000<=H<250000`; release 3.18 handles
larger lengths.

The checked all-start cutoff is therefore `H>=10000`.  The exact residual is
`101<=H<10000` and `N+1 < H! * 2^pi(H)+1`, recorded by
`SylvesterSchurPrimeCountResidualRectangle` and its unrestricted assembly
theorem.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10069 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.20

`SylvesterSchurPrimeCountTailSixThousand.lean` adds the exact bounded
prime-count envelope `6*pi(m)<=m+84` for `100<=m<800`.  The certificate is
evaluated by Lean's kernel over a compact quotient range.  A certified
logarithmic estimate, `log H<=13*sqrt(H)/100`, converts this envelope into the
near-branch gap throughout `6000<=H<10000`.

The release-3.19 far binomial-growth baseline is generalized to `H>=2200`, so
it closes all complementary starts in the same bridge.  Together with the
previous tail this proves the all-start conclusion from `H>=6000` and leaves
exactly `101<=H<6000`, `N+1 < H! * 2^pi(H)+1`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10070 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.21

`SylvesterSchurPrimeCountTailTwoThousandTwoHundred.lean` proves the exact
finite estimate `4*pi(m)<=m+12` on `60<=m<400`.  It then uses an adaptive
transition: `16H` for `2200<=H<3000` and `20H` for `3000<=H<6000`.
Certified bounds `log H<=19*sqrt(H)/100` and
`log H<=16*sqrt(H)/100` close the respective near branches.

At both transition points, `pi(H)<=H/4` gives the strict binomial-growth
baseline; the existing monotonicity theorem handles every larger start.  The
all-start cutoff is therefore `H>=2200`, and the exact residual is
`101<=H<2200`, `N+1 < H! * 2^pi(H)+1`.

On 2026-09-15, `cmd /c run_tao_build.bat --no-pause` completed with
`FINAL RESULT: PASS` after this delta; the isolated production graph contained
10071 jobs, including the root and dependency audit.

## Release delta: prime-equidistribution-3.22

`SylvesterSchurPrimeCountTailFiveHundredTwelve.lean` proves exact finite
prime-count bounds tailored to three adaptive bands: transition `5H` on
`512<=H<625`, `6H` on `625<=H<1134`, and `5H` on
`1134<=H<2200`.  Sparse kernel-checked endpoint certificates yield
`pi(H)<=H/5` and `pi(H)<=H/6`.  Above `pi(1906)=291`, four exact finite
coprimality counts modulo `210` replace the two prohibitively expensive final
prime-count evaluations.

The certified logarithmic estimates close the near branches and the same
finite prime-count bounds give strict binomial-growth baselines on the far
branches.  The all-start cutoff is therefore `H>=512`, and the exact residual
is `101<=H<512`, `N+1 < H! * 2^pi(H)+1`.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10078 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice as the release gate.

## Release delta: prime-equidistribution-3.23

`SylvesterSchurPrimeCountTailOneHundredTwentyOne.lean` checks the central
binomial-growth baseline at `n=2H` for every `121<=H<512` except the five
lengths `139,140,199,200,201`.  Exact prime-counted near-gap certificates
bridge the first pair to `n=281` and the second triple to `n=403`; exact
binomial baselines at those endpoints propagate to every larger upper index.

Together with release 3.22, this proves the all-start conclusion from
`H>=121`.  The exact residual is the twenty-row rectangle `101<=H<121`,
`N+1 < H! * 2^pi(H)+1`.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10079 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice as the release gate.

## Release delta: prime-equidistribution-3.24

`SylvesterSchurComplete.lean` closes the last twenty length rows.  It checks
the common central binomial-growth baseline at upper index `243` for every
`101<=H<121`, then verifies all 420 admissible earlier starts in one bounded
Lean-kernel certificate.  Together with release 3.23, the resulting theorem
`sylvesterSchur` proves `SylvesterSchurConclusion` without a residual
rectangle.

`ErdosSelfridgeComplete.lean` combines the unrestricted Sylvester--Schur
theorem with the audited Hanson theorem to prove the exact square
Erdős--Selfridge specialization used by Tao's Theorem 1.10.  The public
Theorem 1.10 assembly therefore no longer takes Erdős--Selfridge as an
external hypothesis; its remaining inputs are Tao's Theorem 2.5 and
Proposition 2.3(ii).

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10081 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.25

`TypeIIConvolutionBridge.lean` connects the literal product-restricted Vaughan
Type II convolution block to the canonical analytic endpoint.  It proves an
exact outer-sum identity, Cauchy--Schwarz reduction to squared inner sums, and
an exact comparison between bounded product support and the full canonical
Vaughan block.  The actual beta coefficient is bounded by `1`, the gamma
coefficient by `log(2B)`, and arbitrary per-block square majorants reassemble
into the full convolution norm through a sum of square roots.

`TypeIISourceBlock.lean` composes that bridge with the existing conditional
mixed Weyl--Vinogradov theorem.  Its public theorem bounds the norm square of
the literal source Type II double block with the intrinsic low-scale Weyl
error and the high-scale `3(log P)^(-T)` error.  The open analytic proposition
`VinogradovExponentialSumEstimate` remains explicit; release 3.25 does not
claim Theorem 2.5.  The remaining downstream work is the source regime split,
all-block Type I/II summation and simplification, and Fourier assembly.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.26

`TypeIISourceBlock.lean` now closes the finite source-family regime split.
The Möbius-tail coefficient vanishes identically on every outer dyadic band
below the common subdivision budget once `2*budget≤U`; the divisor-tail
coefficient satisfies the analogous result under `2*budget≤V`.  Thus only
large--large block pairs enter the conditional Weyl--Vinogradov estimate.

The new `vaughanTypeIISourceBlockMajorant` records the exact surviving
expression, and the full literal Type II convolution is bounded by the sum of
the square roots of these majorants.  `TypeIIConvolutionBridge.lean` also
proves that a uniform block-square bound `R` yields the exact global factor
`(log₂ B+1)^204 sqrt(R)`, using the existing canonical family count.

Release 3.26 leaves the analytic `VinogradovExponentialSumEstimate` explicit.
The remaining downstream Type II work is to discharge the source cutoff and
block-scale comparisons uniformly and simplify the majorant to the target
logarithmic saving before the Type I/Fourier assembly.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.27

`TypeIISourceBlock.lean` now defines the canonical Vaughan source cutoff
`⌊B^(1/3)⌋₊`.  Kernel-checked little-o arguments prove that this cutoff
eventually dominates twice the `(log₂ B+1)^101` subdivision budget and also
dominates `2B^(1/4)`.  For `P≤B`, these results discharge the cutoff and outer
scale premises of the full Type II family theorem with `c=1/4`.

The same module now uses exact dyadic cutoff tests and an explicit filtered
product support.  Empty supports vanish; a contributing pair bounds the
analytic product scale by `2B`; and the global inequality
`2B*(log B)^d≤|N|` supplies every blockwise reciprocal-phase premise.  The new
canonical-cutoff theorem therefore retains only global source hypotheses and
the explicit `VinogradovExponentialSumEstimate` assumption.

Release 3.27 does not claim Theorem 2.5.  The remaining Type II tasks are the
open Vinogradov estimate and simplification of the explicit summed majorant,
followed by the Type I and Fourier assembly.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.28

`TypeIISourceBlock.lean` now fixes the minimal derivative-order family to
`{5,6}` and exports a fully canonical Type II family theorem.  Canonical
short-block lengths are bounded by `B/(log B)^100`, outer block cardinality by
the corresponding length, and the component-count logarithm by `2log B`.
Survival beyond the cube-root cutoff also gives the literal quarter-power
lower bounds for both dyadic scales.

The new `vaughanTypeIICanonicalGeometricBlockMajorant` replaces the exact
outer cardinality and component count by these bounds.  A separate abstract
monotonicity lemma keeps the comparison algebra auditable, and
`vaughanTypeIICanonicalSourceBlockMajorant_le_geometric` proves the resulting
majorant dominates every exact canonical source block.  The parenthesization
retains the component-count factor on both analytic error terms.

Release 3.28 does not claim Theorem 2.5.  The open boundary remains
`VinogradovExponentialSumEstimate`, followed by the remaining power/logarithm
absorption, Type I estimate, and Fourier assembly.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.29

`TypeIISourceBlock.lean` now retains the two source-critical dyadic widths
instead of using the common global-width fallback.  Literal product support
proves `2^s2^t≤B`, the diagonal cubic bound, and the endpoint-weighted quartic
bound.  Exact field normalization expands the resulting block expression with
logarithmic denominators `298`, `197`, and `297`.

The canonical inner cutoff strengthens the diagonal monomial to
`D²E≤B²/B^(1/4)`.  The new
`vaughanTypeIICanonicalPowerSavedBlockMajorant` retains that power saving while
compressing both analytic monomials to `B²`; it bounds every exact canonical
source block.  The complete conditional Type II convolution is bounded by the
sum of square roots of these power-saved majorants.

Release 3.29 does not claim Theorem 2.5.  Phase and endpoint decay absorption,
the final family summation, `VinogradovExponentialSumEstimate`, Type I, and
Fourier closure remain.

On 2026-09-15, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.30

`TypeIISourceBlock.lean` now removes the final block-dependent decay factors
from the power-saved Type II ledger.  The global phase lower bound replaces
`F^(-1/1024)` by `(log B)^(-d/1024)`, and the outer quarter-power endpoint
replaces `K^(-1/1024)` by `B^(-1/4096)`.  Cutoff and empty-support branches
remain exactly zero.

The new explicit common ledger flattens the diagonal quotient to `B^(7/4)`
and exposes all remaining powers without nested rpow expressions.  The full
conditional canonical convolution is bounded first by the exact family loss
`(log₂ B+1)^204` and then by `(3 log B)^204`, times the square root of this
single block-independent ledger.

Release 3.30 does not claim Theorem 2.5.  The remaining Type II tasks are the
final choice and absorption of `d,T`, the open
`VinogradovExponentialSumEstimate`, and subsequent Type I/Fourier assembly.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.31

`TypeIISourceBlock.lean` now absorbs the block-independent ledger into an
arbitrary requested logarithmic saving.  Fixed negative powers of the source
scale are proved eventually smaller than every prescribed negative
logarithmic power.  Under `P≤B≤2P`, the remaining phase and source terms are
compressed to one squared-block envelope `C B²(log P)^(-E)`.

Square-root extraction and the complete family loss require
`E=2S+408`.  The explicit choices `d=2048S+216064`, `T=2S+111`, and
Vinogradov parameter `(2S+113)/3` discharge all exponent inequalities.  The
new source-facing theorem gives `C B/(log P)^S` for every `S≥0`, conditional
on `VinogradovExponentialSumEstimate`.

Release 3.31 does not claim Theorem 2.5.  The Type II summation and exponent
arithmetic are complete; the named Vinogradov estimate, quantitative Type I,
and final Fourier assembly remain.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10083 jobs, including the root and dependency audit.  The canonical isolated
verifier was then run twice with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.32

The new `Tao2026/TypeIConvolutionBridge.lean` connects both literal Type I
Vaughan convolution terms to their exact ceiling-divided one-dimensional
fibers.  It proves product-box equality, phase rescaling, full-family triangle
reassembly, the source coefficient envelopes `1` and `log(2B)`, and the
finite Abel-summation entry point for the logarithmically weighted term.

Release 3.32 does not claim quantitative Type I cancellation or Theorem 2.5.
The remaining analytic work is the uniform prefix estimate, the named
Vinogradov proposition, quantitative low-frequency PNT, and final Fourier
recombination.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10084 jobs, including the production root and all new axiom-audit entries.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.33

`TypeIConvolutionBridge.lean` now removes zero outer coefficients before the
Type I triangle inequality. The active support of the first coefficient is
contained in `[1,U]`; the active support of the second is contained in
`[1,UV]`. Their block cardinalities are at most `U` and `UV`.

Uniform active-inner callbacks propagate through the exact canonical family
count. The complete first Type I convolution costs
`(logâ‚‚ B+1)^102 U Q`; the second costs
`(logâ‚‚ B+1)^102 log(2B) UV Q`. These are finite reduction theorems and do not
assert the remaining reciprocal-phase cancellation estimate.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10084 jobs, including all new active-support declarations and axiom audits.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.34

`TypeIConvolutionBridge.lean` now proves exact invariance of the
reciprocal-phase scale under Type I parameter rescaling, its antitonicity in
the positive scale variable, and the ceiling geometry of source fibers.
For `P,m>0`, every fiber from a subinterval of `[P,2P)` lies inside
`[ceil(P/m),2ceil(P/m))`; rounding the real scale `P/m` upward can only lower
the rescaled phase scale.  Thus a source bound by `(P/m)^4` transfers to the
rounded fourth-power Weyl condition.

Release 3.34 does not assert Type I cancellation or Theorem 2.5.  The
four-step endpoint-buffer and effective-error premises remain to be supplied
uniformly before the active-support callbacks can be instantiated.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10084 jobs, including the new geometry declarations and their axiom audits.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.35

The new `TypeIWeylBridge.lean` connects the quadratic Type I inner sums to the
four-step analytic estimate.  It reconstructs `[D,2D)` exactly from the
existing quotient decomposition with at most ten blocks.  When `D>=10`, each
nonempty block satisfies the five-length fit needed to contain the interval
and four optimized differencing ranges in its local dyadic window.

The reciprocal-phase scale at a local endpoint in `[D,2D]` is at least one
quarter of its source value.  One explicit source budget therefore controls
the local high-scale, inverse-scale, and interval-length terms, and the
two-term Weyl estimate is proved blockwise.  Release 3.35 does not yet
uniformize the local widths, sum the analytic majorants, or claim Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10085 jobs, including the new quadratic Weyl bridge and its axiom audits.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.36

`TypeIWeylBridge.lean` now bounds every local two-term width by the single
source width `(F/D^5+4/F)^(1/1024)`. All nonempty canonical pieces therefore
share one explicit majorant, and their exact cardinality supplies the factor
ten for a complete dyadic interval.

The decomposition, geometry, analytic estimate, and finite summation are also
proved for every half-open subinterval of `[D,2D)`. This includes the complete
family of initial prefixes consumed by the logarithmic Type I Abel theorem.
Release 3.36 does not yet establish the active-index source budgets or claim
Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10085 jobs, including the uniform subinterval declarations and axiom audits.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.37

`TypeIWeylBridge.lean` now performs the exact Type I substitution
`(N,M,D) -> (N/m,M/m²,ceil(P/m))`. The fixed order set `{5,6}`, explicit
ten-block rescaled majorant, rounded-scale admissibility predicate, and both
literal inner estimates are exported. The logarithmically weighted estimate
uses uniform control of every initial prefix through the finite Abel theorem.

Both estimates are inserted into the complete active Vaughan Type I families.
The resulting bounds retain the exact losses `(log₂ B+1)^102 U` and
`(log₂ B+1)^102 log(2B)UV`. Release 3.37 leaves the active-index source
inequalities and common logarithmically saving majorant as explicit premises;
it does not claim Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10085 jobs, including the rescaled fibers, complete-family callbacks, and all
new axiom-audit entries. The canonical isolated verifier was then run twice
with `FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.38

`TypeIWeylBridge.lean` now implements the source's exact analytic split on
each rounded Type I fiber. Low transformed phase scale uses the ten-block
Weyl estimate; high transformed phase scale uses the fixed-constant source
Vinogradov envelope, including critical deletion and regular-component loss.
The admissibility predicate is branch-local and does not impose unused
hypotheses.

The hybrid estimate is uniform on arbitrary subintervals, feeds every finite
Abel prefix, and is inserted into both complete active Vaughan families. The
source exponential parameter bound and a fixed positive-power lower bound on
the rounded scale eventually discharge the high branch's cutoff and numerical
smallness premises. Release 3.38 leaves the low-scale effective-error budget
and final common-majorant absorption open and does not claim Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10085 jobs, including all hybrid Type I declarations and axiom-audit entries.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.39

`TypeIWeylBridge.lean` now derives the low-scale Weyl effective-error budget
from the branch inequality `F(D) <= D^4` above one explicit absolute
threshold. It also proves the factor-four comparison between the source phase
scale at `P` and the transformed scale at `ceil(P/m)`.

The new `TypeISourceBlock.lean` proves the exact canonical active-support
geometry for both Vaughan Type I coefficient families. Active indices force
`ceil(P/m) >= B^(1/4)` eventually, hence exceed every fixed threshold and
retain one quarter of the ambient logarithm. Combining those facts with the
global source lower and exponential upper frequency bounds yields the full
hybrid admissibility predicate uniformly over every active index. Release
3.39 leaves only common-majorant logarithmic absorption and family summation
open on the Type I side and does not claim Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10086 jobs, including `TypeISourceBlock` and all new axiom-audit entries. The
canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.40

`TypeISourceBlock.lean` now retains the natural reciprocal outer-index factor
in complete Type I family aggregation. The reciprocal sums over the two
canonical active supports are bounded exactly by `harmonic U` and
`harmonic (U*V)`. Consequently, any fiber estimate of the form `(P/m)Q`
propagates through the full first and second Type I families with harmonic
losses instead of the polynomial cardinality factors `U` and `U*V`.

This closes the family-summation geometry required for logarithmic saving.
Release 3.40 leaves the branch-sensitive absorption of the explicit Weyl and
Vinogradov majorants open and does not claim Theorem 2.5.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10086 jobs, including all reciprocal-weighted aggregation declarations and
axiom-audit entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.41

`TypeIWeylBridge.lean` now exports a genuinely branch-sensitive Type I
majorant. The high branch is bounded solely through the named source
Vinogradov envelope, while the low branch reduces its Weyl width to
`(1/D + 16/(log B)^d)^(1/1024)` and uses the active quarter-power lower bound
for `D`. This avoids retaining the potentially large unused Weyl expression
on high fibers.

`TypeISourceBlock.lean` inserts the resulting reciprocal-weighted estimate
into both complete canonical Vaughan Type I families. Harmonic cutoff bounds,
the Abel coefficient, and short-interval aggregation have exact combined
logarithmic loss 104. The final theorems choose `T=S+104` and require the
explicit budgets `S+106<=3A` and `1024*(S+105)+1<=d`, yielding arbitrary
requested logarithmic saving. Quantitative Type I is now complete conditional
only on `VinogradovExponentialSumEstimateAt C1`; Theorem 2.5 itself is not yet
claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10086 jobs, including the complete Type I family bounds and all new
axiom-audit entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.42

The new `MangoldtSourceBlock.lean` imports the exact source-oriented Vaughan
identity and the completed Type I/II source blocks. It proves that the
initial cutoff term vanishes on sufficiently large dyadic intervals, retains
the signs and literal coefficient pairs of all three convolution terms, and
combines their norm estimates by the triangle inequality.

The final theorem uses the common explicit phase exponent
`2048*S+216064` and gives arbitrary logarithmic saving for the complete
quadratic Mangoldt reciprocal-phase sum. Its hypotheses deliberately retain
both the Type I reciprocal-scale formulation and the Type II `|N|`
formulation; proving their common source-facing wrapper is the next interface
step. The only analytic dependency is the named
`VinogradovExponentialSumEstimate` proposition, and Theorem 2.5 itself is not
yet claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10087 jobs, including `MangoldtSourceBlock` and all new axiom-audit entries.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.43

`MangoldtSourceBlock.lean` now proves the elementary comparison
`reciprocalPhaseScale N N 2 P <= 2*|N|` and derives both the logarithmic scale
lower bound and the fixed threshold 64 from the single source lower bound on
`|N|`. The explicit phase exponent `2048*S+216064` is more than sufficient
for the numerical threshold.

The exported theorem
`eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange` consequently uses
only one lower and one upper absolute-frequency hypothesis. It retains the
same arbitrary logarithmic saving and the same sole analytic dependency,
`VinogradovExponentialSumEstimate`.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10087 jobs, including the unified source-range declarations and their axiom
audits. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.44

The new `PrimeSourceBlock.lean` first proves an exact identity between the
half-open interval `[a,b)` and the local interval convention used by the
frozen prime-power-tail theorem. It transports that theorem to the prime sum,
derives a uniform dyadic envelope with a quarter-power saving, and absorbs the
tail into every requested negative logarithmic power.

The theorem
`eventually_norm_primeReciprocalPhaseSum_le_sourceRange` applies the unified
Mangoldt estimate to every initial prefix, removes the prime-power tail, and
uses reverse Abel summation to remove the logarithmic prime weight. The result
is the complete high-frequency unweighted quadratic prime exponential-sum
bound with the same one lower/one upper source-frequency interface.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10088 jobs, including `PrimeSourceBlock` and all new axiom-audit entries. The
canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.45

The new `FourierSourceBlock.lean` identifies the half-open `(1,1)` Fourier
prime sum exactly with the release-3.44 diagonal reciprocal-phase sum. It
then differentiates the diagonal additive character and performs interval
integration by parts with amplitude `t^3/((t+2)*log t)`, obtaining the
explicit dyadic integral bound `6*P^2/(|N|*log P)`.

The exported theorem
`eventually_norm_primeFourierMode_sub_integral_Ico_one_one_le_sourceRange`
combines the prime logarithmic saving with that inverse-frequency term. This
is intentionally only a diagonal Fourier bridge. General modes require
unequal coefficients `(q1*N,q2*M)`. Their exact prime-sum identity, derivative
formula, and same-sign nonstationarity are now audited, but the corresponding
unequal-parameter estimates, opposite-sign stationary cases, and the low-
frequency and zero-mode branches remain open; Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10089 jobs, including `FourierSourceBlock` and all new axiom-audit entries.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.46

The new `UnequalTypeIIVinogradov.lean` retains independent source
coefficients through the high-pair Type II chain. It proves the fixed
logarithmic envelope and eventual arbitrary-logarithmic saving for the exact
product-restricted correlation with parameters `(N,M)`, packages the result
as the source decay-kernel callback, and specializes it to canonical Vaughan
inner blocks.

The general dyadic transformed-scale theorem consumes separate exponential
upper bounds for `|N|` and `|M|` and preserves the factor-five envelope. The
low-scale Weyl distance-kernel theorem is still diagonal, so the full unequal
Type II family and Theorem 2.5 are not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10090 jobs, including `UnequalTypeIIVinogradov` and all new axiom-audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.47

The new `UnequalTypeIIWeyl.lean` closes the low-scale Type II correlation
estimate for independent source coefficients. It proves the combined linear
and quadratic transformed-scale lower bound on positive dyadic bands, the
corresponding distance-kernel and effective-error estimates, and the
source-shaped four-step Weyl bound.

That estimate is propagated through fixed block lengths, nearby-pair
absorption, near/far aggregation, the unequal Weyl--Vinogradov split,
canonical Vaughan inner blocks, and one actual weighted Vaughan Type II
double block. Complete double-family summation and the unequal
Mangoldt/prime/Fourier endpoints remain open; Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10091 jobs, including `UnequalTypeIIWeyl` and all new axiom-audit entries.
The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.48

The new `UnequalTypeIISourceBlock.lean` propagates the independent-coefficient
double-block estimate through complete finite Vaughan-family summation,
canonical cutoff specialization, exact block-majorant compression, explicit
decay, and arbitrary logarithmic saving. The compression reuses the prior
diagonal algebra through a synthetic block coefficient whose diagonal phase
scale is exactly the original unequal scale.

`UnequalMangoldtSourceBlock.lean` combines both general Type I families with
the completed unequal Type II theorem in the exact Vaughan decomposition and
exports one lower phase-scale condition at `4*P`. Separate upper bounds on
the two coefficients are retained. `UnequalPrimeSourceBlock.lean` removes
prime powers and applies reverse Abel summation, yielding the unweighted
prime exponential-sum estimate for every nonzero quadratic coefficient.

General Fourier completion is not claimed: zero-quadratic modes, unequal
oscillatory integrals (including stationary opposite-sign modes), low
frequencies, and the final Fourier sum remain open. Theorem 2.5 is not
claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10094 jobs, including all three new source modules and their axiom-audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.49

The new `UnequalFourierSourceBlock.lean` proves the logarithmic
oscillatory-integral estimate for independent same-sign coefficients. In the
positive chamber, the exact amplitude `t^3/((A*t+2*B)*log t)` is differentiated,
shown to be increasing for `t>=2`, and inserted into interval integration by
parts. Complex conjugation transports the norm bound to the negative chamber.

These integral estimates are combined with the release-3.48 unequal prime
estimate to produce the literal prime-Fourier-mode-minus-integral discrepancy
in both same-sign chambers. Opposite-sign stationary modes, coordinate-axis
modes, low frequencies, and the final Fourier assembly remain open; Theorem
2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10095 jobs, including `UnequalFourierSourceBlock` and all new axiom-audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.50

The new `StationaryFourierSourceBlock.lean` isolates the unique critical
point `-2*B/A` and factors the opposite-sign phase derivative exactly through
distance from it. For a critical point in the dyadic source interval, the
phase-scale lower hypothesis yields an explicit lower bound on `|A|` and,
outside radius `δ`, on the derivative magnitude.

The logarithmic interval integral is decomposed exactly into two far pieces
and a central stationary neighborhood. The latter is bounded by
`2*δ/log P`. This release does not yet claim the opposite-sign discrepancy:
far-piece cancellation and optimization of `δ` remain, followed by axis
modes, low-frequency control, and final Fourier assembly.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10096 jobs, including `StationaryFourierSourceBlock` and all new axiom-audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.51

`StationaryFourierSourceBlock.lean` now supplies the two missing far-piece
cancellation bounds. Integration by parts was generalized to intervals where
the critical linear factor is nonzero. The amplitude derivative has the
required sign on the left and on the first right segment; after the turning
point it is bounded explicitly and integrated over the residual tail.

The far estimates and central length bound give a complete raw stationary
inequality for an interior radius-`δ` neighborhood. Inserting the source
coefficient lower bound and choosing `δ=P/sqrt L` proves
`50*P/(sqrt L*log P)` for `L>=4`. Endpoint clipping, the conjugate chamber,
coordinate-axis modes, low frequencies, and final Fourier assembly remain;
Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10096 jobs, including all release-3.51 declarations and axiom-audit entries.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.62

The new `SpecializedFourierPartition.lean` performs the full per-mode
high/low split for `M=N`, `j=2` on natural half-open dyadic subintervals. Its
high branch exhausts zero-coordinate, same-sign, and opposite-sign modes; in
the last case the fixed Fourier box and stationary-point identity provide the
eventual exterior-left bound. Its scalar absorption ledger then turns the
three-term majorant into `P/(log P)^S` for every target natural `S`.

The theorem remains conditional on the explicit propositions
`ClassicalMangoldtDiscrepancyLogSaving` and
`VinogradovExponentialSumEstimate`. Finite Fourier summation and arbitrary
real-interval reduction remain, so Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10109 jobs, including `SpecializedFourierPartition` and all three new
axiom-audit entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.63

`eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving` sums the
release-3.62 modewise bound over the entire retained Fourier box. It uses the
exact coefficient `ℓ¹` norm supplied by `FourierAssembly.lean` and absorbs
that fixed constant with two spare logarithmic powers. The specialized finite
polynomial discrepancy now has arbitrary log saving on natural half-open
dyadic subintervals. Arbitrary-real-interval reduction remains, so Theorem
2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10109 jobs, including the finite-assembly declaration and its axiom-audit
entry. The canonical isolated verifier was then run twice successfully as the
release gate.

## Release delta: prime-equidistribution-3.64

The new `SpecializedIntervalReduction.lean` identifies the natural points of
an order-convex real dyadic interval with one exact `Finset.Ico`. The induced
real half-open core preserves `primesInScaleSet` and the complete finite prime
sum exactly. For a nonempty core, order convexity confines the symmetric
difference to two unit endpoint intervals, hence its Lebesgue measure is at
most two. Integral endpoint absorption and the empty-core case remain, so
Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10110 jobs, including every interval-reduction declaration and axiom-audit
entry. The canonical isolated verifier was then run twice successfully as the
release gate.

## Release delta: prime-equidistribution-3.65

`SpecializedIntervalReduction.lean` now proves the generic norm bound for
changing measurable integration sets, caps the analytic natural core at
`2P`, and proves that this cap preserves every sampled prime. The only
potential removed natural endpoint is `2P`, which is composite for `P >= 2`.
The capped symmetric difference still has volume at most two. Intervals with
empty natural core are confined to one open unit cell, making both the prime
sum and its endpoint estimate elementary.

Combining these branches with the release-3.63 natural-interval theorem gives
`eventually_specializedFiniteFourierPolynomial_interval_le_logSaving` for
every measurable order-convex real dyadic interval and every fixed finite
Fourier polynomial. The quantitative-PNT and Vinogradov propositions remain
explicit assumptions; general smooth-weight reconstruction remains open, so
Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10110 jobs, including all release-3.65 declarations and axiom-audit entries.
The canonical isolated verifier was then run twice successfully as the
release gate.

## Release delta: prime-equidistribution-3.66

`TorusFourier.lean` now gives an exact pointwise truncation-error bound by the
outer square-box coefficient `l1` tail. `FourierRadial.lean` sums the existing
smooth radial coefficient estimate over that complement. The new
`SpecializedFourierReconstruction.lean` transfers both forms through the
prime-sum/integral stability theorem and the release-3.65 arbitrary-interval
finite-polynomial estimate.

The resulting smooth discrepancy has arbitrary logarithmic saving plus one
explicit universal radial cubic tail remainder. An explicit rate for that
tail and analytic uniformity on a growing Fourier box remain, so Theorem 2.5
is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10111 jobs, including all release-3.66 reconstruction declarations and their
axiom-audit entries.
The canonical isolated verifier was then run twice successfully as the
release gate.

## Release delta: prime-equidistribution-3.67

`FourierDecayRate.lean` proves an explicit `(R+1)^(-1/2)` bound for the
universal radial cubic tail using a summable radial `5/2` envelope.
`SpecializedGrowingFourier.lean` chooses a polylogarithmic Fourier radius,
absorbs its frequency growth into half of the stretched-log epsilon margin,
and proves uniform growing-box mode estimates.

The coefficient-normalized finite assembly and arbitrary-interval endpoint
reduction quantify the coefficient family after the eventual threshold.
Their smooth specialization is uniform in `W`, `I`, and `N` and has one
explicit universal reconstruction constant. The conclusion is presently on
eventual natural scales and remains conditional on the two named analytic
propositions; the literal real-scale Theorem 2.5 contract is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10113 jobs, including both release-3.67 modules and all new axiom-audit
entries. The canonical isolated verifier was then run twice successfully with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.68

`SpecializedRealScale.lean` transfers the eventual natural-scale smooth
estimate to the literal real-scale specialized contract. It proves exact
prime-set preservation after passing to `ceil(P)`, controls the removed lower
endpoint strip by `taoC3Norm W / log P`, transfers the parameter range to the
ceiling scale, converts natural logarithmic powers to arbitrary positive real
exponents, and absorbs bounded initial scales with a uniform elementary bound.

The declaration `taoTheorem25Specialized_of_analyticInputs` now has conclusion
`TaoTheorem25SpecializedConclusion`. It remains conditional exactly on
`ClassicalMangoldtDiscrepancyLogSaving` and
`VinogradovExponentialSumEstimate`; neither proposition is introduced as an
axiom.

On 2026-09-16, `lake build Tao2026.SpecializedRealScale Tao2026
Tao2026.Audit` completed successfully with 10114 jobs. The new audit entries
report only `propext`, `Classical.choice`, and `Quot.sound`. The canonical
isolated verifier was then run twice successfully with `FINAL RESULT: PASS` as
the release gate.

## Release delta: prime-equidistribution-3.69

`QuantitativePNTBridge.lean` converts the conventional de la Vallée Poussin
estimate
`|Chebyshev.psi x - x| <= C*x*exp(-c*sqrt(log x))` into the precise global
half-open Mangoldt discrepancy contract used by the low-frequency proof. The
module proves `cumsum Λ k = Chebyshev.psi k - Λ k`, absorbs the endpoint term,
and proves that the stretched exponential beats every fixed logarithmic
power.

The declaration
`taoTheorem25Specialized_of_chebyshevPsiDeLaValleePoussin` has conclusion
`TaoTheorem25SpecializedConclusion`, conditional on the standard quantitative
`ψ` proposition and `VinogradovExponentialSumEstimate`. These remain explicit
propositions rather than axioms or proved analytic theorems.

On 2026-09-16, `lake build Tao2026.QuantitativePNTBridge Tao2026
Tao2026.Audit` completed successfully with 10115 jobs. The new audit entries
report only `propext`, `Classical.choice`, and `Quot.sound`. The canonical
isolated verifier was then run twice successfully with `FINAL RESULT: PASS` as
the release gate.

## Release delta: prime-equidistribution-3.61

`StationaryFourierSourceBlock.lean` now subtracts endpoint-stationary
integrals to cover every subinterval when the critical point belongs to the
ambient dyadic block. It also proves the exterior-left first-derivative bound
for `0 <= s <= P/2` and the fixed-ratio identity and Fourier-box bound when
`M=N`.

`UnequalFourierSourceBlock.lean` strengthens same-sign cancellation to depend
on the complete reciprocal phase scale, including the quadratic-dominant
case. `LowFrequencyAbsorption.lean` proves the exact comparison
`F(P) <= 16 F(4P)` and the resulting deterministic high/low dichotomy. The
finite mode partition remains, so Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10108 jobs, including every release-3.61 declaration and axiom-audit entry.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.53

The new `CoordinateAxisFourierSourceBlock.lean` closes the pure quadratic
coordinate axis. A positive-variation integration-by-parts theorem gives the
dyadic integral bound, the exact pure quadratic phase scale converts it to
`P/(L*log P)`, and the unequal prime estimate yields the literal
prime-minus-integral Fourier discrepancy.

The pure linear axis remains open because its Type II correlations have zero
quadratic coefficient and do not satisfy the present quadratic Weyl and
Vinogradov interfaces. Low frequencies and final Fourier assembly also
remain; Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10097 jobs, including `CoordinateAxisFourierSourceBlock` and all new audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.54

The new `LinearAxisTypeII.lean` closes the zero-quadratic obstruction at the
pointwise Type II correlation level. The derivative critical sets are empty,
so the high-scale branch uses the existing conditional
`VinogradovExponentialSumEstimate` on the entire interval without deletion or
component loss. The low-scale branch applies the internal four-step Weyl
estimate on the regular interval and proves the exact short-block geometry,
far-pair inverse-scale inequality, and effective-error estimate required by
the standard four-kernel bound.

The pure-linear Fourier integral side is also present, with dyadic bound
`6*P^2/(|A|*log P)`, exact phase scale `|A|/(4*P)`, and source-scale bound
`2*P/(L*log P)`. Aggregation through Type II double blocks and the Vaughan,
Mangoldt, and prime layers remains open. Low frequencies and final Fourier
assembly also remain; neither the complete pure-linear axis nor Theorem 2.5 is
claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10098 jobs, including `LinearAxisTypeII` and all new audit entries. The
canonical isolated verifier was then run twice with `FINAL RESULT: PASS` as
the release gate.

## Release delta: prime-equidistribution-3.55

The pure-linear Type II path is now complete through the full Vaughan source
family. `LinearAxisTypeII.lean` lifts the zero-quadratic pointwise Weyl and
conditional Vinogradov bounds through arbitrary short double blocks,
canonical dyadic blocks, and literal weighted-convolution double blocks.
`LinearAxisTypeIISourceBlock.lean` performs the finite family sum and reuses
the audited scalar ledger to obtain the explicit arbitrary-log-saving source
theorem.

This does not yet give the pure-linear prime endpoint. The two Type I Vaughan
families still need zero-quadratic analogues before Mangoldt and prime
assembly. Low frequencies and final Fourier assembly also remain; Theorem 2.5
is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10099 jobs, including `LinearAxisTypeIISourceBlock` and all new audit entries.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.56

The pure-linear coordinate axis is now complete. `LinearAxisTypeI.lean`
specializes the empty-critical-set Weyl and conditional Vinogradov branches to
both Vaughan Type I families. `LinearAxisMangoldtSourceBlock.lean` combines
them with the release-3.55 Type II family through the exact Vaughan identity;
`LinearAxisPrimeSourceBlock.lean` removes prime powers and performs reverse
Abel summation. `LinearAxisFourierSourceBlock.lean` combines the resulting
prime estimate with the existing pure-linear integral theorem to prove the
literal zero-quadratic Fourier-mode discrepancy.

Both coordinate axes are now closed. Low frequencies and final Fourier
assembly remain; Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10103 jobs, including all release-3.56 modules and axiom-audit entries. The
canonical isolated verifier was then run twice with `FINAL RESULT: PASS` as
the release gate.

## Release delta: prime-equidistribution-3.57

`LowFrequencyIntegral.lean` now proves the elementary discrete-to-continuous
part of Tao's low-frequency argument. On every dyadic interval it controls
the variation of `e(N/t+M/t^j)/log t`, compares each integer sample with its
unit-cell integral, telescopes those cells exactly, and obtains the explicit
full-interval error
`2*pi*(j+1)*F/log(P) + 1/log(P)^2`.

This release does not assume or claim the missing quantitative prime number
theorem. That logarithmic-error Mangoldt discrepancy is now the isolated
analytic input needed before the low-frequency prime comparison can be
assembled. The zero mode and final finite Fourier partition also remain;
Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10104 jobs, including `LowFrequencyIntegral` and all new axiom-audit entries.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.58

The low-frequency Abel layer now uses the logarithmically weighted character
itself. `LowFrequencyIntegral.lean` defines the Mangoldt/log sum, bounds its
endpoint and total variation, and combines it with release 3.57 to compare
that sum directly with the interval integral under one explicit uniform
Mangoldt partial-sum bound.

`LowFrequencyPNT.lean` records the missing classical quantitative PNT as a
global prefix-discrepancy proposition, derives the uniform dyadic estimate,
and inserts it into the complete Mangoldt/log-to-integral consumer. The PNT
proposition is a hypothesis, not an axiom or proved theorem. Prime-power
removal, the zero mode, and final Fourier assembly remain; Theorem 2.5 is not
claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10105 jobs, including `LowFrequencyPNT` and all new axiom-audit entries. The
canonical isolated verifier was then run twice with `FINAL RESULT: PASS` as
the release gate.

## Release delta: prime-equidistribution-3.59

`LowFrequencyPrime.lean` proves the exact `Lambda/log` split into the literal
unweighted prime sum and a higher-prime-power tail. The latter is bounded by
the frozen local prime-power estimate and retains every requested logarithmic
saving. Combining it with release 3.58 gives the conditional low-frequency
prime-minus-integral theorem.

`LowFrequencyFourier.lean` transports that result to the literal Fourier-mode
sum and integral used by the finite assembly. The theorem is uniform in the
integer mode and includes an explicit zero-mode specialization. The sole
analytic hypothesis remains `ClassicalMangoldtDiscrepancyLogSaving`; final
logarithmic absorption and the high/low finite mode partition remain, so
Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10107 jobs, including the two release-3.59 modules and all new axiom-audit
entries. The canonical isolated verifier was then run twice with
`FINAL RESULT: PASS` as the release gate.

## Release delta: prime-equidistribution-3.60

`LowFrequencyAbsorption.lean` proves the deterministic absorption ledger for
the explicit low-frequency estimate. It combines eventual
`C*(log P)^d <= P`, eventual growth of fixed log powers, and the
polylogarithmic phase-scale cutoff to produce the literal uniform bound
`P/(log P)^S` for every target `S`.

The result remains conditional on `ClassicalMangoldtDiscrepancyLogSaving`,
which is a proposition rather than an axiom. The finite high/low Fourier
partition remains, and Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10108 jobs, including `LowFrequencyAbsorption` and its axiom-audit entries.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.52

The stationary estimate is now valid with the optimized neighborhood clipped
at either or both integration endpoints. The exact case split preserves the
release-3.51 bound. Simultaneous coefficient negation preserves the stationary
point and conjugates the integral, so both opposite-sign orientations are
covered by one absolute-coefficient theorem.

The deterministic estimate is exposed for the literal Fourier-mode integral
and combined with the unequal prime theorem. This gives a source-range
prime-minus-integral discrepancy for stationary modes with both coefficients
nonzero. Coordinate-axis modes, low frequencies, and final Fourier assembly
remain open; Theorem 2.5 is not claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10096 jobs, including all release-3.52 declarations and axiom-audit entries.
The canonical isolated verifier was then run twice with `FINAL RESULT: PASS`
as the release gate.

## Release delta: prime-equidistribution-3.70

`ClassicalQuantitativePNT.lean` closes the classical quantitative-PNT
boundary without a new assumption. It combines
`ford_asymptotic_zero_free_native`, the rectangle-uniform finite-low-zero
bridge, `sharpPsiTruncationBound_native`, and the global Jensen zero-count
estimate. A finite low-zero reciprocal constant and the coarse bound
`zeroCount 0 T <= K*T^2` control the truncated zero sum. At the height
`exp(min(1,c/8)*sqrt(log x))`, the zero sum and sharp-Perron error both have a
stretched-exponential square-root-logarithmic saving.

The new public theorems
`classicalChebyshevPsiDeLaValleePoussin_native` and
`classicalMangoldtDiscrepancyLogSaving_native` are unconditional.
`taoTheorem25Specialized_of_vinogradov` reaches the literal
`TaoTheorem25SpecializedConclusion` from
`VinogradovExponentialSumEstimate` alone. The audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for every new declaration.

On 2026-09-16, `lake build Tao2026.ClassicalQuantitativePNT Tao2026
Tao2026.Audit` completed successfully with 10116 jobs.
The canonical isolated verifier `cmd /c run_tao_build.bat --no-pause` then
completed with `FINAL RESULT: PASS`, including hash checks, warning-failing
production and audit builds, forbidden-shortcut and root-reachability scans,
and semantic regression tests.

## Release delta: prime-equidistribution-3.71

Five source-faithful IK modules now prove the formerly residual
`VinogradovExponentialSumEstimate`. They separate the large Taylor-remainder
cutoff from the effective degree `floor(4 log F/log X)`, prove the quarter
block's `k^2/25` mass, use explicit Ford moments for `k>=10000`, and take a
finite maximum of native critical coefficients below that threshold. The
complementary parameter range is closed by the trivial cardinality bound.

`Theorem25Complete.lean` combines this result with the unconditional classical
quantitative PNT, proving the literal specialized Theorem 2.5 and
`TaoTheorem18Conclusion` with no hypotheses. The audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for the new declarations.
`PublicEndpointReductions.lean` then discharges Theorem 2.5 in the established
Section 4 consumers, leaving Proposition 2.3(ii) alone for Theorems 1.9 and
1.10. The production root and audit build contains 10123 jobs.

On 2026-09-16, the canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` completed twice with
`FINAL RESULT: PASS`, including the hash, raw-Mermaid, warning-failing build,
axiom-audit, forbidden-shortcut, root-reachability, and semantic gates.

## Release delta: prime-equidistribution-3.72

`SmoothNumberSaddleTilt.lean` turns the exact finite Euler product into a
normalized tilted mass on positive smooth integers. It proves total mass one,
identifies the first two log-partition derivatives with `-phiOne` and
`phiTwo`, and proves the exact identity
`Psi(X,y) = exp(smoothSaddlePhase) * smoothSaddleCutoffFactor`, where the
cutoff factor lies in `[0,1]`.

At the exact saddle, division by `smoothSaddleMainTerm` is therefore exactly
the cutoff factor times `smoothSaddleGaussianScale`.
`SmoothNumberSaddleLocalLimit.lean` proves that convergence of this explicit
quantity to one is equivalent to `TaoCriticalSmoothSaddleAsymptoticConclusion`.
The Gaussian local-limit estimate itself remains open, so this delta does not
claim Theorem 1.7 unconditionally. The second open input to Theorem 1.7 is
still analytic Burgess.

## Release delta: prime-equidistribution-3.73

`SmoothNumberSaddleProbability.lean` turns the normalized tilted mass into a
literal probability measure on logarithmic size. Its characteristic function
is exactly the absolutely convergent Fourier series of the tilted masses, is
one at zero, and has norm at most one.

At the exact saddle, audited log-partition derivative identities give center
`log X` and positive variance `phiTwo`. The centered variance-normalized
characteristic function is defined and proved equal to the explicit Fourier
series with atoms `(log n - log X) / sqrt(phiTwo)`. Gaussian convergence and
the local-limit inversion step remain open; no unconditional Theorem 1.7 is
claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10126 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.43

`SmoothNumberSaddleHTSmallBetaEdges.lean` proves the reflected weighted
vertical estimate on `Re z=-eta`, the three-shift VK real-part geometry, the
uniform high/low logarithmic-derivative bound, and the complete analytic
three-edge estimate. `SmoothNumberSaddleHTSmallBetaEdgeAbsorption.lean`
absorbs the horizontal terms into the exponentially decaying error summand
and the negative-left term into the pole-scale summand. It combines those
edges with the release-4.42 origin bound and Perron truncation, then joins the
existing large-beta contour. The result is a single uniform eventual HT
transform estimate for all `0<beta<1`. Finite initial-`y` promotion remains,
so the all-`y` Lemma 6 contract and Theorem 1.7 are not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10201 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.44

`SmoothNumberSaddleHTFinitePrefix.lean` proves the elementary estimates
needed below the eventual contour threshold: the transform norm is at most
`Chebyshev.psi y`, the main-term norm is at most `y/beta`, and the literal HT
error dominates `1/beta`. Hence the transform error is bounded by
`(Chebyshev.psi y + y) * smoothSaddleHTMangoldtError`. Extracting the eventual
threshold and applying monotonicity of `psi` gives one positive coefficient
valid both below and above it. The audited endpoint
`smoothSaddleHTMangoldtTransformEstimate` is therefore the complete all-`y`
equation-(3.10) contract of HT Lemma 6. This delta does not claim Theorem 1.7;
outer-frequency Perron decay and local-limit inversion remain.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10202 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.45

`SmoothNumberSaddleHTMinorArc.lean` isolates and proves the exact algebraic
passage from the all-`y` HT Lemma 6 estimate to the source minor-arc contract.
The sharp saddle main term supplies one half of the rational HT loss; under
the displayed one-quarter scalar error budget, the Euler-product cosine loss
retains the other quarter. The existing global product estimate converts
this to `SmoothSaddleHildebrandTenenbaumMinorArcBoundAt` with the explicit
positive coefficient
`1/(384*smoothSaddleHTSharpComparisonConstant)`. The only remaining premise
in this bridge is the uniform scalar absorption of the now-explicit errors.
This delta does not yet claim the outer Perron limit or Theorem 1.7.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10203 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.46

`SmoothNumberSaddleHTMinorArcScale.lean` removes the final scalar hypothesis
from the release-4.45 bridge. It proves divergence of the rational HT loss at
the first physical outer frequency, absorbs the `y^(1-sigma)` factor using
the critical saddle displacement and stretched-exponential decay, derives
the complementary lower bound for `(1-sigma)*log y` from the saddle equation,
and gives explicit normalized bounds for both the Lemma-6 and higher-prime-
power errors. Radial monotonicity then yields the exact
`SmoothSaddleHildebrandTenenbaumMinorArcBoundAt` contract on
`[1/log y, smoothSaddleHTFrequencyCeiling y (1/2)]` eventually in every
Tao-critical smooth regime. This delta does not claim the local-limit
inversion or Theorem 1.7.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10204 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.47

`SmoothNumberSaddleHTMinorArcIntegral.lean` proves the exact physical
Laplace--Fourier kernel norm and preserves its `1/|t|` decay in the Perron
integrand. A generic interval-integral lemma converts such a pointwise bound
into the logarithmic endpoint cost, and its HT specialization bounds the
complete symmetric shell from `1/log y` to
`smoothSaddleHTFrequencyCeiling y (1/2)`. The explicit normalized envelope
tends to zero: `log y<=u^2` reduces it to a constant multiple of
`u^5*exp(-c*u/(log u)^2)`. Splitting the shell at the already established
wide height `pi/log y` and using the exact adjacent-shell identity then proves
that the finite outer segment through the HT ceiling also vanishes. This
delta does not yet claim the sharp finite-height Perron truncation, the final
local-limit inversion, or Theorem 1.7.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10205 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.48

`SmoothNumberSaddleHTMinorArcQuarter.lean` specializes the unconditional HT
minor-arc argument at `epsilon=1/4`, where the source ceiling is
`exp((log y)^(5/4))`. The weaker equation-(3.10) saving still absorbs the
eighth-power Rankin factor. `SmoothNumberSaddleHTMinorArcIntegralQuarter.lean`
retains the reciprocal physical kernel and proves that the full enlarged
shell, including the exact outer segment from `pi/log y`, has vanishing
normalized mass.

`SmoothNumberSaddleFiniteHeightPerron.lean` proves a coefficient-free
finite-height sharp-Perron estimate. Its summable majorant consists of a
`3/2` endpoint allowance, a harmonic near-diagonal weight, and a smooth
Dirichlet-series far weight. A saddle-exponent lower bound for the main term,
exact cancellation of the far Rankin exponential, and the critical limit
`u*log u/log y -> 1/alpha^2` show that all three normalized pieces vanish at
the quarter-epsilon ceiling. Hence the literal sharp-Perron `tsum` differs
from `psiNat` by `o(smoothSaddleMainTerm)`. This delta does not claim Theorem
1.7; final contour/local-limit assembly remains.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10208 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.49

`SmoothNumberSaddleFiniteHeightAssembly.lean` proves the exact identity
decomposing the normalized Perron line at
`smoothSaddleHTFrequencyCeiling y (1/4)` into the central Gaussian term, the
wide principal-phase annulus, and the enlarged HT outer shell. The three
previously audited limits yield convergence of that finite line to one.
Combining the identity with release 4.48's sharp-Perron cutoff estimate gives
the complex limit `psiNat/smoothSaddleMainTerm -> 1`; taking real parts proves
the proposition-valued contract
`taoCriticalSmoothSaddleAsymptoticConclusion`. No smooth-number local-limit,
infinite-tail, or truncation hypothesis remains. This delta does not claim
unconditional Theorem 1.7: the independent explicit Burgess estimate remains.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10209 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.50

`BurgessWeilPrimeKummerOrthogonality.lean` defines the exact kernel fiber
`{x : χ(P(x))=1}` and proves geometric-series orthogonality for the positive
character powers through `orderOf χ`. The positive indexing makes the
identity valid without an auxiliary nonzero hypothesis: a zero polynomial
value contributes zero to every character power in the family.

Finite-sum interchange yields the exact powered-trace formula
`sum_k S(χ^(k+1),P) = orderOf(χ) * #kernelFiber`. For split polynomials this
is transported to `primeKummerRootCorrelation`, the distinct-root normal
form used by the sharp complete-Weil boundary. The result adds no analytic
assumption and introduces no axiom. The remaining source theorem is the
projective Kummer-cover point-count/Weil estimate needed to bound an
individual trace.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10210 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.51

`BurgessWeilPrimeKummerPowerFiber.lean` proves that character evaluation at a
generator of the cyclic finite-field unit group preserves order. It computes
the image of `χ.toUnitHom` to have cardinality `orderOf χ` and its kernel to
have cardinality `#Fˣ / orderOf χ`. The cyclic-group power-map theorem gives
the same cardinality for the `orderOf χ`-power image; direct evaluation of
`χ ^ orderOf χ = 1` supplies subgroup inclusion, hence exact equality.

The field-element corollary is
`χ(a)=1 ↔ ∃ y, y≠0 ∧ y^(orderOf χ)=a`. This is an unconditional algebraic
identification and introduces no new proposition-valued analytic input. The
next bridge is the affine power-fiber cardinality (with the exceptional zero
fiber), followed by the projective Kummer-curve Weil estimate.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10211 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.52

`BurgessWeilPrimeKummerAffineFiber.lean` computes the kernel cardinality of
the `orderOf χ` power map on finite-field units. Translation identifies every
nonempty unit fiber with the kernel. Combined with release 4.51, this proves
that a nonzero field value has `orderOf χ` roots precisely when its character
value is one, and no roots otherwise; the zero field value has the unique
root zero.

Summing over polynomial values proves
`#affinePoints = #zeroFiber + orderOf(χ) * #kernelFiber`. For a nonzero
polynomial, the zero fiber is identified with `P.roots.toFinset`, giving the
exact distinct-root form needed for projective completion. All declarations
are imported by the production root and covered by the axiom audit. The
remaining boundary is the projective Kummer curve, its points at infinity,
and the projective Weil estimate.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10212 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.53

`BurgessWeilPrimeKummerAffineTrace.lean` proves that the affine Kummer point
count is `p` plus the sum of the proper positive character-power traces. It
then proves this formula for every scalar twist `cP` and defines the resulting
affine trace defect.

Exact multiplicative Fourier orthogonality gives
`sum_c χ⁻¹(c) defect(c) = (p-1) S(χ,P)`. Triangle inequality and the unit norm
of nonzero character values therefore transfer a uniform sharp bound for all
nonzero twisted defects to `TaoPrimeKummerPolynomialWeilBound` with no loss.
This is an exact strong Fourier criterion. It is not identified with the
ordinary total-curve Hasse--Weil estimate, because the latter combines all
proper character-power eigentraces.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10213 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.54

`BurgessWeilPrimeKummerIsotypicSpectrum.lean` isolates the actual geometric
input required for the sharp individual trace. The structure
`PrimeKummerIsotypicFrobeniusSpectrum` contains a finite chosen-character
algebraic-integer eigenvalue family, the conductor bound `rank <= #roots-1`,
the mixed-weight bound `‖α_i‖ <= sqrt p`, and the exact trace identity
`S(χ,P) = -sum_i α_i`.

The triangle inequality derives `TaoPrimeKummerPolynomialWeilBound` with the
literal sharp constant. Further checked bridges reach
`TaoPrimeLinearQuotientWeilBound`,
`TaoPrimitiveCubefreeBurgessCompleteWeilBound`, and the fixed
`TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven` used by the downstream
argument. The unresolved source leaf is therefore the construction and
weight/rank proof for this isotypic Frobenius spectrum, rather than a bound
for the undifferentiated total Kummer point count.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10214 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.55

The isotypic spectrum is corrected to require `‖α_i‖ <= sqrt p`, not equality.
This is essential for the weight-zero Jacobi degeneracies that occur already
with two roots. The triangle-inequality transfer retains the identical sharp
Kummer constant.

The existing one-root zero trace and two-root Jacobi estimate now construct
the corresponding rank-zero and rank-one spectral data. The spectral trace
is also tied exactly to the affine geometry by proving that its scaled
negative trace is the `χ⁻¹` Fourier coefficient of all scalar-twisted affine
defects. Finally, the global isotypic-spectrum proposition is proved
equivalent to its restriction to polynomials with at least three distinct
roots, and that residual has a direct checked bridge to the fixed `r=7`
composite Burgess endpoint.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10214 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.56

`PrimeKummerIsotypicFrobeniusSpectrum` now requires each eigenvalue to be an
algebraic integer over `ℤ`. This rules out arbitrary fractional subdivisions
of the target trace and preserves an arithmetic feature of Frobenius spectra.
Because the complete correlation itself is integral, however, it can still
be placed in one eigenvalue; integrality alone is not a full Frobenius
compatibility condition.

`isIntegral_mulChar_apply` proves the zero/root-of-unity dichotomy for every
complex value of a finite-field multiplicative character.
`isIntegral_primePolynomialCharacterCorrelation` then closes integrality
under the finite complete sum. The elementary rank-zero and rank-one spectra
continue to construct under the strengthened definition, and all sharp
polynomial, composite, and fixed-`r=7` transfers remain unchanged.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10214 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.57

`primeKummerExtensionCorrelation` now defines the complete Kummer trace over
every positive-degree canonical finite extension of `ZMod p`. The polynomial
is base-changed and the original character is lifted by the finite-field norm.
Degree one is exactly `primePolynomialCharacterCorrelation`.

`PrimeKummerIsotypicFrobeniusSystem` extends the integral, weight-bounded
spectrum with the simultaneous identities
`S_n = -sum_i alpha_i^n` over all positive extension degrees. These equations
prevent a base-field norm estimate from manufacturing the source object:
rank zero forces every extension trace to vanish, and rank one forces a
kernel-checked geometric recurrence between consecutive traces.

The three-or-more-root system theorem forgets to the existing spectral
residual and hence supplies
`TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven`. The remaining source
leaf is now the construction of this single extension-compatible Kummer
Frobenius system, rather than a base-field spectral repackaging.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10215 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.58

`finiteFieldNormLiftMulChar` packages pullback along the extension norm as a
monoid homomorphism on complex multiplicative characters. Finite-field norm
surjectivity proves this homomorphism injective; consequently it preserves
nontriviality and exact `orderOf`. The higher extension correlations from
release 4.57 are now literal correlations for this lifted character, and all
extension correlations are algebraic integers.

`eval_map_eq_leadingCoeff_mul_pow_of_single_root` gives the exact base-change
factorization for a split polynomial with one distinct root. Exact order
preservation keeps its active character power nontrivial. Translation and
complete-character orthogonality then prove every extension correlation
zero, constructing `PrimeKummerIsotypicFrobeniusSystem` with rank zero.

The newly stated full all-extension source theorem is equivalent to the
conjunction of `TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots` and the existing
three-or-more-root system residual. Thus the Kummer leaf has separated into
the exact two-root Hasse--Davenport compatibility and the genuinely geometric
three-or-more-root cohomology theorem. The full system still forgets to the
sharp spectrum and supplies the fixed-`r=7` Burgess endpoint.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10216 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.59

`BurgessWeilPrimeKummerTwoRootTrace.lean` proves the exact affine two-root
character-sum/Jacobi-sum identity over an arbitrary finite field. It also
proves the exact split-polynomial two-root factorization after base change and
uses both results to express every higher Kummer extension correlation as a
norm-lifted Jacobi sum. The scalar norm calculation
`finiteFieldNormLiftMulChar_algebraMap_extension` shows that each base-field
character factor is raised to the extension degree.

`TaoPrimeFieldJacobiHasseDavenport` is the literal remaining two-root source
statement, including the factor `(-1)^(d-1)`. From exactly this hypothesis,
`primeKummerExtensionCorrelation_eq_neg_neg_base_pow_of_twoRoots` proves the
required power-trace identity, and
`TaoPrimeFieldJacobiHasseDavenport.toTwoRoots` constructs the rank-one
two-root Frobenius system. Hasse--Davenport itself is not claimed: the two
remaining leaves are this classical Jacobi identity and the three-or-more-root
Kummer cohomology theorem.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10217 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.60

`BurgessWeilPrimeKummerHasseDavenport.lean` defines
`finiteFieldTraceLiftAddChar` by composing an additive character with the
field trace. The theorem `finiteFieldTraceLiftAddChar_isPrimitive` uses
separable trace surjectivity to preserve primitivity. The remaining
`TaoPrimeFieldGaussHasseDavenport` proposition is the literal norm/trace
Gauss-sum lifting formula with factor `(-1)^(d-1)`.

`TaoPrimeFieldGaussHasseDavenport.toJacobi` proves the complete Jacobi theorem.
It handles a trivial second character and an inverse product character
directly, then uses `jacobiSum_mul_nontrivial` and nonvanishing of primitive
Gauss sums in the genuinely nondegenerate branch. Its `toTwoRoots` and
`toFull` corollaries construct the two-root Frobenius system and reduce the
full Kummer source to Gauss Hasse--Davenport plus the three-or-more-root
cohomological system. Neither remaining source theorem is claimed here.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10218 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.61

`finiteFieldNormLiftMulChar_tower` and
`finiteFieldTraceLiftAddChar_tower` prove that the two character lifts are
transitive through arbitrary finite-field towers. The local proposition
`FiniteFieldGaussLiftRelation` records the exact signed Gauss identity for one
extension, and `FiniteFieldGaussLiftRelation.tower` proves that two such
relations compose. Its proof includes the exact degree multiplication and
`(-1)^(d-1)` sign arithmetic.

`gaussSum_normTraceLift_extension_one` proves the degree-one relation by
transporting the finite sum through `FiniteField.algEquivOfCardEq`, together
with norm and trace invariance under algebra equivalence. Hence
`taoPrimeFieldGaussHasseDavenport_iff_degreeAtLeastTwo` identifies the full
prime-field residual exactly with degrees at least two. This release does not
claim a prime-degree reduction: that still needs suitable intermediate fields
and a general-base lifting statement. The remaining source leaves are the
positive-degree Gauss lifting theorem and the three-or-more-root Kummer
cohomological system.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10218 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.62

`gaussSum_normTraceLift_eq_of_algEquiv` proves that the lifted Gauss sum is
invariant under an algebra equivalence of extension fields, using invariance
of norm and trace and transport of the finite sum. The corresponding local
relation is invariant as well, and
`finiteFieldGaussLiftRelation_iff_extension` replaces any finite extension by
Mathlib's canonical extension of equal degree.

`TaoFiniteFieldGaussHasseDavenportPrimeDegree` states the remaining theorem
over arbitrary finite base fields, prime-degree extensions, and arbitrary
primitive additive characters. Its `canonical` induction realizes a
composite degree `a*b` as a canonical degree-`a` extension followed by a
canonical degree-`b` extension. Nontriviality and primitivity survive the
first lift, the two relations compose, and algebra-equivalence invariance
returns to the canonical degree-`a*b` field. Therefore
`taoFiniteFieldGaussHasseDavenport_iff_primeDegree` proves that universal
finite-field Hasse--Davenport is exactly its prime-degree fragment.
`TaoFiniteFieldGaussHasseDavenport.toPrimeField` specializes it to the
original two-root source proposition. The universal prime-degree formula and
the three-or-more-root Kummer cohomological system remain unproved.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10218 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.63

`finiteFieldTraceLiftAddChar_mulShift` proves trace lifting commutes with
scalar shifts, while `finiteFieldNormLiftMulChar_algebraMap` computes the norm
factor as the extension-degree power. Together with `gaussSum_mulShift_eq`,
`gaussSum_normTraceLift_mulShift` gives the exact scaling upstairs and
`FiniteFieldGaussLiftRelation.mulShift` transfers any local lifting relation
to a nonzero scalar shift.

The imported finite Pontryagin-duality cardinality theorem combines with
`AddChar.to_mulShift_inj_of_isPrimitive` to prove
`exists_eq_mulShift_of_isPrimitive`. Its primitive-target refinement forces
the scalar to be nonzero. Therefore
`taoFiniteFieldGaussHasseDavenportPrimeDegree_iff_canonicalAddChar` reduces
the universal prime-degree theorem to Mathlib's canonical primitive complex
additive character on each finite base field. The reduced residual has direct
constructors for the original prime-field theorem, Jacobi
Hasse--Davenport, the two-root Frobenius system, and—given the independent
three-root residual—the full Kummer system. The canonical-character
prime-degree formula and the three-or-more-root Kummer cohomological system
remain unproved.

On 2026-09-18, `lake build Tao2026 Tao2026.Audit` completed successfully with
10218 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.64

`BurgessWeilPrimeKummerHasseDavenportMonic.lean` formalizes the first
generating-function layer of the classical Hasse--Davenport proof.
`monicPolynomialEquivCoefficients` identifies fixed-degree monic polynomials
with the vectors of their lower coefficients, and
`hasseDavenportMonicCoefficientWeight_equiv` transports the constant and
subleading coefficient weight across this equivalence.

`sum_hasseDavenportMonicCoefficientWeight_one` and its polynomial form prove
that the degree-one coefficient is exactly `gaussSum chi psi`. For every
degree at least two,
`sum_hasseDavenportMonicCoefficientWeight_eq_zero` isolates the constant
coefficient and applies multiplicative-character orthogonality; its
polynomial counterpart transports the result back to monic polynomials.
The remaining step on this route is the closed-point Euler-product comparison
that relates this monic generating series to the norm/trace Gauss sums over
finite extensions. The canonical-character prime-degree formula and the
independent three-or-more-root Kummer cohomological system remain unproved.

On 2026-09-18, `lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportMonic Tao2026`
completed successfully with 10219 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.65

`BurgessWeilPrimeKummerHasseDavenportEuler.lean` defines the global
constant/subleading coefficient weight and proves its multiplicativity on
monic products, powers, and arbitrary multiset products. The linear-factor
formula identifies each factor weight with the multiplicative/additive
character weight of its root.

Normalized unique factorization now decomposes every monic weight into the
product of its monic irreducible factor weights, counted with multiplicity.
Every such factor is proved irreducible, monic, and positive-degree, and the
factor degrees sum exactly to the degree of the original polynomial.

`normTraceCharacterWeight_eq_minpolyWeight_pow` proves the pointwise
closed-point identity
`chi (norm K x) * psi (trace K L x) = weight (minpoly K x)^[L:K(x)]`.
Summing it gives `gaussSum_normTraceLift_eq_sum_minpolyWeight_pow`, an exact
minimal-polynomial expression for the lifted Gauss sum. The remaining step
on this route is the finite logarithmic-derivative recurrence connecting
this closed-point sum to the already-computed monic coefficients. The
independent three-or-more-root Kummer cohomological system remains unproved.

On 2026-09-18, `lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportEuler Tao2026`
completed successfully with 10220 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.66

`BurgessWeilPrimeKummerHasseDavenportRecurrence.lean` defines the finite
coefficient recurrence corresponding to `X A'(X) = B(X) A(X)`. A direct
induction solves it when `A_0=1`, `A_1=G`, and all higher coefficients
vanish, proving `B_(n+1)=(-1)^n G^(n+1)` without any division or formal-power-
series infrastructure.

The same module packages the genuine fixed-degree sums of the global
Hasse--Davenport monic weight. Releases 4.64 and 4.65 give its complete
coefficient profile: degree zero is one, degree one is the base Gauss sum,
and every degree at least two vanishes for a nontrivial multiplicative
character. Therefore a closed-point sequence satisfying the Euler recurrence
is proved to equal the required signed Gauss-power sequence. What remains is
the finite combinatorial construction of that recurrence from normalized
irreducible factors and the minimal-polynomial extension sum. The independent
three-or-more-root Kummer cohomological system remains unproved.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportRecurrence Tao2026`
completed successfully with 10221 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.67

`BurgessWeilPrimeKummerHasseDavenportEulerProduct.lean` builds the formal
local factor `(1-wX^d)⁻¹` by substituting `X^d` into the weighted geometric
series. Its coefficient is proved exactly equal to `w^(n/d)` when `d ∣ n`
and zero otherwise. Ordinary and shifted logarithmic derivatives are computed
algebraically, giving the local closed-point coefficient
`d*w^(m/d)` precisely on positive multiples of `d`.

The product and sum of these local factors are then formed over an arbitrary
finite alphabet. Induction with the derivation Leibniz rule proves the exact
finite Euler-product logarithmic-derivative identity. Coefficient extraction
proves `weightedEulerProduct_logDerivativeRecurrence`, an immediate instance
of the recurrence solved in release 4.66. No convergence, infinite products,
or analytic logarithms enter this argument. The remaining Hasse--Davenport
work is the finite specialization to bounded-degree monic irreducibles and the
identification of its divisor sum with extension-field minimal-polynomial
fibers. The independent three-or-more-root Kummer cohomological system remains
unproved.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportEulerProduct Tao2026`
completed successfully with 10222 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.68

`BurgessWeilPrimeKummerHasseDavenportIrreducibleEuler.lean` packages monic
irreducible polynomials of every fixed degree as finite types and forms their
dependent finite union through an arbitrary cutoff. The finite weighted
Euler-product engine of release 4.67 then supplies an exact recurrence for the
bounded irreducible Euler coefficients and closed-point coefficients. The
latter are rewritten first as a sum over irreducibles and then as the literal
degree-stratified divisor sum.

The ordinary Euler coefficient is expanded over `finsuppAntidiag` degree
allocations. For any allocation on which every irreducible degree divides its
assigned total degree, `hasseDavenportIrreducibleAllocationPolynomial`
constructs the product of the corresponding irreducible powers. It is proved
monic, its natural degree is exactly the antidiagonal total, and its global
Hasse--Davenport weight is exactly the product weight from the Euler
coefficient. The remaining coefficient-side step is the inverse allocation
from normalized factors and the induced equivalence with fixed-degree monic
polynomials. Minimal-polynomial fiber counting and the independent three-or-
more-root Kummer cohomological system remain unproved.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportIrreducibleEuler Tao2026`
completed successfully with 10223 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.69

`BurgessWeilPrimeKummerHasseDavenportIrreducibleFactorization.lean` constructs
the normalized-factorization inverse omitted by release 4.68. Fixed-degree
monic polynomials are equivalent to multisets of monic irreducibles whose
degrees sum to the target. At every cutoff `N ≥ n`, a second equivalence sends
such multisets to the valid divisible `finsuppAntidiag` allocations and back.
The two inverse laws follow from exact multiset-count formulas, and the
Hasse--Davenport product weight is transported exactly across the maps.

Finite-sum transport now proves
`hasseDavenportIrreducibleEulerCoefficient_eq_monicSum`. A truncated form of
the logarithmic-derivative induction needs the recurrence only through its
target index, so the cutoff product suffices to prove
`hasseDavenportIrreducibleClosedPointCoefficient_eq_signedGaussPower` and the
literal degree-stratified divisor-sum identity. The coefficient and recurrence
sides of the classical Euler-product proof are therefore complete. The
remaining Gauss-lifting step is the minimal-polynomial fiber comparison with
the extension Gauss sum; the independent three-or-more-root Kummer
cohomological system remains unproved.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportIrreducibleFactorization Tao2026`
completed successfully with 10224 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.70

`BurgessWeilPrimeKummerHasseDavenportMinimalPolynomialFibers.lean` closes the
last comparison in the internal Gauss-lifting proof. Each extension element's
minimal polynomial is packaged in the irreducible alphabet at the total
extension degree. The intermediate-field tower formula proves that its
relative multiplicity is the total degree divided by its polynomial degree.

For a fixed monic irreducible `q`, the fiber `minpoly K x = q` is equivalent
to the roots of `q` in the extension. Passing through `AdjoinRoot q` and the
exact finite-field algebra-hom count proves that the fiber cardinality is
`deg q` when `deg q` divides the extension degree and zero otherwise.
`Finset.sum_fiberwise` then regroups the full minimal-polynomial weight sum
into the literal degree-stratified divisor sum from release 4.69.

The resulting theorem
`gaussSum_normTraceLift_eq_signedGaussPower` proves universal finite-field
Hasse--Davenport without an external hypothesis. Its prime-field and Jacobi
specializations and the complete zero-, one-, and two-active-root Kummer
Frobenius system are discharged as corollaries. The only remaining Kummer
source leaf is the three-or-more-active-root cohomological system.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerHasseDavenportMinimalPolynomialFibers Tao2026`
completed successfully with 10225 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.71

`BurgessWeilPrimeKummerExtensionAffineTrace.lean` generalizes the elementary
affine Kummer geometry to an arbitrary finite field. It proves the exact
vertical-fiber point count, the decomposition into proper positive character
powers, scalar-twist compatibility, and multiplicative Fourier inversion.
For nontrivial `χ`, the inverse-character Fourier coefficient of the twisted
affine trace defects is exactly `(#F-1)` times the selected polynomial
character correlation.

Specialization to `FiniteField.Extension (ZMod p) p (n+2)`, the norm-lifted
character, and the base-changed polynomial identifies this correlation with
`primeKummerExtensionCorrelation p χ P (n+1)`. The cardinality-explicit form
has normalization `p^(n+2)-1`. Hence every positive extension trace in the
remaining three-or-more-root Frobenius contract is now connected to literal
scalar-twisted affine Kummer point counts. The still-unproved geometric
content is the bounded-rank integral weight-bounded isotypic decomposition of
those all-degree traces.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerExtensionAffineTrace Tao2026 Tao2026.Audit`
completed successfully with 10226 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.72

`BurgessWeilPrimeKummerAffineFourierSystem.lean` defines
`PrimeKummerAffineFourierFrobeniusSystem`: the base chosen-character spectrum
is unchanged, while each higher trace equation is expressed as the literal
inverse-character Fourier coefficient of scalar-twisted affine Kummer
point-count defects from release 4.71.

Every genuine `PrimeKummerIsotypicFrobeniusSystem` constructs this geometric
system. Conversely, primality proves `p^(n+2)-1 ≠ 0`; cancelling this exact
Fourier normalization reconstructs every original extension power-trace
identity. The two fixed-data existence statements are equivalent, as are the
universal three-or-more-root source propositions. The affine-Fourier source
also transfers directly to the fixed-`r=7` Burgess endpoint. Thus the final
unproved leaf is precisely construction of the pure bounded-rank integral
isotypic decomposition of these affine point-count Fourier coefficients.

On 2026-09-18,
`lake build Tao2026.BurgessWeilPrimeKummerAffineFourierSystem Tao2026 Tao2026.Audit`
completed successfully with 10227 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.74

`SmoothNumberSaddleEulerCharacteristic.lean` proves absolute summability and
the exact finite-prime Euler product for the complex smooth Fourier Dirichlet
series. Dividing by the untwisted Euler product gives the literal normalized
factor `(1-p^(-sigma))/(1-p^(-sigma) exp(i t log p))` for every source prime
`p ≤ y`.

Each local factor is one at zero and has norm at most one. Its squared norm is
identified exactly with
`(1-a)^2 / ((1-a)^2 + 2a(1-cos(t log p)))`, `a=p^(-sigma)`. The complete
centered variance-normalized saddle characteristic function therefore has an
exact finite contraction product. Uniform frequency bounds and local-limit
inversion remain open, so this delta does not claim Theorem 1.7.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10127 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.75

`SmoothNumberSaddleFrequency.lean` converts the exact contraction product into
a quantitative central Gaussian envelope. On the principal period,
`1-cos(theta) ≥ 2theta^2/pi^2`; on the central local window the resulting
reciprocal contraction is bounded by an exponential. Its coefficient is
proved exactly equal to `smoothSaddleSecondPrimeTerm`, so the full exponent is
the literal finite sum `phiTwo`.

After centering and normalization by `sqrt(phiTwo)`, one explicit source-scale
range condition yields
`|characteristic(t)|^2 ≤ exp(-2t^2/pi^2)` and
`|characteristic(t)| ≤ exp(-t^2/pi^2)`. Proving that an expanding normalized
window satisfies this condition, controlling complementary frequencies, and
performing local-limit inversion remain open; Theorem 1.7 is not yet claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10128 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.76

`SmoothNumberSaddleCentralWindow.lean` defines the exact positive central
radius
`pi/2 * (1-2^(-sigma)) * sqrt(phiTwo) / log y`. It proves that membership in
the associated symmetric interval is equivalent to the source-scale condition
used by the central Gaussian estimate, and transfers both the squared and
unsquared universal envelopes to that whole interval.

In a Tao critical smooth regime, the module further proves that the hypothesis
`log y / sqrt(phiTwo) → 0` makes the radius tend to infinity. Consequently
every fixed normalized frequency eventually lies in the central interval and
satisfies the Gaussian envelope. The curvature-scale hypothesis itself,
complementary-frequency estimates, and local-limit inversion remain open;
Theorem 1.7 is not yet claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10129 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.77

`SmoothNumberSaddleCurvatureLower.lean` proves the quantitative curvature
estimate needed to expand the central frequency window. The explicit point
`1-8 log(u)/log(y)` is eventually positive and lies below the exact saddle.
Antitonicity of every second-prime summand and the exact `phiOne` secant
identity then yield
`phiTwo/log(y)^2 ≥ u/(16 log u)` eventually.

Since `u/log u → ∞`, normalized curvature tends to infinity and
`log(y)/sqrt(phiTwo) → 0`. Therefore the exact release-3.76 radius tends to
infinity unconditionally in every critical smooth regime, and each fixed
normalized frequency eventually satisfies the universal Gaussian envelope.
Complementary-frequency decay and local-limit inversion remain open;
Theorem 1.7 is not yet claimed.

On 2026-09-16, `lake build Tao2026 Tao2026.Audit` completed successfully with
10130 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.78

`SmoothNumberSaddleGaussianProduct.lean` proves the deterministic
triangular-array transfer for the exact saddle Euler product. The normalized
characteristic factors into centered prime-local contractions. Their variance
shares are nonnegative and sum exactly to one, and a telescoping product bound
compares the product with `exp(-t^2/2)` through the summed local quadratic
Taylor error and the largest variance share.

On the eventual half-plane `sigma >= 1/2`, every prime curvature contribution
is at most `20 log(y)^2`. Release 3.77 therefore implies that the largest
normalized share tends to zero. Fixed-frequency Gaussian convergence is now
reduced solely to the explicit summed prime-local Taylor remainder. That
estimate, complementary-frequency decay, and Fourier inversion remain open;
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10131 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.79

`SmoothNumberSaddlePrimeTaylor.lean` proves exact first, second, and third
geometric prime-power moments, a summable third absolute centered moment, and
the uniform bound `E|N-EN|^3 <= 4000a` for `a <= 4/5`. A global cubic
remainder for `exp(ix)` then gives the centered local factor estimate with
error at most `16000 |u|^3 a`.

The centered geometric characteristic is identified exactly with the existing
prime-local saddle factor. Summation over `p <= y` bounds the total quadratic
Taylor error by
`16000 |t|^3 log(y)/smoothSaddleStandardDeviation`; release 3.77 makes this
tend to zero. Combined with release 3.78, the exact normalized saddle
characteristic now converges to `exp(-t^2/2)` at every fixed frequency in the
critical regime. Complementary-frequency decay and Fourier inversion remain;
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10132 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.80

`SmoothNumberSaddleLaplaceCutoff.lean` identifies the exact remaining
shrinking-scale quantity. The cutoff factor is a one-sided Laplace moment of
the centered normalized logarithmic law, with rate
`smoothSaddlePoint*sqrt(phiTwo)`. The Gaussian prefactor is exactly
`sqrt(2*pi)` times this rate, and the rate tends to infinity in every critical
regime. Thus the critical saddle asymptotic is equivalent to convergence of
the explicit normalized Laplace target to one. Fixed-frequency convergence
alone does not discharge this shrinking-scale statement; complementary
frequency control and inversion remain.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10133 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.81

`SmoothNumberSaddleCentralIntegral.lean` proves the complete central segment
of the normalized Laplace/Perron calculation. The exact kernel
`lambda/(lambda-i*t)` has norm at most one and tends to one at every fixed
normalized frequency. On the explicit expanding central interval, the
kernel-weighted characteristic function is dominated by the integrable
Gaussian `exp(-t^2/pi^2)` and converges pointwise to `exp(-t^2/2)`.

Dominated convergence and the checked complex Gaussian integral show that
the central integral tends to `sqrt(2*pi)`; its Gaussian-normalized
contribution therefore tends to one. This does not yet identify the literal
cutoff moment with a truncated contour integral or bound the complementary
Perron error, so the critical saddle asymptotic and Theorem 1.7 remain open.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10134 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.82

`SmoothNumberSaddlePerronLine.lean` closes the exact normalization gap between
the source vertical line and the probability-side central integral. The
twisted smooth Dirichlet series at `-t`, its phase `exp(i*t*log X)`, and the
kernel `sigma/(sigma+i*t)` are proved pointwise equal to the centered
characteristic and corrected Laplace kernel at
`-t*sqrt(phiTwo)`. The central Perron height rescales exactly to the explicit
central radius, and the symmetric interval substitution is checked in Lean.

Consequently the release-3.81 normalized central contribution is literally
the normalized central vertical-line Perron integral. The complete
finite-height cutoff comparison and complementary-line bound remain open, so
the critical saddle asymptotic and Theorem 1.7 are not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10135 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.83

`SmoothNumberSaddlePerronCutoff.lean` passes the absolutely convergent smooth
Dirichlet series through every finite vertical segment and identifies the
normalized integral with the sum of the frozen coefficient-free sharp-Perron
kernels. After restoring the saddle factors, this is the literal release-3.82
Perron line.

The inclusive subtype cutoff series is exactly `psiNat X y`. The
kernel-minus-cutoff error is an absolutely convergent termwise sum; below and
above `X` it inherits the frozen logarithmic bounds, and at `n=X` it has the
height-uniform bound `3/2`. Quantitative aggregation at the saddle height and
the complementary-line estimate remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10136 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.84

`SmoothNumberSaddlePerronLimit.lean` proves that the symmetric sharp-Perron
kernel converges to one below the cutoff, one half at the cutoff, and zero
above it. It defines the corresponding smooth half-cutoff and proves that its
complete sum is exactly `psiNat X y` minus the possible source-smooth endpoint
half-mass, whose norm is at most `1/2`.

A height-independent piecewise kernel envelope is proved summable over the
smooth-number subtype. Tannery's theorem therefore upgrades pointwise kernel
inversion to the complete smooth sharp-Perron series. The remaining saddle
input is the quantitative finite-height noncentral-line estimate; Theorem 1.7
is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10137 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.85

`SmoothNumberSaddlePerronComplement.lean` proves the exact saddle
normalization of the complete finite Perron line and identifies it with the
full sharp-kernel sum divided by `smoothSaddleMainTerm`. Subtracting the
already evaluated central Gaussian contribution gives exactly the two literal
tail integrals outside `smoothSaddleCentralPerronHeight`.

The complementary line tends, with height, to the endpoint-corrected saddle
ratio minus the central term. In every critical regime its vanishing is
equivalent to convergence of that corrected ratio to one. The normalized
endpoint correction is bounded by `1/(2*mainTerm)`. Main-term divergence and
the analytic tail-decay estimate remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10138 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.86

`SmoothNumberSaddleMainTermGrowth.lean` proves the uniform curvature estimate
`phiTwo <= 7*log(y)*phiOne` for `sigma >= 1/2`, its exact-saddle specialization
`phiTwo <= 7*log(y)*log(X)`, and the explicit lower bound
`sqrt(X)/(sqrt(14*pi)*log(X)) <= smoothSaddleMainTerm` under the eventual
critical-range hypotheses.

The saddle main term consequently tends to infinity in every critical regime,
so the normalized half-endpoint correction tends to zero. The original
critical smooth saddle asymptotic is now equivalent to vanishing of
`smoothSaddleInfiniteComplementaryPerronLine`; that complementary-frequency
decay is the sole remaining smooth-saddle input, and Theorem 1.7 is not yet
claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10139 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.87

`SmoothNumberSaddleWideFrequency.lean` proves prime-local contraction on the
full range `|t log p| <= pi`, the resulting normalized Gaussian envelope up
to radius `pi*standardDeviation/log(y)`, and dominated-convergence decay of
the annulus outside the central saddle window. The remaining smooth-saddle
input is the outer-frequency Perron estimate beyond physical height
`pi/log(y)`; Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10140 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.88

`SmoothNumberSaddleWidePerron.lean` proves that the wide normalized radius
corresponds exactly to physical Perron height `pi/log(y)`. It carries out the
standard-deviation substitution on both signed annular segments and
identifies their normalized physical contribution with the release-3.87
Fourier integral. This literal Perron contribution tends to zero in every
critical regime. Only the outer tails beyond that height remain, and Theorem
1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10141 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.89

`SmoothNumberSaddleOuterPerron.lean` defines the normalized pair of physical
Perron tails beyond `pi/log(y)` at finite height and proves that the complete
complementary line is exactly the release-3.88 annular contribution plus this
outer line. Its height limit is the named
`smoothSaddleInfiniteOuterPerronLine`. Since the annulus tends to zero, the
critical saddle asymptotic is equivalent to decay of this outer object alone;
that analytic decay and Theorem 1.7 are not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10142 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.90

`SmoothNumberSaddleOuterDecay.lean` defines exact prime-local and aggregate
phase losses and proves a frequency-unrestricted Euler-product contraction.
The tilted characteristic and the literal saddle Perron integrand are bounded
by `exp(-smoothSaddleCosineLoss/96)`, where the exponent is the explicit
nonnegative weighted sum of `1-cos(t log p)` over source primes. Proving a
uniform lower bound for this loss on the outer tails remains; Theorem 1.7 is
not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10143 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.91

`SmoothNumberSaddleOuterShell.lean` proves the first quantitative lower bound
for the global cosine loss. On
`pi/log(y) <= t <= 4*pi/(3*log(y))`, all primes in the top dyadic block have
nonpositive cosine. The compiled Chebyshev–PNT block estimate consequently
gives loss at least `y^(-sigma)*y/(16*log(y))`. Later frequency shells and the
complete outer-tail integral remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10144 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.92

`SmoothNumberSaddleMovingShell.lean` defines the adaptive scale
`N(t)=ceil(exp(pi/t))` and proves exact ceiling, logarithmic, and frequency
bounds. The outer boundary implies `N(t)<=y`; a direct finite estimate gives
the required dyadic half-block width once `N(t)>=81`; and an enlarged
Chebyshev–PNT threshold supplies both block endpoints. The resulting theorem
gives
`N(t)^(-sigma)*N(t)/(16*log(N(t))) <= smoothSaddleCosineLoss y sigma t`
through an explicit small-frequency range. Larger outer frequencies and the
integrated infinite tail remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10145 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.93

`SmoothNumberSaddleMultiShell.lean` replaces the single top block on the
first outer shell by the full retained CEP dyadic alphabet. Its primes all
remain in the negative-cosine phase window and have reciprocal mass
`≫1/log(u)`. Explicit finite estimates from the exact saddle equation and
the CEP cutoff yield a named cosine-loss scale bounded below by a positive
constant times `u/log(u)`. The scale tends to infinity in every critical
regime, giving a uniform vanishing bound for the physical Perron integrand on
the shell. The normalized shell integral and later frequencies remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10146 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.94

`SmoothNumberSaddleFirstShellIntegral.lean` defines the exact symmetric
normalized contribution on the first physical outer shell. The release-3.93
envelope applies at both signs by cosine-loss symmetry; the literal interval
width and the curvature estimate
`standardDeviation/log(y) <= sqrt(7*u)` reduce the contribution to a constant
multiple of `sqrt(u)*exp(-c*u/log(u))`. That expression tends to zero, so the
complete first-shell contribution vanishes in every critical regime. Later
outer-frequency shells and the infinite outer line remain, so Theorem 1.7 is
not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10147 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.95

`SmoothNumberSaddleExtendedShell.lean` strengthens the accumulated CEP phase
window to `3*pi/(2*log(y))`, defines a reusable exact symmetric Perron-shell
contribution and norm estimate, and applies them to the adjacent band beyond
the release-3.94 endpoint. The same divergent `u/log(u)` cosine loss absorbs
the saddle normalization, so this additional normalized contribution tends
to zero in every critical regime. Frequencies beyond the new endpoint and the
infinite outer line remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10148 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.96

`SmoothNumberSaddleSecondShell.lean` moves the accumulated CEP alphabet to
the natural scale `floor(sqrt(y))`. Exact rounding and logarithmic estimates
put all retained primes between one third and one half of `log(y)`, so their
phases have nonpositive cosine throughout
`3*pi/(2*log(y)) <= t <= 3*pi/log(y)`. The critical regime satisfies the
cofactor and PNT hypotheses, yielding an explicit accumulated loss on the
whole second shell. Converting this scale to a divergent normalized envelope
and integrating it remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10149 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.97

`SmoothNumberSaddleSecondShellIntegral.lean` compares the release-3.96
square-root cofactor power with `(u/(15*log(4)))^(2/5)` and defines the
resulting loss scale, comparable to `u^(2/5)/log(u)`. That scale diverges in
every critical regime, and its exponential envelope absorbs the `sqrt(u)`
saddle normalization. Cosine-loss symmetry and the reusable symmetric-shell
bound then prove that the exact normalized Perron contribution on
`3*pi/(2*log(y)) <= |t| <= 3*pi/log(y)` tends to zero. Later frequency
shells and the infinite outer line remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10150 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.98

`SmoothNumberSaddleThirdShell.lean` moves the accumulated CEP alphabet to
the twice-iterated natural square root of `y`. Exact floor-root inequalities
put its logarithm between `1/5*log(y)` and `1/4*log(y)` and every retained
prime above `1/6*log(y)`. Consequently the complete alphabet has
nonpositive cosine throughout
`3*pi/log(y) <= t <= 6*pi/log(y)`. Critical-regime growth verifies the PNT
and cofactor-range hypotheses and yields a uniform explicit third-shell
loss. Its divergent-scale conversion and normalized integral remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10151 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-3.99

`SmoothNumberSaddleThirdShellIntegral.lean` compares the fourth-root
cofactor power with `(u/(15*log(4)))^(1/5)` and defines the corresponding
loss scale of order `u^(1/5)/log(u)`. This scale diverges in every critical
regime, while its exponential absorbs the `sqrt(u)` saddle normalization.
The signed envelope and generic symmetric-shell estimate then prove that the
exact normalized Perron contribution on
`3*pi/log(y) <= |t| <= 6*pi/log(y)` tends to zero. Later frequency shells and
the infinite outer line remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10152 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.00

`SmoothNumberSaddleFourthShell.lean` moves the accumulated CEP alphabet to
the third iterated natural square root of `y`. Exact floor-root estimates put
its logarithm between `1/9*log(y)` and `1/8*log(y)` and every retained prime
above `1/12*log(y)`. Thus the full alphabet has nonpositive cosine throughout
`6*pi/log(y) <= t <= 12*pi/log(y)`. Critical-regime growth verifies its PNT
and cofactor hypotheses, producing a uniform explicit fourth-shell loss. Its
divergent-scale conversion and normalized integral remain, so Theorem 1.7 is
not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10153 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.01

`SmoothNumberSaddleFourthShellIntegral.lean` converts the eighth-root
cofactor power to a loss of order `u^(1/9)/log(u)`, proves its divergence and
exponential absorption of the saddle normalization, and applies the signed
envelope plus symmetric-shell norm theorem. The exact normalized Perron
contribution on `6*pi/log(y) <= |t| <= 12*pi/log(y)` tends to zero. Later
shells and the infinite outer line remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10154 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.02

`SmoothNumberSaddleIndexedShell.lean` replaces the repeated scale geometry
with an indexed iterated-root alphabet. Recursive lower and upper logarithmic
envelopes are proved and solved in closed form; indices one, two, and three
recover the previously certified square-, fourth-, and eighth-root scales.
The indexed physical upper heights likewise recover their endpoints and
double exactly. Uniform indexed loss and infinite aggregation remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10155 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.03

`SmoothNumberSaddleIndexedPhase.lean` proves the common phase-loss theorem
for all indexed shells `k>=2`. If the chosen iterated-root scale retains at
least four fifths of its ideal `2^(-k)` logarithmic size, its CEP alphabet
starts at the exact support needed for the adjacent indexed endpoints. Every
retained prime then lies in the nonpositive-cosine phase window, and the full
accumulated loss follows. Growing-range scale control and summation remain,
so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10156 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.04

`SmoothNumberSaddleIndexedScaleRange.lean` proves that iterated-root scales
are antitone, so terminal noncollapse supplies all intermediate largeness
hypotheses. The exact rounding envelope then converts
`10*(2^k-1)*log(2) <= log(y)` into the four-fifths scale retention required
by the uniform indexed phase theorem. Choosing a growing terminal index and
summing the resulting shells remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10157 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.05

`SmoothNumberSaddleIndexedFixedDepth.lean` proves the exact threshold
`a <= scale(k,y) ↔ a^(2^k) <= y` for survival through `k` natural square
roots. Consequently, every fixed indexed depth is eventually noncollapsed
in a critical regime. Since `log(y)` also tends to infinity, the explicit
rounding criterion from release 4.04 is eventually automatic, and the two
ideal logarithmic scale bounds are packaged together. This certifies every
fixed finite shell prefix; a single growing diagonal index and its summed
shell envelope remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10158 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.06

`SmoothNumberSaddleIndexedFixedLoss.lean` proves that at every fixed index
the critical Rankin ratio is eventually at most the square root of the
iterated prime scale. The exponent choice `(1/5)*2^(-k)` turns the 4/5 scale
retention into this cofactor bound. Combining it with release 4.05 and the
uniform indexed phase theorem gives the full cosine-loss estimate throughout
the exact `k`th physical shell. Thus every fixed shell is now analytically
controlled; diagonal growth, uniform summation, and the residual infinite
tail remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10159 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.07

`SmoothNumberSaddleIndexedDiagonal.lean` packages the complete loss assertion
for one indexed shell, proves simultaneous eventual control over every fixed
finite prefix, and applies the frozen countable-diagonal theorem. It produces
one depth `K(n)` tending to infinity such that, eventually, every shell
`2 <= k <= K(n)` obeys its full critical cosine-loss estimate at the same
parameter value. The growing-index quantifier exchange is therefore closed.
Converting these losses to uniform integral envelopes, summing the prefix,
and controlling frequencies beyond its terminal endpoint remain, so Theorem
1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10160 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.08

`SmoothNumberSaddleIndexedLossScale.lean` defines the natural indexed
exponent `(4/5)*2^(-k)` and converts the raw CEP cofactor bound into an
explicit Rankin-ratio loss scale. The saddle displacement pays the universal
`exp(-16)` cutoff penalty, while the four-fifths scale retention supplies the
power comparison. For every fixed index the resulting scale is eventually a
lower bound for the cosine loss throughout the exact shell and tends to
infinity. Fixed-index integration and moving-prefix summation remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10161 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.09

`SmoothNumberSaddleIndexedShellIntegral.lean` proves that
`sqrt(u)*exp(-a*u^beta/log(u))` tends to zero for every fixed positive
`a,beta`, applies this to the indexed loss scale, extends the pointwise bound
to both frequency signs, and integrates the exact symmetric indexed shell.
Its width is computed from the doubling endpoint formula, so every fixed
indexed Perron contribution tends to zero in a critical regime. Selecting a
single growing prefix whose whole finite sum vanishes remains, as does the
post-terminal tail; Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10162 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.10

`SmoothNumberSaddleIndexedPrefix.lean` proves that every fixed finite sum of
indexed shell contributions tends to zero. It then diagonalizes the joint
predicate asserting both a whole-prefix norm bound `<=1/(K+1)` and all
shellwise cosine-loss estimates. The selected depth tends to infinity, its
entire moving prefix tends to zero, and every shell below it remains
analytically controlled. Identifying this sum with the contiguous physical
Perron segment and controlling the post-terminal tail remain, so Theorem 1.7
is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10163 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.11

`SmoothNumberSaddleIndexedTelescoping.lean` proves exact concatenation of
adjacent normalized symmetric Perron shells. By induction, the algebraic
indexed prefix is the single contiguous segment from indexed height one to
height `K`. Applied to the release-4.10 slow diagonal, this gives a terminal
index tending to infinity whose complete contiguous indexed segment tends to
zero, while all constituent shell-loss estimates remain available. Only the
outer Perron line beyond this moving terminal height remains in the smooth
saddle argument; Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10164 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.12

`SmoothNumberSaddlePostTerminalTail.lean` concatenates the already controlled
first, extended, and second outer pieces into one pre-indexed segment and
proves its contribution tends to zero. It defines the exact remainder after
subtracting this segment and the release-4.11 moving indexed segment from the
infinite outer Perron line. A checked equivalence reduces the full critical
smooth-saddle asymptotic to decay of that one post-terminal remainder along
the existing growing diagonal. The required genuinely high-frequency decay
estimate remains, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10165 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.13

`SmoothNumberSaddleIndexedHeightCeiling.lean` proves an absolute limitation
of the indexed root-shell construction. If shell depth `k >= 1` retains a
terminal iterated prime scale of at least four, then its physical upper
height is at most `3*pi/(2*log 4)`. Therefore any growing index whose terminal
scale remains eventually admissible has bounded physical height and cannot
tend to infinity. Closing the release-4.12 post-terminal remainder requires
a distinct high-frequency argument; Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10166 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.14

`SmoothNumberSaddleHildebrandTenenbaumEnvelope.lean` formalizes the exact
large-frequency loss in Hildebrand--Tenenbaum Lemma 8(ii), equation (3.16):
`u*t^2/((1-sigma)^2+t^2)`. It proves this loss is nonnegative, even, and
radially increasing, packages the source finite-range characteristic bound,
transfers it through the exact Laplace kernel to the normalized Perron
integrand, and integrates the resulting finite symmetric shell. The analytic
proof of the minor-arc contract and HT Lemmas 9–10's truncation mechanism
remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10167 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.15

`SmoothNumberSaddleHTMangoldtTransform.lean` defines the finite complex
Mangoldt transform of HT Lemma 6, its weighted cosine sum, and their
source-shaped main terms. The cosine sum is proved exactly equal to the real
part of the zero-frequency transform minus the frequency-`t` transform. Two
complex approximation errors bounded by `E` therefore give the corollary's
cosine error bounded by `2E`. The uniform Abel–PNT transform estimate remains,
so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10168 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.16

`SmoothNumberSaddleHTLemmaSix.lean` records HT Lemma 6 at its exact source
frequency ceiling `exp((log y)^(3/2-epsilon))` and equation-(3.10) error
shape. As corrected in release 4.40, the source's `O_epsilon` multiplier is
explicit rather than fixed to one. The module states the remaining uniform
transform estimate as a named proposition, computes the complex main term at
zero and at general frequency, computes its norm and the Cartesian cosine
main term, and derives the full cosine corollary. The shifted
Perron/zero-free-region proof of the named proposition remains, so Theorem
1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10169 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.17

`SmoothNumberSaddleHTPrimePowerBridge.lean` splits the HT Mangoldt cosine
sum exactly into prime and non-prime contributions. It bounds the prime
contribution by `log y` times the existing Euler-product cosine loss and the
non-prime cosine tail by twice an explicit prime-power remainder. Combined
with the release-4.16 transform contract, this yields the checked source
lower bound for the Lemma-8(ii) loss. The sharp HT Lemma 5 remainder bound
and transform contract remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10170 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.18

`SmoothNumberSaddleHTPrimePowerBound.lean` decomposes the higher-prime-power
remainder exactly by exponent, proves the first slice vanishes, and bounds
every later slice geometrically in the saddle range `sigma >= 1/2`. Summing
those coefficients and applying the audited weighted Chebyshev estimate gives
an explicit `O(log y)` bound, which supplies the required specialization of
HT Lemma 5. The elementary cosine-main-term lower bound and the analytic
Lemma 6 transform contract remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10171 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.19

`SmoothNumberSaddleHTMainTermLower.lean` proves a phase-uniform lower bound
for the exact Cartesian cosine main term and combines it with the Lemma 6
bridge and the release-4.18 prime-power estimate. This yields a single
explicit lower bound for the Euler-product cosine loss. The saddle-coefficient
comparison and analytic Lemma 6 transform proposition remain, so Theorem 1.7
is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10172 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.20

`SmoothNumberSaddleHTSaddleComparison.lean` combines the canonical finite
Abel weighted-prime estimate with the exact smooth saddle equation. It proves
that the HT main coefficient controls a fixed multiple of the Rankin ratio
and derives the source-shaped rational cosine loss under one explicit cutoff
hypothesis. That cutoff is not expected in the critical regime, so this is
retained as a correct conditional intermediate result; Theorem 1.7 is not
claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10173 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.21

`SmoothNumberSaddleHTSaddleComparisonSharp.lean` proves an exact finite Abel
identity against Chebyshev's theta function and the uniform estimate
`sum_{p<=y} log(p)p^(-sigma) <= log(4)y^(1-sigma)/(1-sigma)`. It bounds the
exact saddle prime sum by `5 log(4)` times that scale, inserts the saddle
equation, and derives the source-shaped rational HT cosine-main-term loss
without the release-4.20 divisor cutoff. The analytic Lemma 6 transform
proposition remains, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10174 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.22

`SmoothNumberSaddleHTShiftedPerron.lean` rewrites the finite HT Mangoldt
transform as the literal source Dirichlet sum at `s=1-beta+i*t` and its main
term as `y^(1-s)/(1-s)`. It proves the shifted-Perron estimate equivalent to
the named Lemma 6 contract and records the exact finite Abel identity against
Chebyshev's `psi`. The omitted contour/zero-free-region estimate remains, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10175 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.23

`SmoothNumberSaddleHTShiftedRightLine.lean` proves absolute convergence and
termwise integration for the shifted von Mangoldt series on
`1<Re(s)+c`, identifies the normalized zeta-logarithmic-derivative integral
with source-weighted frozen sharp-Perron kernels, and proves that the exact
cutoff series is the finite source Dirichlet sum. Their subtraction gives an
exact error series, specialized to `s=1-beta+i*t` for `beta<c`. The contour
shift, pole extraction, and zero-free-region remainder remain, so Theorem 1.7
is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10176 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.24

`SmoothNumberSaddleHTShiftedRectangle.lean` defines the translated
zeta-surrogate Perron integrand and proves its exact residue theorem on a
positive-real rectangle containing `z=1-s`. Under a literal zero-free
hypothesis for the translated surrogate, the only pole contributes
`y^(1-s)/(1-s)`; solving the boundary identity expresses the initial right
line as this source main term plus the two horizontal and left vertical
edges. The source-facing theorem specializes this to `s=1-beta+i*t`,
`left<beta<right`, and `|t|<T`. Uniform zero-freeness and quantitative edge
bounds remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10177 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.25

`SmoothNumberSaddleHTShiftedZeroFree.lean` translates the frozen
rectangle-uniform Vinogradov--Korobov theorem to the HT coordinates. For
left edge `beta-eta`, the physical zeta rectangle begins at `1-eta` and its
height is at most `|t|+T`; the explicit frozen width condition therefore
proves the surrogate nonvanishing required by release 4.24. The resulting
theorem inserts zero-freeness directly into the exact contour identity, and
positive rectangle constants are extracted from the frozen native Ford
proof. Uniform parameter selection and the three edge bounds remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10178 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.26

`SmoothNumberSaddleHTContourParameters.lean` fixes the shifted contour at
`eta=2*(log y)^(epsilon/2-1)`, `T=2Y_epsilon(y)`, and
`right=beta+1/log y`. It proves the exact source decay
`y^(-eta)=exp(-2*(log y)^(epsilon/2))`, the strengthened initial-line power
cost
`y^right=exp(1)y^beta`, and all required positivity and height geometry. The
right-line cutoff identity and the native-zero-free rectangle identity are
then combined into an exact decomposition of the transform error as the
three contour edges minus the finite-height sharp-Perron truncation error.
The eventual VK-width comparison, the complementary small-beta branch, and
quantitative bounds for those two explicit remainders remain, so Theorem 1.7
is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10179 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.27

`SmoothNumberSaddleHTContourWidth.lean` unfolds the VK denominator at the
exact source ceiling and proves that its product with the selected shift is
`(log y)^(-epsilon/6)` times a one-third power of a `log log y` factor.
Log-versus-power decay makes this smaller than the positive native Ford
constant. The frozen factor-three denominator comparison and denominator
monotonicity then prove the literal width uniformly at
`|t|+2Y_epsilon(y)` for every requested frequency. Consequently the native
Ford constants instantiate the exact transform-error decomposition
eventually whenever `beta` exceeds the shift. The explicit contour-edge and
Perron-truncation bounds and the complementary small-beta branch remain, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10180 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.28

`SmoothNumberSaddleHTPerronTruncation.lean` computes the shifted source
coefficient norm and proves that its product with the selected right-line
power is `y^(beta-1)` times the frozen optimized sharp-Perron power. Frozen
strict-lower, endpoint, and strict-upper kernel estimates therefore give a
single nonnegative scalar term majorant. Its infinite upper tail is proved
summable by comparison with the von Mangoldt Dirichlet series beyond
`2y`, and the full complex truncation error is bounded by `y^(beta-1)` times
the majorant `tsum`. An explicit bound for that sum, the three displaced
edges, and the complementary small-beta branch remain, so Theorem 1.7 is not
yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10181 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.29

`SmoothNumberSaddleHTPerronArithmetic.lean` uses the integral cutoff to
bound both nonendpoint reciprocal logarithmic distances by `y+1`. The full
scalar majorant is thereby dominated by its single endpoint plus one
constant multiple of the positive von Mangoldt Dirichlet series at the
optimized Perron abscissa. The frozen `log y+C` estimate and exact identity
`y^(1+1/log y)=exp(1)y` give an explicit bound, which is transferred to the
complete complex truncation error at the selected HT contour height.
Absorption into the target error, the three displaced contour edges, and the
complementary small-beta branch remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10182 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.30

`SmoothNumberSaddleHTPerronArithmeticSharp.lean` replaces the coarse global
distance factor by a near/far split. The near range retains reciprocal
distance and is compared to a frozen half-integral kernel of mass at most
eight harmonic numbers. In the far range the additive-distance factor is at
most two, leaving the positive von Mangoldt Dirichlet series. The endpoint,
near, and far terms are summed explicitly and specialized to the selected HT
height, removing the spurious extra factor of `y` across the full epsilon
range. Eventual absorption, the three contour edges, and the small-beta
branch remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10183 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.31

`SmoothNumberSaddleHTPerronAbsorption.lean` formalizes the strict source
exponent gap `epsilon/2 < 3/2-epsilon` and a fixed-constant logarithmic
absorption theorem. The endpoint, harmonic near, and Dirichlet far pieces
are each assigned one third of `y exp(-(log y)^(epsilon/2))`. Their sum
therefore controls the complete scalar truncation majorant, and restoring
`y^(beta-1)` gives the exact source decay
`y^beta exp(-(log y)^(epsilon/2))`. This is also bounded by the full HT
Lemma-6 allowance uniformly for `0<beta<1`. The three displaced contour
edges and complementary small-beta branch remain, so Theorem 1.7 is not yet
claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10184 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.32

`SmoothNumberSaddleHTContourEdgeBounds.lean` proves generic normalized
horizontal- and vertical-integral estimates from pointwise sup bounds. It
then computes the literal HT horizontal length
`shift+1/log y`, the vertical length `2T`, and combines the two horizontal
edges and left vertical edge into one named scalar majorant for the complete
contour-edge contribution. Thus the remaining large-beta edge task consists
only of three pointwise translated zeta logarithmic-derivative bounds and
their scalar absorption. The complementary small-beta branch also remains,
so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10185 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.33

`SmoothNumberSaddleHTContourEdgeWeighted.lean` retains the reciprocal Perron
denominator on the left vertical edge. Its elementary symmetric envelope is
evaluated exactly, replacing the artificial linear contour-height loss by
the logarithmic factor `4*B*log((a+T)/a)`. The shifted zeta-Perron integrand
norm is factored exactly into the translated zeta logarithmic derivative,
the real power, and the reciprocal Perron denominator. Both horizontal edges
and this weighted left edge are assembled into a source-scale scalar
majorant. The pointwise translated logarithmic-derivative estimate, its
absorption, and the separate small-beta branch remain, so Theorem 1.7 is not
yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10186 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.34

`SmoothNumberSaddleHTLogDerivativeSeparation.lean` strengthens the eventual
HT/VK width comparison to reserve twice the contour shift. It converts the
native zero-free rectangle into a quantitative distance bound from every
frozen sharp-Landau zero to every point with real part at least `1-eta`.
`SmoothNumberSaddleHTLogDerivativeLandau.lean` uses that distance inside the
finite Landau zero sum, proves the evaluation point is outside the larger
zero disk, and reinstantiates the frozen partial-fraction theorem. The result
is an arbitrary-positive-height physical `zeta'/zeta` estimate whose only
separation cost is `1/eta`; no selected good ordinate is assumed. Its
specialization to all three HT edges, scalar absorption, and the small-beta
branch remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10188 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.35

`SmoothNumberSaddleHTLogDerivativeSymmetry.lean` transfers the arbitrary
positive-height VK/Landau estimate to negative height by exact conjugation.
It then uses the absolute ordinate itself as the Landau scale, eliminating
the frozen unit-interval parameter from subsequent applications. Finally,
the frozen logarithm and zero-mass estimates compress the raw bound to an
explicit constant times `(1+1/eta)*log |R|`, uniformly for either sign once
`|R|>=8`. The low-height vertical segment, contour specialization, and scalar
absorption remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10189 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.36

`SmoothNumberSaddleHTLogDerivativeLowHeight.lean` handles the portion of the
left edge that crosses the zeta pole and lies outside the high-height Landau
coordinate. A fixed compact rectangle is placed to the right of half the
native VK boundary. The entire surrogate `(s-1)zeta(s)` is proved nonzero
there using the native zero-free theorem; compactness then bounds its
logarithmic derivative. Restoring zeta adds the explicit `1/|s-1|` term,
which is at most `1/eta` on the shifted left line. Complete contour
specialization and absorption remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10190 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.37

`SmoothNumberSaddleHTLogDerivativeContour.lean` enlarges the spare-width
comparison to nine source frequency ceilings, exactly what the Landau bound
requires after multiplying each physical ordinate by three. It computes the
absolute-height ranges of both horizontal edges and their real-coordinate
strip bounds, obtaining one explicit high-height majorant. On the left edge,
the compact surrogate bound below the fixed native height and the Landau
bound above it are combined into a single max majorant. Thus all three
literal HT edges now have pointwise physical `zeta'/zeta` bounds. Transfer to
the shifted Perron integrand, weighted integration, and scalar absorption
remain, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10191 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.38

`SmoothNumberSaddleHTContourEdgeAnalytic.lean` converts the physical
logarithmic-derivative bounds into estimates for the literal shifted Perron
integrand. The two horizontal edges retain the reciprocal contour-height
gain, while the left edge retains the full Perron denominator under weighted
integration. The translated surrogate-zero-free rectangle supplies all
zeta-nonzero and non-pole conditions. A VK-specialized wrapper assembles the
three pointwise estimates into the explicit weighted edge majorant. Scalar
absorption and the complementary small-beta branch remain, so Theorem 1.7 is
not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10192 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.39

`SmoothNumberSaddleHTContourEdgeAbsorption.lean` corrects the contour
displacement to `2*(log y)^(epsilon/2-1)`, which still fits the native VK
width and supplies two stretched-exponential copies on the left edge. It
bounds both logarithmic-derivative majorants by a cubic logarithm and the
vertical reciprocal-distance logarithm by a quadratic logarithm. One decay
copy absorbs all these scalar losses; the other remains as the exact
equation-(3.10) target. Consequently the complete three-edge norm has the
required target bound uniformly for `2*eta<=beta`. The complementary
small-beta branch remains, so Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10193 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.40

The HT Lemma 6 contract is corrected to match the pinned source literally:
equation (3.10) has an epsilon-dependent implied constant. The new
`SmoothSaddleHTMangoldtTransformEstimateAt epsilon C` exposes that constant,
and the global proposition selects one positive `C` uniformly in `y`, beta,
and frequency. The cosine, prime-power, shifted-coordinate, and main-term
bridges now retain this multiplier rather than assuming it equals one.

`SmoothNumberSaddleHTShiftedTwoPole.lean` constructs the complementary
small-beta contour. It proves the local principal part at `z=0`, identifies
its coefficient with `-zeta'/zeta(s)`, applies the finite-pole residue theorem
to `{0,1-s}`, and solves for the right vertical edge. A new arbitrary-left VK
theorem proves translated surrogate nonvanishing at physical depth
`beta-left`. Finally, the existing right-line cutoff identity is combined
with this two-pole rectangle to give the exact formula
`transform-main = origin residue + negative-left edges - truncation error`
and its norm form. Sharp source-scale control of the origin residue and
absorption of the negative-left edges remain, so Theorem 1.7 is not yet
claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10194 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.41

`SmoothNumberSaddleHTSmallBetaWidth.lean` proves the missing parameter
geometry for the complementary branch. The selected contour shift tends
below every positive target, `3*eta` eventually fits both the unit-depth
condition and the native VK width at the actual translated height, and
`beta<=2*eta` supplies `beta+eta<=3*eta`. Native VK constants therefore give
an eventual exact two-pole decomposition uniformly over the complete source
frequency range.

The same package identifies the Perron-origin coefficient with the physical
`-zeta'/zeta(1-beta+it)`. On the fixed low-height VK rectangle, compactness of
the nonvanishing entire surrogate `(s-1)zeta(s)` yields the sharp
`C+1/beta` bound for this residue. The remaining high-height estimate must
have source scale `O(D(t)+1/beta)`; the previously proved Landau logarithmic
bound is too coarse near `beta=0`. Negative-left edge absorption remains, so
Theorem 1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10195 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.

## Release delta: prime-equidistribution-4.42

`SmoothNumberSaddleHTVariableDisk.lean` builds the physical disk centered at
`1+w+it` with radius `2*w`. It proves that the small-beta source coordinate
lies at normalized radius at most `5/6`, derives disk zero-freeness from the
native VK rectangle, bounds the center reciprocal by the frozen
Euler-product right-line estimate, and bounds the disk maximum by the frozen
Pintz zeta window. With the normalized zero set empty, the frozen
`GafniTao.FinalBound` gives a physical logarithmic-derivative estimate.

`SmoothNumberSaddleHTVariableDiskScale.lean` specializes to native VK width
and proves that estimate is `O(D(A)*loglog(A))` uniformly at high height.
`SmoothNumberSaddleHTSmallBetaScale.lean` proves the exact HT ceiling and
scale identities needed to absorb this into `O(1/beta)`.
`SmoothNumberSaddleHTSmallBetaHighHeight.lean` combines the high-height disk
argument with release 4.41's compact low-height theorem, producing a single
eventual `K/beta` bound for the origin residue over the full small-beta and
frequency ranges. Negative-left three-edge absorption remains, so Theorem
1.7 is not yet claimed.

On 2026-09-17, `lake build Tao2026 Tao2026.Audit` completed successfully with
10199 jobs. The canonical isolated verifier
`cmd /c run_tao_build.bat --no-pause` then completed with
`FINAL RESULT: PASS`, including inventory, source-hash, raw-Mermaid,
warning-failing build, axiom-audit, forbidden-shortcut, root-reachability, and
semantic regression gates.
