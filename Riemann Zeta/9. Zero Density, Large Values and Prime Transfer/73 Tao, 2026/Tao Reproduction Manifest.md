# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `prime-equidistribution-0.80`. It
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
- Matomäki--Radziwiłł--Shao--Tao--Teräväinen 2021/2022 PDF and TeX archive:
  pinned by SHA-256 with arXiv and DOI provenance and an exact Proposition
  1.12 proof locator; this is the cited input behind Tao's Theorem 2.5, not yet
  a formal proof.

## Lean package

- Package directory: `Extension/`.
- Package/library name: `Tao2026`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Production modules: `Anatomy`, `Intervals`, `Asymptotics`, `Counting`,
  `CoefficientBounds`, `CoefficientProduct`, `CoefficientSelection`, `CriticalIntervals`,
  `FactorialAsymptotics`, `FactorialFibers`, `FactorialIntervals`, `FactorialOneTerm`, `FourierAssembly`, `FourierApproximation`, `FourierDecay`, `FourierIntegrationByParts`, `FourierRadial`, `FourierSlices`,
  `IntervalMultiples`, `PrimeIntervals`, `PrimeEquidistribution`,
  `PrimePowerReduction`, `PartialSummation`, `PhaseVariation`, `LowFrequency`, `PowerfulAsymptotics`, `PowerfulExtraction`,
  `PowerfulLimit`, `PowerfulNumbers`,
  `PowerfulRelations`, `PowerfulRelationCounting`, `SquareRelations`, `ConvolutionRearrangement`,
  `QuadraticIdealDivisors`, `QuadraticSolutionCount`, `QuadraticUnits`, `ShortIntervalDecomposition`, `SmoothNumbers`,
  `PublicStatements`, `TypeIReduction`, `TypeIIReduction`, `TypeIIArithmetic`, `TypeIIKernel`, `VeryBadIntervals`,
  `TorusFourier`, `VinogradovPhase`, `Vinogradov`, `VaughanCoefficients`, `VaughanIdentity`, and `Audit`.
- Frozen theorem dependency: the exact 1,226-module import closure of
  `GafniTao.Theorem11`, with 852 `GafniTao`, 291 `RiemannZeta`, and 83
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
  `badOneTermCount_eq_sum_psiNat` are also proved and audited; Proposition
  2.1's analytic estimates and Lemma 1.6 remain open. The positive powerful-
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
  square consecutive product is also proved; Erdős--Selfridge itself remains
  an explicitly open, source-pinned dependency.
  All three source-facing total counts are proved to decompose exactly into
  their nontrivial and one-term value counts.
  The `b=1` powerful-number family gives audited `⌊√x⌋` lower bounds for
  `VB¹` and `VB`, together with their reverse-big-O square-root lower halves.
  Termwise domination of the exact `VB¹` sum by the convergent `b⁻³ᐟ²`
  p-series gives the summable majorant used in the audited normalized limit;
  its squarefree p-series constant is proved equal to the public zeta ratio.
  The exact-once prime divisor lemma and the positive-start `H<N` conclusion
  of Tao's Lemma 3.1 are also proved; the documented `{1}` edge case prevents
  claiming the unrestricted wording verbatim.
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
  contained coordinatewise in `|d_j|≤ℓV^(j+1)`. The remaining portion begins
  with the equation-(18) regrouping and multiplicity bound, then Lemma 12 and
  the VMVT estimate.
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
2. all six pinned source artifact hashes (Tao PDF and TeX archive,
   Baker--Harman--Pintz PDF, Erdős--Selfridge PDF, and the Singmaster PDF and
   TeX archive);
3. all 1,226 frozen dependency hashes and the exact frozen source file set;
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
