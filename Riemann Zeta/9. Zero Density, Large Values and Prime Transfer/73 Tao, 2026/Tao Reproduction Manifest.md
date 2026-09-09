# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `prime-equidistribution-0.74`. It
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
  `FactorialAsymptotics`, `FactorialFibers`, `FactorialIntervals`, `FactorialOneTerm`, `FourierAssembly`, `FourierApproximation`,
  `IntervalMultiples`, `PrimeIntervals`, `PrimeEquidistribution`,
  `PrimePowerReduction`, `PartialSummation`, `PhaseVariation`, `LowFrequency`, `PowerfulAsymptotics`, `PowerfulExtraction`,
  `PowerfulLimit`, `PowerfulNumbers`,
  `PowerfulRelations`, `PowerfulRelationCounting`, `SquareRelations`, `ConvolutionRearrangement`,
  `QuadraticIdealDivisors`, `QuadraticSolutionCount`, `QuadraticUnits`, `ShortIntervalDecomposition`, `SmoothNumbers`,
  `PublicStatements`, `TypeIReduction`, `TypeIIReduction`, `TypeIIArithmetic`, `TypeIIKernel`, `VeryBadIntervals`,
  `VinogradovPhase`, `VaughanIdentity`, and `Audit`.
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
  discarded `ℓ¹` norm and propagated through the full discrepancy. Fourier
  coefficient decay and construction of the infinite-to-finite uniform
  approximation remain open.
  The `j=1` phase and its finite prime sums are proved exactly equal to the
  `j=2, M=0` case after absorbing `M` into `N`.
  The finite core of the shorter-than-dyadic decomposition is proved: exact
  quotient-block regrouping, ceiling control of the block count, and strict
  within-block diameter. Every coefficient sequence supported on the original
  interval is also decomposed exactly, pointwise and in arbitrary finite
  weighted sums, into block restrictions that preserve uniform norm bounds.
  Concrete instantiation for every Vaughan coefficient family, the Vinogradov/Weyl
  cancellation, Type I/II estimates, and Fourier coefficient
  decay/truncation beyond the proved finite assembly remain open.
  Independently, every finite weighted divisor-antidiagonal convolution is
  reindexed exactly into a bounded product box with the literal condition
  `m*n∈I`. Reassociation of the nested terms puts all three convolution terms
  of the reciprocal-phase Vaughan identity into this product-restricted form.
  Each bounded product sum then decomposes exactly into quotient blocks of its
  outer coefficient, and into double quotient blocks of both coefficients,
  while retaining the product restriction. The source's quantitative
  polylogarithmic family/count and coefficient envelopes remain open.
  For the subsequent Type II decay-kernel summation, fixed natural-distance
  fibers are proved to have cardinality at most two, sums are regrouped
  exactly by distance, and nonnegative kernels incur only this factor two.
  The source real-power decay kernel is defined and proved nonnegative,
  normalized to one at distance zero, and antitone under `R>0`, `F≥0`, and
  `c≥0`. The discrete distance sum is bounded by one plus the corresponding
  real integral, which is evaluated exactly using a proved affine-rpow
  antiderivative, yielding a closed-form finite-sum bound. The bound is
  normalized exactly to `N_r F^{-c}` and, under the explicit endpoint
  condition `1≤N_r F^{-c}`, the endpoint is absorbed with constant
  `1+2^(1-c)/(1-c)`. Combining this with the sharp distance-fiber result gives
  the full finite-support correlation-kernel bound with only an additional
  factor two. The unconditional version retaining `1 + O(N_r F^{-c})` is
  proved too. Since the distance-zero summand is exactly one, a further
  audited lower bound shows that any pure `C N_r F^{-c}` majorant must dominate
  one; deriving this endpoint condition from the source's later quantitative
  parameter choices remains open.
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
  Both support cardinalities are then eliminated from the final double-block
  estimate in favor of the explicit lengths `qouter` and `qinner`.
  The high-frequency logarithmic arithmetic is formalized exactly: if
  `ℓ≥1`, `ℓ^d≤F`, and `b+t≤dc`, then `ℓ^b F^(-c)≤ℓ^(-t)`. Direct corollaries
  use `ℓ=log P`, the explicit threshold `P≥e`, and the source's strict
  `log^d P<F` hypothesis.

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
