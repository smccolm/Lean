# Tao 2026 Source-to-Lean Crosswalk

## Authority and status

Primary source: Terence Tao, *Products of consecutive integers with unusual
anatomy*, arXiv `2603.27990v2`, pinned under `Sources/`.

This is an active crosswalk. Rows marked **definition compiled** identify
kernel-checked source objects, not proofs of any paper theorem. The immutable
1,226-module `GafniTao.Theorem11` closure, its Tao-facing dyadic prime-free
measure bridge, exact Proposition 2.3(iii), and the exact finite `B¹` smooth-
number sum, exact `VB¹` zeta-ratio asymptotic, positive-start first clause
of Lemma 3.1, and complete Lemma 3.2 polynomial-coefficient relation are complete; the analytic smooth-number estimates and the full
Section 2--6 lemma ledger remain open.

## Source conventions

| Source object | Exact paper location | Lean representation | Representation note | Status |
|---|---|---|---|---|
| Consecutive interval `{N+1,...,N+H}` | Display (1.1), before Theorem 1.1 | `Tao2026.consecutiveInterval` | `Finset.Ioc N (N+H)` preserves both endpoints, including `H=0` | Definition compiled |
| Consecutive product | Display (1.1) | `Tao2026.consecutiveProduct` | Finite product over the literal interval | Definition compiled |
| Largest prime factor | Definition 1.2(i), including footnote | `Tao2026.largestPrimeFactor` | `Option ℕ`; `0` and `1` return `none`, so `1` gets no fictitious factor | Definition plus basic interface compiled |
| Bad interval | Definition 1.2(i), under the introductory `H≥1` convention | `Tao2026.IsBadInterval` | Carries `1≤H` explicitly and requires the square of the actual maximum prime factor to divide the product | Definition and positive-length projection compiled |
| Powerful/squarefull | Definition 1.2(ii); square-times-cube reduction before Corollary 2.11 | `Tao2026.Powerful`, `powerful_iff_exists_sq_mul_cube_squarefree`, `sq_mul_cube_squarefree_unique` | Literal prime-divisor-square divisibility predicate; every positive powerful number has a unique positive `a²b³` form with squarefree `b` | Definition and complete decomposition interface proved and audited |
| Very bad interval | Definition 1.2(ii), under the introductory `H≥1` convention | `Tao2026.IsVeryBadInterval` | Carries `1≤H` explicitly and applies powerfulness to the literal consecutive product | Definition and positive-length projection compiled |
| Squarefree component `s(n)` | Definition 1.2(iii), footnote | `Tao2026.squarefreeComponent` | Product of primes having odd factorization exponent; squarefreeness, divisibility, exact prime support, and the existence/uniqueness decomposition after removal of a square are proved | Definition and required decomposition interface compiled |
| Type `F₃` interval | Definition 1.2(iii) | `Tao2026.IsFactorialThreeInterval`, `isFactorialThreeInterval_iff_factorialSquare` | Preserves `1≤H`, `1≤a<N`, and equality of squarefree components; proved equivalent to the exact factorial-square equation with indices `(a,N,N+H)` | Definition and source equivalence proved and audited |
| Bad set `B` | Definition 1.3(i) | `Tao2026.badSet` | Union of interval elements, not a count of intervals | Definition compiled |
| Very bad set `VB` | Definition 1.3(ii) | `Tao2026.veryBadSet` | Union of interval elements | Definition compiled |
| Type-`F₃` set | Definition 1.3(iii) | `Tao2026.factorialThreeSet` | Right endpoints `N+H`, not all interval elements | Definition compiled |
| One-term sets | Definition 1.3, following clauses `(i)₁`--`(iii)₁` | `badOneTermSet`, `veryBadOneTermSet`, `factorialThreeOneTermSet` | Defined through the literal `H=1` interval predicates with positivity explicit | Definitions and all three subset bridges compiled |
| Inclusive `y`-smooth natural and `Ψ` | Before Proposition 2.1 | `IsSmooth n y`, `psiNat x y` | Bridges Tao's `≤ y` convention to Mathlib's strict `Nat.smoothNumbers (y+1)` convention | Definition and membership interface compiled |
| Exact `B¹` representation and sum | Display `box` following Proposition 2.1 | `mem_badOneTermSet_iff_exists_prime_sq_mul_smooth`, `prime_unique_of_sq_mul_smooth`, `badOneTermCount_eq_sum_psiNat` | Proves the unique `n=p²m` representation and the literal natural-division identity over primes `2≤p≤√x`; counts values only after injectivity | Proved, warning-free, and axiom-audited |
| Exact `VB¹` representation and sum | One-term powerful-number discussion used for the Theorem 1.8 main term | `mem_veryBadOneTermSet_iff_exists_sq_mul_cube_squarefree`, `veryBadOneTermCount_eq_sum_sqrt_div_cube`, `veryBadOneTermCount_normalized_tendsto`, `squarefreePSeriesConstant_eq_powerfulNumberConstant`, `veryBadOneTermCount_asymptotic_powerfulNumberConstant` | Proves `VB¹` is exactly the positive powerful numbers, counts its unique `a²b³` forms, applies dominated convergence to the normalized finite sum, reindexes positive integers as square times squarefree, and identifies the resulting product of p-series with the real Riemann-zeta values | Exact identity and source asymptotic `#(VB¹∩[1,x]) ~ ζ(3/2)/ζ(3) √x` proved, warning-free, and axiom-audited |
| Exact `F₃¹` representation and square family | Display `f31` and its preceding paragraph | `mem_factorialThreeOneTermSet_iff`, `mem_factorialThreeOneTermSet_iff_exists_sq_mul`, `square_mem_factorialThreeOneTermSet`, `sqrt_sub_one_le_factorialThreeOneTermCount`, `factorialThreeOneTermCount_powerScale_lower` | Identifies `F₃¹` with square multiples of values `s(a!)` under the literal `a<n-1` condition; embeds distinct squares `q²`, `2≤q≤⌊√x⌋`, first into `F₃¹` and then into `F₃` | Exact representation, `⌊√x⌋-1` bound, and reverse-big-O half of the square-root scale proved and audited; the upper/constant asymptotic remains open |
| Factorial-square triple | Equation labelled `f3-eq`; Definition 1.2(iii); Theorem 1.10 | `IsFactorialSquareTriple`, `mem_factorialThreeSet_iff_exists_triple` | Counts ordered triples; the existential nonnegative square root is unique, and `F₃` right endpoints are proved exactly equivalent to largest indices of such triples | Definition, uniqueness, and endpoint correspondence proved and audited |
| Values in `[1,x]` | Theorems 1.7--1.9 | `countUpTo`, specialized count functions, `countUpTo_sdiff_add_countUpTo_of_subset` | Counts literal values, not representations; each total is proved to split exactly as nontrivial plus one-term count | Definitions and all three exact decomposition identities proved and audited |
| Factorial solutions up to `x` | Theorem 1.10 | `factorialSquareTriplesUpTo`, `factorialSquareTripleCount`, `image_factorialSquareTriplesUpTo_endpoint`, `factorialThreeCount_le_factorialSquareTripleCount` | Finite nested product filtered by strict order and the square equation; projection to the largest index has image exactly `F₃∩[1,x]`, hence every endpoint supplies at least one triple | Exact endpoint image and lower cardinal inequality proved and audited |

## Asymptotic-language crosswalk

| Source notation | Lean declaration | Quantifier contract | Status |
|---|---|---|---|
| `f(x) ≪ x^(a+o(1))` | `PowerUpperBound f a` | For every fixed `ε>0`, an `IsBigO atTop` bound by `x^(a+ε)` | Definition compiled |
| `f(x) = x^(a+o(1))` | `PowerScale f a` | Matching epsilon-power upper and reverse-big-O lower bounds | Definition compiled; equivalence lemmas open |
| `f ≪ g/log^(1-o(1)) x` | `LogPowerSavingRelative f g` | Every fixed positive epsilon has its own big-O constant | Definition compiled |
| `f = numerator/scale^(a+o(1))` | `QuotientPowerScale f numerator scale a` | Direct eventual sandwich with correctly oriented denominator exponents | Definition compiled |
| `f ~ g` | `SequenceEquivalent f g` | Mathlib asymptotic equivalence at `atTop` | Definition compiled |

## Public theorem ledger

| Paper item | Exact source conclusion | Principal imported inputs | Lean endpoint | Status |
|---|---|---|---|---|
| Theorem 1.7, bad sets | `#((B \ B¹)∩[1,x]) ≪ #(B¹∩[1,x])/log^(1-o(1))x`; hence `#(B∩[1,x])=x/z^(2+o(1))` | Proposition 2.1, Lemma 1.6, Proposition 2.3(iii), large sieve, Lemma 5.1, Propositions 6.5--6.8 | `TaoTheorem17Conclusion` | Contract compiled; proof not started |
| Theorem 1.8, very bad sets | `#((VB \ VB¹)∩[1,x]) ≪ x^(2/5+o(1))`; hence zeta-ratio asymptotic | Theorem 2.5, Lemmas 2.10--2.11 and 3.1--3.2 | `TaoTheorem18Conclusion`; `veryBadOneTermCount_asymptotic_powerfulNumberConstant`; `IsVeryBadInterval.length_lt_start_of_pos` | Exact one-term asymptotic and positive-start elementary length restriction proved; nontrivial-`VB` upper bound and public endpoint remain open |
| Theorem 1.9, type `F₃` | `#((F₃ \ F₃¹)∩[1,x]) ≪ x^(1/2+o(1))`; hence `#(F₃∩[1,x])=x^(1/2+o(1))` | Proposition 2.3, Theorem 2.5, large sieve, Lemmas 4.1--4.3 | `TaoTheorem19Conclusion` | Contract compiled; proof not started |
| Theorem 1.10, factorial equation | Number of `1≤a₁<a₂<a₃≤x` solutions is `x^(1/2+o(1))` | Theorem 1.9 plus endpoint projection, the `f31` square family, `hf3`, and Erdős--Selfridge fiber control | `TaoTheorem110Conclusion`; `factorialSquareTripleCount_powerScale_lower` | Contract compiled; complete reverse-big-O/lower half proved; analytic upper bound remains open |
| Erdős--Selfridge input | Theorem 1.1(ii), used after Theorem 1.10 | Original Theorem 1 specialized to exponent two | `squarefreeComponent_factorial_eq_iff_consecutiveProduct_square`, `squarefreeComponent_factorial_succ_eq_iff_square`; final no-square theorem not yet present | Exact factorial-fiber reduction proved and audited; original paper pinned and hashed; no completed external Lean proof found |

## Supporting theorem ledger

| Paper item | Exact source conclusion | Lean endpoint | Status |
|---|---|---|---|
| Proposition 2.3(i) | If `N >= 2`, there is a prime `p` with `N/2 < p <= N` | `Tao2026.taoProposition23i` | Proved from Mathlib's kernel-checked Bertrand theorem and axiom-audited |
| Proposition 2.3(ii) | If `N >= 0`, `H >= 1`, and `{N+1,...,N+H}` has no prime, then `H ≪ N^0.525` | No Lean endpoint | Primary source pinned as `Sources/baker-harman-pintz-2001.pdf`, SHA-256 `D3B6011255C49E52B002E08FAEBB7D252CA1027E545B72FA097176E6285443A2`; Baker--Harman--Pintz Theorem 1, journal p. 532/PDF p. 1, gives the sufficiently-large backward prime interval; journal p. 561/PDF p. 30 gives the final positive lower bound. The natural-endpoint and small-value transfer, and the full analytic proof, remain open. |
| Proposition 2.3(iii) | If `theta > 2/15`, there is `c>0` such that the real `0<=x'<=X` for which the closed interval `[x',x'+X^theta]` contains no prime have measure `O(X^(1-c+o(1)))` | `Tao2026.taoProposition23iii_guthMaynard` | Proved, warning-free, and axiom-audited |
| Exact one-term bad-set identity | `#(B¹∩[1,x]) = ∑_{p≤√x} Ψ(x/p²,p)` | `Tao2026.badOneTermCount_eq_sum_psiNat` | Proved with floor encoded by natural division, a prime-restricted finite sum, and an injectivity proof for the unique representation |
| Exact one-term very-bad-set identity | Positive powerful integers are uniquely `a²b³` with squarefree `b`; hence `#(VB¹∩[1,x]) = ∑_{b≤x, squarefree} ⌊√(x/b³)⌋` | `Tao2026.veryBadOneTermCount_eq_sum_sqrt_div_cube`, `Tao2026.veryBadOneTermCount_asymptotic_powerfulNumberConstant` | Exact finite identity, dominated-convergence limit, square-times-squarefree series product, zeta identification, and precise `ζ(3/2)/ζ(3) √x` asymptotic proved and audited |
| Lemma 3.1, first conclusion | A very bad interval has `H<N` | `Tao2026.prime_dvd_consecutiveProduct_exactly_once`, `Tao2026.IsVeryBadInterval.length_lt_start_of_pos` | Proved for `N≥1` using Proposition 2.3(i). With the project's literal powerfulness convention, `N=0,H=1` gives the interval `{1}` and is a real counterexample to the source's unrestricted wording; the asymptotic use has positive large `N`. The stronger subexponential bound remains open. |
| Lemma 3.2 | Every interval term is `a_h n_h`, where `n_h` is powerful and `a_h` is a product of distinct primes `≤H`; two selected terms have `a,b≪H^O(1)` and give `an+h=bm` with `0<h<H` | `singleExponentPart`, `powerfulCore`, `intervalCoefficientProduct_dvd_smallPrimeEnvelope`, `log_smallPrimeCoefficientEnvelope_le_polynomial`, `exists_two_polynomially_bounded_coefficients`, `veryBadInterval_exists_polynomial_powerfulRelation` | Complete. Canonical extraction, squarefreeness, small-prime support, `a_h∣H!`, exact product divisibility, finite Abel/Chebyshev logarithmic bound, two-half averaging, one explicit fixed exponent, and the final powerful relation are proved, warning-free, and axiom-audited. |
| Corollary 2.11, exact finite reduction | Powerful pairs satisfying `an+h=bm`, `an≤x`, reindex uniquely as solutions `a n₁² n₂³+h=b m₁² m₂³` (with squarefree cube bases in the canonical representation) | `powerfulRelationPairsUpTo`, `powerfulRelationRepresentationsUpTo`, `image_powerfulRelationRepresentationsUpTo`, `injOn_powerfulRelationRepresentationValue`, `card_powerfulRelationRepresentationsUpTo`, `powerfulRelationPairsUpTo_powerUpperBound_half` | Exact finite bijection and cardinal equality proved and audited. Injectivity of either coordinate gives the unconditional `x^(1/2+o(1))` baseline. The source's uniform `x^(2/5+o(1))` estimate still requires Lemma 2.10, divisor bounds, dyadic assembly, and the three-bound interpolation. |
| Lemma 2.10, discriminant split and square branch | For positive solutions of `a n²+h=b m²` with nonzero integer `h`, write `ab=Dc²` with squarefree `D`; when `D=1`, factor `(cm-an)(cm+an)=ah` | `squareRelationSolutionsBoxInt`, `exists_squarefree_discriminant`, `card_squareRelationSolutionsBoxInt_le_const_mul_rpow_of_mul_isSquare`, `card_fundamentalUnitPowersUpTo`, `quadraticPolynomial_irreducible_of_not_isSquare`, `quadraticOrderToRingOfIntegers_injective`, `maximalOrderNormFiberIdealDivisor`, `maximalOrderNormFiberIdealDivisor_eq_iff_associated`, `maximalOrderIdealDivisors`, `quadraticField_ncard_primesOver_le_two` | The canonical discriminant decomposition and injective norm-equation bridge are proved, and the signed split branch has its divisor-epsilon estimate. Fundamental Pell powers have an exact logarithmic candidate count. The concrete field `ℚ[X]/(X²-D)` is proved quadratic; its square root is integral, so `ℤ[√D]` embeds injectively into the actual maximal order. Every fixed-norm point generates a member of a constructed finite ideal-divisor set for `(N)`, whose fibers are exactly maximal-order unit association classes. The abstract at-most-two splitting result is instantiated for each rational prime in this field. The sharp `d(|N|)²` ideal-divisor cardinal bound, height control within the full maximal-order unit group, uniform coefficient bookkeeping, and full lemma remain open. |

## Verified and candidate upstream boundaries

| Input | Evidence and exact declaration | Node-73 status |
|---|---|---|
| Mathlib | Commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; resolved in `Extension/lake-manifest.json` | Active pinned dependency |
| Node 71 Guth--Maynard | Frozen tag `gm-foundation-freeze-v1.0.1`, commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`; publication theorem `RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native` | Included transitively in the frozen node-73 source closure; no mutable import |
| Node 74 Gafni--Tao | Source closure rooted at `GafniTao.Theorem11`; its native density chain yields `Tao2026.exists_uniform_dyadic_exceptional_power_guthMaynard` for `2/15 < θ < 1` | Exact 852-module Gafni--Tao closure frozen and hashed; prime-power tail, dyadic measure bridge, constant-length prefix assembly, and full-range Proposition 2.3(iii) compiled and audited |
| PNT+ | Revision `4ecb950126c4290293c5662dfe0e884123171df5`; exact 83-module reachable closure | Included transitively in the frozen node-73 package and hash manifest |
| Baker--Harman--Pintz | R. C. Baker, G. Harman, J. Pintz, *The Difference Between Consecutive Primes, II*, PLMS 83 (2001), Theorem 1; DOI `10.1112/plms/83.3.532` | Exact PDF pinned and hashed; source statement inspected; no Lean formalization found or claimed |
| `scottdhughes/erdos137` | Apache-2.0 commit `3027d9add77a1f2b203977501987c7def955475d` | Reviewed candidate for elementary lemmas only; not imported |

## Crosswalk completion rule

A row becomes complete only when the exact source location, quantifiers,
conventions, imported mathematical inputs, compiling Lean declaration, axiom
audit, and every representation delta are recorded. No compiled definition in
this table constitutes a proof of a Tao theorem.
