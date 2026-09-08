# Tao 2026 Source-to-Lean Crosswalk

## Authority and status

Primary source: Terence Tao, *Products of consecutive integers with unusual
anatomy*, arXiv `2603.27990v2`, pinned under `Sources/`.

This is now an active crosswalk. Rows marked **definition compiled** identify
kernel-checked source objects, not proofs of any paper theorem. The complete
Section 2--6 lemma ledger and immutable node-74 snapshot remain open.

## Source conventions

| Source object | Exact paper location | Lean representation | Representation note | Status |
|---|---|---|---|---|
| Consecutive interval `{N+1,...,N+H}` | Display (1.1), before Theorem 1.1 | `Tao2026.consecutiveInterval` | `Finset.Ioc N (N+H)` preserves both endpoints, including `H=0` | Definition compiled |
| Consecutive product | Display (1.1) | `Tao2026.consecutiveProduct` | Finite product over the literal interval | Definition compiled |
| Largest prime factor | Definition 1.2(i), including footnote | `Tao2026.largestPrimeFactor` | `Option ℕ`; `0` and `1` return `none`, so `1` gets no fictitious factor | Definition plus basic interface compiled |
| Bad interval | Definition 1.2(i) | `Tao2026.IsBadInterval` | Requires the square of the actual maximum prime factor to divide the product | Definition compiled |
| Powerful/squarefull | Definition 1.2(ii) | `Tao2026.Powerful` | Literal prime-divisor-square divisibility predicate | Definition compiled |
| Very bad interval | Definition 1.2(ii) | `Tao2026.IsVeryBadInterval` | Applied to the literal consecutive product | Definition compiled |
| Squarefree component `s(n)` | Definition 1.2(iii), footnote | `Tao2026.squarefreeComponent` | Product of primes having odd factorization exponent; squarefreeness, divisibility, and exact prime support are proved; maximal-square characterization remains | Definition and partial interface compiled |
| Type `F₃` interval | Definition 1.2(iii) | `Tao2026.IsFactorialThreeInterval` | Preserves `1 ≤ a < N` and equality of squarefree components | Definition compiled |
| Bad set `B` | Definition 1.3(i) | `Tao2026.badSet` | Union of interval elements, not a count of intervals | Definition compiled |
| Very bad set `VB` | Definition 1.3(ii) | `Tao2026.veryBadSet` | Union of interval elements | Definition compiled |
| Type-`F₃` set | Definition 1.3(iii) | `Tao2026.factorialThreeSet` | Right endpoints `N+H`, not all interval elements | Definition compiled |
| One-term sets | Definition 1.3, following clauses `(i)₁`--`(iii)₁` | `badOneTermSet`, `veryBadOneTermSet`, `factorialThreeOneTermSet` | Defined through the literal `H=1` interval predicates with positivity explicit | Definitions and all three subset bridges compiled |
| Factorial-square triple | Equation labelled `f3-eq`; Theorem 1.10 | `IsFactorialSquareTriple` | Counts ordered triples; the existential nonnegative square root is unique when it exists | Definition compiled; uniqueness bridge open |
| Values in `[1,x]` | Theorems 1.7--1.9 | `countUpTo`, specialized count functions | Counts literal values, not representations | Definitions compiled |
| Factorial solutions up to `x` | Theorem 1.10 | `factorialSquareTriplesUpTo`, `factorialSquareTripleCount` | Finite nested product filtered by strict order and the square equation | Definition compiled |

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
| Theorem 1.7, bad sets | `#((B \ B¹)∩[1,x]) ≪ #(B¹∩[1,x])/log^(1-o(1))x`; hence `#(B∩[1,x])=x/z^(2+o(1))` | Proposition 2.1, Lemma 1.6, Proposition 2.3(iii), large sieve, Lemma 5.1, Propositions 6.5--6.8 | Not declared | Not started |
| Theorem 1.8, very bad sets | `#((VB \ VB¹)∩[1,x]) ≪ x^(2/5+o(1))`; hence zeta-ratio asymptotic | Theorem 2.5, Lemmas 2.10--2.11 and 3.1--3.2 | Not declared | Not started |
| Theorem 1.9, type `F₃` | `#((F₃ \ F₃¹)∩[1,x]) ≪ x^(1/2+o(1))`; hence `#(F₃∩[1,x])=x^(1/2+o(1))` | Proposition 2.3, Theorem 2.5, large sieve, Lemmas 4.1--4.3 | Not declared | Not started |
| Theorem 1.10, factorial equation | Number of `1≤a₁<a₂<a₃≤x` solutions is `x^(1/2+o(1))` | Theorem 1.9 plus representation and lower-bound arguments | Not declared | Not started |

## Verified and candidate upstream boundaries

| Input | Evidence and exact declaration | Node-73 status |
|---|---|---|
| Mathlib | Commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; resolved in `Extension/lake-manifest.json` | Active pinned dependency |
| Node 71 Guth--Maynard | Frozen commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`; publication theorem `RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native` | Indirect source through node 74; no mutable import permitted |
| Node 74 Gafni--Tao | `GafniTao.gafniTaoTheorem11_almostAll_guthMaynard_native` proves the dyadic exceptional-density conclusion for `θ>2/15`; `gafniTaoTheorem11_almostAll_guthMaynard_singleSet_native` supplies a single density-zero set | Exact exceptional-measure bridge and immutable source snapshot pending |
| PNT+ | Revision `4ecb950126c4290293c5662dfe0e884123171df5`; node 74 has an audited 83-file closure | Candidate only; exact needed closure pending |
| `scottdhughes/erdos137` | Apache-2.0 commit `3027d9add77a1f2b203977501987c7def955475d` | Reviewed candidate for elementary lemmas only; not imported |

## Crosswalk completion rule

A row becomes complete only when the exact source location, quantifiers,
conventions, imported mathematical inputs, compiling Lean declaration, axiom
audit, and every representation delta are recorded. No compiled definition in
this table constitutes a proof of a Tao theorem.
