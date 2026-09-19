# Tao 2026 Checklist

This is the detailed readiness and future completion ledger for node 73.
Checked groundwork and input items do not imply that a public theorem from the
paper has been formalized.

## Current completion delta: 5.10

- [x] Formally amend the completion contract to accept endpoint-equivalent,
  hypothesis-free substitutions at every unchanged public consumer.
- [x] Accept native quantitative PNT at `4 H (log N)^2 ≤ N` in place of the
  stronger unused BHP `0.525` construction.
- [x] Accept the proved Selberg upper-sieve weight in place of the literal
  unused `{-1,0,1}` Rosser construction.
- [x] Inventory every public theorem/lemma declaration from comment-stripped
  production source and require a unique, case-sensitive direct audit target.
- [x] Cover all 7,307 inventoried public theorem/lemma declarations with 8,755
  unique reports: 8,708 standard-axiom lists and 47 axiom-free declarations.
- [x] Perform and record the release source-fidelity review of endpoints,
  sets, counts, multiplicity, and asymptotic signs/quantifiers.
- [x] Align the Goal Prompt, Architecture, Checklist, Crosswalk, Agenda,
  Sources, READMEs, verifier documentation, and reproduction manifest.

- [x] Prove arbitrary logarithmic savings for Chebyshev theta from native quantitative PNT.
- [x] Prove eventual prime-free shortness `4 H (log N)^2 ≤ N`, including endpoints and thresholds.
- [x] Apply that exact scale to actual F3 witnesses and close both cases of Lemma 4.2.
- [x] Prove the exact unconditional Theorems 1.9 and 1.10.
- [x] Export all four unchanged public contracts in `PublicTheorems.lean`.
- [x] Directly import all four new modules and audit all 20 new declarations.
- [x] Pass the integrated 10284-job build with zero warnings or tactic diagnostics.
- [x] Pass the explicit axiom audit: 8297 nonempty lists use only standard logical axioms.
- [x] Run and pass all 10 explicit semantic regression assertions.
- [x] Pass source hashes, frozen boundaries, pins, root coverage, inventory, and forbidden-shortcut checks.
- [x] Complete the canonical release verifier with exit code 0 and save the unsuppressed log.
- [x] Record the log's exact status and SHA-256 in the reproduction manifest and synchronize release documentation.
- [ ] Out-of-scope stronger alternative: Proposition 2.3(ii)/BHP `0.525` remains unformalized.
- [ ] Out-of-scope source construction: literal `{-1,0,1}` Rosser weights remain unformalized.
- [ ] Out-of-scope broader Kummer alternative: arbitrary-multiplicity geometric interfaces remain conditional.

The three out-of-scope items are not hypotheses of any of the four public endpoints.
The crosswalk records exactly why the proved PNT scale supplies every actual
Section 4 consumer without strengthening a public hypothesis. All older
checkpoint and open-item lists below are historical, not remaining release
obligations.

## Historical completion delta: 5.08

- [x] Prove Hasse multiplicity bounds and the auxiliary linear constraints.
- [x] Prove nonvanishing from separated simple-root orders and the exact dimension condition.
- [x] Choose integer parameters and prove explicit square-root norm-fiber and character-sum bounds.
- [x] Translate an arbitrary simple root and amplify eventual bounds to sharp all-extension Weil bounds.
- [x] Consume the actual unique-tag Burgess data, including the denominator-root swap.
- [x] Prove prime and cubefree complete Weil bounds for all r and the required r=7.
- [x] Prove `taoTheorem17BurgessCertificate_unconditional` and the exact `taoTheorem17_unconditional`.
- [x] Import all twelve production modules and add 61 declaration audits.
- [ ] Prove Proposition 2.3(ii)/BHP and thereby close Theorems 1.9 and 1.10.
- [ ] Complete every combined main-theorem release gate.

The broader arbitrary-multiplicity Kummer interfaces in historical sections
are conditional alternatives, not remaining premises of Theorem 1.7.
All release-numbered sections below record their historical checkpoint;
their old open-item lists are superseded by this current completion ledger.

## Historical Kummer delta: 5.07

- [x] Identify Frobenius orbits with monic irreducible polynomials, including degree and weight.
- [x] Prove the finite Euler-product coefficient identity by unique factorization.
- [x] Prove monic-polynomial character-sum vanishing by interpolation and orthogonality.
- [x] Prove all-degree Newton polynomiality and the literal characteristic recurrence.
- [x] Prove the Legendre quadratic specialization and the Weil-only Theorem 1.7 bridge.
- [x] Add all five production imports and 68 declaration/endpoint axiom audits.
- [ ] Prove the remaining literal all-extension Weil bounds.
- [ ] Prove Proposition 2.3(ii)/BHP and complete the main-theorem release.

## Groundwork record

- [x] Preserve the human-readable RH-map node `73 Tao, 2026/`.
- [x] Identify the intended paper from the local inference agenda and verify
  it against arXiv.
- [x] Pin arXiv `2603.27990v2` as both PDF and TeX source archive.
- [x] Record SHA-256 hashes and provenance under `Sources/`.
- [x] Create distinct README, Architecture, Checklist, Goal Prompt, Research
  Agenda, Crosswalk, Sources, and Reproduction Manifest roles.
- [x] Reserve `Dependencies/`, `Extension/`, `Sources/`, and `Tools/`.
- [x] Create a minimal isolated `Tao2026` Lake package shell.
- [x] Add a local scaffold runner that produces no persistent logs.
- [x] Compile source-faithful arithmetic-anatomy, interval, counting, and
  asymptotic-language definitions and exact conclusion contracts for
  Theorems 1.7--1.10.

## Source study - initial survey complete; authoritative crosswalk pending

- [ ] Extract the v2 source into an intentional, documented source directory
  if direct TeX navigation is needed.
- [ ] Record every definition used by the principal statements.
- [ ] Record exact theorem, proposition, lemma, and equation numbers.
- [ ] Separate elementary arithmetic inputs from analytic-number-theory inputs.
- [ ] Identify all uses of exceptional-interval estimates and their exact
  quantifiers, uniformity, and numerical thresholds.
- [ ] Determine whether the RH Map's node-71 and node-74 arrows correspond to
  literal source dependencies, replaceable estimates, or only conceptual
  ancestry.
- [ ] Populate `Tao Crosswalk.md` with source-accurate rows.

## Dependency boundary - first analytic boundary frozen

- [x] Identify `GafniTao.Theorem11` as the root of the first required
  Guth--Maynard/Gafni--Tao analytic boundary.
- [x] Freeze its exact recursive source import closure: 965 Gafni--Tao, 291
  Guth--Maynard foundation, and 83 PNT+ modules.
- [x] Pin the selected revisions and record every copied Lean source hash.
- [x] Ensure node 73 imports the frozen package rather than mutable sibling
  development files.
- [x] Add a deterministic refresh tool that follows both `import` and
  `public import` declarations.
- [x] Add the exact node-74 Mathlib revision justified by the source-object
  and analytic-infrastructure audit; keep later packages crosswalk-driven.
- [ ] Freeze any additional dependency closure only when a later crosswalk row
  demonstrates that it is required.

## Historical implementation ledger (original source program)

- [x] Freeze exact Lean conclusion contracts for Theorems 1.7--1.10, with
  literal counting functions and distinct quantified asymptotic predicates.
- [x] Establish the initial production module graph from the source proof.
- [x] Implement the principal definitions without silently changing the
  paper's conventions.
- [x] Prove the exact finite value-count decompositions `nontrivial + one-term
  = total` for `B`, `VB`, and `F₃`.
- [x] Prove existence and uniqueness of the positive square-times-squarefree-
  cube parameterization of powerful numbers used before Corollary 2.11.
- [x] Reindex the finite powerful pairs in Corollary 2.11 bijectively by the
  unique four square/cube parameters, preserving the linear equation and
  count without multiplicity loss.
- [x] Prove the squarefree-discriminant decomposition for Lemma 2.10, its
  exact `bm+cn√D` norm-equation encoding, and injectivity of that encoding.
- [x] Complete the square-discriminant branch of Lemma 2.10 for the source's
  nonzero integer shift by injecting solutions into the signed divisors of
  `a*h` and applying the frozen divisor-epsilon estimate.
- [x] Define and verify the norm-one Pell action on every fixed-norm fiber in
  `ℤ[√D]`, including its orbit membership interface.
- [x] Prove exponential growth and the exact `2 log₂(B)+1` candidate count
  for fundamental-unit powers whose `x`-coordinate has size at most `B`.
- [x] Prove that a squarefree discriminant `D>1` is nonsquare over `ℤ` and
  obtain its fundamental positive Pell solution from the pinned Mathlib API.
- [x] Prove on nonzero fixed-norm fibers that equality of generated principal
  ideals is equivalent to membership in the same norm-one Pell orbit.
- [x] Map each fixed-norm orbit to the principal ideal divisor `(z) | (N)` and
  prove that this ideal-divisor representation has exactly the orbits as fibers.
- [x] Derive from the Galois fundamental identity that every prime has at most
  two primes above it in a Dedekind Galois extension with group order two.
- [x] Construct `ℚ(√D)` as the irreducible quadratic quotient, place `√D`
  in its ring of integers, and prove the canonical map from `ℤ[√D]` into
  that maximal order is injective.
- [x] Map every fixed-norm point to a divisor of `(N)` in the maximal order,
  construct the finite ideal-divisor set, and identify each fiber with a
  maximal-order unit association class.
- [x] Instantiate the at-most-two primes-above theorem for every rational prime
  in the concrete maximal order of `ℚ(√D)`.
- [x] Specialize Dirichlet's unit theorem to the concrete positive real
  quadratic field: prove signature `(2,0)`, unit rank one, torsion exactly
  `{±1}`, unique torsion-times-power decomposition, and the explicit
  `2(2B+1)` count under a `B log λ_D` place-height cutoff.
- [x] Prove the sharp `d(|N|)^2` bound for the finite maximal-order ideal-divisor
  set; derive the required place-height cutoff from the boxed norm points and
  make the growth-base bound uniform, completing both discriminant branches
  and the polynomial-family form of Lemma 2.10.
- [x] Prove Corollary 2.11 for the literal signed-shift powerful relation:
  exact dyadic partition, both coordinate bounds, Lemma 2.10 cube fibers,
  `2/5,2/5,1/5` interpolation, logarithmic absorption, and uniform
  `a,b,|h| ≪ x` family quantifiers.
- [x] Prove the exact finite `VB¹` identity
  `∑_{b≤x, squarefree} ⌊√(x/b³)⌋`, with representation injectivity.
- [x] Extract the `b=1` square family to prove `⌊√x⌋ ≤ #VB¹(x) ≤ #VB(x)`
  and the reverse-big-O half of square-root growth for both counts.
- [x] Bound every term of the exact `VB¹` sum by `√x b⁻³ᐟ²`, sum the
  convergent p-series, and combine it with the square family to prove the
  complete `x^(1/2+o(1))` `PowerScale` contract for `VB¹`.
- [x] Enforce `H≥1` in all interval predicates and prove zero-length
  exclusion; this prevents spurious `F₃` endpoints at `H=0`.
- [x] Prove the exact equivalence between type-`F₃` intervals and the
  three-factorial square equation, and the corresponding right-endpoint
  characterization of `F₃`.
- [x] Prove the first conclusion of Tao's Lemma 4.1 (`abound`): every
  type-`F₃` interval has `H<N`. The proof extracts a Bertrand prime from
  `(N,N+H]`, shows that it occurs exactly once in the interval product, and
  contradicts its occurrence in the smaller factorial component. Deduce the
  triple form `a₃-a₂<a₂`, and prove that every integer lying in a type-`F₃`
  interval is nonprime, the exact arithmetic input needed before applying
  Proposition 2.3(ii).
- [x] Prove the remaining quantitative conclusion of Lemma 4.1,
  `a ≪ H log N`, uniformly for the smaller factorial index in a type-`F₃`
  interval. Formalize the exact upper-half-prime product divisibility and
  Chebyshev-theta inequality, use the pinned PNT for a positive theta-mass
  lower bound, and absorb the finite exceptional range into one constant.
- [x] Formalize the common arithmetic spine of Lemma 4.2 (`hf3`). Eventually
  Lemma 4.1 gives `a<P=H log²N`; every prime `p>P` therefore has even interval-
  product valuation, and because `p>H`, any occurrence is concentrated twice
  in one interval element. In the large-`P` branch `√(2N)<P<p` this is
  impossible since `p²>N+H`, so the prime does not divide the interval product.
- [x] Formalize the large-`P` equidistribution interface for Lemma 4.2. Prove
  that the final fractional arc detects a divisor in `(N,N+H]`, that Tao's
  narrower `1/(10 log²N)` support lies in this arc for `P<p<2P`, and hence
  that the prime sum vanishes exactly; consume specialized Theorem 2.5 to
  obtain the corresponding integral upper bound. Define a concrete
  shrinking cutoff and prove it smooth, periodic, nonnegative, supported,
  and accepted by that upper-bound theorem. Derive the Theorem 2.5 frequency
  range internally from the stretched-log contradiction hypothesis and
  package the source-growth integral upper bound with multiplier one.
- [x] Construct a normalized smooth-transition plateau weight for the
  high-`P` branch. Prove it is one on the source inner arc, has mass at least
  `1/(60 log²N)` per unit period, transport the long-interval mass through
  `u=N/t`, remove the logarithmic weight, and combine the resulting norm lower
  bound with Theorem 2.5 into the exact logarithmic sandwich.
- [x] Complete the high-`P` analytic contradiction conditional on the stated
  inputs. Prove the normalized cutoff's uniform `O(log^12 N)` `C³` bound, fix
  the uniform constant ordering in the sandwich, derive `4P≤N` from the exact
  `21/40` Proposition 2.3(ii) interface, and finish the logarithmic
  contradiction.
- [x] Formalize the low-`P` arithmetic and upper-bound package. Define the
  two-coordinate shrinking cutoff, prove its support excludes the forced
  `p²` divisor, obtain exact prime-sum vanishing, prove its uniform
  `O(log^12 N)` `C³` bound, and consume Theorem 2.5 with one uniform constant.
- [x] Complete the low-`P` shrinking-band geometry and analytic contradiction.
  Formalize both changes of variables, trim the endpoint cells, count occupied
  unit cells, insert the `1/(60 log²N)` first band, derive prime-set measure
  `≥H/1920`, lower-bound the fixed quadratic bump, and join the low/high split.
- [ ] Prove the pinned Baker--Harman--Pintz result behind Proposition 2.3(ii),
  thereby discharging the last external interface in the conditional Lemma
  4.2 proof and obtaining its uniform `H ≤ exp(log^(2/3+o(1)) N)` conclusion.
  - [x] State the source-shaped eventual backward real interval theorem and
    prove its exact transfer to Tao's uniform forward natural-number bound,
    including the `N+2N^(21/40)` shift and finite-range Bertrand absorption.
- [x] Prove Lemma 4.3. Decompose every type-`F₃` interval element canonically
  as `c n²`, prove that `c` is positive, squarefree, and supported on primes
  at most `P=max a H`, and prove the exact product divisibility
  `∏c | ∏_{p≤P} p^(H/p+1)`. Bound its logarithm by
  `log 4 · H(2+log P)+log 4 · P`, average separately over the two interval
  halves, and obtain ordered elements satisfying
  `c₁n₁²+h=c₂n₂²`, `0<h<H`, with both coefficients at most
  `exp(3 log 4 (2+log P+P/H))`.
- [x] Formalize the exact finite counting reduction following Lemma 4.3.
  Separate nontrivial endpoint values from interval witnesses, choose a
  structured bounded smooth relation certificate for each witness, and prove
  that the certificate together with the interval length and selected-element
  offset determines the interval. For arbitrary bounds `A,C,G`, construct the
  budgeted source subfamily and prove its endpoint count is at most
  `A·C²·G³` times one uniform Lemma 2.10 relation-count budget. Define the
  literal small-index-or-bounded-length family and its complement, prove they
  partition every interval witness, and bound the total nontrivial endpoint
  count by the sum of their endpoint-image cardinalities.
- [x] Refine the bounded-length finite family to the exact smooth coefficient
  range. Prove that the pair range has cardinality `psiNat x P ^ 2`, that
  Lemma 4.3 puts both chosen coefficients in it whenever `max a H ≤ P`, and
  bound its endpoint image by `A·psiNat(x,P)²·G³` times the uniform Lemma 2.10
  budget.
- [x] Close the actual fixed-bounded-`H` branch. Retain smoothness through an
  arbitrary number of square-times-squarefree decompositions, prove the exact
  bound `Ψ(x,P) ≤ (2^π(P))^r iterSqrt(r,x)`, combine it with Chebyshev's
  `π(P)=O(P/log P)` estimate to obtain
  `Ψ(x,⌈C log(x+2)⌉)=x^o(1)`, and use Lemma 4.1 to put every `H≤B` interval
  into that logarithmic smooth family. The resulting endpoint count is
  `x^o(1)` for every fixed `B`.
- [x] Close the small-`a` numerical-coefficient regime at the concrete
  threshold `a ≤ H log(x+2)/100`. Lemma 4.3 gives both selected coefficients
  exponent `1/10`; the exact certificate code then gives the literal endpoint
  family exponent `1/4` after the Lemma 4.2 gap budget.
- [x] Discharge the remaining `a ≍ H log x` family via the large sieve. The
  bounded-`H`, small-`a`, and maximal-degree complementary branches now
  combine into the conditional nontrivial Theorem 1.9 upper bound.
- [x] Formalize the finite large-sieve interface for that family. Prove that
  each prime `a/2<p≤a` leaves at most `H` start residues and hence removes at
  least `p-H`; inject each fixed `(a,H)` fiber into the literal survivor set,
  reassemble budgeted fibers with an `A·G` loss, and derive the exact
  three-way reduction of the nontrivial count. Lemmas 4.1 and 4.2 supply the
  required subpolynomial global `(a,H)` box. The upper-half primes are now
  proved pairwise coprime, every selected product is bounded by `a^k`, PNT
  supplies the explicit cardinal lower bound `a/(4 log a)`, and deletion of
  up to `k` weights leaves the source-scale lower bound
  `a log(x+2)/(3200 log a)`. This surrogate sum is connected pointwise to the
  literal complement/allowed ratio. Native cyclic DFT Parseval, the one- and
  two-modulus Montgomery uncertainty inequalities, the arbitrary finite
  tensor inequality, pairwise-coprime iterated CRT, and its finite-support
  residue-class specialization are compiled. The additive CRT character
  reindexing, exact tensor/cyclic energy identity, interval residue-fiber
  bound, one-product-denominator upper inequality, and resulting finite
  survivor-cardinality inequality are now compiled as well. The finite Schur
  Gram-form estimate, exact analysis/synthesis identities, coordinate
  Cauchy--Schwarz, synthesis-to-analysis operator duality, and Bombieri
  duality are compiled in `LargeSieveGlobal`; `LargeSieveCircle` gives the
  exact circle-character Dirichlet-kernel Gram formula and diagonal. Its
  Fejér construction embeds the original synthesis energy with exact
  multiplicity `L` into `2L` shift differences, computes the resulting
  nonnegative squared-Dirichlet Gram kernel, and reduces the desired analysis
  inequality without loss to Fejér row/column bounds. `LargeSieveSeparated`
  now proves the separated-circle row-sum estimate via centered
  representatives and two-point radial bins, yielding an explicit `8L`
  analysis bound for every finite `1/L`-separated frequency family. The
  rational/selection/aggregation layers now compute the CRT numerator, prove
  nondivisibility at every nonzero tensor coordinate, use an exclusive
  modulus to separate different `k`-subsets, identify circle analysis with
  tensor DFT energy, and derive the global finite Corollary 2.8 survivor bound
  `(∑ S, ρ(S))·#survivors ≤ 8L` without a subset-count loss. The
  fixed-cardinality elementary-symmetric denominator is now compiled from the
  exact binomial selection count and `choose n k ≥ (n/(2k))^k`. The literal
  factorial residue complements, exact tensor ratio, `Fin (x+1)` survivor
  transport, source-scale Corollary 2.9 survivor bound, and fixed-`(a,H)`
  fiber bound are compiled as well. The maximal choice
  `k=⌊log(x+1)/(2 log a)⌋` now verifies the product and selection conditions,
  gives a uniform square-root fiber estimate, reassembles only nonempty
  fibers, and absorbs the Lemma 4.1/4.2 budgets. The literal `F₃¹` upper
  bound is also compiled from exponential growth of `s(a!)` and an
  `O(log x)·⌊√x⌋` representation cover. Consequently the full
  `TaoTheorem19Conclusion` follows from Lemma 4.2 and is reduced exactly to
  Theorem 2.5 plus Proposition 2.3(ii) (or the pinned BHP contract).
- [x] Prove that largest-index projection maps the finite factorial-square
  triple set exactly onto `F₃∩[1,x]`, yielding the lower-count transfer
  `#F₃(x) ≤ #triples(x)` used in Theorem 1.10.
- [x] Formalize Tao's exact upper-counting key
  `(a₃, a₃-a₂-1, a₁ mod 2)`. Under Erdős--Selfridge it is injective, and a
  uniform tail-gap bound `a₃-a₂≤g` places its image in
  `(F₃∩[1,x])×[0,g)×[0,2)`, proving the exact finite inequality
  `#triples(x) ≤ 2g #F₃(x)`.
- [x] Lift the finite inequality through the exact asymptotic API: any
  eventual gap budget `g(x)=x^(o(1))`, the total power-scale conclusion of
  Theorem 1.9, and Erdős--Selfridge imply the literal public Theorem 1.10
  contract. The reverse-big-O half is discharged by the proved square family.
- [x] Instantiate that gap input from Lemma 4.2 using
  `g(x)=⌈exp((log x)^(3/4))⌉`. Prove it bounds every triple, including bounded
  middle indices, prove `g=x^(o(1))`, and reduce Theorem 1.10's remaining
  inputs exactly to Theorem 1.9, Erdős--Selfridge, Theorem 2.5, and BHP. With
  Theorem 1.9 now derived internally from Lemma 4.2, also compile the direct
  bridge requiring only Erdős--Selfridge, Theorem 2.5, and BHP.
- [x] Characterize `F₃¹` as square multiples of factorial squarefree
  components and prove the unconditional `⌊√x⌋-1` lower bounds for both
  `F₃¹`, `F₃` endpoints, and factorial-square triples, including the explicit
  triple `1! (q²-1)! (q²)! = (q (q²-1)!)²`.
- [x] Lift the finite square-family bounds to the reverse-big-O half of the
  `x^(1/2+o(1))` contracts for `F₃¹`, `F₃`, and Theorem 1.10's triple count.
- [x] Pin Erdős--Selfridge and prove the exact factorial-fiber reduction:
  equal squarefree components are equivalent to the intervening consecutive
  product being a square; adjacent repetition is exactly at a square index.
- [x] Prove the full long-interval square obstruction from Bertrand: if
  `N≤H` and `2≤N+H`, then `(N+1)⋯(N+H)` is not a square. Consequently any repeated
  positive factorial component at indices `a≤b` has `b-a<a`. Define the
  exact Erdős--Selfridge square proposition and derive, without any axiom,
  its complete finite two-element factorial-fiber consequence. Also prove
  the length-two case by strict inequalities between consecutive squares, so
  the full proposition is equivalent to only the core range `3≤H<N`.
- [x] Prove the Erdős--Selfridge square specialization by combining the
  unrestricted Sylvester--Schur theorem with the formalized Hanson primorial
  argument; instantiate the unconditional two-element factorial-fiber bound
  used in Theorem 1.10.
- [x] Sharpen the proved square-root power scale to the source's
  `ζ(3/2)/ζ(3) √x` asymptotic for `VB¹` from the exact sum.
- [x] Prove the final Theorem 1.8 asymptotic bookkeeping: any
  `x^(2/5+o(1))` bound for the nontrivial count is little-oh of the positive
  zeta-ratio square-root main term, and the exact finite decomposition then
  yields the literal public conclusion.
- [x] Begin the remaining Theorem 1.8 counting assembly with an exact finite
  cover: every nontrivial value below `x` lies in a positive-start very-bad
  interval with `2≤H<x`, and its count is at most the sum of all witness
  interval lengths.
- [x] Prove the elementary `H<N` conclusion of Lemma 3.1 for `N≥1`, by
  extracting a Bertrand prime that divides the interval product exactly once;
  record that the literal `N=0,H=1` interval is an exception to the paper's
  unrestricted natural-number wording.
- [x] Prove that `(N,H)=(0,1)` is the unique zero-start exception and package
  the exact all-start alternative `(N=0 ∧ H=1) ∨ H<N` into the corrected
  Lemma 3.1 contract.
- [x] Pin and hash both the PDF and TeX archive of the exact source cited for
  Theorem 2.5, with the Proposition 1.12 statement and proof locator.
- [x] Compile the exact Theorem 2.5 finite prime sum, logarithmic integral,
  complex-valued periodicity, and sum-of-derivative-orders `C³`-norm contract,
  and derive the `M=N,j=2` consumer from the full contract.
- [x] Formalize the reciprocal additive character and prove the source's
  all-orders reciprocal-phase derivative identity, including its binomial
  `M_r` coefficient and normalized absolute form; prove `1 ≤ binom ≤ (r+j)^r`
  and the resulting upper, reverse-triangle, and dominant-term derivative
  bounds. Prove the exact Type I product rescaling and Type II conjugate
  correlation-phase identities.
- [x] Define exact arithmetic-function cutoffs and tails and prove the
  four-term Vaughan convolution identity used by Proposition 1.12, its
  pointwise nested-divisor expansion, and its finite complex-weighted
  reciprocal-phase summation form.
- [x] Reassociate Vaughan's identity into the source's canonical Type I and
  Type II coefficient pairs. Prove their exact cutoff/tail supports and the
  absolute envelopes `1`, `log P`, `1`, `log P` on positive arguments at
  most `P`, and reindex that source-oriented identity with literal `m*n∈I`.
- [x] Prove the exact Type II Cauchy--Schwarz correlation algebra: expand the
  finite inner sum times its conjugate and identify every transformed phase
  with the source's displayed `X_{n,n'}` phase. Sum the squared norms over the
  outer support, interchange the finite sums exactly, and prove the outer
  coefficient-bounded Cauchy--Schwarz inequality.
- [x] Split the Type II correlation expression exactly into diagonal and
  off-diagonal parts, evaluate `X_{n,n}=#K`, bound the diagonal by
  `#K·#S·L²`, and isolate the remaining off-diagonal correlation norms.
- [x] Propagate one uniform off-diagonal `X_{n,n'}` estimate through the exact
  ordered-pair count `#S(#S-1)`.
- [x] Prove nonvanishing of both transformed Type II reciprocal coefficients
  for distinct positive indices and nonzero original coefficients.
- [x] Prove exact and support-uniform absolute-size bounds for both transformed
  coefficients, including
  `|n'^j-n^j| ≤ |n'-n|·j·B^(j-1)` and lower-support denominator bounds.
- [x] Normalize the full transformed scale at product scale `KR`, exposing
  `|n'-n|/R` with higher loss `j(B/R)^(j-1)`, and specialize it to the
  dyadic factor `j·2^(j-1)`.
- [x] Retain the literal Type II product restriction `mn∈I`, rearrange the
  squared inner sums into correlations on `K ∩ (1/n)I ∩ (1/n')I`, and
  evaluate and bound the restricted diagonal.
- [x] Split the literal restricted correlation expression, propagate a
  uniform off-diagonal estimate through `#S(#S-1)`, and derive the final
  real squared-inner-sum bound used after Cauchy--Schwarz.
- [x] Prove the exact Type I finite reduction with variable inner supports:
  rescale the phase to `N/m, M/m^j` and remove the outer coefficients using
  an explicit uniform-envelope triangle bound.
- [x] Isolate the exact critical expression `N+M_r/t^(j-1)` controlling
  derivative cancellation and prove its two-point sublevel and
  power-difference separation inequalities.
- [x] Convert the critical-expression algebra into an explicit quotient
  diameter bound, a single closed-interval cover of length at most `16Xq`
  under the source's `t^(j-1) ≤ 2X^(j-1)` condition, and a finite-union
  Lebesgue-measure bound for all selected derivative orders.
- [x] Prove the discrete critical-set deletion bound: one derivative order
  contains at most `16Xq+1` natural summation points, and a finite order set
  contains at most `#orders·(16Xq+1)` points.
- [x] Prove the exact prime-logarithm/Mangoldt phase-sum decomposition and
  bound its oscillatory higher-prime-power tail by the explicit frozen local
  prime-power majorant.
- [x] Prove the exact finite Abel-summation identity on natural intervals and
  the explicit `2 log b` norm loss used to reduce the alternate
  logarithm-weighted Type I form to uniform unweighted prefix bounds.
- [x] Prove the reverse prime partial-summation bridge from uniform prime-log
  prefix bounds to the unweighted prime reciprocal-phase sum, with explicit
  factor `1/log a`.
- [x] Prove the low-frequency reciprocal-phase derivative and dyadic
  oscillation bounds `|f'| ≤ (j+1)F/X` and `osc(f) ≤ (j+1)F`.
- [x] Prove the additive-character Lipschitz and dyadic total-variation
  bounds, complex-coefficient finite Abel summation, and the exact
  low-frequency reduction
  `‖Σ(Λ(n)-1)e(f(n))‖ ≤ (1+2π(j+1)F)B` from uniform initial-subinterval
  `Λ-1` discrepancy bound `B`.
- [x] Connect the frozen qualitative `WeakPNT` to the exact discrepancy:
  prove global `o(k)`, uniform `o(P)` on every subinterval of `[P,2P]`, and
  the resulting `o(P)` Mangoldt-to-integer phase comparison for each fixed
  reciprocal-phase scale bound.
- [x] Prove the exact finite Fourier-mode assembly: two-dimensional integer
  characters become reciprocal phases with rescaled parameters, finite prime
  sums and logarithmic integrals interchange with the mode sum, and modewise
  errors aggregate with the Fourier-coefficient `ℓ¹` norm. Propagate bounded
  integer frequencies through `VinogradovParameterBound`.
- [x] Discharge Fourier-mode integrability from `P≥2` and `I⊆[P,2P]`; define
  the retained square frequency box, prove its exact `(2R+1)²` cardinality,
  and derive the explicit mode-count × coefficient-envelope × uniform-error
  estimate. Prove both rescaled mode parameters share the positive uniform
  Vinogradov constant `(R+1)K`.
- [x] Prove continuous-weight integrability and the uniform-approximation
  transfer from a Fourier polynomial to the source weight, with explicit
  perturbation costs `(2P+1)δ` in the prime sum and `Pδ/log P` in the
  logarithmic integral.
- [x] Prove the exact finite Fourier truncation identity and uniform discarded
  coefficient `ℓ¹` bound, then propagate that tail through the full
  prime/integral discrepancy.
- [x] Prove the source cubic envelope `(1+|n|+|m|)^(-3)` is summable on
  `ℤ²`, that square frequency boxes exhaust all modes and have vanishing
  outer `ℓ¹` tails, and that coefficients under this envelope give uniform
  convergence of the finite square Fourier polynomials to their series.
- [x] Descend every continuous `ℤ²`-periodic weight through the open quotient
  `ℝ² → (ℝ/ℤ)²`, identify Mathlib's torus monomials with `fourierMode2D`,
  identify its coefficients with the literal fundamental-square integral,
  and use torus Fourier reconstruction to prove that the cubic coefficient
  estimate makes the square partial sums converge uniformly to the original
  weight `W`.
- [x] Prove the exact unit-interval Fourier integration-by-parts identity,
  iterate it three times for periodic derivatives, and derive the resulting
  one-dimensional cubic coefficient bound by a uniform third-derivative
  bound.
- [x] Factor the actual two-torus coefficient by Fubini in both coordinate
  orders, identify real-coordinate torus slices with unit-interval Fourier
  coefficients, and propagate the cubic bound along either nonzero frequency.
- [x] Combine the zero mode and both directional cubic bounds into the exact
  radial envelope with constant `27`; prove smooth periodicity bounds all four
  derivative ranges on a compact fundamental square; construct the pure
  coordinate derivative chains automatically; and close the unconditional
  `taoC3Norm` coefficient estimate from the public hypotheses.
- [x] Prove the exact source reduction of `j=1` to `j=2, M=0` after absorbing
  `M` into `N`, pointwise and for the relevant finite prime sums.
- [x] Prove the generic finite shorter-than-dyadic quotient-block
  decomposition: exact sum regrouping, a ceiling block-count bound, and
  strict within-block diameter.
- [x] Prove the exact dyadic family-count envelope: block length `ceil(D/L)`
  gives at most `L` blocks in `[D,2D)`, hence `S` dyadic ranges give at most
  `S*L` short families.
- [x] Construct the canonical family over `[1,B]` with budget
  `(log₂ B+1)^101`; prove exact cardinality `(log₂ B+1)^102`, coverage of
  every positive index, the rounded relative diameter `D/L+1`, exact weighted
  coefficient decomposition, and the final counted Type I/II Vaughan-family
  identity retaining `m*n∈I`.
- [x] Compare `Real.log B` with `log₂ B+1` and absorb ceiling rounding via
  the extra subdivision power, proving the literal source support width
  `(1+log(B)^(-100))M` for every block; treat sub-budget bands as singletons
  and transfer to `(1+log(P)^(-100))M` whenever `P≤B`.
- [x] Lift the quotient blocks to coefficient sequences: prove exact
  pointwise and arbitrary finite weighted-sum decompositions for coefficients
  supported on the original interval, with uniform norm bounds preserved by
  every block restriction.
- [x] Reindex finite divisor-antidiagonal convolution sums into bounded
  product boxes with the literal condition `m*n ∈ I`, and apply this to all
  three convolution terms of the reciprocal-phase Vaughan identity.
- [x] Decompose each bounded product convolution exactly into short outer
  coefficient blocks (Type I) and short double coefficient blocks (Type II),
  retaining the literal product restriction in every summand.
- [x] Regroup the Type II correlation decay exactly by natural distance and
  prove the sharp at-most-two multiplicity bound for every distance fiber.
- [x] Define the resulting real-power decay kernel and prove its
  nonnegativity, value at zero, and antitonicity in distance.
- [x] Reduce its finite one-dimensional sum to one plus the matching real
  integral by the antitone sum--integral comparison.
- [x] Prove the affine-rpow antiderivative, evaluate the kernel integral
  exactly, and obtain the closed-form finite-sum bound.
- [x] Normalize that bound to the source scale `N_r F^(-c)`, absorb the
  zero-distance endpoint under the explicit condition `1 ≤ N_r F^(-c)`, and
  combine it with the sharp distance-fiber bound.
- [x] Prove the unconditional finite-support `1 + O(N_r F^(-c))` form and the
  diagonal lower bound showing that any pure source-scale majorant must itself
  dominate `1`.
- [x] Propagate a pointwise `Q(A·kernel(|n-n'|)+E)` correlation estimate over
  the exact ordered off-diagonal support and substitute it into the literal
  product-restricted squared-inner-sum reduction.
- [x] Specialize the resulting estimate to the actual inner quotient block
  and exact Vaughan outer/inner double blocks, discharging block diameter and
  nonzero reciprocal-index hypotheses from membership.
- [x] Prove a quotient block is literally one `Finset.Ico`; identify
  `mn∈[a,b)` with the ceiling-divided interval in `m`; and rewrite the exact
  product-restricted correlation support as one explicit intersection
  interval of length at most the outer block length. Specialize this rewrite
  through the canonical Vaughan block to `reciprocalPhaseSum`.
- [x] Prove every quotient block has cardinality at most its chosen length and
  replace both double-block support cardinalities by `q_outer` and `q_inner`
  in the final squared-sum estimate.
- [x] Formalize the high-frequency logarithmic absorption
  `(log P)^d≤F`, `b+t≤dc` ⇒ `(log P)^b F^(-c)≤(log P)^(-t)`, including the
  source's strict-frequency variant.
- [x] Remove the spurious Type II endpoint-absorption obligation at its actual
  off-diagonal use: prove the zero-distance fiber vanishes after erasing the
  center, obtain a pure `N_r F^(-c)` kernel bound without extra assumptions,
  and propagate it through the complete squared-inner-sum reduction, the
  exact Vaughan double blocks, and their source-facing block-length bound.
- [x] Begin the unconditional Weyl engine with the exact shifted-pair fibers,
  prove the `H`-fold averaged-shift identity and its finite Cauchy--Schwarz
  inequality, expand the summed window squares into the literal constraint
  `n+h=n'+h'`, identify both shift orders with truncated forward correlations,
  and derive the sharp-lag divided finite van der Corput bound. Specialize it
  to translated `reciprocalPhaseSum`, split the zero lag exactly, prove the
  uniform recursive rule, and connect discrete iterates to smooth real-phase
  differences and their derivatives on the positive ray. Prove the terminal
  affine geometric-sum identity and the nonresonant bound
  `min(N, 2 / ‖e(alpha)-1‖)`, then lower-bound the denominator by four
  times the canonical nearest-integer distance to obtain the standard
  reciprocal-distance form. Package arbitrary finite repetition through
  `UniformIteratedPhaseBound` and `weylRecursiveMajorant`, and expose the
  exact four-step source-facing interface for the cited `k=5` branch. Identify
  each one-step real finite difference exactly with an interval integral of
  its derivative, and derive upper and signed lower derivative-separation
  bounds from that identity. Iterate these estimates for globally smooth
  phases, gaining the exact product of all lags in the upper, positive signed,
  negative signed, and sign-independent separation bounds. Localize the full
  iteration to the positive ray and the exact evaluation interval, specialize
  it to `reciprocalPhase`, convert the normalized source derivative window to
  explicit raw upper and lower finite-difference bounds, and obtain the lower
  bound from absolute derivative separation by proving constant sign through
  continuity and the intermediate value theorem. Identify the derivative of
  a terminal iterated difference with the difference of the next source
  derivative and prove a uniform critical-regular two-sided derivative window;
  in particular, the four-lag terminal phase now consumes the fifth original
  derivative exactly. Adapt the frozen radian-normalized Kusmin--Landau theorem
  exactly to `exp(2πix)`, prove the mean-value and second-derivative sign bridges
  from absolute derivative windows to monotone increments, and close the
  nonlinear terminal reciprocal-phase sum under explicit expanded-interval
  regularity and upper-one-period hypotheses. Prove that admissible lag sums
  and products are bounded by `rH` and `H^r`, uniformize the terminal estimate
  over every admissible lag list and every truncated initial length on one
  expanded regular interval, feed it through the recursive majorant, and expose
  the literal four-round theorem with derivative orders five and six and its
  single `H^4` upper-smallness condition. Replace the uniform-leaf loss by an
  exact lag-sensitive Weyl tree retaining every accumulated lag list and
  boundary-truncated length; feed the reciprocal-phase leaf profile
  `min(L, 1/(prod(lags)*scale))` into that tree, sum the innermost lag with the
  exact harmonic factor, and expose the resulting one-level square-root bound.
  Collapse every successive outer lag sum to explicit scalar length and scale
  recurrences using `iteratedRootHarmonic`; prove each generalized harmonic
  factor is at most `H`, expose the closed four-round source theorem, and prove
  that its fourfold iterated scale root has sixteenth power equal to the
  original inverse scale. Replace all generalized harmonic factors by `H` in
  a coarse scale recurrence, prove its four-round sixteenth power is
  `(weylTreeStepFactor H L * H)^15`, combine it with the inverse terminal scale,
  and expose the resulting source-facing coarse majorant. Split the remaining
  length recurrence into four explicit nonnegative terms, prove their exact
  sixteenth powers `D^8`, `E^8 D^4`, `E^12 D^2`, `E^14 D`, derive the powered
  denominator bounds from `E≤6L` and `D(H+1)≤6L²`, and expose the corresponding
  source-facing expanded majorant. Extract all four diagonal bounds and the
  inverse-scale term as sixteenth roots, rewrite them as exact real `1/16`
  powers, and expose the resulting source-facing five-term majorant. Define the
  floor-rounded canonical range `floor((2U)^(-1/4))`, prove that it discharges
  the exact upper-smallness condition, and instantiate both root and rpow
  source estimates at that range. Delete every integer start whose `4H+1`
  forward window can meet a critical set, prove the expanded deletion count,
  fill each order's bad-start holes by its interval hull, prove that its two
  endpoints suffice as cuts, derive the sharp `2*orders.card+1` component
  multiplier and real expanded-interval regularity on each surviving component,
  and assemble the global Weyl bound with trivial handling of components
  shorter than `H`. Preserve the generalized harmonic factors via successive
  Cauchy--Schwarz, prove the sharp four-round product bound
  `H^11 * harmonic(H)^4` and terminal bound
  `(6L)^15 * harmonic(H)^4 / (H+1)^4 / scale`, generalize the global theorem to
  every upper-small range, and instantiate it at the automatically fitting
  adaptive range `min(L, floor((2U)^(-1/4)))`, including the source-readable
  `harmonic(H) <= 1 + log H` specialization. Combine both adaptive branches
  through `(H+1)^(-4) <= 2U+(L+1)^(-4)`, propagate this into an effective
  global majorant, and fix the critical width to the `1/128` power of the
  complete effective error scale `2U+(L+1)^(-4)+1/F`. Normalize this exactly
  to `240(5+j)^5 F/X^5+(L+1)^(-4)+1/F` and bound it by the explicit
  derivative-order factor times the source-shaped three-term error.
  Refine the differencing range to `min(floor(L*q), canonicalRange)`, prove it
  preserves upper-smallness, bound its cast and expanded margin by `Lq` and
  `4Lq+1`, bound its harmonic logarithm by `log L`, and substitute these bounds
  into the global component theorem. Prove
  `(H+1)^(-4) <= 2U+(Lq)^(-4)` for this range and propagate it through the
  optimized terminal root. Extract the four diagonal roots into `72Lq`, bound
  the terminal root by `100((5+j)^5+1)(1+log L)Xq`, combine these into the
  fixed-power optimized majorant, and propagate it through both the global
  component theorem and its explicit source-normalized `1/128`-power wrapper.
  Absorb the additive endpoint constant to obtain one explicit coefficient
  times `X` and the same source power.
- [x] Remove the Weyl interval-length term under `F≤X^4` by an exact
  short/long dichotomy, obtaining the arbitrary-subinterval two-term width
  `(F/X^5+1/F)^(1/1024)`.
- [x] In the `N=M` specialization, prove the transformed Type II phase-scale
  lower bound in natural distance, dominate the Weyl width by the fixed
  distance kernel plus `E^(1/1024)`, uniformize the interval logarithm by the
  outer block length, and propagate the result through the endpoint-free exact
  Vaughan double-block squared-sum reduction.
- [x] Discharge the pairwise Type II `F'/K^5≤E` premise uniformly on each
  inner short block, using its literal left endpoint as the reciprocal support
  scale and its chosen length as the distance bound; expose the resulting
  `typeIIShortIntervalScaleError` in the full double-block theorem.
- [x] In the final quadratic specialization, derive the correlation interval's
  endpoint membership, expanded upper endpoint, and power-evaluation condition
  from the literal outer-block left endpoint and one expansion-margin bound.
- [x] Derive the transformed low-scale condition `F'≤K^4` from the uniform
  short-block comparison `typeIIShortIntervalScaleError≤1/K`, eliminating the
  remaining pairwise scale family from the quadratic interface.
- [x] Bound the quadratic short-block scale error by the explicit monomial
  `5q|N|/(K^6R^2)` and derive `E≤1/K` from `5q|N|≤K^5R^2` as the intermediate
  block-error comparison.
- [x] Derive that monomial condition from the source-shaped low-frequency
  inequality `10qF≤K^4R`, and expose only the source-scale inequality in the
  canonical dyadic Vaughan theorem.
- [x] On inner dyadic bands above the subdivision budget, derive
  `10qF≤K^4R` from the literal logarithmic width and
  `10F≤K^4(log Bcap)^100`; expose this cleaner frequency bound in the
  canonical theorem.
- [x] Close inner bands below the Vaughan subdivision budget: prove their
  block length is at most one, erase every off-diagonal support exactly, and
  obtain the canonical diagonal bound `qouter·L²` without phase hypotheses.
- [x] Derive the canonical `F≥1` condition internally from the source lower
  split `(log Bcap)^d≤F`, using `0≤d` and `2≤log Bcap`.
- [x] Factor the near/far Type II summation through a common theorem accepting
  an arbitrary far-pair correlation estimate, so the source's pairwise
  Weyl/Vinogradov scale split can share the exact kernel aggregation layer.
- [x] Implement that pairwise split in generic and canonical quadratic Type II
  theorems: prove `F'≤K^4` by four-step Weyl with a pair-local error budget and
  expose only the complementary `K^4<F'` correlation bound as analytic input.
- [x] Separate the two analytic remainders in the common aggregation and both
  hybrid endpoints: low-scale Weyl contributes `E^(1/1024)`, while the
  high-scale callback contributes an independent nonnegative error `V`.
- [x] Prove that `exp(-c(log P)^ρ)`, even after multiplication by an arbitrary
  real power of `log P`, eventually beats every requested logarithmic saving
  whenever `c,ρ>0`.
- [x] Convert the source parameter growth
  `log F≤C(log P)^(3/2-ε)` into the explicit Vinogradov exponent lower bound
  `C⁻²(log P)^(2ε)` and combine it uniformly with that logarithmic absorption.
- [x] Derive that logarithmic parameter bound from the primitive source form
  `F≤C exp((log P)^(3/2-ε))`, preserving the hidden multiplier as an explicit
  positive adjusted constant.
- [x] Package the complete regular-component derivative window for every
  `1≤r≤R`, and discharge its coefficient conditions from the literal source
  choices `α=(log P)^(4A)` and `q=(log P)^(-3A)`.
- [x] Prove Vinogradov's numerical side condition
  `log α·(log F)^2/(log X)^3<10^-3` eventually from the primitive source
  parameter bound and `log X≥c log P`.
- [x] Define the literal derivative cutoff `R=10⌈log F/log X⌉+1`, prove the
  shifted source budget `R+j≤log P` eventually for
  `j≤(log P)^(1/2)`, and assemble the full source-cutoff derivative window on
  every regular interval in `Tao2026.Vinogradov`.
- [x] Propagate a local Vinogradov inequality whose only analytic hypothesis is
  that source-cutoff derivative window through the global regular-component
  decomposition, with explicit component and critical-deletion costs.
- [x] State the exact absolute-constant Vinogradov exponential-sum proposition,
  including `X≥2`, `F≥X^4`, the `10^-3` hypothesis, and the source `2^-18`
  decay exponent, and prove that it supplies the complete global
  reciprocal-phase estimate.
- [x] Prove that dyadic Type II correlations preserve the source exponential
  parameter class, with multiplier `1+j·2^(j-1)` and canonical quadratic loss
  exactly `5`.
- [x] Generalize the endpoint-free Type II kernel and Weyl propagation from
  artificial `[1,B]` blocks to arbitrary positive short-block endpoints, and
  specialize the result to the exact named dyadic blocks in the canonical
  Vaughan double family.
- [x] Compress the pairwise effective-error conditions to the single explicit
  `typeIIShortIntervalEffectiveErrorBound≤1`; prove the optimized range is
  controlled by its `1/128` power and derive the expansion margin from
  `5q≤K`. Prove `5q≤K` for Vaughan bands above the subdivision budget from the
  existing `log(B)^{-100}` width estimate.
- [x] Replace the over-strong uniform inverse-scale premise by the source
  distance split. For `distance·F/B≤3`, absorb the trivial correlation through
  the kernel lower bound `1/4`; for farther pairs, prove reciprocal transformed
  scale `≤2/3` and combine it with a `1/4` upper-scale budget.
- [x] Derive the far-pair `1/4` upper-scale budget from `E≤1/K` and the fixed
  eventual threshold `vaughanShortIntervalBudget Bcap≥4·(240·7^5)`, which
  bounds every large-band outer endpoint and removes the redundant second
  monomial hypothesis from the canonical theorem.
- [x] Prove that the standing assumption `2≤log Bcap` already implies that
  Vaughan-budget threshold, removing it from the canonical theorem interface.
- [x] Replace the retained global low-branch block error by the intrinsic
  `(1/K)^(1/1024)` consequence of `F'≤K^4`, propagate it through arbitrary
  blocks and canonical Vaughan blocks, and remove the former upper
  source-scale hypothesis from the mixed Weyl--Vinogradov theorem.
- [x] Rewrite each actual high transformed-scale Type II correlation to its
  ceiling-divided quotient interval and prove its explicit global estimate
  from `VinogradovExponentialSumEstimate`, including critical deletion.
- [x] Package the eventual logarithmic, amplitude, degree-two cutoff, and
  `10^-3` conditions directly from the primitive transformed-scale bound.
- [x] Bound the exact component/deletion multiplicities by `log P` and absorb
  the complete normalized Vinogradov envelope into `3(log P)^(-T)`, including
  both deletion terms, under the explicit budget `T+2≤3A`.
- [x] Preserve the single absolute Vinogradov constant through the global and
  Type II consumers, convert the saving to the exact hybrid callback
  `Q(4·kernel+3(log P)^(-T))`, and discharge the transformed pair-scale upper
  bound from canonical Vaughan inner-block membership with factor `5`.
- [x] Feed that callback into the canonical intrinsic-error Vaughan
  double-block theorem, eliminating its abstract `hhigh` premise and proving
  the complete mixed Weyl--Vinogradov squared-inner-sum estimate conditional
  only on `VinogradovExponentialSumEstimate` and the source parameter bounds.
- [x] Rewrite the literal product-restricted Vaughan Type II double block as
  the exact Type II outer sum, prove the Cauchy--Schwarz bridge to its squared
  inner sums, and show that bounded product support can be enlarged exactly to
  the canonical Vaughan inner block.
- [x] Insert the actual source beta/gamma coefficients into that bridge using
  the sharp outer bound `1` and the blockwise inner bound `log(2B)`, then
  compose it with the mixed Weyl--Vinogradov theorem to bound the norm square
  of the literal source Type II double block.
- [x] Reassemble arbitrary Vaughan double-block square bounds into a bound for
  the full product convolution norm by the exact sum of square roots.
- [x] Formalize the Taylor front end of the pinned Vinogradov proof: use
  pointwise neighborhood smoothness, identify Tao's ordinary-derivative
  polynomial `F_n(q)`, prove the Lagrange remainder and factorial cancellation,
  and include the exact finite-interval shift boundary term.
- [x] Formalize the product-multiset averaging reduction with multiplicities:
  prove cardinality `V²`, sum all shift errors into a uniform envelope, and
  cancel the unnormalized average so a `V²`-normalized polynomial-pair-sum
  estimate transfers directly to the original exponential sum. Cover intervals
  shorter than a shift and specialize `V=⌊X^(1/4)⌋` to the source's `√X` plus
  normalized top-derivative remainder.
- [x] Prove both numerical factors in the source Taylor-error display are at
  most one, absorb `√X+2π` into nine copies of the target decay scale, and show
  that the exact residual polynomial-pair estimate implies the full named
  Vinogradov proposition.
- [x] Decompose the interval pair sum into complete local product sums and a
  right-boundary strip bounded exactly by `V⁴`; rewrite each local sum as the
  generic coefficient-only bilinear polynomial sum after removing its unit
  constant phase.
- [x] Prove the generic trivial `V²` bound and use it to close the branch where
  the requested normalized majorant is at least one. Propagate the remaining
  nontrivial coefficient-only estimate through the local, pair-sum, and full
  Vinogradov interfaces with an explicit total constant shift of eighteen.
- [x] Convert the derivative window to exact logarithmic coefficient bounds;
  control cubic distortion in the nontrivial branch; and prove that the block
  `[(4/3)(log F/log X),(7/4)(log F/log X)]` supplies at least `R/128` medium
  coefficients with `c₀=1/128`, including floor and ceiling effects.
- [x] Formalize both Hölder steps in the bilinear mean-value argument; define
  the representation function; prove `∑ν=V^ℓ`, `∑ν²=J`, and the exact
  equal-power-sum solution interpretation; derive the unnormalized equation
  (16); and prove the signed difference support has total multiplicity
  `(V^ℓ)²` and lies in `|d_j|≤ℓV^(j+1)`. Expand the linearized even
  moment, prove every difference multiplicity satisfies `μ(d)≤J`, regroup
  exactly by differences, derive equation (18), enlarge both variables to the
  full symmetric box, and factor the double phase sum by coordinates.
- [ ] Prove the remaining Theorem 2.5 analytic chain: the named high-scale
  Vinogradov proposition (now reduced exactly to
  `VinogradovBilinearPolynomialNontrivialEstimate`; the geometric-series,
  separated-fiber, harmonic integral-test, explicit coordinate bounds,
  normalized medium-coordinate saving, fixed-power scalar reduction, exact
  medium-degree product reindexing, quadratic degree-sum estimate, and source
  initial product bound `V^(-R^2/307200)` in Lemma 12 now compiles; its scalar-growth
  hypothesis is discharged, the native frozen Wooley VMVT is proved, and its
  Ford moment is exactly bridged to the local count; the squared-box product
  `(3ℓ)^(2R)V^(R(R+1))`, exact critical exponent cancellation, real-power
  normalization, and abstract bound
  `|B|^(2ℓ²) ≤ C² A V^(4ℓ²+2ε-δ)` now compiles; the sharper `c₀=1/4` block has
  floor-rounded weight `R²/193`, the `1/1024` envelope gives
  `V^(-255R²/197632)`, and `ε=δ/128` is propagated through the exact critical
  root; its exponent dominates `4·2⁻¹⁸/s²`, and the floor-rounded `V` power is
  converted to twice the exact source decay. The native Section-12 coefficient
  is now exposed as `C·(p^(B₀+1)κ_R)^ε`, and a rooted bound for this expression
  is proved sufficient for the existing coefficient contract; native existence
  of all data except that uniform inequality is audited. The alternative
  supercritical Ford moment `3R+⌊R/5⌋` is quantitative but loses the required
  decay after its larger root. The maximal multiplier `4R` is now available
  for `R≥10000`; its loss is `3R²/8000`, equation (18) is proved at arbitrary
  supercritical moment, and the resulting positive power saving has a uniform
  absolute coefficient after the `32R⁴` root. Its normalized saving still
  falls short of the fixed `2^-18` source target, so it does not remove the
  critical-moment residual. All native critical constants for `40≤R<1000`
  are now combined into one finite envelope, and the global coefficient
  contract plus its bilinear consumer are derived from a rooted hypothesis only
  for `R≥1000`. The supremal optimal coefficient is proved both to be a valid
  witness and to lie below every witness, so this contract is equivalent to
  scalar boundedness of its rooted sequence. Retained Wooley concentration
  data bound the optimum by the exact Section-12 coefficient. Thus only the
  uniform infinite-degree bound for that explicit expression remains here;
  its prime is already constrained by Bertrand to `R<p≤2R`, leaving only `C`
  and `B₀` growth uncontrolled. The coordinate-box root is in `[1,3]`, and
  the coefficient-only root condition is sufficient for the final bilinear
  consumer; this root equals `C_R^(1/κ_R²)`, so its bound by `A` is equivalent
  to `C_R≤A^(κ_R²)`. The remaining p-adic condition is exactly
  `C·(p^(B₀+1)κ_R)^ε≤A^(κ_R²)`, with a direct final consumer) and
  the uniform source-scale simplification and quantitative Type I/II estimates.
  The finite all-block regime split and exact family summation are complete. The
  conditional high-scale estimate is already inserted through the actual
  source Type II double blocks. Its full
  conditional uniform logarithmic consequence is now proved. The source lower split already supplies
  `F≥1`. The canonical Vaughan coefficient
  envelopes and their support cutoffs are now proved. The
  two-dimensional slice/Fubini assembly, directional bounds, radial arithmetic,
  automatic smooth-periodic derivative chains, and unconditional `taoC3Norm`
  coefficient estimate are now proved. Identification of the summable
  Fourier series with the original periodic weight is now proved. The
  compiled contract and exact weighted
  Vaughan identity are not proof of this estimate.
- [x] Prove Lemma 3.1's subexponential bound
  `H ≤ exp(log^(2/3+o(1)) N)` from Theorem 2.5.
  - [x] Prove that a prime `H<p≤2H` dividing an element of a very bad
    interval has its square dividing that same element.
  - [x] Formalize the exact forbidden fractional-part rectangle
    `{N/p}≥0.9`, `{N/p²}<0.9` and prove that it produces a nonsquare prime
    divisor in the interval.
  - [x] Prove the supported prime sum vanishes and instantiate the specialized
    Theorem 2.5 contract to obtain the source integral upper bound.
  - [x] Construct an explicit nonzero `C∞`, `ℤ²`-periodic, nonnegative cutoff
    supported in the forbidden rectangle and specialize the integral upper
    bound to it.
  - [x] Convert `H>exp((log N)^(2/3+η))` to the exact Theorem 2.5 parameter
    bound with `ε25=3/2-(2/3+η)⁻¹` and multiplier `K=1`.
  - [x] Prove the cutoff has a fixed positive minimum on the inner rectangle,
    the integral is real and nonnegative, and reduce its norm lower bound to
    the measure of the explicit inner prime-scale good set.
  - [x] Formalize both source changes of variables, including the exact
    reciprocal and square Jacobians and their quantitative measure comparisons.
  - [x] Prove the periodic quadratic-slice lower bound uniformly for
    `N/H²≥1/2`; in particular the quadratic reciprocal set has measure at
    least `H/32`.
  - [x] Prove the unit-cell slow-variation estimate: for `H≥200`, meeting the
    narrower quadratic band forces the entire cell into the enlarged band.
  - [x] Complete the finite unit-cell measure comparison inserting
    `{s}∈[0.91,0.99]`; after endpoint trimming and the reciprocal Jacobian,
    obtain inner prime-scale measure at least `H/400` for `H≥200`.
  - [x] Convert the Sylvester--Schur large-prime conclusion to the exact source
    scale `N/H²≥1/2`, and discharge the eventual `H≥200` threshold from
    contradiction growth.
  - [x] State the standard binomial Sylvester--Schur contract and prove its
    exact bridge to the consecutive-product contract used by Lemma 3.1.
  - [x] Avoid the stronger unrestricted contract by proving the sufficient
    eventual quadratic-window large-prime theorem from the frozen PNT and
    exact binomial bounds; promote it to eventual `N/H²≥1/2` and `H/400`.
  - [x] Remove the unused quadratic-window hypothesis from the binomial proof
    and obtain Sylvester--Schur uniformly for every start at all sufficiently
    large interval lengths.
  - [x] Prove start monotonicity of the binomial envelope, verify the explicit
    fixed-length threshold `H^H+1`, and reduce the unrestricted contract to a
    genuinely finite bounded rectangle in `(H,N)`.
  - [x] Choose the cutoff and Theorem 2.5 constants outside the eventual
    quantifiers, prove the two-logarithm gap, and package the full eventual
    contradiction conditional on `TaoTheorem25SpecializedConclusion`.
  - [x] Package the positive-start `H<N` clause and every fixed-slack
    subexponential bound into `TaoLemma31Conclusion`, and derive it from both
    the specialized and full Theorem 2.5 contracts.
  - [ ] Optional strengthening: prove the unrestricted exact
    `SylvesterSchurConclusion` prime-factor contract.
- [x] Build Lemma 3.2's canonical exponent-one/powerful-core factorization;
  prove its coefficient squarefree, supported on primes `≤H`, and dividing
  `H!`, and derive the exact two-position relation `an+h=bm`.
- [x] Complete Lemma 3.2's averaging step selecting two distinct positions
  whose coefficients are each `H^O(1)`.
- [x] Encode every bounded nontrivial very-bad interval injectively by its
  chosen Lemma 3.2 certificate, interval length, and selected-element offset.
- [x] Turn Lemma 3.1 into a uniform subpolynomial natural length budget and
  Lemma 3.2 into a uniform subpolynomial natural coefficient budget.
- [x] Bound the complete finite certificate family by `A²G` uniform
  Corollary 2.11 fibers and close the nontrivial `x^(2/5+o(1))` count.
- [x] Prove the full literal Theorem 1.8 endpoint conditional only on the
  specialized (and hence also the full) Theorem 2.5 contract.
- [x] Prove and audit a uniform fixed-power bound below one for the frozen
  dyadic Gafni--Tao discrepancy exceptional measures when `2/15 < θ < 1`.
- [x] Formalize the literal closed prime-free endpoint set and its measurable
  variable-length dyadic counterpart.
- [x] Control the full higher-prime-power tail and transfer the discrepancy
  estimate to a fixed-power bound for the genuine dyadic prime-free measure.
- [x] Assemble the dyadic estimates into Tao's constant-length `[0,x]`
  exceptional-measure statement and prove the full `theta > 2/15` range of
  Proposition 2.3(iii).
- [x] Prove Proposition 2.3(i) with Tao's `N/2 < p <= N` endpoints from
  Mathlib's Bertrand theorem.
- [x] Prove the exact unique `n=p²m` characterization of `B¹` and the finite
  identity `#(B¹∩[1,x]) = ∑_{p≤√x} Ψ(⌊x/p²⌋,p)`.
- [x] Begin the Section 6 branch with the exact arithmetic core of Lemma 6.1.
  Define admissible bad intervals through a literal dyadic-window witness;
  prove unconditionally that every non-singleton bad interval has `H≤N`;
  and, from the isolated Sylvester--Schur contract, prove that its largest
  prime `p₀` exceeds `H`, that one interval element is `p₀²m` with
  `m` `p₀`-smooth, and that every interval element is `p₀`-smooth.
  Prove unconditionally that every interval element is nonprime, and record
  the exact rounded dyadic bounds `N<x≤4N+1` and `p₀²m≤2x`.
- [x] Formalize the valid exact core of Lemma 6.2. Choose the source's largest
  power of two below `(H+3)/2`; prove `2≤H'≤H<4H'`; retain a contained bad
  subinterval with `p₀²m` as an endpoint and the same largest prime; and record
  the exact replacement scale bounds `x≤4N'+1` and `N'+H'≤2x`. Do not assume
  the paper's unsupported claim that containment preserves intersection with
  the identical dyadic window `[x/2,x]`; the later maximal-function transfer
  must use the proved comparable-scale formulation.
- [x] Put the post-Lemma-6.2 maximal reduction into exact finite form. Define
  the bounded admissible and comparable-scale normalized index families and
  their unions; prove the parent lies in the four-length enlargement of its
  normalized child; and prove every admissible-union point has a witnessing
  enlarged interval with normalized-union lattice density at least `1/10`.
- [x] Prove the finite one-dimensional weak-`(1,1)` interval covering
  inequality by greedy maximal-length selection and disjoint threefold
  enlargements. Deduce the exact cardinality comparison
  `#admissibleUnion≤30·#normalizedUnion`.
- [x] Formalize Definitions 6.3--6.4 with explicit finite cutoffs for the
  source's slowly varying prime windows. Encode the ordered 1000-prime
  anatomy, smooth remainder, the exact typical/non-typical dichotomy, the
  consequence `p₀<squareThreshold`, and the displayed bound
  `m'≤2x/(p₀²p₁⋯p₁₀₀₀)`.
- [x] Close the finite covering/counting reduction for failure of typicality
  condition (ii). Every short comparable-scale interval containing `d² | j`
  with `d≥D` lies in an explicit neighborhood union of cardinality at most
  `(2L+1)∑_{D≤d≤2x}⌊2x/d²⌋`. Prove the sharp telescoping estimate
  `∑d⁻²≤1/(D-1)` and hence the closed real bound
  `#exceptional≤(2L+1)(2x)/(D-1)`.
- [x] Substitute the literal source cutoffs
  `L=⌈(log x)^20⌉₊` and `D=⌈z(x)^3⌉₊`. Prove `z(x)→∞`, absorb
  `(log x)^20+1≤2√z(x)` eventually, and obtain the explicit estimate
  `#exceptional≤24x/z(x)^(5/2)`. Define the actual finite union of short
  normalized intervals failing (ii), prove it lies in this cover, and package
  its cardinality as the weak
  `x/z(x)^(2+δ)` alternative with `δ=1/2`. The other Proposition 6.5
  failure branches remain open.
- [x] Build the exact finite large-sieve layer for failure of condition (i).
  Prove that the `H` classes `-1,…,-H` are distinct modulo every
  `p₀<p≤2p₀`; use normalized-interval smoothness to show every actual start
  avoids them; package the restrictions into the tensor sieve; and apply the
  loss-free global Corollary 2.9 machinery. For each fixed `(p₀,H)` fiber the
  actual interval union now satisfies the explicit compiled weighted bound
  `W(p₀,H,k)^k #union ≤ H·8(2x+1)`. The maximal degree for this ambient-start
  sieve and its eventual PNT range are compiled. Separately define Tao's
  literal cofactor budget `2x/p₀²` and floor-defined `k`, proving exact
  conditional positivity, product, and prime-cardinality constraints. Transfer
  both endpoint orientations to `H` distinct affine restrictions on `m`, prove
  smoothness avoidance, preserve the tensor ratio, apply global Corollary 2.9
  on the cofactor range, and recombine both interval covers. This gives the
  source-faithful fixed-fiber bound with explicit factor `16`. Asymptotic
  optimization now also extracts the exact base `H/(8k log(2p₀))` from the
  PNT count and proves that the source comparison
  `8k log(2p₀)≤H^(1/10)` yields the canonical `H^(0.9k)`-weighted bound.
  Prove floor maximality in the strict next-power form, expand the quotient
  budget to `2x<(2p₀)^(2k+4)`, and derive
  `log(2x)/log(2p₀)<2k+4`. The paper's quarter comparison is encoded on its
  valid finite range `k≥4`; it is false for `k=2,3`. Under
  `8k log(2p₀)≤H^(3/50)`, absorb the leading `H` and obtain both the exact
  `16(⌊2x/p₀²⌋+1)H^(-0.9(k-1))` fiber bound and its canonical exponential
  consequence. Prove that `8k log(2p₀)≤4log(⌊2x/p₀²⌋+1)`, and that the literal
  long cutoff eventually makes this at most `H^(3/50)`, uniformly in `p₀`.
  For the complementary `k<4` branch, derive `2x<(2p₀)^10`; combine the
  unsieved two-orientation cofactor cover with `p₀²≤2x` to obtain the uniform
  fiber saving `4096x^(9/10)`. Perform the exact AM--GM saddle in `p₀`: under
  the literal long cutoff its numerator is at least
  `(9/2)log x log₂x`, and exponentiation gives the canonical `k≥4` estimate
  `#fiber≤128x/(p₀z(x)^6)` eventually. Repair the source's `k=2,3` gap with
  the valid eighth-comparison for all `k≥2`; the adjusted `22/25` absorption
  and saddle give `#fiber≤128x/(p₀z(x)^4)`. On the exact upper source range
  `p₀^20≤x^3`, prove degree two eventually, extract `p₀²≤2x` from every
  nonempty normalized fiber, and discharge the PNT and large-budget
  conditions from `⌈(log x)^20⌉≤H<p₀`. Sum the exact finite dyadic `H` and
  moderate-prime `p₀` fibers, bound the reciprocal-prime sum by the harmonic
  number, absorb both logarithmic losses by one `z(x)`, and prove the actual
  long moderate-prime failure-union estimate `#union≤x/z(x)^3` eventually.
- [x] Formalize Tao's preliminary large-`p₀` disposal under the exact
  ceiling-rounded `H<x^(7/50)` range. Bridge `H^50<x^7` and `p₀^20>x^3` to
  the finite length and prime cutoffs, sum the unsieved `8Hx/p₀²` fixed-fiber
  estimate over dyadic lengths and the reciprocal-square tail, and prove the
  actual normalized failure-union bound `#union≤x^(199/200)` eventually.
- [x] Formalize Tao's preliminary large-`H` disposal on the exact
  `H≥x^(7/50)` range. Use the fixed exponent `41/300∈(2/15,7/50)`, prove its
  prime-gap length at scale `2x` is eventually at most `H/2`, select a
  disjoint finite interval family across all lengths, embed its real start
  segments in the literal Proposition 2.3(iii) endpoint set, prove
  `#union≤6 primeFreeEndpointMeasure(2x,41/300)`, and deduce an existential
  fixed power saving for the actual normalized failure union.
- [x] Formalize Tao's small-`p₀` smooth-number disposal. Define the actual
  normalized index family admitting distinguished data with `p₀≤y`, prove
  its interval union is contained in the `y`-smooth naturals up to `2x`, and
  reduce its cardinality exactly to `Ψ(2x,y)`. Define the natural cutoff
  `⌊z(x)^β⌋`, prove flooring preserves both divergence and the logarithmic
  critical exponent, and apply Proposition 2.1(i) to obtain
  `#union≤2x/z(x)^(1/β-ε)` eventually. Record the explicit acceptable source
  specialization `β=2/5`, `ε=1/10`, giving `2x/z(x)^(12/5)`.
- [x] Build the exact smooth-cofactor cover for the later Proposition 6.5
  prime bands. Cover each fixed `(p₀,H)` normalized fiber by the two possible
  square-endpoint orientations over cofactors `m≤⌊2x/p₀²⌋`, retain literal
  `p₀`-smoothness, and prove
  `#fiber≤2H Ψ(⌊2x/p₀²⌋,p₀)` before exponent-band aggregation.
- [x] Aggregate the actual short normalized smooth-prime union over all
  literal dyadic lengths and a concrete 60-cell exponent grid. Prove every
  retained cell from exponent `6/5` through `2` has
  `a+1/b≥2+1/100`, handle exponents `2` through `3` in one final band, and
  sum the resulting smooth-cofactor counts with exponent `2+1/200`. Prove
  arbitrary logarithmic length costs are absorbed by `z^(1/400)`, prove
  eventual monotonicity under `x↦2x`, and obtain the actual source-scale
  weak bound `#union≤x/z(x)^(2+1/800)`.
- [x] Prove `log z(2x)/log z(x)→1`, transfer
  `⌈z(2x)^(6/5)⌉≤⌈z(x)^(5/4)⌉`, and prove that the literal source
  prime range `z(x)^(5/4)<p₀≤⌈z(x)^3⌉` is covered by the 60-cell
  range. Deduce `#union≤x/z(x)^(2+1/800)` for that source-defined actual union.
- [x] Construct condition (iii) from multiplicity-counted prime factors:
  whenever a `p₀`-smooth cofactor has at least 1000 factors above the lower
  cutoff, select its 1000 largest factors in nonincreasing order and prove
  the remainder is smooth below the last. Thus failure of condition (iii),
  after the short and square branches are excluded, implies fewer than 1000
  such factors.
- [x] Package the deficient branch canonically as
  `m=p₁⋯pⱼ m'` with `j<1000`, multiplicities retained, every `pᵢ` between
  the lower cutoff and `p₀`, and `m'` smooth at the lower cutoff. Produce this
  packet directly from any remaining non-typical normalized interval.
- [x] Build the exact finite deficient-cofactor product/remainder cover and
  reduce the actual short, square-avoiding condition-(iii) union to
  `4L ∑_{p₀}∑_a Ψ((2x/p₀²)/a,y)`, with `a` a product of fewer than 1000
  admissible large primes.
- [x] Prove the source-strength analytic bound for that deficient-factor sum:
  use `y=⌊z(x)^(9/10)⌋`, diagonalize uniformly over the distinguished prime
  and every factor list, retain `1/(p₀²∏q)`, bound the finite list mass by
  `1000(1+log⌈z(x)^3⌉)^999`, absorb it, and obtain the central-band
  actual-union estimate `#union≤x/z(x)^(2+1/200)` for
  `z(x)^(9/10)<p₀≤z(x)^(11/10)`.
- [x] Close the two fixed outside-central smooth-prime gaps. Use a 600-cell
  mesh and exact `x↦2x` cutoff transfer to cover
  `z(x)^(2/5)<p₀≤z(x)^(9/10)` and
  `z(x)^(11/10)<p₀≤z(x)^(5/4)`, sum the actual short normalized interval
  union, absorb its fixed grid and dyadic-length cost, and prove
  `#union≤x/z(x)^(2+1/1000)` eventually.
- [x] Assemble the complete fixed-cutoff Proposition 6.5 failure union.
  Define the actual non-typical family at lower cutoff `⌊z^(9/10)⌋`, prove
  exhaustive containment in the eight quantified branches, convert the two
  fixed-power estimates via `log z/log x→0`, normalize all branch bounds, and
  obtain `#union≤x/z(x)^(2+1/4000)` eventually.
- [x] Diagonalize the fixed-window Proposition 6.5 estimates to a single
  slowly increasing row selector. For row denominator `d=n+10`, use the exact
  lower floor `⌊z(x)^(1-2/d)⌋` and upper ceiling `⌈z(x)^(1+2/d)⌉`, prove both
  logarithmic cutoff ratios tend to one, cover the moving low, deficient, and
  high prime bands, and obtain the source-facing selected-union bound
  `#union≤x/z(x)^2` eventually.
- [x] Define Proposition 6.6's random choice literally. Use the finite product
  probability measure on `Fin 1001 → ℕ`, put the exact uniform PMF on each
  half-open dyadic prime band `[Pⱼ,2Pⱼ)`, prove every coordinate law and
  almost-sure band membership, and prove mutual independence of all 1001
  coordinate projections. Define the source tuple product, divisibility
  indicators, typical-tuple event, and its probability.
- [x] Prove Proposition 6.6's anti-sieve probability estimate on this product
  space, conditional on explicit analytic Burgess. The exceptional `p∣l`
  contribution is now bounded pointwise by
  `H log H`, then by `H log z(x)` eventually, and its large event has exactly
  zero probability. The small-prime cutoff, `p∤l` index set, fixed moment 50,
  exact ordered-tuple expectation expansion, and primitive CRT fiber are also
  compiled. Exact Dirichlet-character orthogonality now expands and integrates
  each primitive fiber probability. Independence factors its character
  expectation, the coordinate laws give the literal normalized dyadic prime
  averages, and norm bounds plus weak AM--GM reduce it to the all-character
  sum of their 1000th powers. The exact `2^50/lcm` coefficient is proved and
  inserted into the full fiftieth-moment expansion; finite reordering and
  pigeonholing select one of the 1000 tail coordinates. The normalized
  character sum, exact `Z^(-1/125)` exceptional threshold, and primitive
  exceptional/unexceptional partition are compiled. Unexceptional 1000th
  moments contribute at most `φ(q)Z^(-8)`, and exceptional 1000th moments are
  reduced to the squared moment in Lemma 5.1. Scale separation proves exact
  equality with primitive counterparts; the principal term is `1`, and all
  nonprincipal characters are regrouped into exact positive-conductor fibers.
  The resulting ambient moment is bounded by a divisor sum of exceptional
  squares plus `φ(d)Z^(-8)`. That conductor bound is now inserted termwise
  into the ordered tuple expression and, after the factor-1000 coordinate
  pigeonhole, into the full fiftieth moment. The tuple lcm is now exactly the
  product of its distinct prime support; support multiplicities sum to 50 and
  split the coefficient into one `log p/p` per distinct prime plus repeated
  logarithms of exact total exponent `50-#support`. The explicit finite
  weighted-prime estimate is applied pointwise. Every fixed ordered prime tuple
  has at most `H^50` compatible shift tuples, and these fibers can be summed by
  a generic reduction. Exact support regrouping, a uniform `50^50` fiber bound,
  and the elementary-symmetric inequality now sum all ordered-prime equality
  patterns, giving `H^50 O(log(cutoff)^50)`. The conductor sum is split into
  principal, exceptional-square, and totient-error parts. The principal and
  totient-error terms are bounded explicitly, using the totient-divisor
  identity and Chebyshev theta for the latter. The finite weighted
  Bombieri--Halász--Montgomery inequality of Lemma 5.3 is now proved, together
  with Hermitian row-only reduction, exact prime-indicator specialization, the
  diagonal/off-diagonal Gram-row split, normalization by the exact band
  cardinality, and the finite Markov bound with exponent `2/125=0.016`. It
  The maximal admissible conductor family and literal tuple-conductor union
  now apply the conditional Lemma 5.1 uniformly at all 1001 scales;
  conditional on analytic Burgess, both the exceptional sum and totient error
  are absorbed into the principal small-prime majorant. The large-prime
  contribution now has exact mean, second-moment, variance, and covariance
  expansions. Its diagonal is bounded by the mean, and when the prime cutoff
  is at least `H`, distinct shifts with the same prime have empty joint event
  and nonpositive covariance. Single events are now reduced to primitive
  character fibers modulo `p`, and distinct-prime joint events to primitive
  fibers modulo `pp'`, with exact 1000th-moment probability bounds. Aggregate
  Lemma 5.1 now gives the exceptional-prime count with exponent `2/125`; its
  common-factor form, uniform self-improvement, and selector diagonalization
  give the exceptional-`p'` count with one constant uniform in the fixed
  prime `p`. The principal character is now isolated before AM--GM: its exact
  tuple expectation is a coprimality probability, and its one-prime and
  two-prime deficits are bounded by coordinate-collision union bounds with
  reciprocal band-cardinality costs. For a prime modulus, every nonprincipal
  character is now proved primitive; outside the coordinate-wise exceptional
  union, the full nonprincipal moment is bounded by
  `φ(p) ∑_{j≠0} P_j^(-8)` and inserted into the direct deviation from
  `1/φ(p)`. For `pp'`, the exact conductor regrouping and totient-error sum are
  also complete under band separation, giving `pp' ∑_{j≠0} P_j^(-8)` and the
  corresponding direct deviation theorem. The separation hypothesis is now
  removed: the ambient-to-primitive difference is supported on at most
  `{p,p'}`, costs at most `4/card`, and contributes an explicit
  `(4/card)^1000` correction after convexity. The Burgess-conditional dyadic
  summation for Propositions 6.7--6.8 is complete. Exact moment-50 Markov and
  variance Chebyshev bounds give the source-shaped small- and large-prime
  tails. The exact logarithmic partition of every squarefree shift component,
  together with square avoidance and the one-eighth scalar gap, puts the
  typical event in their three-branch union. The final compiled estimate is
  `Pr(typical) ≤ B(8 log₂(x))^50/(H log(z)^2)` eventually. Thus probability
  normalization is closed conditional on explicit Burgess; proving analytic
  Burgess remains. The first crude-counting primitive is complete: a residue
  class modulo `q>0` contains at most `⌊2Z/q⌋+1` primes of `[Z,2Z)`.
  The tuple law is now exactly a uniform finite Cartesian law: its support has
  measure one, supported singleton masses are computed, and every event is
  converted to its supported tuple count times the common atom mass.
  Coordinate freezing is also complete as a finite probability bridge: the
  frozen-support cardinality cancels exactly, pairwise residue rigidity gives
  the `⌊2P/q⌋+1` bound, and factoring the source product proves single- and
  joint-divisibility crude bounds after splitting noncoprime source products
  into the already-controlled coordinate-collision unions. The final costs are
  respectively one and two explicit collision sums.
- [x] Put Proposition 6.6 in the quantifier order required by the source tuple
  sum. Choose one Burgess-dependent constant before the eventual ambient
  scale, then prove the estimate simultaneously for every positive
  `H≤taoTypicalLengthCutoff x` and every remainder `m'`. Define the finite
  typical support, prove its probability is exactly its cardinality divided by
  the product of all band cardinalities, and export the corresponding uniform
  cardinality bound. The remaining Theorem 1.7 typical-counting step is the
  finite summation and bounded-representation layer.
- [x] Sum the uniform Proposition 6.6 tuple bound at fixed prime scales. Define
  the exact budget `2x/(P₀²P₁⋯P₁₀₀₀)` and smooth cutoff `2P₁₀₀₀`, identify the
  remainder-family cardinality with `Psi`, and form the dependent tuple sigma
  family. Sum all power-of-two lengths and use `Σ 2⁻ʳ≤2`, with no logarithmic
  loss. Evaluate every counted tuple into the literal `B¹∩[1,2x]`, bound the
  distinct image by `badOneTermCount (2x)`, and reduce the full domain count to
  a uniform evaluation-fiber bound.
- [x] Assemble every ordered 1001-coordinate prime-scale choice. Construct the
  moving slow dyadic grid, compare original bands with Tao's enlarged bands,
  and prove the fixed and global evaluation-fiber bounds `≤1000^1000` by
  recovering the canonical 1000 largest prime factors. Sum the simultaneous
  Proposition 6.6 estimates, absorb the PNT band loss `8^1001` into an explicit
  factor tending to zero, and obtain a little-o bound relative to
  `badOneTermCount` at one fixed dilation, conditional on Burgess.
- [x] Upgrade the all-scale tuple estimate to the interval-length-weighted
  count. Cancel each weight `2^r` against Proposition 6.6's `1/2^r`, bound the
  number of dyadic length exponents by `50 iteratedLog x`, prove the weighted
  assembly factor tends to zero, and obtain weighted little-o at the same fixed
  dilation, conditional on Burgess.
- [x] Bridge actual forward typical normalized intervals into the weighted
  global tuple family. Choose canonical prime/cofactor/anatomy data, prove the
  tuple start is exactly `N+1` and its length is exactly `H`, prove the code is
  injective, and deduce little-o for the actual forward interval union. Define
  the full and backward unions and prove the exact forward/backward cover.
- [x] Prove the backward/right-endpoint `N+H` branch using the symmetric `v-l`
  anti-sieve. Reflect the small-prime moment and the exact large-prime
  mean/covariance/variance bounds, close Markov--Chebyshev normalization and
  the uniform support count, assemble the length-weighted family, and encode
  every actual backward interval injectively by its right endpoint and length.
  Combine both orientations to obtain little-o for the full typical union at
  the same fixed dilation, conditional on explicit Burgess.
- [x] Retain an explicit `1/log(x)^(1-o(1))` saving through the Proposition
  6.5 slow diagonal, normalize it by the actual `badOneTermCount x`, and
  recombine it with the quantitative full typical-union estimate. Use the
  eventual admissible-scale large-prime theorem and Lemma 1.6(ii), then apply
  the exact factor-`30` maximal transfer to obtain the corresponding local
  dyadic-window bad-interval bound conditional on explicit Burgess.
- [x] Isolate the exact adjacent-scale regular-variation input
  `badOneTermCount(2^r)/badOneTermCount(2^(r+1)) -> 1/2`, prove that it survives
  every fixed logarithmic weight and yields a geometric finite-tail bound,
  absorb the early scales, and sum the exact power-of-two cover without losing
  the logarithmic saving. This gives both clauses of `TaoTheorem17Conclusion`
  conditional on that ratio, analytic Burgess, and Lemma 1.6(ii); unrestricted
  Sylvester--Schur is eliminated by the eventual scale-local bridge.
- [x] Derive the adjacent-dyadic `badOneTermCount` ratio from the sharp
  critical smooth-number dilation limit. Partition the exact one-term sum
  into a slowly widening central prime band and four complementary ranges,
  prove the complement is `o(B¹(x))`, uniformize dilation by `1/2` across the
  central packet, and squeeze
  `badOneTermCount(x/2)/badOneTermCount(x) -> 1/2`. Composition at
  `x=2^(r+1)` gives the exact adjacent ratio. The required dilation limit is
  itself derived from `TaoCriticalSmoothSaddleAsymptoticConclusion`; the
  coarse `x/z^(2+o(1))` bounds alone would not suffice.
- [x] Derive the complete fixed-dilation clause of Lemma 1.6(ii) from the
  same half-ratio. Prove `B¹(x) <= 4 B¹(floor(x/2))`, iterate through every
  fixed power of two, bracket both `floor(cx)` and `x` with power-of-two
  endpoints for arbitrary fixed `c>0`, and assemble both `IsBigO` directions
  with the literal natural-floor convention.
- [x] Prove one start cutoff beyond which Sylvester--Schur holds for every
  positive length, using the uniform large-length tail and the fixed-length
  threshold `H^H+1` on the finitely many remaining lengths.
- [x] Show every sufficiently large admissible dyadic scale lies beyond that
  cutoff, thread the resulting scale-local large-prime witness through
  normalization, maximal transfer, recombination, and dyadic summation, and
  remove unrestricted Sylvester--Schur from the Theorem 1.7 hypotheses.
- [x] Formalize the literal multi-coordinate freezing arguments in
  Propositions 6.7(i) and 6.8(i): prove arbitrary finite frozen-support
  cardinality cancellation, the general product-residue/multiplicity bound,
  multiplicity at most `2` for products of two prime coordinates and at most
  `6` for three, and the resulting exact finite ratios
  `2(⌊4P₁P₂/p⌋+1)/(#B₁#B₂)` and
  `6(⌊8P₁P₂P₃/(pp')⌋+1)/(#B₁#B₂#B₃)`. The nonzero shifts discharge the
  cofactor-coprimality hypotheses. Their common PNT scale instantiation and
  dyadic aggregation remain.
- [x] Normalize the exact crude ratios under the reusable common band contract
  `P_j≤L·#band(P_j)`: absorb `⌊U/q⌋+1` when `q≤U`, cancel two or three
  coordinate scales, and obtain the source-shaped bounds `16L²/p` and
  `96L³/(pp')`. The next item supplies the uniform PNT/anatomy-scale
  instantiation.
- [x] Give `P_j=z^{1+o(1)}` a precise 1001-coordinate sequence contract and
  apply the dyadic PNT uniformly over `Fin 1001`. Prove simultaneous band
  nonemptiness and `P_j≤4log(z)#band(P_j)`, then obtain the explicit eventual
  crude estimates `256log²(z)/p` and `6144log³(z)/(pp')`. The exact
  modulus/product comparisons are retained for the dyadic-scale consumer.
- [x] Transfer the improved prime and product-modulus character estimates to
  the literal divisibility probabilities. Prove the absolute one-prime error,
  retain upper estimates through empty-event branches, and combine the exact
  marginal errors with `φ(pp')=φ(p)φ(p')` to obtain the explicit distinct-prime
  covariance bound. The later adaptive modules complete the finite dyadic
  aggregation.
- [x] Perform the exact finite anti-sieve aggregation: partition the literal
  mean by exceptional prime conductor, partition the ordered distinct-prime
  covariance sum by exceptional pair, retain supplied crude majorants on the
  exceptional pieces, and combine both partitions with the diagonal variance
  reduction. Analytic cardinality and source-scale summation remain.
- [x] Resolve the product exceptional predicate into counted families. Prove
  that the nontrivial divisors of `pp'` are exactly `p`, `p'`, and `pp'`, cover
  every bad pair by the two prime-exceptional sets or the common-factor partner
  set, and bound the union over 1000 coordinate scales by the corresponding
  sum and factor-1000 cardinalities.
- [x] Compile the finite dyadic Proposition 6.7 first-moment block. Identify
  `(R-1,2R-1]` with `[R,2R)`, prove `1/φ(p)≤2/R`, obtain the eventual PNT main
  sum `≤4/log R`, and retain the uniform improved error and exceptional-count
  times crude-bound terms in the exact shift-prime sum.
- [x] Compile the exact finite Proposition 6.8 two-band covariance block.
  Preserve the ordered distinct-prime restriction and literal `(H-1)^2`
  shift multiplicity, charging the improved contribution to the full product
  of dyadic-band cardinalities and the exceptional contribution to its exact
  ordered-pair cardinality times a supplied crude joint bound. The later
  adaptive modules now complete source normalization and dyadic summation.
- [x] Reduce the exact exceptional ordered modulus-pair finset to the three
  source families over any ambient conductor range containing both bands:
  exceptional first endpoints, exceptional second endpoints, and the sum of
  common-factor exceptional-partner fibers. Supply the real-valued uniform
  cardinality interface needed by the eventual Burgess estimates.
- [x] Normalize the literal improved error formulas through their exact three
  coordinate aggregates. Prove simultaneous source envelopes for reciprocal
  band cardinalities, the nonprincipal eighth-power mass, and the 1000th-power
  change-level collision mass from `P_j=z^(1+o(1))` and PNT, and compose them
  into uniform one-prime, joint, and covariance envelopes. Absorb the fixed
  logarithmic powers and prove the direct literal source forms
  `3R^-1.001` and `C R^-1.001 S^-1`, with the latter covering both the joint
  and ordered covariance errors. The adaptive chain below now inserts the
  Burgess cardinalities and completes the dyadic scale sum conditionally.
- [x] Correct the exceptional endpoint count to the modulus scale used by
  Proposition 6.7. Define the adaptive threshold
  `max(P_j^-0.008,R^-0.01)`, prove its character family is contained in the
  fixed exceptional family, apply the uniform Lemma 5.1 squared moment and
  finite Chebyshev, and union the 1000 ordinary coordinates to obtain one
  Burgess-conditional `O(R^0.02)` conductor count.
- [x] Prove the exact squared-moment identity for the common-factor cofactor
  embedding, strengthen it to one eventual moment constant pointwise uniform
  in the fixed prime and cofactor set, and deduce the adaptive
  Burgess-conditional `O(S^0.02)` partner count after the 1000-coordinate
  union.
- [x] Insert adaptive emptiness into the character-moment estimates. Prove
  the exact threshold-power bound by `P_j^-8+R^-10`, derive the adaptive
  one-prime probability error and its `1003R^-1.001` source form, and carry
  the same argument through product conductor fibers and covariance. Record
  the exact mixed pair predicate in which conductor `p` uses `R` and
  conductors `p'`,`pp'` use `S`; prove it is covered by the two adaptive
  endpoint sets plus the adaptive partner set, and derive the mixed product
  moment and literal joint-probability bound.
- [x] Normalize the exact mixed joint and covariance errors to the ordered
  `R^-1.001 S^-1` source power. Insert the adaptive endpoint and mixed-pair
  predicates into the finite one-band probability and two-band covariance
  sums with literal `(H-1)` and `(H-1)^2` multiplicities. Reduce the adaptive
  exceptional-pair finset to the two endpoint counts plus adaptive partner
  fibers.
- [x] Compose the exact adaptive endpoint and partner counts with explicit
  Burgess and insert them, together with the normalized adaptive improved
  errors, into both complete finite block sums. Obtain the exceptional pair
  source shape `R^0.02·#band(S)+#band(R)·S^0.02`.
- [x] Build the exact source dyadic grid, prove disjoint coverage and its
  `4 log z` scale count, uniformize one Burgess constant over every retained
  scale and ordered scale pair, and sum the complete adaptive blocks. On the
  literal source cutoffs this gives `mean ≤ 2000000 H`, distinct-prime
  covariance sum `≤ H`, and `variance ≤ 2000001 H`, conditional on explicit
  Burgess.
- [x] Formalize the finite algebra around Lemma 5.4: the truncated divisor-sum
  weight, exact value `ν(p)=1` for primes above the level when `λ₁=1`, exact
  floor-weighted mass expansion, coefficient `ℓ¹` bound, quantitative error
  `|Σν-XΣλ_d/d|≤R`, and the resulting upper-mass transfer theorem. The analytic
  coefficient construction giving squarefree support, nonnegativity, and
  `O(1/log R)` main mass remains open.
- [x] Instantiate the frozen Selberg upper-bound sieve as an unconditional
  real-valued alternative: prove level and primorial support, `λ₁=1`, the
  upper-Möbius property, global nonnegativity, exact value one on dyadic
  primes, main mass at most `2/log R`, coefficient bound `3^ω(d)`, and
  `Σ_{n≤X}ν(n)≤2X/log R+R(1+log R)^3`. This is sufficient for the diagonal
  power separation but does not discharge Tao's source-exact `{−1,0,1}`
  Rosser-weight statement.
- [x] Connect the concrete Selberg weight to normalized finite BHM: remove the
  zero coordinate, prove the exact weighted divisor expansion, reindex
  `d∣n` as `n=md` on `m≤⌊(2Z-1)/d⌋`, extract the divisor value by
  multiplicativity and norm-one control, discharge the diagonal, and reduce
  the full normalized second moment to uniform unshifted off-diagonal prefix
  correlations. Burgess is now the sole analytic hypothesis in this chain.
- [x] Formalize Tao's heterogeneous exceptional-character family: dependent
  primitive levels `q₁q₂`, squarefree/coprime data, the exact common-factor
  lcm identity, squarefreeness and `Z^3.09` bound for every pair period, and
  exact equality of `χ_j(n)conj(χ_k(n))` with a single quotient character even
  at nonunits. The family BHM theorem is reduced to one explicit cubefree
  Burgess prefix-bound predicate. The exact `0.0002` off-diagonal exponent
  margin and the strict `3.09<3.1(1-0.0001)` range check are proved; proving
  the analytic predicate remains.
- [x] Make the Burgess boundary source-faithful and discharge its scale side
  conditions: quantify only the sieve prefixes `⌊(2Z-1)/d⌋`, state the
  explicit cubefree target with saving `0.0163`, fixed cutoff, and
  `q≤H^3.1`, choose `R=⌊Z^0.0001⌋`, and prove uniformly that every requested
  prefix is eventually large enough and satisfies the range. Bertrand also
  proves eventual dyadic prime-band nonemptiness. The analytic Burgess proof
  remains.
- [x] Compile Tao's numerical specialization of the published Burgess theorem:
  define cube-free literally by exclusion of prime cubes, prove every
  squarefree downstream period is cube-free, encode the cited `r=7` bound as
  `A H^(6/7)q^(2/49+ε')`, take `ε'=1/2000000`, and prove this implies the exact
  `H^(1-0.0163)` target throughout `q≤H^3.1`. Only the cited two-factor
  character-sum estimate itself remains analytic.
- [x] Reduce the analytic Burgess boundary from arbitrary nonprincipal
  characters to primitive characters. Prove the exact changed-level
  evaluation formula, Möbius-expand its coprimality indicator, reindex every
  divisor contribution as a primitive prefix of length `H/d`, and bound the
  resulting coefficient sum by `#divisors(q)`. Split the fixed positive
  epsilon in half and use the proved divisor-epsilon theorem to absorb this
  loss. Thus a primitive cube-free `r=7` estimate at
  `ε'=1/4000000` implies the all-character decimal contract used downstream.
- [x] Reduce the primitive Burgess target to its genuinely nontrivial prefix
  range. Reindex `Ioc 0 H` as a shifted range, identify one complete period
  with the finite sum over `ZMod q`, prove all complete periods cancel for a
  nonprincipal character, and obtain the exact identity `S(H)=S(H % q)`.
  Prove the trivial bound `|S(H)|≤H` and the exact threshold equivalence
  `q^(2/49+ε')<H^(1/7) ↔ q^(2/7+7ε')<H`. Hence it now suffices to prove
  the primitive cube-free estimate with a constant `A≥1` only when
  `q^(2/7+7ε')<H<q` (at `ε'=1/4000000`).
- [x] Pin an accessible composite cube-free proof architecture: the PDF and
  TeX source of Hasanalizade--Lin--Martin--Luna Martínez--Treviño,
  arXiv `2511.17778v2`, are hashed with exact locators for Theorem 1.3's
  shifted `2r`-moment, Lemma 2.1's complete Weil-type character sum, and
  Lemmas 2.3--2.4's gcd-tuple bounds. This auxiliary source does not replace
  the still-unretrieved Burgess 1963 original or count as a Lean proof.
- [x] Compile the finite Burgess moment and diagonal combinatorics. Define the
  shifted character sum and the ordered pair of `r`-tuples, expand the exact
  complete `2r`-moment, rewrite it as complete quotient-character
  correlations (including nonunits), and split at `r` distinct shifts. Encode
  every degenerate tuple by `r` values and `2r` labels to prove
  `#degenerate≤r^(2r)B^r`; hence derive
  `moment≤r^(2r)B^r q+B^(2r)W` and the literal `r=7` fourteenth-moment form.
  The nondegenerate composite Weil bound remains.
- [x] Formalize the pinned composite source's coefficient boundary. Define
  the two tagged blocks of integer shifts and the literal
  `A_j=∏_{i≠j}(b_i-b_j)`. Prove by exact fiber-cardinality summation that a
  nondegenerate tuple has a uniquely occurring shift, equivalently a nonzero
  `A_j`. Define `∑_{A_j≠0}gcd(|A_j|,q)`, prove its trivial pointwise bound,
  state the relaxed composite Weil interface with factor
  `(4r)^ω(q)√q`, and reduce both the general moment and the `r=7` fourteenth
  moment to that interface and the explicit gcd sum.
- [x] Prove the finite Burgess gcd-weight sum. Majorize `gcd(n,q)` by the
  divisors of `q` which divide `n`, count their multiples to obtain
  `∑_{n≤H}gcd(n,q)≤H τ(q)`, split the centered shift sum into its two sides,
  prove gcd submultiplicativity over the literal product `A_j`, and factor
  the remaining independent coordinates exactly. Conclude
  `∑_uv burgessTupleGcdWeight q uv≤2r B(2B τ(q))^(2r-1)` and feed this into
  both the general and `r=7` composite-Weil moment reductions.
- [x] Absorb the arithmetic losses in the literal `r=7` moment. Use the
  fixed-base prime-factor epsilon theorem on `28^ω(q)` and the divisor-epsilon
  theorem on `τ(q)^13`, allocating `ε/2` to each. Conditional only on the
  composite Weil predicate, obtain a positive `C_ε` and the source-shaped
  bound `moment≤7^14 B^7 q+C_ε B^14 q^(1/2+ε)`.
- [x] Prove the exact CRT multiplicative layer for the composite Weil
  predicate. Define the canonical local characters at coprime factors, prove
  global character-value factorization and coordinatewise compatibility of
  the tuple numerator and denominator, and factor the complete correlation.
  Prove multiplicativity of `(4r)^ω(q)√q` and of each fixed
  `gcd(|A_j|,q)` contribution, then assemble two local bounds sharing `j`
  into the relaxed global gcd-weight bound. Primitivity transport, iteration
  through a cube-free factorization, and local prime/prime-square Weil bounds
  remain.
- [x] Prove primitivity transport through the canonical CRT factors. Express
  the global character as the product of the two local characters changed
  back to level `mn`. Show that a left factorization through `d` induces a
  global factorization through `dn`, and symmetrically on the right. For a
  primitive global character, conductor divisibility and cancellation force
  each local conductor to equal its full local level.
- [x] Iterate the CRT estimate over every cube-free modulus. Split each
  nontrivial modulus as `p^k n`, where `k∈{1,2}`, `(p^k,n)=1`, and `n<q`.
  Use strong induction to retain the same nonzero coefficient witness through
  every split, obtaining the fixed-gcd composite estimate. Select one nonzero
  `A_j` from each nondegenerate tuple and insert its contribution into the
  relaxed gcd weight. This proves that the complete composite Weil predicate
  follows solely from the primitive local estimates modulo `p` and `p^2`.
- [x] Remove the coefficient-divisible part of the local Weil boundary.
  When `p ∣ |A_j|`, combine the trivial correlation bound with the resulting
  gcd contribution to prove the required estimate at both `p` and `p^2`.
  Split the genuinely nontrivial remainder into separate primitive prime and
  prime-square predicates under `gcd(|A_j|,p)=1`, and prove that they
  reassemble into the prime-power and full composite predicates.
- [x] Build the exact prime-square stationary-phase infrastructure. Reindex
  `ZMod (p^2)` as base points `a : ZMod p` and principal-unit directions
  `t : ZMod p`; prove the resulting complete-correlation fiber identity,
  characterize unit status by reduction modulo `p`, and show all singular
  fibers vanish with at most `2r` singular bases. Restrict a primitive
  character to `1+pt`, prove this is a nontrivial additive character, and
  define the numerator, denominator, and stationary polynomial `F'G-FG'`.
  Its degree and root count are at most `2r`.
- [x] Close the primitive prime-square Weil estimate. Prove the exact
  first-order product identities for `F(a+pt)` and `G(a+pt)`, identify each
  nonsingular quotient fiber with the principal additive character at
  `(F'/F-G'/G)t`, and cancel every nonzero frequency. Coprimality of the
  selected `A_j` makes its tagged root simple in exactly one of `F,G`, so
  `F'G-FG'` is nonzero. Its at most `2r` roots support all surviving fibers,
  yielding `‖correlation‖≤4rp`. Only the prime-modulus local Weil estimate
  remains in the composite Burgess boundary.
- [x] Normalize the primitive prime-modulus boundary to the exact finite-field
  theorem it needs. Rewrite the Burgess correlation as the complete character
  sum of a quotient of two products of linear factors, prove that
  `gcd(|A_j|,p)=1` makes the selected tagged root unique modulo `p`, and prove
  a primitive prime-level character is nontrivial. Verify that the resulting
  `TaoPrimeLinearQuotientWeilBound` implies the primitive prime predicate and,
  through the completed prime-square and CRT layers, the composite predicate.
- [x] Reduce the linear-quotient theorem to the standard split-polynomial
  Weil form. Clear the inverse character with denominator exponent
  `orderOf χ - 1`, prove exact equality of the complete sums, calculate the
  selected root multiplicity as `1` or `orderOf χ - 1`, and deduce that the
  polynomial is not an `orderOf χ`-th power. Prove it splits and has at most
  `2r` distinct roots, then bridge `TaoPrimeSplitPolynomialWeilBound` to the
  linear-quotient and composite predicates.
- [x] Prove the one- and two-distinct-root cases of
  `TaoPrimeSplitPolynomialWeilBound`: group the split polynomial by root
  multiplicity, show the one-root sum vanishes, identify the two-root sum
  with a Jacobi sum by an affine reindexing, and derive its `√p` bound from
  the Gauss--Jacobi identities. Bridge the residual
  `TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore` contract to the full
  split-polynomial and composite Weil predicates.
- [x] Partition a split polynomial's roots into active and inactive roots
  according to divisibility of their multiplicities by `orderOf χ`. Prove the
  full root product is zero at inactive roots and equals the active product
  elsewhere; bound the deleted-input correction by the inactive-root count
  and absorb it into `2 #roots √p`. This extends the Jacobi proof to every
  polynomial with at most two active roots and bridges the residual
  `TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore` contract to the
  full split-polynomial and composite predicates.
- [x] Prove the exactly-three-active-root case needed by Burgess. Compute the
  cleared polynomial's degree as `r * orderOf χ`, deduce divisibility of the
  active multiplicity sum, and verify a fractional-linear reindexing that
  sends one root to infinity. The denominator character cancels and the sum
  becomes a two-root Jacobi sum with one deleted point, giving `√p+1`; absorb
  this and the inactive-root correction into `2 #roots √p`.
- [x] Remove small prime characteristics from the remaining Weil input. Prove
  the trivial complete-sum bound `p` and show it is at most `2D√p` whenever
  `p ≤ 4D²`, where `D` is the distinct-root count.
- [x] Normalize the exactly-four-active-root case by a fractional-linear
  reindexing. Send one root to infinity, cancel the denominator characters
  from degree divisibility, and reduce the sum exactly to a canonical
  three-point hypergeometric sum with one deleted value. Lift a `2√p`
  canonical bound through multiplicities and inactive-root correction to the
  split-polynomial target.
- [x] Restrict the generic five-active-root split-polynomial residual to the
  exact `primeLinearOrderPolynomial` family produced by Burgess. Dispatch all
  small-characteristic and zero-through-four-active-root branches internally,
  show four active roots force `p > 64`, and bridge the resulting source-
  specific predicates to the full cube-free composite endpoint.
- [x] Restrict the canonical four-root input to three powers of the single
  ambient Burgess character and normalize every exponent modulo `orderOf χ`.
  Prove by `pow_mod_orderOf` that the finite range
  `m,n,l < orderOf χ` covers arbitrary active-root multiplicities.
- [x] Scale the remaining marked points to Legendre form `(0,1,t,∞)`, prove
  the exact complete-sum identity and norm transport, and reduce the
  four-root geometric input from two parameters to one `t ≠ 0,1`.
- [ ] Prove
  `TaoPrimeReducedPowerLegendreHypergeometricWeilBoundAboveSixtyFour` and
  `TaoPrimeLinearOrderPolynomialWeilBoundFiveActiveRootsLargeCharacteristic`.
  The checked bridge from precisely these two inputs supplies the full
  cube-free composite predicate; the latter residual may assume `4D² < p`.
- [x] Normalize by the exact dyadic-prime cardinality: prove
  `#([Z,2Z)∩Primes)=π′(2Z)-π′(Z)`, transfer the pinned PNT to `π′`, derive
  `#([Z,2Z)∩Primes)∼Z/log Z`, and record the concrete eventual denominator
  bound `Z/(2 log Z)≤#([Z,2Z)∩Primes)`.
- [x] Complete the non-Burgess Lemma 5.1 absorption: prove the Selberg main
  and floor-error diagonal terms are `O(Z/log Z)`; under
  `J≤A Z^(2/125)`, combine the exact exponents into
  `Z^(1-1/5000)log^3 Z=o(Z/log Z)`; divide by the exact band cardinality with
  a constant independent of the preliminary coefficient; and implement
  Tao's finite truncation bootstrap. Conditional on explicit Burgess, obtain
  both `J≪Z^(2/125)` and an eventual constant bound for the full exceptional
  second moment. Only the analytic Burgess proof remains.
- [x] Specialize the heterogeneous Lemma 5.1 family to the literal
  fixed-conductor exceptional-character finsets used in Section 6: take
  `q₂=1`, transport primitive characters across `q*1=q`, prove exact
  cardinality and squared-sum preservation, and derive the source's general
  `O(λ⁻²)` tail statement. For varying squarefree `q≤Z^3.09`, all three
  conclusions now follow conditional only on explicit Burgess.
- [x] Aggregate exceptional primitive characters over an arbitrary finite
  conductor set: prove primitive lcm-lift uniqueness across unequal levels,
  deduce automatic separation, encode the dependent conductor-character
  sigma family, and preserve its total cardinality and complete double
  squared-moment sum exactly. One Burgess-conditional Lemma 5.1 application
  now gives a uniform bound for the whole admissible conductor set.
- [x] Construct the literal small-prime conductor union over every tuple
  modulus, prove all tuple lcms and divisor conductors squarefree, and bound
  them by `taoSmallAntiSievePrimeCutoff x ^ 50`. Under the explicit Lemma 5.1
  square-root range comparison, derive the uniform union moment conditional
  on Burgess and insert it into the exact weighted exceptional conductor sum,
  reducing the latter to the completed logarithmic-lcm Mertens coefficient.
- [x] Prove the rounded source selector comparison
  `cutoff^50<⌊z^(9/10)⌋≤P_j`, dominate all admissible conductor sets by one
  maximal finite squarefree universe, and obtain one Burgess-conditional
  constant simultaneously for all 1001 selectors. Absorb the exceptional
  conductor sum into the principal Mertens majorant. Use
  `P_j⁻⁸ cutoff⁵⁰≤1` to absorb the explicit totient error too, closing the
  entire small-prime fiftieth moment conditional on analytic Burgess.
- [x] Prove the exact positive-smooth-number Dirichlet-series Euler product
  and finite Rankin inequality in Tao's inclusive `p≤y` convention.
- [x] Convert the Euler product to an exponential geometric-tail bound,
  uniformize its denominators by the prime-two factor, and expose the exact
  Rankin saddle exponent involving `∑_{p≤y}p^(-sigma)`.
- [x] Prove the exact finite Abel identity for `∑_{p≤y}p^(-sigma)`, show its
  backward-difference coefficients are nonnegative, apply Mathlib's explicit
  Chebyshev bound pointwise, absorb its square-root remainder into the clean
  global majorant `(2 log 4+2)n/log n`, and substitute both resulting
  unconditional finite majorants into the Rankin saddle exponent.
- [x] Apply real Bernoulli to prove the sharp first-order backward-difference
  estimate `n^(-sigma)-(n+1)^(-sigma)≤sigma*n^(-sigma)/n` on
  `0≤sigma≤1`, cancel the prime-counting factor exactly, and reduce the
  weighted prime sum to its endpoint plus
  `(2 log 4+2)*sigma*∑ n^(-sigma)/log n`.
- [x] Prove a second Bernoulli/telescoping finite `p`-sum comparison and the
  coarse but completely sum-free bound
  `∑ n^(-sigma)/log n ≤ y^(1-sigma)/((1-sigma)log 2)` for
  `0≤sigma<1`, then propagate it into an explicit Rankin exponent.
- [x] Split the canonical power-log sum at an arbitrary natural cutoff
  `2≤k≤y`, retain `log k` on the upper range, and prove the normalized
  saddle-scale bound with denominator `log y` from the exact hypotheses
  `k^(1-sigma)log y≤y^(1-sigma)` and `log y≤L log k`; propagate both the
  raw split and normalized estimates through the weighted prime sum and the
  source-facing Rankin exponent.
- [x] Construct the canonical divisor `R=(log y)^(1/(1-sigma))` and integer
  cutoff `floor(y/R)`, prove the exact identity `R^(1-sigma)=log y`, transfer
  both cutoff comparisons through the floor, and show that for `y≥4` the
  single separation `2R≤sqrt y` gives the normalized estimate with `L=2`.
  Propagate this concrete bound through the weighted-prime sum and the
  source-facing Rankin exponent.
- [x] Define the actual saddle variables `u=log X/log y` and
  `sigma=1-log u/log y`, prove the exact positivity/range criteria, and
  kernel-check `y^(1-sigma)=u` together with the negative-exponent identity
  `-(1-sigma)log X=-u log u`.
- [x] Restore the endpoint cancellation discarded by the coarse integral
  comparison: prove the exact local bound on every `[a,b)` with numerator
  `(b-1)^(1-sigma)-(a-1)^(1-sigma)` and denominator
  `(1-sigma)log a`. Prove exact reassembly and termwise bounds along an
  arbitrary monotone natural cutoff chain, supplying the finite primitive for
  the critical-regime multi-scale argument, and propagate its named majorant
  through the weighted-prime and source-facing Rankin inequalities.
- [x] Choose the concrete saturated dyadic chain `min y 2^(i+1)`, prove its
  exact `clog 2 y - 1` length and terminal saturation, and replace the local
  integral loss by a block-cardinality estimate. Reduce the chain to the
  scalar sum `∑ 2^(j delta)/j`; split at an arbitrary cutoff, sum the tail
  geometrically, prove `2^delta-1≥delta log 2`, and obtain the closed midpoint
  bound with terminal term `2^(m delta)/(m delta)` and half-exponential
  harmonic prefix.
- [x] Prove the exact dyadic depth/logarithm comparisons, including
  `log y≤(clog 2 y)log 2`, midpoint denominator at least `(log y)/2`, and
  terminal overshoot below `2y`. Convert the terminal scalar contribution to
  `2(2y)^delta/(delta log y)` and, at the actual Rankin saddle, to
  `2*2^delta*u/log u`.
- [x] Compress the half-exponential prefix to
  `sqrt(2^delta*u) * (1+log(floor(m/2)))` and prove the finite absorption
  interface giving the complete scalar bound `5u/log u` from
  `2(1+log(floor(m/2)))log u ≤ sqrt u`.
- [x] Bound the natural dyadic prefix by `1+log(log(2y)/log 2)`, prove
  `log u ≤ 4u^(1/4)`, and reduce the absorption hypothesis to the
  continuous-scale fourth-root comparison
  `8(1+log(log(2y)/log 2)) ≤ u^(1/4)`.
- [x] Encode the critical regime by the precise fixed-parameter limits
  `log X/log x → 1` and `log y/log z(x) → α`. Prove `log x/log z=u₀`,
  `u₀→∞`, `u/u₀→1/α`, and therefore `u→∞` for every fixed `α>0`.
- [x] Prove `log z/u₀²→0`, transfer it to `log(2y)/u²→0`, and discharge
  the critical quadratic-depth and saddle-range hypotheses. Apply the generic
  consumer to obtain the complete eventual scalar estimate `5u/log u`
  directly from the critical source contract.
- [x] Insert the scalar estimate into the finite smooth-number Rankin bound,
  prove `u₀ log u₀/log z→1`, `u log u/log z→1/α`, and show the complete
  positive dyadic error is `o(log z)`. Deduce the quantified critical upper
  bound `Psi(X,y)≤X/z^(1/α-ε)` for every fixed `ε>0`.
- [x] Encode the polylogarithmic regime by `log X/log x→1` and
  `log y/log₂x→A` for fixed `A>1`. Prove `u/(log x/log₂x)→1/A`,
  `sigma→1-1/A`, discharge the quadratic depth and saddle-range hypotheses,
  show `u log u/log x→1/A` with dyadic error `o(log x)`, and deduce
  `Psi(X,y)≤X/x^(1/A-ε)` for every fixed `ε>0`.
- [x] Begin the matching lower bound with Granville's finite lattice-count
  construction: prove fixed-size prime-subset products are injective, smooth,
  and bounded, and deduce `choose (π(y)) k ≤ Psi(X,y)` whenever `y^k≤X`.
- [x] Complete the polylogarithmic lower estimate: take `k=Nat.log y X`, prove
  its normalized and logarithmic asymptotics, use the frozen PNT to obtain
  `log π(y)/log₂x→A` and eventually `2k≤π(y)`, and deduce
  `x^(1-1/A-ε)≤Psi(X,y)` from the binomial entropy lower bound.
- [x] Connect the same exact integral depth to the critical regime: prove
  `k/u₀→1/α`, `log k/log₂x→1/2`, `k log k/log z→1/α`, the critical PNT limit
  `log π(y)/log z→α`, and eventually `2k≤π(y)`.
- [x] Replace the squarefree-only finite lower family by Granville's full
  exponent simplex.  Prove unique factorization of prime multisets, count all
  total degrees `j≤k` by stars and bars as
  `choose(k+π(y),π(y))`, and embed them in `Psi(X,y)` whenever `y^k≤X`.
- [x] Prove the exact largest-prime-factor recurrence
  `Psi(X,y)=1+sum_{p≤min(X,y)}Psi(X/p,p)` for `X≥1`, including the finite
  largest-prime/cofactor bijection and injectivity.
- [x] Prove the exact finite Chebyshev--Hildebrand weighted identity: identify
  smooth multiples of every `p^a` with smooth cofactors, double count total
  prime multiplicity, sum the logarithmic factorization formula, and retain
  the boundary error as an explicit nonnegative finite defect; deduce the
  first-prime-power recursive inequality.
- [x] Iterate the weighted inequality at finite depth: prove
  `theta(y)^d<=Psi(X,y)(log X)^d` whenever `y^d<=X`, including every natural
  quotient, positivity, and logarithmic-denominator comparison.
- [x] Recover the fractional finite endpoint with
  `b=floor(X/y^Nat.log_y(X))`: prove `1<=b<y`, retain a final prime packet up
  to `b`, and construct a fixed PNT threshold with `theta(b)>=b/2` above it
  while safely omitting bounded endpoints below it.
- [x] Audit the full asymptotic strength of the endpoint-Hildebrand route:
  prove `X/(B*2^d*(log X)^(d+1))<=Psi(X,y)`, show its denominator has
  logarithm `(2/alpha+o(1))*log z`, and derive the quantified fallback
  `X/z^(2/alpha+epsilon)<=Psi(X,y)`.
- [x] Isolate and prove the sharp critical lower consumer: any finite packet
  `X*exp(-(u*log u+E))<=Psi(X,y)` with `E/log z->0` yields
  `X/z^(1/alpha+epsilon)<=Psi(X,y)` for every positive `epsilon`; prove in
  particular that each fixed CEP-sized error `E=C*u*log(log u)` is
  `o(log z)`, prove the critical regime eventually satisfies the uniform
  source range `u<=y^(1/2)`, and instantiate the consumer from the resulting
  exact two-variable finite CEP contract.
- [x] Complete the matching critical lower estimate by a finite coarse CEP
  saddle: use fixed dyadic PNT blocks to obtain reciprocal mass
  `1/(16 log 2 log u)`, multiplicity `floor(u-2u/log u)`, cofactor depth at
  most `10u/log u`, and total secondary loss at most `60u log(log u)`; deduce
  `X/z^(1/alpha+epsilon)<=Psi(X,y)` and thereby complete all four quantified
  upper/lower halves of Proposition 2.1.
- [x] Instantiate the critical Proposition 2.1 lower estimate uniformly over
  the fixed prime block `z<p<3z`; insert reciprocal-prime mass into the exact
  `B¹` sum and prove `x/z^(2+epsilon) <= #B¹(x)` eventually for every
  `epsilon>0`, the lower half of Lemma 1.6(i).
- [x] Prove the small- and large-prime pieces of the Lemma 1.6(i) upper
  decomposition: uniformize the `alpha=1/2` estimate below `ceil(sqrt z)`
  and telescope the reciprocal-square tail above `ceil(z²)`.
- [x] Complete the finite exponent-band estimate in the remaining middle
  prime range, absorb the fixed grid cardinality, and prove the exact
  `QuotientPowerScale` conclusion of Lemma 1.6(i).
- [x] Fix the exact `floor(cX)` convention for multiplicative stability;
  prove its ratio/logarithmic limits, preservation of the critical regime,
  smooth/count cutoff monotonicity, and the automatic direction of both the
  smooth-number and Lemma 1.6(ii) comparisons.
- [x] State Granville (3.24)'s exact critical quotient-limit target and prove
  abstractly that its positive limit gives the required `IsTheta` contract;
  keep this as a proposition-valued target rather than an assumed theorem.
- [x] Construct the genuine finite smooth-number saddle parameter: prove the
  first prime sum is continuous and strictly decreasing from `+infinity` to
  zero, obtain the unique positive solution, define the positive `phiTwo`
  sum, prove `phiOne'=-phiTwo`, and prove the exact mean-value sensitivity
  identity between two ambient cutoffs.
- [x] Locate the genuine saddle in the critical regime: prove explicit
  Abel--Chebyshev and prime-counting comparisons at `sigma=1` and
  `sigma=1-epsilon`, then deduce `smoothSaddlePoint(X(x),y(x)) -> 1`; prove
  `phiTwo >= log(2) log(X)`, its divergence, an exact finite sensitivity
  bound, and `o(1)` saddle displacement under fixed dilation.
- [x] Define the exact logarithmic Euler-product phase and Gaussian saddle
  main term; prove exponentiation recovers the source Euler product,
  `phase'=log(X)-phiOne`, the derivative of this derivative is `phiTwo`,
  Rankin's inequality at the saddle, and the saddle's unique positive global
  minimum property.
- [x] Prove the exact old/new minimum-phase squeeze under changing `X`; for
  fixed positive dilation deduce phase difference `-> log(c)` and exponential
  saddle-main-term quotient `-> c`.
- [x] Prove prime-scale saddle displacement `o(1/log y)`, uniform
  prime-local curvature comparison, `phiTwo` quotient `-> 1`, and complete
  Gaussian saddle-main-term quotient `-> c` under fixed dilation.
- [x] State the remaining uniform `Psi/mainTerm -> 1` saddle asymptotic as an
  exact proposition-valued contract and prove it implies Granville's quotient
  limit and the constant-factor `IsTheta` stability contract.
- [x] Prove the constant-factor stability clause Lemma 1.6(ii), conditional
  on the sharp critical smooth-number dilation limit. The proof now follows
  from the half-ratio by finite power-of-two iteration and exact floor
  bracketing; it is no longer a separate analytic input.
- [x] Pin and hash the Baker--Harman--Pintz primary source, with exact theorem
  and proof locators.
- [ ] Optional stronger alternative: formalize the Baker--Harman--Pintz bound
  in Proposition 2.3(ii). Its pinned paper is provenance, not proof evidence.
  The endpoint transfer is proved, but the analytic sieve theorem is not.
  Release 5.10 accepts the exact consumed upper scale proved by quantitative PNT,
  so this is no longer an endpoint prerequisite.
- [x] Prove all four selected public contracts without `sorry`, `admit`,
  project postulates, or unsafe proof bypasses.
- [x] Add an executable development `Audit.lean` covering every current Tao
  theorem declaration.
- [x] Extend the development verifier with real source, import, diagnostic,
  frozen-hash, file-set, and axiom contracts.
- [x] Promote the verifier to the four-theorem proof-release verifier and pass
  its explicit audit, semantic, and persistent-log gates.

## Release acceptance - passed in 5.10

- [x] Every claimed result has an exact source crosswalk, including the PNT substitution.
- [x] Every vendored or copied dependency has immutable provenance.
- [x] The production root builds with zero project diagnostics.
- [x] All four public endpoints pass the explicit transitive axiom audit.
- [x] Every inventoried public theorem/lemma has direct, unique,
  case-sensitive audit coverage.
- [x] Source hashes and frozen dependency boundaries pass.
- [x] All 10 semantic regression assertions pass explicitly.
- [x] The complete unsuppressed log and exact status are recorded in the manifest.
- [x] README claims match the executable audit and reproduction manifest.
- [x] The architecture distinguishes the proved main route from unused conditional alternatives.

## Historical stop line

The verified stop line includes Proposition 2.3(i),(iii), the exact `VB¹`
zeta-ratio asymptotic, the corrected full Lemma 3.1 contract conditional on
Theorem 2.5, the complete polynomial-coefficient relation of Lemma 3.2, and
the full Theorem 1.8 counting/asymptotic assembly conditional only on Theorem
2.5. It also includes
the exact smooth-number saddle parameter, its existence, uniqueness,
positive second logarithmic derivative, and finite cutoff-sensitivity
identity, together with its critical-regime limit to `1`, but not the uniform
saddle-point asymptotic needed for Granville (3.24). It further includes
the exact Theorem 2.5 interface, reciprocal-phase calculus and character
variation, bidirectional finite partial-summation/log-weight reductions, and
the low-frequency Abel reduction and the frozen qualitative PNT's uniform
dyadic and fixed-bounded-frequency `o(P)` consequences, but not the stronger
arbitrary-logarithmic-saving PNT bound or the full prime exponential-sum
estimate.
The unrestricted Sylvester--Schur theorem and the square specialization of
Erdős--Selfridge are now proved. The exact Theorem 1.7
contract is now derived conditionally from analytic Burgess and the sharp
critical smooth-number saddle asymptotic. The formerly separate
adjacent-dyadic ratio and Lemma 1.6(ii) are both derived from that saddle
input. This still does not prove any of Theorems 1.7--1.10 unconditionally.
Do not mark a release item complete merely because this conditional endpoint
builds.

## Prime-equidistribution 2.57

- [x] Define positive interval character sums and identify the zero-start case
  with the established `Ioc` prefix.
- [x] Prove exact first/last splitting, additive shift differencing, and the
  norm error `<= 2K`.
- [x] Prove affine reindexing and norm preservation for coprime multipliers.
- [x] Exchange the interval and additive-shift sums to recover the exact
  `burgessShiftSum` consumed by the complete moment.
- [x] Define the coprime multiplier residue multiplicity, prove its exact
  first moment, and regroup the affine average by residue.
- [ ] Prove the second-moment collision bound for the residue multiplicity.
- [ ] Apply Hölder and optimize the Burgess parameters to prove the primitive
  `r = 7` core bound.

These checked items are unconditional finite algebra; they do not discharge
the remaining analytic Burgess input.

## Prime-equidistribution 2.58

- [x] Identify the multiplicity second moment with ordered residue collisions.
- [x] Convert residue collisions for unit multipliers to the source's
  cross-multiplied congruence.
- [x] Define fixed-multiplier collision fibers with an exact membership lemma.
- [x] Prove the three-factor powered Hölder estimate for the multiplicity-
  weighted sum and the original affine average.
- [ ] Prove the source collision-fiber bound
  `card <= 1 + H*gcd(a,c)/max(a,c)` under its required range hypotheses.
- [ ] Sum that bound and finish the Burgess induction and parameter choices.

## Prime-equidistribution 2.59

- [x] Convert the collision congruence into divisibility of the integer
  determinant and prove the no-wrap consequence under `2*A*H <= q`.
- [x] Prove reduced-multiplier spacing in each fixed-`a,c` fiber.
- [x] Prove the local source-shaped bound
  `card <= H / (max a c / gcd a c) + 1`.
- [x] Decompose the global collision cardinality by multiplier pairs and bound
  it by the corresponding finite `max/gcd` sum.
- [ ] Estimate the remaining elementary gcd sum in the source's divisor-sum
  form.
- [ ] Finish the Burgess induction, boundary-error absorption, and `r = 7`
  parameter choices.

These checked statements are unconditional finite arithmetic. They do not
prove analytic Burgess or any of Theorems 1.7--1.10.

## Prime-equidistribution 2.60

- [x] Bound the fixed-upper-multiplier gcd quotient sum by
  `H * c.divisors.card` through divisor incidence and multiple counting.
- [x] Prove the exact finite identity
  `sum_{c<=A} tau(c) = sum_{d<=A} floor(A/d)`.
- [x] Bound the real summatory divisor function by `A * harmonic A`.
- [x] Deduce the complete collision estimate with explicit off-diagonal term
  `2*H*A*harmonic A`.
- [ ] Run the Burgess induction and absorb the affine translation boundary.
- [ ] Optimize `A` and `B` at `r = 7` to prove the primitive core bound.

The collision-counting package is now complete at the strength needed for
the amplification argument. Analytic Burgess and Theorems 1.7--1.10 remain
unproved unconditionally.

## Prime-equidistribution 2.61

- [x] Add real-valued residue-multiplicity regrouping.
- [x] Bound the sum over `a` of affine `b`-average norms by the literal
  multiplicity-weighted shifted-character sum.
- [x] Generalize the additive-shift error to arbitrary majorants for both
  shorter endpoint intervals.
- [x] Prove the exact source pre-Hölder recursion inequality under `A*B <= H`.
- [ ] Specialize the boundary majorant to the inductive Burgess power and sum
  it over `a,b`.
- [ ] Insert Hölder, collision, and complete-moment bounds and optimize the
  `r = 7` parameters.

No main theorem is claimed by these finite identities.

## Prime-equidistribution 2.62

- [x] Collapse the coprime-multiplier boundary sum using monotonicity.
- [x] Bound a nonnegative power boundary sum by `B` copies of its endpoint.
- [x] Specialize equation (28) to `E(K)=C*K^alpha*Q`.
- [x] Divide by the positive affine-average denominator and cancel its common
  boundary factor.
- [ ] Extract the `2r`-th root from the powered Hölder estimate.
- [ ] Substitute the harmonic collision and complete moment bounds.
- [ ] Choose and verify the natural `r = 7`, `A`, and `B` parameters.

The scalar translation-boundary calculation is now complete. Analytic
Burgess and Theorems 1.7--1.10 remain unproved unconditionally.

## Prime-equidistribution 2.63

- [x] Extract the `2r`-th root from powered Hölder using nonnegativity.
- [x] Prove monotone substitution of collision and complete-moment majorants.
- [x] Insert the harmonic collision estimate at `r = 7`.
- [x] Insert the diagonal-plus-`q^(1/2+epsilon)` complete moment.
- [x] Combine the rooted main term with the normalized power-boundary
  recurrence.
- [ ] Prove a quantitative lower bound for the coprime multiplier count.
- [ ] Select integer `A,B`, verify all range conditions, and absorb the
  inductive boundary term.

The full pre-optimization Burgess recurrence is compiled. Its complete-Weil
hypothesis and the scalar optimization are not yet discharged.

## Prime-equidistribution 2.64

- [x] Prove exact Möbius inversion for the short coprime multiplier count.
- [x] Recover the exact totient density from the complete-period identity.
- [x] Prove `A*phi(q)/q - tau(q) <= #A` over the reals.
- [x] Export the bound in Burgess multiplier-pair notation.
- [x] Deduce a half-density lower bound under explicit discrepancy dominance.
- [x] Prove `q/phi(q) <= tau(q)` and reduce discrepancy dominance to
  `2*tau(q)^2 <= A`.
- [x] Establish discrepancy dominance for the eventual parameter range.
- [ ] Bound the divisor-square criterion and harmonic factor at the required
  epsilon losses.
- [ ] Select and round `A,B`, verify no-wrap/shortening, and absorb the
  inductive boundary.

The multiplier denominator is no longer an unformalized counting placeholder.
The complete-Weil input and parameter optimization remain open.

## Prime-equidistribution 2.65

- [x] Prove eventual `2*tau(q)^2 <= floor(q^eta)` for every `eta>0`.
- [x] Remove both multiplier-cardinality factors from the rooted Holder term.
- [x] Compress the collision factor to `3*H*A*harmonic(A)` when `A<=H`.
- [x] Export the fully scalar normalized fourteenth-moment recurrence.
- [x] Define `B=floor(q^(1/14))` and `A=H/(K*B)`.
- [x] Prove the rounded floor/quotient losses and all current parameter
  admissibility implications.
- [ ] Absorb harmonic and totient losses into the epsilon budget.
- [ ] Complete the scalar exponent calculation and inductive boundary
  absorption.

The rounded parameters and their divisor criterion are no longer open. The
complete-Weil input and the last scalar/inductive closure remain open.

## Prime-equidistribution 2.66

- [x] Bound `harmonic(A)` and `q/phi(q)` by explicit conductor epsilon powers.
- [x] Normalize the half-density denominator to expose `1/(A*B)`.
- [x] Collapse the complete-moment scalar to `q^(3/2+epsilon)`.
- [x] Extract the exact `q^(3/28+epsilon/14)` fourteenth-root exponent.
- [x] Factor and bound the compressed pre-substitution main term.
- [ ] Substitute the rounded lower bounds for `A,B` and derive `2/49`.
- [ ] Make the inductive boundary coefficient strictly less than one.

## Prime-equidistribution 2.67

- [x] Convert the rounded `A,B` denominator into a fourteenth-power base.
- [x] Prove the exact normalized `A,H` fourteenth-root identity.
- [x] Bound the normalized factor by
  `2*K^(1/14)*H^(6/7)/q^(13/196)`.
- [x] Combine this with the rooted complete moment and derive the exact
  conductor exponent `2/49 + epsilon/14 + delta/14`.
- [ ] Insert the reciprocal-totient loss and allocate the final epsilon.
- [ ] Make the inductive boundary coefficient strictly less than one.

The main term has passed the decisive rounded substitution. The analytic
complete-Weil input and the final scalar/inductive closure remain open.

## Prime-equidistribution 2.68

- [x] Multiply the rounded main term by the reciprocal-totient bound.
- [x] Allocate the three losses to obtain the single exponent `2/49+eta`.
- [x] Export the exact stronger geometry `K*A*B<=H`.
- [x] Bound the normalized boundary by one half under `K^(6/7)>=4`.
- [x] Verify the concrete safety factor `K=128`.
- [ ] Combine the main and boundary bounds with the full scalar recurrence.
- [ ] Discharge the complete-Weil analytic hypothesis.

Both scalar estimates needed for induction are now independently compiled.
Their recurrence-level integration is the next bounded package.

## Prime-equidistribution 2.69

- [x] Assemble the rounded main and half-boundary estimates in the scalar
  recurrence.
- [x] Prove every multiplier product is strictly shorter than the parent
  interval.
- [x] Close the recurrence coefficient by strong induction.
- [x] Use the trivial interval bound for recursive lengths below the Burgess
  core threshold.
- [x] Derive all rounded parameter hypotheses eventually from the core lower
  inequality and the quadratic no-wrap range.
- [x] Prove the eventual primitive estimate throughout that medium range.
- [ ] Prove the Pólya--Vinogradov large-length bridge.
- [ ] Discharge the prime finite-field complete-Weil residual.

There is no longer an open Burgess recursion or parameter-induction step. The
two remaining analytic tasks are the large-length Fourier bridge and the
source-specific prime finite-field estimates.

## Prime-equidistribution 2.70

- [x] Prove primitive Fourier inversion on `ZMod q`.
- [x] Prove the exact primitive Gauss-sum norm for composite conductors.
- [x] Bound the completed interval kernel by the reciprocal-distance
  geometric majorant.
- [x] Sum all frequencies with an explicit harmonic loss.
- [x] Absorb Pólya--Vinogradov into the large-length Burgess monomial.
- [x] Combine medium and large ranges and absorb finitely many conductors.
- [x] Export the primitive, all-character, and exact decimal Burgess
  contracts from complete Weil.
- [ ] Discharge the prime finite-field complete-Weil residual.

The Pólya--Vinogradov and all-prefix parts of Lemma 5.2 are complete. Its only
remaining analytic dependency is the source-specific complete-Weil estimate.

## Prime-equidistribution 2.71

- [x] State the sharp split Kummer estimate with coefficient
  `(t-1)*sqrt(p)`.
- [x] Include the full exceptional shape `C(c)*Q^(orderOf χ)` with `c≠0`.
- [x] Prove the tagged nondivisible root multiplicity excludes that shape.
- [x] Derive the split-polynomial, linear-quotient, and composite contracts.
- [x] Add every new declaration to the root and dependency audit.
- [ ] Prove the canonical Kummer finite-field estimate.

The two earlier prime residual presentations are now specializations of one
sharp analytic boundary. Lemma 5.2 remains conditional only on that theorem.

## Prime-equidistribution 2.72

- [x] Add the bounded-search-to-unbounded-existence certificate bridge.
- [x] Use the analytic fixed-length tail automatically for `H=1,2`.
- [x] Reduce `H=3` to `N<=24` and check every remaining start.
- [x] Reduce `H=4` to `N<=252` and check every remaining start.
- [x] Add arbitrary-baseline binomial-growth propagation.
- [x] Prove the rows `5<=H<=10` from small baselines and finite certificates.
- [x] Prove and audit `sylvesterSchurBelow_eleven`.
- [x] Verify `T=3H` binomial growth for `11<=H<=48`.
- [x] Close every start below `3H` with one bounded finite-type certificate.
- [x] Prove and audit `sylvesterSchurBelow_fortyNine`.
- [ ] Discharge the remaining finite Sylvester--Schur rectangle for `H>=101`.

The unrestricted theorem is still open, but its finite residual has strictly
fewer length rows and no new proposition parameter was introduced.

## Prime-equidistribution 2.73

- [x] Define and prove `SylvesterSchurAboveStart` from the large-length tail
  and fixed-length thresholds.
- [x] Prove `eventually_admissibleSylvesterSchurAtScale`.
- [x] Add scale-local large-prime versions of the normalization, maximal,
  recombination, and dyadic-window theorems while preserving the global
  Sylvester--Schur compatibility interfaces.
- [x] Package and prove the window-to-tail, tail-to-partial-sums, and
  partial-sums-to-log-saving transformations.
- [x] Prove and audit `taoTheorem17_of_explicitBurgess` without an unrestricted
  Sylvester--Schur argument.
- [x] Prove and audit
  `taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess`.
- [x] Remove the incidental unused-variable warnings in the compatibility
  wrapper.
- [ ] Prove the analytic Burgess endpoint.
- [ ] Prove `TaoCriticalSmoothSaddleAsymptoticConclusion`.

The still-open finite Sylvester--Schur rectangle is now independent of the
Theorem 1.7 dependency chain. Theorem 1.7 has exactly two remaining analytic
inputs: Burgess and the critical smooth-number saddle asymptotic.

## Prime-equidistribution 2.74

- [x] Rewrite a split polynomial character correlation as a product over its
  distinct roots with exact root-multiplicity exponents.
- [x] Construct `kummerRootPowerBase` by dividing every divisible root
  multiplicity by `orderOf χ`.
- [x] Prove the converse scalar-power criterion and the exact equivalence
  between Kummer nondegeneracy and existence of a nondivisible root
  multiplicity.
- [x] Package the distinct-root trace estimate as
  `TaoPrimeKummerRootProductWeilBound` and prove it equivalent to the existing
  polynomial Kummer endpoint.
- [ ] Prove the distinct-root Kummer trace bound.

The remaining Burgess theorem is now a pure finite-field trace estimate; no
polynomial splitting, scalar-power, or root-multiplicity conversion remains
outside its hypotheses.

## Prime-equidistribution 2.75

- [x] Prove the sharp one-root Kummer trace bound by character orthogonality.
- [x] Prove the sharp two-root Kummer trace bound through the formalized
  Jacobi-sum estimate.
- [x] Package
  `TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore` and prove it equivalent
  to the full polynomial Kummer endpoint.
- [x] Add a direct bridge from the restricted trace endpoint to the composite
  Burgess estimate.
- [ ] Prove the Kummer trace bound for at least three distinct roots.

Thus the remaining finite-field input excludes all elementary low-root cases.

## Prime-equidistribution 2.76

- [x] Prove the sharp three-root Kummer estimate whenever the character order
  divides the polynomial degree.
- [x] Separate active and inactive roots exactly and absorb the single
  deleted-point cost into the second square-root unit.
- [x] Package
  `TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible`.
- [x] Prove this refined residual equivalent to the full polynomial Kummer
  endpoint and connect it directly to composite Burgess.
- [ ] Prove the remaining four-or-more-root or degree-nondivisible three-root
  Kummer trace estimate.

For Tao's degree-divisible cleared Burgess polynomials, no three-root trace
case remains.

## Prime-equidistribution 2.77

- [x] Prove the converse active-root degree-divisibility identity.
- [x] Translate the three-active-root trace exactly to the existing
  three-point hypergeometric normal form.
- [x] Handle inactive-root and small-characteristic three-root cases without
  new analytic assumptions.
- [x] Package `TaoPrimeKummerRootProductWeilBoundFourRootsOrMore` and prove
  that it plus `TaoPrimeThreePointHypergeometricWeilBound` is equivalent to
  the full polynomial Kummer endpoint.
- [x] Connect this pair directly to composite Burgess.
- [ ] Prove the three-point hypergeometric estimate.
- [ ] Prove the four-or-more-root Kummer trace estimate.

All three-root algebra is now closed; its sole non-elementary case is exactly
the previously documented hypergeometric trace theorem.

## Prime-equidistribution 2.78

- [x] Prove the sharp degree-divisible four-root Kummer estimate from the
  existing three-point hypergeometric endpoint.
- [x] Cover every two-, three-, and four-active-root configuration and account
  exactly for inactive deleted points.
- [x] Package
  `TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible`.
- [x] Prove the corresponding full-Kummer equivalence and composite Burgess
  bridge under the three-point endpoint.
- [ ] Prove the three-point hypergeometric estimate.
- [ ] Prove the five-or-more-root or degree-nondivisible four-root Kummer
  estimate.

For Tao's degree-divisible polynomial family, the unresolved sharp trace
problem now starts at five distinct roots.

## Prime-equidistribution 2.79

- [x] State the exact four-point hypergeometric endpoint for four nontrivial
  local characters with nontrivial product.
- [x] Translate every degree-nondivisible four-active-root trace to that
  endpoint with the sharp `3*sqrt(p)` target.
- [x] Prove a general inactive-root deletion lemma and close all four-root
  active/inactive configurations.
- [x] Package `TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore` and prove
  its full-Kummer equivalence and composite bridge under the three- and
  four-point endpoints.
- [ ] Prove the three-point hypergeometric estimate.
- [ ] Prove the four-point hypergeometric estimate.
- [ ] Prove the five-or-more-root Kummer trace estimate.

All Kummer cases below five distinct roots are now reduced to explicit
lower-point analytic endpoints; no such endpoint is being assumed proved.

## Prime-equidistribution 2.80

- [x] Prove the pointwise and complete-sum five-root Möbius identities.
- [x] Derive the sharp `3*sqrt(p)+1` active-five-root estimate from the
  four-point endpoint.
- [x] Close every degree-divisible five-root active/inactive configuration
  with the sharp `4*sqrt(p)` Kummer coefficient.
- [x] Package the exact generic six-root-or-nondivisible-five-root residual.
- [x] Reduce the exact cleared Burgess polynomial to a source-specific
  six-active-root large-characteristic residual and connect it to the
  linear-quotient and composite endpoints.
- [ ] Prove the three-point hypergeometric estimate.
- [ ] Prove the four-point hypergeometric estimate.
- [ ] Prove the source-specific six-active-root residual.

For Tao's degree-divisible cleared family, no five-active-root analytic input
remains.

## Prime-equidistribution 2.81

- [x] Restrict the four-point endpoint on the Burgess path to four powers of
  the single source character.
- [x] Reduce all four exponents modulo `orderOf χ`.
- [x] Scale the finite points to the two-parameter Legendre form `0,1,t,u`.
- [x] Prove power-specific five-root, active-root, and split-polynomial
  bridges.
- [x] Route the six-active-root source residual through the reduced
  four-point power endpoint above `64`.
- [ ] Prove the reduced one-parameter three-point endpoint.
- [ ] Prove the reduced two-parameter four-point power endpoint.
- [ ] Prove the source-specific six-active-root residual.

The global four-unrelated-character endpoint is no longer an assumption on
the exact cleared Burgess production path.

## Prime-equidistribution 2.82

- [x] Prove the six-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped five-point power-character endpoint.
- [x] Reduce its five exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v`.
- [x] Close the exactly-six-active-root split-polynomial branch.
- [x] Package the seven-active-root source residual and its direct composite
  bridge.
- [ ] Prove the reduced one-parameter three-point endpoint.
- [ ] Prove the reduced two-parameter four-point endpoint.
- [ ] Prove the reduced three-parameter five-point endpoint.
- [ ] Prove the source-specific seven-active-root residual.

No exact cleared Burgess trace with six or fewer active roots remains outside
the named lower-point analytic endpoints.

## Prime-equidistribution 2.83

- [x] Define the complete cubefree Weil input literally at `r = 7`.
- [x] Propagate that fixed input through the fourteenth moment, amplification,
  rounded induction, Pólya--Vinogradov, and explicit Burgess endpoints.
- [x] Prove a fixed-`Fin 7` prime/prime-square CRT iteration independently of
  the stronger all-orders local predicate.
- [x] Package the prime linear-quotient and seven-active-root source residual
  at `r = 7` and connect them to the fixed composite endpoint.
- [ ] Prove the reduced one-parameter three-point endpoint.
- [ ] Prove the reduced two-parameter four-point endpoint.
- [ ] Prove the reduced three-parameter five-point endpoint.
- [ ] Prove the fixed-`r = 7` seven-active-root source residual.

The exact Burgess production path no longer assumes any complete character-
sum estimate at unused moment orders.

## Prime-equidistribution 2.84

- [x] Prove the seven-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped six-point power-character endpoint.
- [x] Reduce all six exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w`.
- [x] Close the exactly-seven-active-root split-polynomial branch.
- [x] Package both generic and fixed-`r=7` eight-active-root source residuals
  with direct composite bridges.
- [ ] Prove the reduced one-parameter three-point endpoint.
- [ ] Prove the reduced two-parameter four-point endpoint.
- [ ] Prove the reduced three-parameter five-point endpoint.
- [ ] Prove the reduced four-parameter six-point endpoint.
- [ ] Prove the fixed-`r=7` eight-active-root source residual.

No exact cleared Burgess trace with seven or fewer active roots remains
outside the named lower-point analytic endpoints.

## Prime-equidistribution 2.85

- [x] Prove that the fixed `r=7` cleared polynomial has at most fourteen
  distinct roots.
- [x] Transfer that upper bound to the active-root set.
- [x] Replace the unbounded eight-or-more source residual by the exact finite
  window `8 ≤ activeRoots.card ≤ 14`.
- [x] Connect the finite-window residual directly to the fixed prime quotient
  and composite complete-Weil endpoints.
- [ ] Prove the reduced lower-point endpoints.
- [ ] Close the seven remaining exact active-root cardinalities `8..14`.

No impossible higher-root case remains in the literal Burgess hypothesis.

## Prime-equidistribution 2.86

- [x] Prove the eight-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped seven-point power-character endpoint.
- [x] Reduce all seven finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z`.
- [x] Prove the sharp `6*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-eight-active-root split-polynomial branch.
- [x] Narrow the literal fixed-order residual to `9..14` and connect it to
  the prime quotient and composite endpoints.
- [ ] Prove the reduced one-, two-, three-, four-, and five-parameter trace
  endpoints.
- [ ] Close the six remaining exact active-root cardinalities `9..14`.

Every exact cleared Burgess trace with eight or fewer active roots is now
covered by an explicit projective reduction or a named reduced trace endpoint.

## Prime-equidistribution 2.87

- [x] Prove the nine-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped eight-point power-character endpoint.
- [x] Reduce all eight finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z,r₀`.
- [x] Prove the sharp `7*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-nine-active-root split-polynomial branch.
- [x] Narrow the literal fixed-order residual to `10..14` and connect it to
  the prime quotient and composite endpoints.
- [ ] Prove the reduced one- through six-parameter trace endpoints.
- [ ] Close the five remaining exact active-root cardinalities `10..14`.

Every exact cleared Burgess trace with nine or fewer active roots is now
covered by an explicit projective reduction or a named reduced trace endpoint.

## Prime-equidistribution 2.88

- [x] Prove the ten-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped nine-point power-character endpoint.
- [x] Reduce all nine finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z,r₀,s₀`.
- [x] Prove the sharp `8*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-ten-active-root split-polynomial branch.
- [x] Narrow the literal fixed-order residual to `11..14` and connect it to
  the prime quotient and composite endpoints.
- [ ] Prove the reduced one- through seven-parameter trace endpoints.
- [ ] Close the four remaining exact active-root cardinalities `11..14`.

Every exact cleared Burgess trace with ten or fewer active roots is now
covered by an explicit projective reduction or a named reduced trace endpoint.

## Prime-equidistribution 2.89

- [x] Prove the eleven-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped ten-point power-character endpoint.
- [x] Reduce all ten finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z,r₀,s₀,a₀`.
- [x] Prove the sharp `9*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-eleven-active-root split-polynomial branch.
- [x] Narrow the literal fixed-order residual to `12..14` and connect it to
  the prime quotient and composite endpoints.
- [ ] Prove the reduced one- through eight-parameter trace endpoints.
- [ ] Close the three remaining exact active-root cardinalities `12..14`.

Every exact cleared Burgess trace with eleven or fewer active roots is now
covered by an explicit projective reduction or a named reduced trace endpoint.

## Prime-equidistribution 2.90

- [x] Prove the twelve-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped eleven-point power-character endpoint.
- [x] Reduce all eleven finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀`.
- [x] Prove the sharp `10*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-twelve-active-root split-polynomial branch.
- [x] Narrow the literal fixed-order residual to `13..14` and connect it to
  the prime quotient and composite endpoints.
- [ ] Prove the reduced one- through nine-parameter trace endpoints.
- [ ] Close the two remaining exact active-root cardinalities `13..14`.

Every exact cleared Burgess trace with twelve or fewer active roots is now
covered by an explicit projective reduction or a named reduced trace endpoint.

## Prime-equidistribution 2.91

- [x] Prove the thirteen-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate and normalize the source-shaped twelve-point endpoint.
- [x] Prove the sharp `11*sqrt(p)+1` exact-cardinality bridge.
- [x] Narrow the literal fixed-order residual to exact cardinality fourteen.
- [ ] Prove the reduced trace endpoints through twelve points.

## Prime-equidistribution 2.92

- [x] Prove the fourteen-root pointwise Möbius identity and complete-sum formula.
- [x] Isolate the source-shaped thirteen-point power-character endpoint.
- [x] Reduce all fourteen finite exponents modulo `orderOf χ`.
- [x] Scale its marked points to `0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀`.
- [x] Prove the sharp `12*sqrt(p)+1` active-root estimate.
- [x] Close the exactly-fourteen-active-root split-polynomial branch.
- [x] Eliminate the literal fixed-`r=7` source-cardinality residual and connect
  the reduced endpoints directly to prime quotient and composite bounds.
- [ ] Prove the reduced trace endpoints through thirteen points.

Every possible active-root cardinality of the literal cleared `r=7` Burgess
polynomial is now covered by an explicit projective reduction or a named
reduced trace endpoint.

## Prime-equidistribution 2.93

- [x] Transcribe Erdős--Selfridge Theorem 2 as the exact source-shaped
  prime-multiplicity proposition.
- [x] Prove that the local `Ioc N (N+H)` product is the source product over
  `Icc (N+1) (N+H)`.
- [x] Construct the least prime `p^(H)` and prove its minimality.
- [x] Use Bertrand to discharge `p^(H) <= N+H` throughout `H<N`.
- [x] Specialize the valuation witness to exponent two and derive the exact
  residual square conclusion, the full square proposition, and the existing
  public Theorem 1.10 consumers.
- [x] Re-audit `scottdhughes/erdos137` at commit
  `3027d9add77a1f2b203977501987c7def955475d`; no declaration is imported,
  because its useful unconditional interval facts are already subsumed and it
  does not prove the required perfect-power theorem.
- [ ] Recursively formalize the prime-multiplicity theorem itself (or the
  weaker square core) with no unproved source proposition.

The remaining Erdős--Selfridge boundary is now the paper's stronger Theorem 2
statement itself; all interval, least-prime, Bertrand, valuation, and public
Theorem 1.10 translation steps are compiled and audited.

## Prime-equidistribution 2.94

- [x] Define the canonical `l`-power-free and `l`-power-root factorizations.
- [x] Prove the exact decomposition `m=a*x^l` and `v_p(a)<l`.
- [x] Strengthen prime uniqueness to `H<=p`, including the boundary `p=H`.
- [x] Identify the full interval-product valuation with the valuation of its
  unique divisible factor.
- [x] Express negation of source Theorem 2 as a structured counterexample.
- [x] Derive equation (3) simultaneously for every counterexample factor, with
  all coefficient prime factors below `H`.
- [x] Formalize source Lemma 1: every product of fewer than `l` distinct
  coefficients is distinct, equivalently no quotient is an `l`-th power.

The recursive Erdős--Selfridge formalization has now entered the body of the
proof; equation (3) and its valuation-localization prerequisite are complete.

## Prime-equidistribution 2.95

- [x] Derive source equation (2), `H^l<N`, from counterexample failure and the
  Sylvester--Schur large-prime witness.
- [x] Prove equation (4): distinct equally sized subfamilies of the interval
  have unequal products whenever their cardinality is below `l`.
- [x] Prove the strict powered interval-gap upper bound needed by Lemma 1.
- [x] Prove the complementary lower gap for ratios of coprime positive
  rational `l`-th powers.
- [x] Cancel arbitrary numerator/denominator gcds and exclude every rational
  `l`-th-power ratio between distinct interval subproducts.
- [x] Transfer the result through equation (3) to the canonical power-free
  coefficients, proving both the stronger ratio clause and displayed
  distinctness conclusion of source Lemma 1.
- [x] Package the full lemma directly from failure of Theorem 2 and the
  existing `SylvesterSchurConclusion` contract.
- [x] Formalize source Lemma 2's maximal-valuation deletion and resulting
  factorial-divisibility statement.

The full source Lemma 1 is now kernel-checked. The remaining
Erdős--Selfridge proof proceeds with Lemma 2 and its later case/counting
arguments; the Sylvester--Schur finite residual and final Theorem 2 closure
remain explicit rather than silently assumed.

## Prime-equidistribution 2.96

- [x] Define the maximal-valuation position chosen for each prime `p<H` and
  prove its membership and universal maximality properties.
- [x] Compute the exact distance product outside one position as
  `m!*(H-1-m)!`.
- [x] Bound each retained coefficient valuation by the corresponding distance
  valuation and derive divisibility by `(H-1)!`.
- [x] Prove that the core deletion set lies in `range H` and has cardinality
  at most `primeCounting (H-1)`.
- [x] Pad duplicate prime choices to an exact deletion set of source
  cardinality `primeCounting (H-1)` and prove the exact survivor cardinality
  `H-primeCounting (H-1)`.
- [x] Package equation (9) as full source Lemma 2 for the canonical
  power-free coefficients.
- [x] At exponent two, use squarefreeness to bound each discarded prime
  valuation by one and prove source equation (21).
- [x] Prove that every 36-term interval has exactly twelve values divisible
  by `4` or `9`, hence at most 24 squarefree values, in both interval and
  source-offset form.
- [x] Complete equation (22)'s product lower bound from coefficient
  distinctness and the 36-term density estimate.
- [ ] Formalize the remaining large-length contradiction through equation
  (23), then discharge the finite residual lengths.

Lemmas 1 and 2 of the Erdős--Selfridge proof are now kernel-checked. The next
route toward the no-square theorem is the paper's Section 3 size comparison;
its explicit numerical and finite-case gates remain open.

## Prime-equidistribution 2.97

- [x] Prove the general exact formula for multiples of `d` in `(N,N+L]`
  when `d∣L`.
- [x] Apply inclusion--exclusion to `4`, `9`, and `36` and prove the exact
  cardinality twelve.
- [x] Exclude these positions using `squarefree_iff_prime_squarefree` and
  prove the source cardinality bound 24.
- [x] Transport the result to the interval-offset indexing `N+(i+1)`.
- [x] Import the module through the production root and audit all four main
  endpoints.
- [x] Prove the full numerical product inequality (22) for `H≥64`
  (completed in release 2.98).

The first sentence of Section 3.1 was kernel-checked here without finite
enumeration; release 2.98 completes its equation-(22) product consequence.

## Prime-equidistribution 2.98

- [x] Upgrade the 36-block bound to `3*Q(M)≤2*M` for every `M≥44`.
- [x] Identify the first 64 squarefree naturals as the values at most 103
  avoiding `4`, `9`, `25`, and `49`.
- [x] Verify the strict cleared-denominator base product inequality.
- [x] Prove prefix-cardinality formulas for increasing finset enumerations
  and minimality of the first-64 squarefree product.
- [x] Propagate the inequality to every `H≥64` by maximum deletion.
- [x] Use source Lemma 1 to prove coefficient injectivity and instantiate
  equation (22) for every square-case counterexample.
- [ ] Formalize equation (23)'s 2- and 3-adic valuation inequalities and
  primorial comparison.

Equation (22) is now kernel-checked exactly as
`3^H*H! < 2^H*∏aᵢ`. The next large-length obligation is equation (23).

## Prime-equidistribution 2.99

- [x] Define the canonical squarefree coefficient product used in equations
  (21)--(23) and prove it is positive.
- [x] Prove that every prime below `H` occurs exactly once in the source
  primorial.
- [x] Extract the complete 2- and 3-adic content from equation (21) as an
  exact natural-number divisibility theorem.
- [x] Combine the extracted equation-(21) ledger with the canonical strict
  equation-(22) inequality.
- [ ] Prove the paper's lower bounds for the 2- and 3-adic valuations of
  `(H-1)!`.
- [ ] Prove the upper bounds for the corresponding valuations of the
  squarefree coefficient product.
- [ ] Simplify these bounds to displayed equation (23) and insert the
  primorial estimate giving the contradiction for `H≥71`.

The algebraic cancellation linking equations (21) and (22) is now
kernel-checked. Only the explicit counting/logarithmic estimates and their
numerical consequence remain in the large-length square case.

## Prime-equidistribution 3.00

- [x] Prove the binary and ternary digit-sum logarithmic inequalities.
- [x] Deduce the source lower bounds for the `2`- and `3`-adic valuations of
  `(H-1)!`.
- [x] Prove exact halving and thirding recurrences for odd interval
  valuations, with uniform discrepancy estimates.
- [x] Identify those interval counts with the valuations of the canonical
  squarefree coefficient product and deduce both source upper bounds.
- [x] Cancel `(H-1)!` in `ℝ`, divide out the coefficient valuations, normalize
  to real powers, and insert all four bounds.
- [ ] Simplify the logarithmic real-power inequality to the displayed
  constant `14/3` in equation (23).
- [ ] Insert the primorial estimate and finish the finite residual square
  cases.

The large-length proof now stops at the exact logarithmic inequality directly
before the source's `14/3` simplification.

## Prime-equidistribution 3.01

- [x] Rewrite the two logarithmic valuation factors exactly using `rpow` and
  `logb` identities.
- [x] Bound the residual root factor by `4H² ≤ (14/3)H²`.
- [x] Prove the displayed equation (23) for every canonical counterexample
  with `64≤H<N`.
- [ ] Apply the explicit primorial estimate and derive the large-length
  contradiction.
- [ ] Complete the remaining finite square lengths.

## Prime-equidistribution 3.09

- [x] Prove sharp ceiling and arbitrary finite-prime union bounds.
- [x] Establish five surviving positions for `18 <= H <= 20`.
- [x] Transfer avoidance to coefficient coprimality and divisibility by six.
- [x] Exclude every square-case failure with `3 <= H <= 20`.
- [ ] Formalize the next small-prime count beginning at `H=21`.

## Prime-equidistribution 3.10

- [x] Prove the nine-survivor ceiling sum for every `21 <= H <= 70`.
- [x] Transfer prime avoidance to divisibility of coefficients by `30`.
- [x] Exclude every finite square-case failure with `3 <= H < 71`.
- [ ] Formalize the explicit Section 3.1 cutoff for every `H >= 71`.

## Prime-equidistribution 3.11

- [x] Prove a rational lower bound `31335/10000` for the equation-(23) base.
- [x] Prove the explicit exponential-growth comparison for every `H >= 297`.
- [x] Kernel-check the actual prime-product comparison for all `71 <= H <= 296`.
- [x] Connect the full square conclusion conditional on the named `3^H`
  primorial statement.
- [x] Prove `prod_{p<H} p <= 3^H` in Lean and discharge that final condition
  (release 3.12).

## Prime-equidistribution 3.03

- [x] Embed all canonical squarefree coefficients into the finite set of
  positive divisors of `prod_{p<H} p`.
- [x] Rule out `H=3` by the two available coefficient candidates.
- [x] Prove directly that four consecutive positive integers cannot have
  square product.
- [x] Rule out `H=4` by showing its four coefficients are exactly
  `1,2,3,6`.
- [x] Rule out `H=5` by the four available coefficient candidates.
- [x] Formalize the `H=6` residue split.
- [ ] Formalize the remaining small-prime counts through `H<71`.

## Prime-equidistribution 3.04

- [x] Count exactly the five length-six positions avoiding `5` outside the
  exceptional residue class.
- [x] Prove coefficients at those positions lie among the four candidates
  supported on `2` and `3`.
- [x] Handle `5 | N+1` by showing the middle four coefficients exhaust
  `1,2,3,6` and force a square four-term subproduct.
- [x] Exclude every square-case failure with `3 <= H <= 6`.
- [ ] Formalize the remaining small-prime counts for `7 <= H < 71`.

## Prime-equidistribution 3.05

- [x] Enumerate the length-seven residue classes modulo five and prove that at
  least five positions avoid `5`.
- [x] Place their canonical coefficients among the four products supported on
  `2` and `3`.
- [x] Exclude every square-case failure with `3 <= H <= 7` while retaining the
  release-3.04 compatibility endpoint.
- [ ] Formalize the `H=8` exceptional residue split and the remaining counts
  for `9 <= H < 71`.

## Prime-equidistribution 3.06

- [x] Reduce the length-eight ordinary count to the `35` residue classes.
- [x] Prove that the unique deficient class is exactly
  `7 | N+1` and `5 | N+2`.
- [x] Close that class using the middle four terms and the square-product
  contradiction.
- [x] Exclude every square-case failure with `3 <= H <= 8`.
- [ ] Formalize the remaining small-prime counts for `9 <= H < 71`.

## Prime-equidistribution 3.07

- [x] Prove the modulo-`35` five-position count and extend it through
  `9 <= H <= 11`.
- [x] Prove the modulo-`385` five-position count and extend it through
  `12 <= H <= 13`.
- [x] Reduce the surviving coefficient candidates in both blocks to
  `1,2,3,6` without large finite evaluation.
- [x] Exclude every square-case failure with `3 <= H <= 13`.
- [ ] Formalize the remaining small-prime counts for `14 <= H < 71`.

## Prime-equidistribution 3.08

- [x] Replace large-modulus enumeration with a reusable union bound for four
  prime-divisibility filters.
- [x] Prove five surviving coefficients for every `14 <= H <= 17`.
- [x] Exclude every square-case failure with `3 <= H <= 17`.
- [ ] Extend the union-count framework from `H=18`, where prime `17` enters.

## Prime-equidistribution 3.02

- [x] Identify the prime product below `H` with `primorial (H-1)`.
- [x] Derive the eventual bound `prod_{p<H} p <= 3^H` from the frozen PNT.
- [x] Prove the effective equation-(23) base is strictly larger than `3` by
  exact rational root comparisons.
- [x] Absorb `(14/3)H^2` by exponential growth and rule out every sufficiently
  large square-case multiplicity failure.
- [ ] Replace the extracted threshold by the paper's explicit numerical
  primorial cutoff.
- [ ] Complete the remaining finite square lengths.

## Prime-equidistribution 3.12

- [x] Formalize the Sylvester recurrence, reciprocal telescoping identity, and
  strict quotient-floor sum used by Hanson.
- [x] Prove that every prime below `n` divides Hanson's factorial coefficient.
- [x] Build the fixed `2,3,7,43` five-part multinomial and its exact weighted
  entropy bound.
- [x] Prove the integer base gap, floor-loss absorption, and the finite block
  certificate below `1400`.
- [x] Prove `ErdosSelfridgeThreePrimorialConclusion` for every natural length
  and remove it from the square-case assumptions.
- [ ] Prove the remaining unrestricted `SylvesterSchurConclusion` internally.

## Prime-equidistribution 3.13

- [x] Derive the general factorial/exponent gap
  `H! 2^r < (N+1)^(H-r)` from the binomial factorization envelope.
- [x] Specialize to the exact exponent `r=pi(H)` and prove the cutoff
  `H! 2^pi(H)+1`.
- [x] Recover the classical `H! 2^(H-1)+1` cutoff as a checked corollary.
- [x] Replace the `H^H+1` residual by the exact-prime-count factorial finite
  rectangle and connect it to `SylvesterSchurConclusion`.
- [ ] Discharge the remaining rectangle for lengths `H>=49`.

## Prime-equidistribution 3.14

- [x] Kernel-check the `3H` binomial-growth baseline for every
  `49<=H<=100`.
- [x] Kernel-check every bounded start below the `3H` baseline in that range.
- [x] Assemble `sylvesterSchurBelow_oneHundredOne`, uniform over all starts.
- [ ] Discharge the remaining exact-prime-count factorial rectangle for
  `H>=101`.

## Prime-equidistribution 3.15

- [x] Split the binomial factorization at `sqrt n` and bound the low-prime
  contribution by `n^sqrt(n)`.
- [x] Prove that high supported primes have exponent at most one.
- [x] In the central range `2k<=n`, eliminate supported primes in
  `(n/3,k]` and bound the remainder by `primorial (n/3)`.
- [x] Insert Hanson's all-length theorem and export explicit `3`-power gap
  criteria for binomial coefficients and consecutive products.
- [ ] Prove a uniform explicit numerical gap on a large-length central
  region and finish the remaining `H>=101` rectangle.

## Prime-equidistribution 3.16

- [x] Prove an integral exponential bound absorbing
  `(3H)^sqrt(3H)` into `2^(H/4)` from an explicit cutoff.
- [x] Prove the remaining `3^(H+1)` versus `4^H` comparison by fixed-base
  induction.
- [x] Close every central start `H<N<=2H` uniformly for `H>=34134`.
- [x] Export and audit both binomial and consecutive-product endpoints.
- [ ] Close noncentral starts for large `H` and the finite bridge
  `101<=H<34134`.

## Prime-equidistribution 3.17

- [x] Prove an explicit Chebyshev logarithmic margin at upper index `1024H`.
- [x] Establish the binomial-growth baseline there and propagate it to every
  larger upper index.
- [x] Absorb the square-root/Hanson envelope uniformly below `1024H` for
  `H>=4^101`.
- [x] Prove the effective all-start Sylvester--Schur tail.
- [x] Reduce unrestricted Sylvester--Schur to the concrete rectangle
  `101<=H<4^101`, `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that explicit finite rectangle.

## Prime-equidistribution 3.18

- [x] Prove `log H<=sqrt(H)/40` uniformly from `H>=250000`.
- [x] Move the explicit Chebyshev binomial-growth baseline from `1024H` to
  `64H`.
- [x] Absorb the square-root/Hanson envelope uniformly through `64H`.
- [x] Close every start for `H>=250000` and reduce unrestricted
  Sylvester--Schur to `101<=H<250000`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that sharpened finite rectangle.

## Prime-equidistribution 3.19

- [x] Retain the exact low-prime exponent `pi(sqrt(n))` in the
  square-root/Hanson envelope.
- [x] Prove by reduced-residue counting and a finite kernel certificate that
  `pi(m)<=m/4` for every `m>=120`.
- [x] Prove the prime-counted near gap through `64H` for every `H>=10000`.
- [x] Establish and propagate the far-branch binomial-growth baseline on
  `10000<=H<250000`, using the release-3.18 tail above that band.
- [x] Close every start for `H>=10000` and reduce unrestricted
  Sylvester--Schur to `101<=H<10000`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that sharpened finite rectangle.

## Prime-equidistribution 3.20

- [x] Kernel-check `6*pi(m)<=m+84` for every `100<=m<800`.
- [x] Prove `log H<=13*sqrt(H)/100` from `H>=6000`.
- [x] Close the near branch throughout `6000<=H<10000`.
- [x] Generalize the far-branch baseline to `H>=2200` and close the
  complementary starts on the bridge.
- [x] Reduce unrestricted Sylvester--Schur to `101<=H<6000`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that sharpened finite rectangle.

## Prime-equidistribution 3.21

- [x] Kernel-check `4*pi(m)<=m+12` for every `60<=m<400`.
- [x] Prove the near gap through `16H` on `2200<=H<3000`.
- [x] Prove the near gap through `20H` on `3000<=H<6000`.
- [x] Establish binomial-growth baselines at both adaptive transitions and
  propagate them through the far branches.
- [x] Close every start for `H>=2200` and reduce unrestricted
  Sylvester--Schur to `101<=H<2200`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that sharpened finite rectangle.

## Prime-equidistribution 3.22

- [x] Kernel-check the endpoint certificates proving `pi(H)<=H/5` on
  `360<=H<1134` and `pi(H)<=H/6` on `1134<=H<2200`.
- [x] Replace the expensive final prime-count endpoints above `1906` by four
  exact coprimality counts modulo `210`.
- [x] Prove the near gaps through `5H`, `6H`, and `5H` on the three adaptive
  bands beginning at `512`, `625`, and `1134`.
- [x] Establish and propagate all three matching far binomial-growth
  baselines.
- [x] Close every start for `H>=512` and reduce unrestricted
  Sylvester--Schur to `101<=H<512`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge that sharpened finite rectangle.

## Prime-equidistribution 3.23

- [x] Kernel-check the central binomial-growth baseline at `n=2H` on
  `121<=H<512` away from the five exact exceptional lengths.
- [x] Prove the prime-counted near gap through `n=281` for `H=139,140` and
  the matching exact binomial-growth baseline.
- [x] Prove the prime-counted near gap through `n=403` for
  `H=199,200,201` and the matching exact binomial-growth baseline.
- [x] Close every start for `H>=121` and reduce unrestricted
  Sylvester--Schur to the twenty rows `101<=H<121`,
  `N+1 < H! * 2^pi(H)+1`.
- [ ] Discharge those twenty remaining length rows.

## Prime-equidistribution 3.24

- [x] Kernel-check the common binomial-growth baseline at upper index `243`
  for every `101<=H<121`.
- [x] Kernel-check all 420 starts below that baseline with one bounded prime
  divisor certificate.
- [x] Prove the unrestricted `SylvesterSchurConclusion`.
- [x] Insert it into the Hanson/Erdős--Selfridge chain and prove the exact
  unconditional square specialization used by factorial fibers.
- [x] Export the unconditional two-element factorial-fiber bound and remove
  Erdős--Selfridge from the remaining Theorem 1.10 hypotheses.

## Prime-equidistribution 3.25

- [x] Identify each literal product-restricted Type II Vaughan double block
  with the exact Type II outer sum.
- [x] Prove the outer Cauchy--Schwarz bridge and the exact bounded/full inner
  support comparison.
- [x] Insert the source beta/gamma bounds `1` and `log(2B)` and compose the
  result with the mixed Weyl--Vinogradov squared-inner-sum estimate.
- [x] Bound the full product convolution norm by the sum of square roots of
  arbitrary double-block square majorants.
- [ ] Prove `VinogradovExponentialSumEstimate` and sum/simplify the Type I/II
  majorants needed by Theorem 2.5.

## Prime-equidistribution 3.26

- [x] Prove exact vanishing of every small outer Type II block from the
  Möbius-tail cutoff.
- [x] Prove exact vanishing of every small inner Type II block from the
  divisor-tail cutoff; retain the independent diagonal estimate as a fallback.
- [x] Package the zero/large--large split in an explicit source block
  majorant and sum it over the complete literal Vaughan Type II convolution.
- [x] Convert a uniform block-square bound into the exact family loss
  `(log₂ B+1)^204 sqrt(R)`.
- [x] Instantiate the source cutoffs and block-scale bounds uniformly.
- [ ] Simplify the explicit all-block majorant to the required logarithmic
  saving.
- [ ] Prove `VinogradovExponentialSumEstimate` and combine the resulting Type
  II estimate with the quantitative Type I and Fourier assembly.

## Prime-equidistribution 3.27

- [x] Replace budget-only small-band tests by the actual dyadic cutoff tests
  `2*2^s≤U` and `2*2^t≤V`.
- [x] Define the exact source product support, annihilate empty blocks, and
  prove that every contributing analytic product scale is at most `2B`.
- [x] Derive every surviving block's phase-scale premise from the single
  global inequality `2B*(log B)^d≤|N|`.
- [x] Define `vaughanSourceTailCutoff B = ⌊B^(1/3)⌋₊` and prove eventual
  dominance over both `2*vaughanShortIntervalBudget B` and `2*B^(1/4)`.
- [x] Export the complete canonical-cutoff Type II family theorem with no free
  cutoff parameters and no blockwise scale hypotheses.
- [ ] Simplify the explicit summed majorant to the target logarithmic saving
  after proving `VinogradovExponentialSumEstimate`.
- [ ] Combine the resulting Type II bound with Type I and the finite Fourier
  assembly for Theorem 2.5.

## Prime-equidistribution 3.28

- [x] Fix the minimal canonical derivative-order family to `{5,6}` and export
  the all-family theorem with no order-set parameter.
- [x] Bound every canonical short-block length by `B/(log B)^100`, its outer
  block cardinality by that length, and its component logarithm by `2log B`.
- [x] Derive the literal quarter-power lower bounds for both surviving dyadic
  scales from the cube-root cutoff.
- [x] Define the canonical geometric block majorant and prove that it bounds
  the exact piecewise source majorant on every canonical block.
- [ ] Simplify the geometric majorant and its full square-root family sum to
  the target logarithmic saving after proving `VinogradovExponentialSumEstimate`.
- [ ] Combine the resulting Type II bound with Type I and the finite Fourier
  assembly for Theorem 2.5.

## Prime-equidistribution 3.29

- [x] Retain the separate dyadic source widths `2^s/(log B)^100` and
  `2^t/(log B)^100` in the canonical block majorant.
- [x] Prove the product-support bounds for `2^s2^t`, `2^(2s+t)`, and the
  endpoint-weighted monomial occurring in both analytic error terms.
- [x] Expand the block majorant exactly and expose logarithmic denominators
  `298`, `197`, and `297`.
- [x] Use the inner cube-root cutoff to strengthen the diagonal monomial to
  `D²E≤B²/B^(1/4)`.
- [x] Propagate the power-saved product majorant through the complete
  conditional canonical Type II convolution.
- [x] Absorb the phase and endpoint factors and evaluate the complete
  square-root family with an explicit real-logarithmic loss.
- [ ] Choose the phase and source exponents and absorb the flattened ledger
  into the target arbitrary logarithmic saving.
- [ ] Prove `VinogradovExponentialSumEstimate` and combine Type II with Type I
  and the finite Fourier assembly.

## Prime-equidistribution 3.30

- [x] Replace every surviving reciprocal phase by
  `(log B)^(-d/1024)` using the global phase lower bound.
- [x] Replace every inverse outer endpoint by the fixed power
  `B^(-1/4096)`.
- [x] Flatten the diagonal term to `B^(7/4)/(log B)^298` and expose the
  complete block-independent squared ledger.
- [x] Evaluate the canonical double-family sum exactly and bound its discrete
  loss by `(3 log B)^204`.
- [x] Absorb the explicit ledger into `B/(log P)^A` after choosing `d,T`
  and recording the source comparison `B≤2P`.
- [ ] Prove `VinogradovExponentialSumEstimate` and combine Type II with Type I
  and the finite Fourier assembly.

## Prime-equidistribution 3.31

- [x] Prove that each fixed negative power of the source scale eventually
  dominates an arbitrary negative logarithmic power.
- [x] Compress the explicit squared-block ledger to
  `C B²(log P)^(-E)` under the two exact exponent inequalities.
- [x] Extract the square root and cancel the full `(3log B)^204` family loss
  with `E=2S+408`.
- [x] Fix `d=2048S+216064`, `T=2S+111`, and the matching Vinogradov exponent
  and export the conditional source-form bound `C B/(log P)^S`.
- [ ] Prove `VinogradovExponentialSumEstimate` and combine the finished Type II
  estimate with quantitative Type I and the finite Fourier assembly.

## Prime-equidistribution 3.32

- [x] Rewrite each literal canonical Type I Vaughan block as the exact
  product-restricted weighted outer sum.
- [x] Identify the inner fiber over `[a,b)` with the exact natural interval
  `[⌈a/m⌉,⌈b/m⌉)` and expose the rescaled phase `(N/m,M/m^j)`.
- [x] Propagate the unit and `log(2B)` coefficient envelopes through both
  complete canonical outer families.
- [x] Connect the logarithmically weighted inner directly to the existing
  finite Abel-summation prefix interface.
- [ ] Prove uniform quantitative cancellation for these exposed Type I
  prefixes, then combine Type I, Type II, low frequency, and Fourier assembly.

## Prime-equidistribution 3.33

- [x] Filter each Type I block to its literal nonzero short-coefficient
  support before applying the triangle inequality.
- [x] Prove the active supports lie in `[1,U]` and `[1,UV]`, hence have
  cardinalities at most `U` and `UV`.
- [x] Propagate a uniform inner estimate through all
  `(logâ‚‚ B+1)^102` canonical blocks without a spurious factor `B`.
- [x] Export the exact complete-family losses
  `(logâ‚‚ B+1)^102 U Q` and `(logâ‚‚ B+1)^102 log(2B) UV Q`.
- [ ] Derive the required uniform `Q` from reciprocal-phase cancellation and
  absorb the explicit cutoff and family losses.

## Prime-equidistribution 3.34

- [x] Prove antitonicity of `reciprocalPhaseScale` in a positive scale.
- [x] Prove exact Type I scale invariance under
  `(N,M,X) -> (N/m,M/m^j,X/m)` and its multiplication form.
- [x] Prove positivity and dyadic containment for the ceiling-divided fiber
  scale `ceil(P/m)`.
- [x] Transfer `reciprocalPhaseScale N M j P <= (P/m)^4` to the rounded
  rescaled Type I scale.
- [ ] Discharge the four-step Weyl endpoint-buffer and effective-error
  premises uniformly on Type I fibers, then instantiate the active callback.

## Prime-equidistribution 3.35

- [x] Specialize the four-step endpoint geometry to the source case `j=2`.
- [x] Prove that effective error at most one bounds the optimized range by the
  interval length.
- [x] Reconstruct `[D,2D)` exactly from at most ten canonical short blocks.
- [x] Prove every nonempty block satisfies the five-length endpoint margin.
- [x] Prove the quadratic phase scale loses at most a factor four across a
  dyadic window and transfer one source effective-error budget to every block.
- [x] Apply the two-term four-step Weyl estimate to each nonempty block.
- [x] Uniformize the local widths, sum the ten block estimates, and instantiate
  both active Type I callbacks.

## Prime-equidistribution 3.36

- [x] Bound every local two-term width by the source width
  `(F/D^5+4/F)^(1/1024)`.
- [x] Export one nonnegative uniform block majorant and sum the at-most-ten
  blocks on `[D,2D)`.
- [x] Generalize the exact decomposition and endpoint geometry to every
  subinterval of `[D,2D)`.
- [x] Prove the same factor-ten bound uniformly for all such subintervals,
  including all Abel prefixes.
- [x] Substitute the rescaled Type I parameters, expose the exact source-budget
  premises over active `m`, and instantiate the complete-family callbacks.

## Prime-equidistribution 3.37

- [x] Fix the quadratic derivative orders to `{5,6}` and define the explicit
  ten-block majorant after `(N,M,D) -> (N/m,M/m²,ceil(P/m))`.
- [x] Bound the literal unweighted Type I fiber by that majorant.
- [x] Use uniform arbitrary-prefix control and finite Abel summation to bound
  the literal logarithmically weighted fiber.
- [x] Insert both fiber estimates into the exact active-support Vaughan family
  bounds with losses `U` and `log(2B)UV`.
- [x] Derive active-index admissibility and one sufficiently small common `Q`
  from the eventual source parameter choices, then absorb all displayed
  family and coefficient losses.

## Prime-equidistribution 3.38

- [x] Define the exact fixed-constant Vinogradov majorant after the literal
  Type I substitution.
- [x] Prove its arbitrary-subinterval estimate on the rounded dyadic fiber.
- [x] Split each fiber at `F(D)=D^4`, imposing only the branch-local Weyl or
  Vinogradov hypotheses.
- [x] Propagate the hybrid estimate through every Abel prefix and both full
  active Vaughan Type I families.
- [x] Derive the high-branch cutoff and numerical smallness conditions
  eventually from the source exponential bound and `log D >= c log P`.
- [x] Prove the low-branch effective-error budget uniformly for the canonical
  active cutoffs and absorb both hybrid majorants into the target log saving.

## Prime-equidistribution 3.39

- [x] Compare the source phase scale at `P` with the transformed scale at
  `ceil(P/m)`, with an explicit factor-four ceiling loss.
- [x] Derive the complete low-branch Weyl effective-error budget from
  `F(D) <= D^4` above one explicit absolute threshold.
- [x] Prove that both canonical active Type I supports force
  `ceil(P/m) >= B^(1/4)` eventually.
- [x] Deduce the complete hybrid admissibility predicate for every active
  index from the global source lower and exponential upper frequency bounds.
- [x] Bound and sum the explicit hybrid majorants with sufficient logarithmic
  saving to close both Type I convolution families.

## Prime-equidistribution 3.40

- [x] Bound the reciprocal sum over the first canonical active support by
  the exact harmonic number at cutoff `U`.
- [x] Bound the reciprocal sum over the second canonical active support by
  the exact harmonic number at cutoff `UV`.
- [x] Prove complete-family aggregation theorems for inner bounds of the form
  `(P/m)Q`, replacing the losses `U` and `UV` by harmonic factors.
- [x] Prove branch-sensitive logarithmic bounds for the explicit Weyl and
  Vinogradov fiber majorants and instantiate the reciprocal-weighted family
  theorems.

## Prime-equidistribution 3.41

- [x] Replace the maximum hybrid envelope by the exact low/high branch
  majorant, so an unused Weyl term is never charged on a high fiber.
- [x] Bound the high branch by `3 D (log B)^(-T)` from the named source
  Vinogradov hypothesis.
- [x] Reduce the low Weyl width to
  `(1/D + 16/(log B)^d)^(1/1024)` and absorb it using active-fiber geometry.
- [x] Insert the common `(P/m)` estimate into both reciprocal-weighted
  canonical Type I family theorems.
- [x] Verify the exact total loss 104 and export arbitrary-saving family
  bounds under `S+106<=3A` and `1024*(S+105)+1<=d`.
- [x] Combine the completed Type I and Type II estimates through Vaughan's
  identity to obtain the quantitative Mangoldt reciprocal-phase estimate.

## Prime-equidistribution 3.42

- [x] Prove the initial Vaughan cutoff term vanishes once the source interval
  begins above the canonical cube-root cutoff.
- [x] Assemble the two Type I components and the Type II component through
  the exact source-oriented Vaughan identity.
- [x] Use the common phase exponent `2048*S+216064` and export an arbitrary-
  saving quadratic Mangoldt reciprocal-phase theorem.
- [x] Import the new module in the production root and audit every exported
  theorem.
- [x] Derive both displayed scale interfaces from one source-facing frequency
  range.

## Prime-equidistribution 3.43

- [x] Prove `reciprocalPhaseScale N N 2 P <= 2*|N|` for positive natural
  scales.
- [x] Derive the logarithmic Type I scale lower bound from the source lower
  bound on `|N|`.
- [x] Derive the fixed threshold `64<=F` from the same source lower bound and
  the explicit common phase exponent.
- [x] Export the quadratic Mangoldt estimate with a single lower/upper
  source-frequency range.
- [x] Perform the Mangoldt-to-prime partial-summation transfer.
- [ ] Connect the resulting prime estimate to the smooth periodic Fourier
  assembly.

## Prime-equidistribution 3.44

- [x] Prove the exact endpoint identity converting `[a,b)` to the frozen
  prime-power local-interval convention.
- [x] Transfer the explicit prime-power-tail estimate to half-open dyadic
  intervals and derive a uniform quarter-power-saving envelope.
- [x] Absorb the prime-power tail into an arbitrary negative logarithmic
  power uniformly over every initial prefix.
- [x] Remove prime powers from the Mangoldt estimate and obtain a uniform
  logarithmically weighted prime estimate.
- [x] Apply reverse Abel summation and export the high-frequency unweighted
  quadratic prime estimate with the unified source range.
- [x] Bound the logarithmic integral and assemble the discrepancy for the
  diagonal `(1,1)` Fourier mode.
- [ ] Extend the prime and integral estimates to unequal mode coefficients,
  then combine them with the low-frequency and zero-mode contributions.

## Prime-equidistribution 3.45

- [x] Identify the half-open `(1,1)` Fourier prime sum exactly with the
  diagonal reciprocal-phase prime sum.
- [x] Identify every general mode with the unequal reciprocal coefficients
  `(q1*N,q2*M)` and prove its derivative and same-sign nonstationarity.
- [x] Prove the derivative identities needed for integration by parts against
  `e(N/t+N/t^2)/log t`.
- [x] Bound the diagonal logarithmic integral by
  `6*P^2/(|N|*log P)` on every dyadic subinterval.
- [x] Combine the prime estimate and integral estimate into the audited
  diagonal Fourier discrepancy theorem.
- [ ] Generalize the source estimate from `(N,N)` to `(q1*N,q2*N)` and finish
  the low-frequency, zero-mode, and Fourier-truncation assembly.

## Prime-equidistribution 3.46

- [x] Generalize the fixed Type II product-correlation Vinogradov envelope to
  independent reciprocal coefficients `N` and `M`.
- [x] Export the corresponding uniform arbitrary-logarithmic-saving theorem.
- [x] Preserve both coefficients through the decay-kernel callback.
- [x] Discharge the transformed-scale upper bound on a canonical Vaughan
  inner block from separate source bounds on `|N|` and `|M|`.
- [ ] Generalize the low-scale Weyl distance-kernel comparison and propagate
  the result through the complete Type II block family.

## Prime-equidistribution 3.47

- [x] Prove the unequal quadratic transformed-scale lower bound on a positive
  dyadic inner band.
- [x] Generalize the low-scale four-step Weyl distance-kernel estimate to
  independent `N` and `M`.
- [x] Generalize nearby-pair absorption and near/far Type II aggregation.
- [x] Combine the unequal Weyl and Vinogradov branches on canonical Vaughan
  inner blocks.
- [x] Propagate the estimate through one actual weighted Vaughan Type II
  double block.
- [ ] Sum the unequal estimate over the complete Vaughan double-block family
  and propagate it through Mangoldt, prime, and Fourier endpoints.

## Prime-equidistribution 3.48

- [x] Sum the unequal double-block estimate over the complete Vaughan Type II
  family.
- [x] Reuse the compressed scalar majorant through an exact blockwise
  phase-scale diagonalization.
- [x] Export explicit decay and arbitrary logarithmic saving for the unequal
  Type II family.
- [x] Reassemble the exact Vaughan identity with unequal coefficients and a
  unified source-facing range.
- [x] Remove prime powers and logarithmic prime weights to obtain the
  unequal unweighted prime exponential-sum estimate.
- [ ] Treat the zero-quadratic Fourier modes and the unequal oscillatory
  integrals, then assemble low, zero, and high modes.

## Prime-equidistribution 3.49

- [x] Generalize the integration-by-parts amplitude to independent positive
  linear and nonnegative quadratic coefficients.
- [x] Prove monotonicity, endpoint control, and the dyadic inverse-linear-
  frequency integral bound.
- [x] Transfer the bound to the negative same-sign chamber by complex
  conjugation.
- [x] Combine both same-sign integral bounds with the unequal prime theorem
  in the literal Fourier-mode discrepancy.
- [ ] Split the opposite-sign stationary chamber and treat coordinate-axis
  modes before assembling the finite Fourier approximation.

## Prime-equidistribution 3.50

- [x] Define the unique quadratic reciprocal stationary point and prove the
  exact derivative factorization and zero criterion.
- [x] Convert an interior stationary point and the source phase-scale lower
  bound into an explicit lower bound on the linear coefficient.
- [x] Derive a quantitative first-derivative lower bound outside a radius
  `δ` neighborhood on the dyadic interval.
- [x] Split the logarithmic integral exactly into left-far, central, and
  right-far pieces and bound the central piece by `2*δ/log P`.
- [ ] Prove cancellation on both far pieces and optimize `δ`, then handle
  coordinate-axis modes.

## Prime-equidistribution 3.51

- [x] Generalize unequal integration by parts to intervals on which the
  critical linear factor is merely nonzero.
- [x] Prove monotone first-derivative bounds for the left far interval and
  the right interval up to the amplitude turning point.
- [x] Bound the post-turning amplitude derivative and its interval integral,
  then reassemble the complete right far piece.
- [x] Combine both far pieces with the central length estimate and insert the
  source lower bound on the linear coefficient.
- [x] Optimize with `δ=P/sqrt L` and prove the interior stationary bound
  `50*P/(sqrt L*log P)` for `L>=4`.
- [ ] Clip the stationary neighborhood at interval endpoints, transfer the
  estimate to the conjugate chamber, and handle coordinate-axis modes.

## Prime-equidistribution 3.52

- [x] Prove the left-clipped, right-clipped, and fully clipped stationary
  decompositions without weakening the optimized constant.
- [x] Propagate the clipped raw estimate through the source coefficient lower
  bound and `δ=P/sqrt L` optimization.
- [x] Transfer the result through coefficient negation and expose a unified
  absolute-linear-coefficient theorem.
- [x] Bound the literal stationary Fourier-mode integral and combine it with
  the unequal prime estimate in a source-range discrepancy theorem.
- [ ] Prove the two coordinate-axis mode estimates, then assemble low, zero,
  and high Fourier modes.

## Prime-equidistribution 3.53

- [x] Prove the positive-variation integration-by-parts endpoint estimate.
- [x] Derive the pure quadratic dyadic integral bound for both coefficient
  signs and identify its exact source scale.
- [x] Convert the scale lower bound into `P/(L*log P)`.
- [x] Combine the literal pure quadratic Fourier integral with the unequal
  prime estimate.
- [x] Prove the pure-linear integral estimate and the high- and low-scale
  pointwise Type II correlation bounds.
- [x] Aggregate the pure-linear correlations through arbitrary and canonical
  Type II double blocks and the complete logarithmically saving source family.
- [x] Prove the two pure-linear Type I families and propagate through Vaughan,
  Mangoldt, primes, and the literal coordinate-axis Fourier discrepancy.
- [ ] Control low and zero modes, then perform the final finite Fourier
  assembly.

## Prime-equidistribution 3.69

- [x] Prove the exact endpoint identity between the half-open Mangoldt prefix
  sum and `Chebyshev.psi`.
- [x] Prove that `exp(-c*sqrt(log x))` beats every fixed inverse logarithmic
  power and absorb the `Λ(k)` endpoint.
- [x] Derive `ClassicalMangoldtDiscrepancyLogSaving` from the standard de la
  Vallée Poussin `ψ` error proposition.
- [x] Expose the literal specialized Theorem 2.5 conclusion from that
  classical PNT proposition and `VinogradovExponentialSumEstimate`.
- [ ] Prove the quantitative `ψ` proposition and the residual Vinogradov
  polynomial mean-value proposition.

## Prime-equidistribution 3.70

- [x] Derive an eventual quadratic full-strip zero count from the frozen
  Jensen estimate.
- [x] Convert Ford's rectangle-uniform Vinogradov--Korobov region to a common
  `c/log T` zero-free width.
- [x] Bound the complete truncated zero sum, separating the finite low-zero
  reciprocal mass from the high zeros.
- [x] Optimize the sharp Perron formula at
  `T=exp(min(1,c/8)*sqrt(log x))` and prove the de la Vallee Poussin psi error.
- [x] Discharge `ClassicalMangoldtDiscrepancyLogSaving` unconditionally and
  reduce the literal specialized Theorem 2.5 conclusion to the Vinogradov
  proposition alone.
- [ ] Prove the residual uniform critical-VMVT coefficient-growth estimate
  and hence `VinogradovExponentialSumEstimate`.

## Prime-equidistribution 3.71

- [x] Separate the Taylor remainder cutoff from the effective IK mean-value
  degree `floor(4 log F/log X)`.
- [x] Prove the effective-degree Taylor remainder, pair transfer, and the
  quarter-block weighted mass bound `k^2/25`.
- [x] Prove the high-degree Ford branch and the finite native-critical branch,
  including the trivial complementary parameter range.
- [x] Prove `VinogradovExponentialSumEstimate` unconditionally.
- [x] Combine it with the native quantitative PNT to prove the literal
  specialized Theorem 2.5 and Tao's Theorem 1.8 unconditionally.

## Prime-equidistribution 3.72

- [x] Normalize the positive `y`-smooth Dirichlet weights and prove their
  total mass is one.
- [x] Identify the tilted log-partition derivatives exactly with `-phiOne`
  and `phiTwo`.
- [x] Factor `Psi(X,y)` exactly as the saddle exponential times a cutoff
  expectation and prove that expectation lies in `[0,1]`.
- [x] Prove the critical saddle asymptotic equivalent to the explicit
  Gaussian local-limit target for the tilted cutoff factor.
- [ ] Prove that Gaussian local-limit target uniformly in the critical
  smooth-number regime.

## Prime-equidistribution 3.73

- [x] Realize the tilted smooth-number masses as a probability measure on
  logarithmic size.
- [x] Prove the exact absolutely convergent characteristic-function series,
  its value at zero, and its unit norm bound.
- [x] Identify the exact saddle center and variance from the log-partition
  derivatives.
- [x] Construct the centered variance-normalized saddle characteristic
  function and prove its explicit Fourier-series formula.
- [ ] Prove its Gaussian convergence with the uniform estimates required by
  the cutoff local-limit theorem.

## Prime-equidistribution 3.74

- [x] Prove absolute summability and the finite-prime Euler product for the
  complex smooth Fourier Dirichlet series.
- [x] Normalize that product to the literal local characteristic factor
  `(1-p^(-sigma))/(1-p^(-sigma) exp(i t log p))`.
- [x] Prove each local factor has norm at most one.
- [x] Prove the exact local and global squared-norm contraction products with
  oscillatory loss `1-cos(t log p)`.
- [ ] Establish the small-, intermediate-, and large-frequency estimates and
  complete local-limit inversion.

## Prime-equidistribution 3.75

- [x] Convert `1-cos(theta)` into a quadratic loss on the principal period.
- [x] Prove a prime-local Gaussian exponential bound on the central window.
- [x] Identify its coefficient exactly with the corresponding `phiTwo`
  summand and multiply the local estimates.
- [x] Derive the universal variance-normalized Gaussian envelope from one
  explicit source-scale frequency condition.
- [ ] Prove an expanding normalized window satisfies that condition and
  control the complementary frequencies needed for inversion.

## Prime-equidistribution 3.76

- [x] Define the exact positive symmetric central radius.
- [x] Prove interval membership is equivalent to the source-scale frequency
  condition from release 3.75.
- [x] Transfer both normalized Gaussian envelopes to the whole interval.
- [x] Prove conditionally that `log y / sqrt(phiTwo) → 0` makes the radius
  diverge and eventually captures every fixed frequency.
- [ ] Prove that curvature-scale limit unconditionally in the critical regime.
- [ ] Control complementary frequencies and complete Fourier inversion.

## Prime-equidistribution 3.77

- [x] Prove the second saddle sum is antitone in the positive parameter.
- [x] Place the exact saddle above `1-8 log(u)/log(y)` in the critical regime.
- [x] Combine that comparison with the exact secant identity to prove
  `phiTwo/log(y)^2 ≥ u/(16 log u)` eventually.
- [x] Prove normalized curvature tends to infinity and
  `log(y)/sqrt(phiTwo) → 0`.
- [x] Deduce unconditional divergence of the central radius and the eventual
  fixed-frequency Gaussian envelope.
- [ ] Prove complementary-frequency decay and complete Fourier inversion.

## Prime-equidistribution 3.78

- [x] Factor the normalized saddle characteristic exactly into centered
  prime-local factors.
- [x] Define the prime variance shares and prove they are nonnegative and sum
  exactly to one.
- [x] Prove the quantitative finite-product Gaussian transfer theorem.
- [x] Bound every variance share by `20 log(y)^2/phiTwo` on the eventual
  half-plane and prove this uniform bound tends to zero.
- [x] Reduce fixed-frequency convergence to `exp(-t^2/2)` solely to the summed
  prime-local quadratic Taylor remainder.
- [x] Prove the explicit prime-local Taylor remainder estimate.
- [ ] Prove complementary-frequency decay and complete Fourier inversion.

## Prime-equidistribution 3.79

- [x] Prove the exact centered first and second geometric moments and a
  uniform summable third absolute centered moment bound.
- [x] Prove a global cubic Taylor remainder for the pure-imaginary
  exponential and transfer it to the centered geometric characteristic.
- [x] Identify that characteristic exactly with the centered prime-local
  saddle Euler factor.
- [x] Bound the summed local Taylor error by
  `16000 |t|^3 log(y)/sqrt(phiTwo)` and prove it tends to zero.
- [x] Deduce fixed-frequency convergence of the normalized saddle
  characteristic to `exp(-t^2/2)` in every critical smooth regime.
- [ ] Prove complementary-frequency decay and complete Fourier inversion.

## Prime-equidistribution 3.80

- [x] Rewrite the saddle cutoff factor as a one-sided Laplace moment of the
  centered variance-normalized logarithmic law.
- [x] Identify the Gaussian prefactor with `sqrt(2*pi)` times the Laplace
  rate and prove that rate tends to infinity.
- [x] Prove the critical saddle asymptotic equivalent to convergence of the
  explicit normalized Laplace target.
- [ ] Establish the complementary-frequency bounds needed to control that
  shrinking-scale target and complete inversion.

## Prime-equidistribution 3.81

- [x] Define the exact normalized Laplace/Perron kernel
  `lambda/(lambda-i*t)` on the centered characteristic scale.
- [x] Restrict the characteristic-function integrand to the explicit
  expanding central interval and prove strong measurability.
- [x] Dominate that integrand uniformly by the integrable Gaussian
  `exp(-t^2/pi^2)`.
- [x] Prove pointwise convergence of the exact kernel-weighted integrand to
  `exp(-t^2/2)` and evaluate its integral as `sqrt(2*pi)`.
- [x] Deduce that the normalized central-frequency contribution to the
  one-sided Laplace target tends to one.
- [ ] Bound the complementary Perron/truncation contribution and identify
  the truncated contour integral with the literal cutoff moment.

## Prime-equidistribution 3.82

- [x] Define the exact central Perron height on the original vertical-line
  frequency scale.
- [x] Define the normalized source integrand using the twisted smooth
  Dirichlet series, phase `exp(i*t*log X)`, and kernel
  `sigma/(sigma+i*t)`.
- [x] Prove pointwise equality with the centered characteristic and corrected
  Laplace kernel at frequency `-t*sqrt(phiTwo)`.
- [x] Prove the exact standard-deviation substitution from the vertical line
  to the normalized central interval.
- [x] Identify the release-3.81 normalized central contribution exactly with
  this source-facing Perron-line integral.
- [ ] Extend the finite-height line to a sharp cutoff formula and prove its
  complementary-frequency/truncation error is negligible.

## Prime-equidistribution 3.83

- [x] Pass the absolutely convergent smooth Dirichlet series through every
  finite vertical interval.
- [x] Identify the normalized line with the sum of frozen sharp-Perron
  kernels.
- [x] Prove the inclusive smooth cutoff series equals `psiNat X y`.
- [x] Express the Perron error as a summable kernel-minus-cutoff series.
- [x] Transfer the strict lower/upper logarithmic bounds and the uniform
  `3/2` endpoint bound.
- [ ] Aggregate these bounds at the saddle height and prove the complementary
  line negligible on the Gaussian main-term scale.

## Prime-equidistribution 3.84

- [x] Prove the scalar symmetric sharp-Perron limits below, at, and above the
  endpoint, including the exact half-weight at equality.
- [x] Define the half-weighted smooth cutoff and its explicit endpoint
  correction.
- [x] Prove its full smooth sum is `psiNat X y` minus that correction and
  bound the correction norm by `1/2`.
- [x] Construct a summable height-independent envelope for every height at
  least one.
- [x] Apply Tannery's theorem to the complete smooth sharp-Perron series.
- [ ] Prove the finite saddle-height noncentral line negligible on the
  Gaussian main-term scale.

## Prime-equidistribution 3.85

- [x] Normalize the complete finite Perron line by the exact saddle main term.
- [x] Identify that line with the full sharp-kernel sum divided by the same
  main term.
- [x] Express the complementary line exactly as the two integrals outside the
  central Perron height.
- [x] Identify its infinite-height limit with the endpoint-corrected saddle
  ratio minus the central Gaussian contribution.
- [x] Prove critical corrected-ratio convergence is equivalent to vanishing of
  the named infinite complement.
- [x] Bound the normalized endpoint correction by `1/(2*mainTerm)`.
- [ ] Prove main-term divergence and complementary-line decay in every
  critical regime.

## Prime-equidistribution 3.86

- [x] Prove `phiTwo <= 7*log(y)*phiOne` uniformly for `sigma >= 1/2`.
- [x] Specialize this to `phiTwo <= 7*log(y)*log(X)` at the exact saddle.
- [x] Prove the explicit lower bound
  `sqrt(X)/(sqrt(14*pi)*log(X)) <= smoothSaddleMainTerm`.
- [x] Prove the saddle main term tends to infinity in every critical regime.
- [x] Prove the normalized endpoint correction tends to zero.
- [x] Identify the original critical saddle asymptotic exactly with decay of
  `smoothSaddleInfiniteComplementaryPerronLine`.
- [ ] Prove that complementary Perron line tends to zero in every critical
  regime.

## Prime-equidistribution 3.87

- [x] Extend prime-local contraction to the full range `|t log p| <= pi`.
- [x] Multiply the local estimates into a normalized Gaussian envelope on
  `|t|*log(y)/standardDeviation <= pi`.
- [x] Define the annulus between the central and full principal-phase radii.
- [x] Prove its integrand is uniformly dominated by an integrable Gaussian.
- [x] Prove its full integral tends to zero in every critical regime.
- [ ] Control the complementary Perron line beyond physical height
  `pi/log(y)`.

## Prime-equidistribution 3.88

- [x] Define the physical Perron height corresponding to the wide radius.
- [x] Prove that height is exactly `pi/log(y)`.
- [x] Convert both signed physical annular intervals under the exact
  standard-deviation substitution.
- [x] Identify the normalized physical annular contribution with the
  release-3.87 Fourier integral.
- [x] Prove that contribution tends to zero in every critical regime.
- [ ] Prove decay of the two outer tails beyond `|t| = pi/log(y)`.

## Prime-equidistribution 3.89

- [x] Define the finite normalized outer Perron line beyond `pi/log(y)`.
- [x] Decompose the complementary line as annulus plus outer line.
- [x] Define and identify the infinite-height outer Perron object.
- [x] Prove outer-line decay is equivalent to complementary-line decay in
  every critical regime.
- [x] Restate the complete critical saddle asymptotic using only the named
  infinite outer line.
- [ ] Prove `smoothSaddleInfiniteOuterPerronLine -> 0` in every critical
  regime.

## Prime-equidistribution 3.90

- [x] Define the exact prime-local and aggregate outer phase losses.
- [x] Prove their nonnegativity and symmetry in frequency.
- [x] Establish a phase-unrestricted exponential contraction for every
  normalized prime Euler factor.
- [x] Multiply these estimates over the complete source-prime product.
- [x] Bound the literal physical Perron integrand by
  `exp(-smoothSaddleCosineLoss/96)`.
- [ ] Prove a uniform lower bound for `smoothSaddleCosineLoss` sufficient to
  integrate the outer tails.

## Prime-equidistribution 3.91

- [x] Derive a cardinality lower bound for the top dyadic prime block from
  the compiled Chebyshev–PNT reciprocal-mass estimate.
- [x] Place all top-block phases in the cosine-negative range on the first
  outer shell.
- [x] Prove
  `y^(-sigma)*y/(16*log(y)) <= smoothSaddleCosineLoss` on that shell.
- [ ] Extend quantitative loss bounds across all later outer shells.
- [ ] Integrate those bounds and pass to the infinite outer Perron line.

## Prime-equidistribution 3.92

- [x] Define the adaptive scale `ceil(exp(pi/t))` and prove its sharp ceiling
  and logarithm bounds.
- [x] Derive `N(t) <= y` from the outer-frequency boundary and place the
  adaptive block in the cosine-negative phase window.
- [x] Enlarge the qualitative Chebyshev–PNT threshold and discharge the
  dyadic half-block logarithmic-width condition.
- [x] Prove the adaptive weighted cosine-loss lower bound on the controlled
  small-frequency range.
- [ ] Obtain uniform loss for the remaining outer frequencies.
- [ ] Integrate the full bound and pass to the infinite outer Perron line.

## Prime-equidistribution 3.93

- [x] Keep every coarse CEP dyadic block inside the first-shell
  negative-cosine phase window.
- [x] Convert the accumulated reciprocal mass into a weighted cosine-loss
  lower bound.
- [x] Use the exact saddle equation and cutoff displacement to obtain a named
  loss scale comparable from below to `u/log(u)`.
- [x] Prove that scale diverges and uniformly bounds the physical Perron
  integrand on the first shell.
- [x] Absorb the normalization and prove the first-shell integral tends to
  zero.
- [ ] Extend accumulated loss to later outer-frequency ranges.

## Prime-equidistribution 3.94

- [x] Define the exact symmetric normalized first outer-shell Perron
  contribution.
- [x] Bound both physical interval integrals from a uniform absolute-frequency
  envelope.
- [x] Extend the release-3.93 positive-frequency envelope to negative
  frequencies by cosine-loss symmetry.
- [x] Prove
  `standardDeviation/log(y) <= sqrt(7*u)` from the curvature upper bound.
- [x] Prove the generic decay
  `sqrt(u)*exp(-c*u/log(u)) -> 0` and deduce first-shell vanishing.
- [x] Extend accumulated phase loss beyond `4*pi/(3*log(y))`.
- [ ] Assemble all later shells and prove
  `smoothSaddleInfiniteOuterPerronLine -> 0`.

## Prime-equidistribution 3.95

- [x] Sharpen the accumulated-alphabet cosine window to
  `3*pi/(2*log(y))`.
- [x] Define a reusable exact symmetric Perron-shell contribution.
- [x] Prove its norm bound from a uniform absolute-frequency envelope.
- [x] Define and integrate the adjacent band from `4*pi/(3*log(y))` to
  `3*pi/(2*log(y))`.
- [x] Prove that adjacent normalized contribution tends to zero in every
  critical regime.
- [ ] Recover divergent accumulated loss beyond `3*pi/(2*log(y))`.
- [ ] Pass all remaining bands to the infinite outer Perron line.

## Prime-equidistribution 3.96

- [x] Define the natural square-root prime scale.
- [x] Prove its logarithm lies between `2/5*log(y)` and `1/2*log(y)` on the
  required tail.
- [x] Put the retained CEP alphabet above `1/3*log(y)`.
- [x] Place all retained phases in the nonpositive-cosine window on
  `[3*pi/(2*log(y)), 3*pi/log(y)]`.
- [x] Prove the accumulated square-root-alphabet cosine-loss lower bound.
- [x] Verify its cofactor-range hypotheses in every critical regime.
- [ ] Convert the explicit second-shell loss to a divergent Rankin-ratio
  scale and integrate the normalized shell.
- [ ] Extend coverage beyond `3*pi/log(y)`.

## Prime-equidistribution 3.97

- [x] Compare the square-root-alphabet cofactor power with a positive
  `2/5` power of the Rankin ratio.
- [x] Define the second-shell loss scale and prove that it tends to infinity
  in every critical regime.
- [x] Prove that its exponential envelope absorbs the `sqrt(u)` saddle
  normalization.
- [x] Extend the positive-frequency loss to both signs by cosine-loss
  symmetry.
- [x] Define and integrate the exact symmetric shell from
  `3*pi/(2*log(y))` through `3*pi/log(y)`.
- [x] Prove that normalized second-shell contribution tends to zero.
- [ ] Recover divergent accumulated loss beyond `3*pi/log(y)`.
- [ ] Assemble all remaining bands into the infinite outer Perron line.

## Prime-equidistribution 4.29

- [x] Convert both off-endpoint logarithmic Perron denominators to additive
  distance.
- [x] Use integrality of `y` to bound every reciprocal distance by `y+1`.
- [x] Dominate all off-endpoint terms by one positive von Mangoldt Dirichlet
  series.
- [x] Insert the frozen `log y+C` estimate and exact optimized-line power.
- [x] Deduce the explicit complete HT contour-truncation bound at `T=2Y`.
- [ ] Absorb the endpoint and height terms into the target error.
- [ ] Bound the two horizontal and one left vertical contour edges.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.30

- [x] Define a finite reciprocal-distance weight around the integral cutoff.
- [x] Compare it with the frozen half-integral kernel and bound its sum by
  eight harmonic numbers.
- [x] Prove sharp additive near-range and Dirichlet far-range majorants.
- [x] Sum the endpoint, near, and far components explicitly.
- [x] Specialize the harmonic-strength bound to the selected HT height.
- [ ] Prove eventual absorption using `3/2-epsilon > epsilon/2`.
- [ ] Bound the two horizontal and one left vertical contour edges.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.31

- [x] Prove `epsilon/2 < 3/2-epsilon` throughout the source epsilon range.
- [x] Absorb fixed constants and logarithmic powers into the height exponent.
- [x] Bound each endpoint/near/far component by one third of the target.
- [x] Absorb the complete scalar truncation majorant.
- [x] Prove the exact complex truncation-error decay uniformly in frequency.
- [x] Embed that decay into the full HT Mangoldt-error allowance.
- [ ] Bound the two horizontal and one left vertical contour edges.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.32

- [x] Prove a generic normalized horizontal-integral bound from a pointwise
  sup bound.
- [x] Prove the corresponding normalized vertical-integral bound.
- [x] Compute the exact HT horizontal and vertical edge lengths.
- [x] Bound the complete three-edge contribution by one scalar sup majorant.
- [ ] Prove the three pointwise translated zeta log-derivative bounds.
- [ ] Absorb the resulting edge majorant into the Lemma-6 allowance.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.33

- [x] Retain the reciprocal Perron denominator on the left vertical edge.
- [x] Evaluate its elementary symmetric envelope with logarithmic height
  cost.
- [x] Prove the exact norm factorization of the shifted zeta-Perron integrand.
- [x] Assemble the two horizontal edges and weighted left edge into one
  source-scale majorant.
- [ ] Prove the translated zeta log-derivative bound on the zero-free strip.
- [ ] Absorb the weighted edge majorant into the Lemma-6 allowance.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.34

- [x] Reserve twice the HT contour shift inside the eventual native VK width.
- [x] Convert VK zero-freeness into quantitative separation from every local
  sharp-Landau zero.
- [x] Bound the complete finite Landau zero sum by reciprocal spare width.
- [x] Reinstantiate the frozen partial-fraction theorem without a selected
  good ordinate.
- [x] Transport the estimate to the physical positive-height `zeta'/zeta`.
- [ ] Specialize the estimate uniformly to all three HT contour edges.
- [ ] Absorb the resulting weighted edge majorant.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.35

- [x] Transfer the arbitrary-height estimate to negative ordinates by zeta
  conjugation.
- [x] Package both signs using the absolute ordinate as Landau scale.
- [x] Replace the raw partial-fraction logarithm and zero mass by an explicit
  `(1+1/eta)*log |R|` bound.
- [ ] Prove the near-pole low-height vertical bound.
- [ ] Instantiate and absorb the complete weighted contour-edge majorant.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.36

- [x] Define the fixed compact half-VK low-height rectangle.
- [x] Prove the entire zeta surrogate is nonzero throughout it.
- [x] Bound the surrogate logarithmic derivative by compactness.
- [x] Restore zeta with the explicit simple-pole term.
- [x] Deduce the low-height left-line bound `C+1/eta`.
- [ ] Combine the high- and low-height pointwise bounds in the weighted edge.
- [ ] Absorb the complete edge majorant and close the small-beta branch.

## Prime-equidistribution 4.37

- [x] Prove the twice-shift VK comparison at nine source frequency ceilings.
- [x] Compute the physical ordinate range on both horizontal edges.
- [x] Prove their real coordinates remain in the Landau strip.
- [x] Obtain one explicit high-height logarithmic-derivative majorant.
- [x] Combine compact and Landau bounds across the complete left edge.
- [ ] Transfer all three estimates to the shifted Perron integrand.
- [ ] Apply and absorb the weighted edge majorant.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.38

- [x] Transfer a horizontal physical log-derivative bound to the shifted
  Perron integrand with its reciprocal-height gain.
- [x] Transfer the left-line bound while retaining the full Perron
  denominator pointwise.
- [x] Derive every zeta-nonzero and non-pole side condition from the
  translated surrogate-zero-free rectangle.
- [x] Instantiate the weighted three-edge integration theorem.
- [x] Derive the rectangle and all pointwise bounds from the VK/Landau inputs.
- [ ] Absorb the explicit weighted scalar majorant.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.39

- [x] Correct the contour displacement to
  `2*(log y)^(epsilon/2-1)` and reverify the VK comparison.
- [x] Bound the high and full-left log-derivative majorants by a cubic log.
- [x] Bound the vertical reciprocal-distance logarithm by a quadratic log.
- [x] Absorb the horizontal term using the full frequency height.
- [x] Absorb the vertical polynomial losses using the spare exponential copy.
- [x] Prove the complete three-edge target uniformly for `2*eta<=beta`.
- [ ] Close the complementary small-beta branch.

## Prime-equidistribution 4.40

- [x] Correct HT Lemma 6 from a coefficient-one inequality to its literal
  epsilon-dependent `O_epsilon` contract.
- [x] Thread the displayed constant through the cosine and Euler-loss bridges.
- [x] Compute the shifted integrand's principal coefficient at `z=0`.
- [x] Prove the two-pole negative-left rectangle and right-line identities.
- [x] Discharge arbitrary-left rectangle zero-freeness from native VK data.
- [x] Combine the two-pole contour with the existing Perron truncation error.
- [x] Prove a source-scale bound for the origin logarithmic derivative.
- [x] Absorb the negative-left three-edge contribution.

## Prime-equidistribution 4.43

- [x] Reflect the denominator-retaining vertical integral to `Re z=-eta`.
- [x] Prove three-shift VK logarithmic-derivative control on both horizontal
  edges and the complete negative-left edge.
- [x] Transfer those bounds to the shifted Perron integrand and assemble the
  weighted three-edge majorant.
- [x] Absorb that majorant into the literal HT Mangoldt error.
- [x] Combine origin, edges, and truncation in the small-beta branch.
- [x] Join small and large beta into one uniform eventual transform estimate.
- [x] Promote the eventual estimate over the finite initial `y` range to the
  named all-`y` HT Lemma 6 contract.

## Prime-equidistribution 4.44

- [x] Bound the finite Mangoldt transform by `Chebyshev.psi y`.
- [x] Bound the HT main term by `y/beta` for `y>=2` and `0<beta<1`.
- [x] Show the literal HT error dominates `1/beta` and obtain the uniform
  crude initial-range estimate with coefficient `psi(y)+y`.
- [x] Extract the eventual contour threshold and absorb every smaller `y`
  using monotonicity of `psi`.
- [x] Prove `SmoothSaddleHTMangoldtTransformEstimate` for all `y>=2`.
- [ ] Propagate the now-unconditional HT cosine estimate through the complete
  outer-frequency Perron decay needed for the smooth saddle local limit.

## Prime-equidistribution 4.45

- [x] Define an explicit positive HT minor-arc coefficient.
- [x] Combine Lemma 6, the prime-power bridge, and the sharp saddle comparison
  into a quarter-loss lower bound for the Euler-product cosine loss.
- [x] Transfer that lower bound through the global Euler-product norm estimate
  to `SmoothSaddleHildebrandTenenbaumMinorArcBoundAt`.
- [x] Package the complete fixed-parameter implication with the exact HT
  frequency ceiling.
- [x] Prove the remaining scalar error absorption uniformly from the first
  outer frequency to that ceiling.

## Prime-equidistribution 4.46

- [x] Prove `u/log y -> 0` and the eventual bound `u<=log y`.
- [x] Lower-bound the first outer-frequency HT loss by
  `u/(65*(log u)^2)` and prove that scale tends to infinity.
- [x] Absorb `y^(1-sigma)` into `u^8` and then into the HT
  stretched-exponential saving.
- [x] Derive `(log u)/2 <= (1-sigma)*log y` from the saddle equation and
  bound the normalized Lemma-6 error by `4/log u`.
- [x] Uniformly bound the normalized higher-prime-power remainder.
- [x] Absorb the complete scalar error at `1/log y`, propagate by radial
  monotonicity, and prove the unconditional full-range minor-arc contract.
- [ ] Combine the central and minor-arc estimates in the smooth saddle
  local-limit inversion required for Theorem 1.7.

## Prime-equidistribution 4.47

- [x] Compute the exact norm of the physical Laplace--Fourier kernel and
  retain its reciprocal-frequency decay.
- [x] Prove a generic logarithmic-cost interval-integral estimate for
  integrands bounded by `C/|t|`.
- [x] Integrate the unconditional HT minor-arc estimate over the complete
  finite shell from `1/log y` to the epsilon-`1/2` source ceiling.
- [x] Prove the normalized shell envelope tends to zero using `log y<=u^2`
  and `u^5*exp(-c*u/(log u)^2) -> 0`.
- [x] Split the shell exactly at `pi/log y` and prove that the resulting
  finite outer Perron segment tends to zero.
- [ ] Prove the sharp finite-height Perron truncation connecting the finite
  HT segment to the smooth-number cutoff and finish the local-limit inversion.

## Prime-equidistribution 4.48

- [x] Re-run the HT Lemma-6 scalar absorption at fixed `epsilon=1/4` and
  prove the unconditional minor-arc contract through
  `exp((log y)^(5/4))`.
- [x] Integrate the enlarged minor arc with logarithmic endpoint cost and
  absorb the resulting seventh-power Rankin loss.
- [x] Split the coefficient-free sharp-Perron error into endpoint,
  harmonic near-diagonal, and smooth Dirichlet-series far terms.
- [x] Prove summability and the explicit `tsum` bound for that complete
  finite-height majorant.
- [x] Prove `u*log u/log y -> 1/alpha^2` and use it to absorb
  `X^(1-sigma)` at the quarter-epsilon ceiling for every fixed `alpha>0`.
- [x] Prove that the finite sharp-Perron sum differs from `psiNat` by
  `o(smoothSaddleMainTerm)`.
- [ ] Assemble the finite Perron identity with the central local-limit and
  outer-shell limits, then state the completed Theorem 1.7 consequence.

## Prime-equidistribution 4.49

- [x] Split the normalized quarter-height Perron line exactly into the
  central contribution, wide annulus, and enlarged HT outer shell.
- [x] Combine their limits to prove the normalized finite Perron line tends
  to one.
- [x] Transfer the sharp-Perron cutoff error to prove
  `psiNat/smoothSaddleMainTerm -> 1` in complex and real form.
- [x] Prove `TaoCriticalSmoothSaddleAsymptoticConclusion` with no remaining
  local-limit or Perron-tail assumption.
- [ ] Close the independent explicit Burgess input and apply the existing
  transfer theorem to obtain the unconditional Theorem 1.7 contract.

## Prime-equidistribution 4.50

- [x] Define the exact polynomial kernel fiber `χ(P(x))=1`.
- [x] Prove positive character-power orthogonality through `orderOf χ`, with
  the zero field element handled by the positive indexing.
- [x] Sum over polynomial values and prove the exact powered-correlation
  family equals `orderOf χ` times the kernel-fiber cardinality.
- [x] Transport the identity to the split-polynomial distinct-root Kummer
  trace normal form.
- [x] Identify the character kernel with the nonzero `orderOf χ`-power image.
- [x] Obtain the exact affine Kummer-cover point-count formula.
- [ ] Formalize the projective Kummer-curve Weil estimate and recover the
  individual complete character-sum bound.

## Prime-equidistribution 4.51

- [x] Prove evaluation at a cyclic unit-group generator preserves character
  order.
- [x] Compute the character image and kernel cardinalities.
- [x] Compute the `orderOf χ`-power subgroup cardinality from finite cyclicity.
- [x] Prove the power subgroup equals the unit-group character kernel.
- [x] Deduce `χ(a)=1` iff `a` is a nonzero `orderOf χ`-th power.
- [x] Count the zero and nonzero affine power fibers and sum them over
  polynomial values.
- [ ] Add the points at infinity and apply the projective Weil estimate.

## Prime-equidistribution 4.52

- [x] Compute the kernel cardinality of the `orderOf χ` power map.
- [x] Count every nonzero affine power fiber by translation from the kernel.
- [x] Prove the zero power fiber is the singleton `{0}`.
- [x] Sum the vertical fibers into the exact affine Kummer-curve point count.
- [x] Rewrite the polynomial zero fiber as `P.roots.toFinset` for `P≠0`.
- [ ] Construct the projective completion and count its points at infinity.
- [ ] Apply the projective Weil estimate and recover the individual trace.

## Prime-equidistribution 4.53

- [x] Rewrite the affine Kummer count as `p` plus all proper character-power
  traces.
- [x] Prove the trace identity for every scalar twist `cP`.
- [x] Establish multiplicative orthogonality against the `χ⁻¹` weight.
- [x] Fourier-invert the twisted trace defects to recover exactly
  `(p-1)S(χ,P)`.
- [x] Transfer a uniform sharp twisted point-count bound to the existing
  `TaoPrimeKummerPolynomialWeilBound` contract without constant loss.
- [x] Record that this uniform twisted-defect hypothesis is a stronger
  Fourier criterion, not the ordinary total-curve Hasse--Weil estimate.

## Prime-equidistribution 4.54

- [x] Define the chosen-character Kummer Frobenius spectrum with an explicit
  finite eigenvalue family.
- [x] State the conductor bound `rank <= #roots-1` and exact trace formula.
- [x] State the weight-at-most-one bound as `‖eigenvalue‖ <= sqrt p`.
- [x] Derive the sharp polynomial Kummer bound by triangle inequality.
- [x] Connect the spectral theorem to the prime quotient and complete
  cubefree Burgess endpoints.
- [x] Connect it specifically to the fixed `r=7` endpoint used downstream.
- [ ] Construct the normalized Kummer sheaf/curve eigenspace and prove the
  trace formula, weight bound, and rank bound furnishing this spectrum.

## Prime-equidistribution 4.55

- [x] Correct exact purity to the mixed-weight inequality required by the
  low-root Jacobi degeneracies.
- [x] Construct the rank-zero spectrum in the one-root case.
- [x] Construct the rank-one spectrum in the two-root case from the Jacobi
  bound.
- [x] Express the spectral trace as the `χ⁻¹` Fourier projection of the
  scalar-twisted affine point-count defects.
- [x] Prove the full spectral source contract equivalent to its restriction
  to at least three distinct roots.
- [x] Connect that genuine residual directly to fixed-`r=7` composite
  Burgess.
- [ ] Construct the weight-bounded isotypic spectrum for at least three
  distinct roots.

## Prime-equidistribution 4.56

- [x] Add algebraic integrality to every spectral eigenvalue.
- [x] Prove every finite-field multiplicative-character value is integral by
  its zero/root-of-unity dichotomy.
- [x] Prove every complete polynomial character correlation is integral.
- [x] Upgrade the one- and two-root spectra to the strengthened contract.
- [x] Recheck the sharp Kummer and fixed-`r=7` transfers without changing
  their constants.
- [ ] Construct the integral weight-bounded spectrum for the remaining
  three-or-more-root cases.

## Prime-equidistribution 4.57

- [x] Define the norm-lifted Kummer correlation over every positive-degree
  canonical finite extension of `ZMod p`.
- [x] Make degree one exactly the existing base-field polynomial correlation.
- [x] Strengthen the spectrum by the simultaneous Frobenius power-trace
  identities over all extension degrees.
- [x] Prove that rank zero forces all extension traces to vanish and rank one
  forces the consecutive-trace geometric recurrence.
- [x] Forget the extension traces to recover the three-or-more-root spectral
  residual and the exact fixed-`r=7` Burgess endpoint.
- [ ] Construct the extension-compatible system for the remaining
  three-or-more-root Kummer cases.

## Prime-equidistribution 4.58

- [x] Package finite-field norm pullback as a monoid homomorphism on complex
  multiplicative characters.
- [x] Prove norm pullback is injective and preserves nontriviality and exact
  character order.
- [x] Rewrite every higher Kummer extension correlation through the
  norm-lifted character and prove its algebraic integrality.
- [x] Prove the exact single-root base-change factorization.
- [x] Prove every one-root extension correlation vanishes and construct the
  empty rank-zero Frobenius system.
- [x] Prove the full Frobenius system theorem equivalent to the conjunction
  of the exact two-root and three-or-more-root residuals.
- [ ] Prove the two-root Hasse--Davenport power-trace identity.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.59

- [x] Evaluate the arbitrary-finite-field two-root character sum exactly as a
  Jacobi sum, with both translation factors.
- [x] Prove the exact two-root split-polynomial factorization after base
  change.
- [x] Express every higher two-root Kummer extension correlation as the
  corresponding norm-lifted Jacobi sum.
- [x] Prove that norm lifting on a base scalar raises the character value to
  the extension degree.
- [x] State the literal Jacobi Hasse--Davenport identity with its exact sign.
- [x] Derive the rank-one two-root Frobenius system from that literal identity.
- [ ] Prove the literal Jacobi Hasse--Davenport identity.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.60

- [x] Define additive-character pullback along the finite-field trace.
- [x] Prove trace pullback preserves primitivity over finite separable
  extensions.
- [x] State the exact Gauss Hasse--Davenport norm/trace lifting formula.
- [x] Prove the trivial-second-character Jacobi branch directly.
- [x] Prove the inverse-product Jacobi branch directly with the exact sign.
- [x] Reduce the nondegenerate Jacobi branch to the three corresponding Gauss
  lifting identities.
- [x] Derive the two-root and full-system constructors from Gauss lifting.
- [ ] Prove the Gauss Hasse--Davenport lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.61

- [x] Prove norm-lifted multiplicative characters compose through finite-field
  towers.
- [x] Prove trace-lifted additive characters compose through finite-field
  towers.
- [x] Package the exact Gauss lifting relation for one finite extension.
- [x] Prove two local Gauss lifting relations compose with the exact degree
  product and Hasse--Davenport sign.
- [x] Prove the degree-one Gauss lifting identity by finite-field uniqueness.
- [x] Prove the full prime-field statement is equivalent to its restriction
  to degrees at least two.
- [ ] Construct a general-base/intermediate-field reduction of composite
  degrees to prime degrees.
- [ ] Prove the remaining positive-degree Gauss Hasse--Davenport identity.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.62

- [x] Prove norm/trace-lifted Gauss sums are invariant under algebra
  equivalence of extension fields.
- [x] Prove the local Gauss lifting relation is invariant under algebra
  equivalence.
- [x] Replace any finite extension by the canonical extension of equal
  degree.
- [x] State universal finite-base Hasse--Davenport and its prime-degree
  fragment with arbitrary primitive additive character.
- [x] Split every composite degree into a nested pair of canonical
  extensions and compose the induction hypotheses.
- [x] Prove universal finite-field Hasse--Davenport is equivalent to its
  prime-degree fragment.
- [x] Specialize the universal theorem to the original prime-field residual.
- [ ] Prove universal Hasse--Davenport in prime extension degree.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.63

- [x] Prove trace lifting commutes with scalar shifts of additive characters.
- [x] Compute norm-lifted character values on base scalars in arbitrary
  finite extensions.
- [x] Compute the exact degree-th-power scaling of the lifted Gauss sum.
- [x] Transfer a local Gauss lifting relation to every nonzero additive
  character shift.
- [x] Use finite Pontryagin duality to prove shifts of a primitive complex
  additive character exhaust all complex additive characters.
- [x] Prove a primitive target character is represented by a nonzero shift.
- [x] Reduce the universal prime-degree theorem to the canonical primitive
  additive character on each finite base field.
- [x] Connect the reduced leaf to the prime-field, Jacobi, two-root, and full
  Kummer-system constructors.
- [ ] Prove the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.64

- [x] Identify monic polynomials of fixed degree with their coefficient
  vectors below the leading term.
- [x] Transport the constant and subleading coefficient weight across that
  equivalence.
- [x] Prove the degree-one weighted monic sum is exactly the Gauss sum.
- [x] Prove every degree-at-least-two weighted monic sum vanishes for a
  nontrivial multiplicative character.
- [x] Expose both coefficient-vector and polynomial versions of the two
  identities.
- [ ] Relate the monic generating series to norm/trace Gauss sums through
  the finite-field closed-point Euler product.
- [ ] Prove the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.65

- [x] Extend the fixed-degree coefficient weight to a global polynomial
  weight.
- [x] Prove multiplicativity on monic products, powers, and multiset
  products.
- [x] Compute the weight of each linear factor from its root.
- [x] Decompose every monic weight over its normalized monic irreducible
  factors, with exact preservation of total degree.
- [x] Express each finite-extension norm/trace character weight through the
  minimal polynomial and relative degree `[L:K(x)]`.
- [x] Rewrite the lifted Gauss sum as the exact minimal-polynomial weighted
  sum over extension elements.
- [ ] Prove the finite logarithmic-derivative recurrence between monic
  coefficients and closed-point sums.
- [ ] Deduce the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.66

- [x] Define the finite logarithmic-derivative coefficient recurrence
  `X A' = B A`.
- [x] Prove that the coefficient profile `A = 1 + G X` uniquely forces the
  signed-power sequence `B(n+1)=(-1)^n G^(n+1)`.
- [x] Package the global Hasse--Davenport monic weight into its actual
  fixed-degree coefficient sequence.
- [x] Prove that this sequence is `1`, the Gauss sum, and zero in degrees
  zero, one, and at least two respectively.
- [x] Reduce the signed Gauss-power conclusion to the single genuine
  closed-point recurrence.
- [ ] Construct that recurrence from normalized irreducible factorization
  and the minimal-polynomial extension sum.
- [ ] Deduce the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.67

- [x] Define the formal local factor `(1-wX^d)⁻¹` and compute its exact
  coefficients by power-series substitution.
- [x] Compute the ordinary and shifted local logarithmic derivatives.
- [x] Prove the local closed-point coefficient is `d*w^(m/d)` precisely
  when `d ∣ m`.
- [x] Differentiate arbitrary finite weighted Euler products exactly.
- [x] Extract the finite Euler-product coefficient recurrence required by
  release 4.66.
- [ ] Instantiate the finite alphabet with bounded-degree monic irreducible
  polynomials and identify product coefficients with weighted monic sums.
- [ ] Identify the irreducible divisor sum with finite-extension Gauss sums.
- [ ] Deduce the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.68

- [x] Make fixed-degree monic irreducibles and the bounded-degree union into
  finite types.
- [x] Instantiate the finite Euler-product recurrence on this irreducible
  alphabet.
- [x] Rewrite its closed-point coefficient as both an irreducible sum and a
  degree-stratified divisor sum.
- [x] Expand its ordinary coefficient over finite degree allocations.
- [x] Map every divisible allocation to a monic polynomial of the exact total
  degree and prove exact preservation of the Hasse--Davenport weight.
- [ ] Construct the inverse allocation from normalized factorization and
  identify Euler coefficients with weighted monic sums.
- [ ] Identify the irreducible divisor sum with finite-extension Gauss sums.
- [ ] Deduce the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.69

- [x] Construct normalized-factorization and multiplication as inverse maps
  between fixed-degree monic polynomials and irreducible factor multisets.
- [x] Convert factor multisets to bounded divisible degree allocations and
  back, with exact multiplicity formulas and inverse laws.
- [x] Transport the Hasse--Davenport product weight across both equivalences.
- [x] Identify every bounded Euler coefficient below the cutoff with
  `hasseDavenportMonicSum`.
- [x] Prove the cutoff-aware logarithmic-derivative signed-power induction.
- [x] Evaluate the bounded closed-point coefficient and its explicit
  degree-stratified irreducible divisor sum as the signed Gauss-sum power.
- [ ] Identify the irreducible divisor sum with finite-extension Gauss sums
  by minimal-polynomial fibers.
- [ ] Deduce the canonical-character prime-degree Gauss lifting formula.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.70

- [x] Package each extension element's minimal polynomial in the bounded
  irreducible alphabet at the extension degree.
- [x] Prove the relative closed-point multiplicity is extension degree
  divided by minimal-polynomial degree.
- [x] Equate a prescribed minimal-polynomial fiber with the corresponding
  irreducible root fiber.
- [x] Compute its cardinality as `d` when `d` divides the extension degree
  and zero otherwise via finite-field algebra-hom counting.
- [x] Regroup the full minimal-polynomial weight sum into the exact
  degree-stratified irreducible divisor sum.
- [x] Prove universal and prime-field Gauss Hasse--Davenport unconditionally.
- [x] Deduce Jacobi Hasse--Davenport and the complete at-most-two-root Kummer
  Frobenius system.
- [ ] Construct the three-or-more-root Kummer cohomological system.

## Prime-equidistribution 4.71

- [x] Generalize polynomial character correlations, zero fibers, character-
  kernel fibers, and affine Kummer covers to arbitrary finite fields.
- [x] Prove the exact arbitrary-field affine point-count and proper-character-
  power trace formulas.
- [x] Prove scalar-twist compatibility and multiplicative Fourier inversion
  for every finite field.
- [x] Specialize the Fourier identity to norm-lifted characters and
  base-changed polynomials over every canonical positive extension.
- [x] Identify the exact normalization factor as `p^(n+2)-1`.
- [ ] Construct the bounded-rank integral weight-bounded isotypic Frobenius
  decomposition for three or more active roots.

## Prime-equidistribution 4.72

- [x] Package higher affine point-count Fourier coefficients with the
  bounded-rank integral weight-bounded base Frobenius spectrum.
- [x] Construct the affine-Fourier system from every genuine all-extension
  Kummer Frobenius system.
- [x] Prove `p^(n+2)-1` is nonzero and cancel the Fourier normalization in
  every positive extension degree.
- [x] Reconstruct the genuine power-trace system from the affine-Fourier
  equations.
- [x] Prove exact equivalence of the three-or-more-root source propositions
  and retain the direct fixed-`r=7` Burgess transfer.
- [ ] Construct the pure bounded-rank isotypic affine Kummer decomposition
  for three or more active roots.

## Prime-equidistribution 4.73

- [x] Construct the finite-field three-root projective Möbius equivalence.
- [x] Reduce the three-root character sum exactly to a scaled Jacobi sum
  minus the deleted projective point.
- [x] Prove the corresponding identity in every canonical extension degree.
- [x] Apply unconditional Jacobi Hasse--Davenport to identify two fixed
  base-field eigenvalues whose power sums give every extension trace.
- [x] Prove both eigenvalues algebraic integral and of norm at most `sqrt p`.
- [x] Construct the genuine rank-two Frobenius system for every
  degree-divisible exactly-three-root case, including one inactive root.
- [x] Reduce the remaining three-or-more-root source to nondivisible
  three-root cases and cases with at least four roots.
- [ ] Construct the residual bounded-rank isotypic Kummer decomposition.

## Prime-equidistribution 4.74

- [x] Prove that a trivial third local character deletes exactly its root.
- [x] Express every inactive-root three-root correlation as a two-root Jacobi
  main term minus one deleted value.
- [x] Prove the formula over every canonical finite extension.
- [x] Use Jacobi Hasse--Davenport and norm lifting to obtain two fixed power-
  trace eigenvalues.
- [x] Prove their algebraic integrality and weight-at-most-one bounds.
- [x] Construct a rank-two Frobenius system for every exact-three-root case
  with at least one inactive root, without a degree hypothesis.
- [x] Reduce the exact-three-root residual to the all-active,
  degree-nondivisible case.
- [ ] Construct that three-point hypergeometric Frobenius system and the
  four-or-more-root systems.

## Prime-equidistribution 4.75

- [x] Prove arbitrary split-polynomial root factorization after base change.
- [x] Decompose every extension correlation into its unrestricted active-root
  sum minus the values at all inactive roots.
- [x] Prove every inactive-root deleted value lifts by an ordinary degree
  power and is algebraic integral of norm at most one.
- [x] Construct the exact one-active-root spectrum indexed by inactive roots.
- [x] Construct the exact two-active-root spectrum from one Jacobi eigenvalue
  and all inactive-root eigenvalues.
- [x] Verify the rank is exactly the allowed `#roots-1` in both branches.
- [x] Prove equivalence of the three-or-more-distinct-root source and the
  three-or-more-active-root source.
- [x] Transfer the latter directly to the full Kummer Frobenius theorem.
- [ ] Construct the three-or-more-active-root cohomological system.

## Prime-equidistribution 4.76

- [x] Define the unrestricted active-root trace sequence from the base field
  through every canonical extension.
- [x] State its natural Frobenius system with rank at most
  `#active roots-1`.
- [x] Prove the full correlation is the active trace minus the power sum of
  all inactive-root deleted values in every indexed degree.
- [x] Append the inactive values as explicit integral weight-zero
  eigenvalues.
- [x] Prove the active and inactive rank budgets combine to `#roots-1`.
- [x] Transfer the at-least-three-active-root system directly to the complete
  Kummer Frobenius theorem.
- [ ] Construct the bounded-rank active-root spectrum from Kummer cohomology.

## Prime-equidistribution 4.77

- [x] Define the canonical polynomial retaining exactly the active linear
  factors, original multiplicities, and leading scalar.
- [x] Prove its nonvanishing, splitness, exact root multiset, and unchanged
  active-root multiplicities.
- [x] Prove every retained root is active and the canonical polynomial is
  Kummer-nondegenerate when its active set is nonempty.
- [x] Prove the evaluation identity after arbitrary scalar extension.
- [x] Identify its ordinary Kummer trace with the active trace in the base
  field and every canonical extension degree.
- [x] Convert its full Frobenius system to an active-root system without rank
  loss.
- [x] Prove equivalence between the active-system source and the full Kummer
  source restricted to all-active split polynomials.
- [ ] Construct the all-active bounded-rank Kummer cohomology system.

## Prime-equidistribution 4.78

- [x] Reduce every active multiplicity modulo the character order.
- [x] Prove every retained residue is nonzero and strictly below the order.
- [x] Prove the reduced polynomial is nonzero, split, and has exactly the
  original active distinct roots with the reduced multiplicities.
- [x] Prove reduced-exponent polynomials have every root active and are
  Kummer-nondegenerate when they have a root.
- [x] Prove base-field correlation invariance under exponent reduction.
- [x] Prove norm lifting preserves the modulo-order power identity.
- [x] Prove all extension correlations are invariant under reduction.
- [x] Prove equivalence with the full Frobenius source restricted to the
  finite exponent range below `orderOf χ`.
- [ ] Construct the reduced-exponent bounded-rank Kummer cohomology system.

## Prime-equidistribution 4.79

- [x] Prove the exact all-extension scalar-multiplication trace formula.
- [x] Construct the explicit monic normalization of every nonzero polynomial.
- [x] Prove normalization preserves splitness, roots, multiplicities, and the
  reduced-exponent condition.
- [x] Absorb the leading-character value into every Frobenius eigenvalue.
- [x] Preserve rank, algebraic integrality, the weight bound, and every power
  trace under that twist.
- [x] Prove equivalence between the reduced source and its monic restriction.
- [ ] Construct the monic reduced-exponent bounded-rank Kummer cohomology
  system.

## Prime-equidistribution 4.80

- [x] Construct the affine root normalization sending two distinct roots to
  `0` and `1`.
- [x] Prove monicity, splitness, root-cardinality, and multiplicity
  preservation.
- [x] Preserve the strict reduced-exponent condition under normalization.
- [x] Prove the exact affine evaluation and all-extension correlation laws.
- [x] Absorb the affine scalar into every Frobenius eigenvalue while
  preserving rank, integrality, weight, and every power trace.
- [x] Prove equivalence between the monic source and its two-point-normalized
  restriction.
- [ ] Construct the two-point-normalized reduced-exponent bounded-rank Kummer
  cohomology system.

## Prime-equidistribution 4.81

- [x] Construct the canonical three-root Legendre polynomial from its third
  root and three multiplicities.
- [x] Prove its monicity, splitness, exact roots, degree, and root
  multiplicities.
- [x] Prove the canonical polynomial satisfies the reduced-exponent condition
  for positive exponents below the character order.
- [x] Extract the unique third root from every normalized three-root source.
- [x] Prove literal equality with the canonical Legendre polynomial.
- [x] Remove the already solved degree-divisible three-root case.
- [x] Split the residual source exactly into the nondivisible Legendre family
  and the normalized four-or-more-root family.
- [ ] Construct the nondivisible Legendre and four-or-more-root Frobenius
  systems.

## Prime-equidistribution 4.82

- [x] Define the explicit power-Legendre character correlation over an
  arbitrary finite field.
- [x] Evaluate the canonical Legendre polynomial after arbitrary scalar
  extension.
- [x] Identify its polynomial correlation with the three local character
  powers.
- [x] Prove equality with the Kummer correlation in every extension degree.
- [x] Define the rank-two integral weight-one Legendre Frobenius-system
  contract.
- [x] Transport systems exactly in both directions between polynomial and
  character-sum formulations.
- [x] Restate the complete residual source using the pure power-Legendre
  system together with the four-or-more-root source.
- [ ] Construct the required power-Legendre and four-or-more-root Frobenius
  systems.

## Prime-equidistribution 4.83

- [x] Replace every rank-at-most-two Legendre system by an explicit ordered
  eigenpair, padding lower ranks with zero.
- [x] Construct the converse `Fin 2` Frobenius system from any eigenpair.
- [x] Prove nonempty-system equivalence and source-level equivalence.
- [x] Derive the exact second-order recurrence for all extension traces.
- [x] Recover the reduced-power Legendre `2√p` Weil bound from the eigenpair
  weight bounds.
- [x] Preserve the complete implication to the full Kummer source.
- [ ] Construct the integral bounded Legendre eigenpair and the normalized
  four-or-more-root systems.

## Prime-equidistribution 4.84

- [x] Define the canonical polynomial product attached to a finite root
  multiset.
- [x] Prove its monicity, splitness, exact root multiset, and exact degree.
- [x] Identify every root multiplicity with the corresponding multiset count.
- [x] Express reduced exponents as the finite inequalities
  `R.count r < orderOf χ` on the multiset support.
- [x] Prove every monic split polynomial equals the product formed from its
  roots.
- [x] Replace the normalized four-or-more-root polynomial source by the
  equivalent root-multiset source.
- [x] Combine that source with the literal Legendre eigenpair and preserve the
  implication to the full Kummer Frobenius system.
- [ ] Construct the integral bounded Legendre eigenpair and the normalized
  four-or-more-root multiset systems.

## Prime-equidistribution 4.85

- [x] Replace the variable-rank higher-root spectrum by a fixed vector indexed
  by `Fin (R.toFinset.card - 1)`.
- [x] Pad every smaller spectrum with zero while preserving integrality and
  weight bounds.
- [x] Prove the padded power sum equals the original power sum in every
  positive degree.
- [x] Construct the converse maximal-rank Frobenius system from the fixed
  vector.
- [x] Prove nonempty-system equivalence and source-level equivalence.
- [x] Derive the sharp all-extension norm bound directly from the vector.
- [x] Preserve the complete implication to the full Kummer source.
- [ ] Construct the Legendre pair and higher-root fixed eigenvalue vectors.

## Prime-equidistribution 4.86

- [x] Define the explicit finite-field root-multiset character correlation.
- [x] Evaluate the mapped canonical root-multiset polynomial as the product
  of its local character powers.
- [x] Identify the polynomial character correlation with the explicit sum
  over every finite extension.
- [x] Prove equality of the complete norm-lifted Kummer and root-multiset
  extension sequences.
- [x] Transport fixed integral weight-one eigenvalue vectors exactly in both
  directions.
- [x] Restate the complete residual using only explicit character sums and
  fixed eigenvalue vectors.
- [x] Preserve the all-extension norm bound and implication to the full
  Kummer source.
- [ ] Construct the two remaining explicit eigenvalue-vector families.

## Prime-equidistribution 4.87

- [x] Replace the ordered higher-root eigenvalue vector by its spectral
  multiset, preserving multiplicities.
- [x] Prove the spectrum has cardinality exactly
  `R.toFinset.card - 1`.
- [x] Transport integrality, weight bounds, and every power trace in both
  directions between vectors and multisets.
- [x] Construct the canonical monic split Frobenius polynomial from the
  spectral multiset.
- [x] Prove its roots are exactly the spectrum and its degree is exactly the
  conductor bound.
- [x] Express every explicit extension trace as a power sum of its roots.
- [x] Preserve the all-extension norm bound and implication to the full
  Kummer source.
- [ ] Construct the Legendre pair and intrinsic higher-root Frobenius
  spectra.

## Prime-equidistribution 4.88

- [x] Replace the ordered Legendre pair by an intrinsic two-element spectral
  multiset.
- [x] Transport integrality, weight bounds, and every extension trace in both
  directions.
- [x] Construct its canonical monic split quadratic Frobenius polynomial.
- [x] Prove its roots are exactly the spectrum and its degree is two.
- [x] Express all Legendre extension traces as power sums of its roots.
- [x] Derive the uniform bound `2*(√p)^(q+1)` in every extension degree.
- [x] Restate the complete residual as two intrinsic spectral families and
  preserve its implication to the full Kummer source.
- [ ] Construct the Legendre and higher-root Frobenius spectra.

## Prime-equidistribution 4.89

- [x] Identify the multiset sum with the sum of the two enumerated Legendre
  eigenvalues.
- [x] Identify the multiset product with their product.
- [x] Prove that both symmetric coefficients are algebraic integers.
- [x] Expand the canonical Frobenius polynomial exactly as
  `X^2 - C(sum) * X + C(product)`.
- [x] Derive the order-two recurrence for every explicit extension
  correlation from the intrinsic trace and determinant.
- [x] Remove eigenvalue-order dependence from the characteristic recurrence.
- [ ] Construct the Legendre and higher-root Frobenius spectra.

## Prime-equidistribution 4.90

- [x] Compose the unconditional critical saddle asymptotic into the public
  Theorem 1.7 endpoint.
- [x] Prove that a nonnegative explicit cubefree Burgess estimate alone
  implies `TaoTheorem17Conclusion`.
- [x] Extract a nonnegative explicit Burgess coefficient from the fixed
  seventh-moment complete Weil estimate.
- [x] Package that coefficient, its Burgess bound, and Theorem 1.7 as one
  checked certificate.
- [x] Carry the full Kummer Frobenius system through to this certificate.
- [x] Carry the final Legendre-plus-higher-root intrinsic spectra directly to
  the public Theorem 1.7 conclusion.
- [ ] Construct the Legendre and higher-root Frobenius spectra, the sole
  remaining input on the Theorem 1.7 route.

## Prime-equidistribution 4.91

- [x] Recover the Legendre trace coefficient from the base-field explicit
  correlation.
- [x] Recover the determinant from the base and degree-two correlations by
  the quadratic Newton identity.
- [x] Prove these explicit coefficients are algebraic integers.
- [x] Prove the coefficient bounds `‖trace‖ ≤ 2*√p` and
  `‖determinant‖ ≤ p`.
- [x] Define the explicit correlation-determined characteristic polynomial.
- [x] Prove every Legendre Frobenius polynomial equals it and has its roots.
- [x] Express the complete extension recurrence using only the first two
  literal correlations.
- [x] Prove uniqueness and a `Subsingleton` instance for the Legendre
  spectrum at fixed input data.
- [ ] Prove existence of the bounded integral roots of the explicit
  characteristic polynomial and construct the higher-root spectra.

## Prime-equidistribution 4.92

- [x] Define the unconditional canonical root multiset of the explicit
  Legendre characteristic polynomial.
- [x] Prove the polynomial is monic of degree two and splits over `ℂ`.
- [x] Prove the canonical multiset has cardinality two and its sum and product
  are the explicit trace and determinant.
- [x] Characterize existence of a Legendre spectrum exactly by root
  integrality, the `√p` root bound, and the literal order-two recurrence.
- [x] Reconstruct every extension power trace from those conditions by
  two-step induction.
- [x] Carry the canonical residual source through the explicit Burgess
  certificate to the public Theorem 1.7 conclusion.
- [ ] Prove the canonical Legendre conditions and construct the higher-root
  spectra.

## Prime-equidistribution 4.93

- [x] Prove every finite-field power-Legendre correlation is an algebraic
  integer.
- [x] Carry this through every literal extension degree.
- [x] Prove the explicit characteristic trace is unconditionally integral.
- [x] Prove that both canonical roots are integral if and only if the explicit
  determinant coefficient is integral.
- [x] Restate the global Legendre source using determinant integrality alone.
- [x] Carry the determinant-only residual through the explicit Burgess
  certificate to the public Theorem 1.7 conclusion.
- [ ] Prove determinant integrality, the canonical-root `√p` bound, and the
  literal recurrence, and construct the higher-root spectra.

## Prime-equidistribution 4.94

- [x] Prove quadratic Frobenius is an involution and preserves the norm-lifted
  Legendre weight.
- [x] Identify its fixed field exactly with the embedded base field.
- [x] Decompose the degree-two correlation into its squared base-weight
  diagonal and paired Frobenius orbits.
- [x] Decompose the square of the base correlation into the same diagonal and
  paired coordinate-swap orbits.
- [x] Cancel the Newton factor `2` and prove the explicit determinant is an
  algebraic integer unconditionally.
- [x] Remove determinant integrality from the global Legendre residual and
  carry the sharper source to the public Theorem 1.7 endpoint.
- [ ] Prove the canonical-root `√p` bound and the literal recurrence, and
  construct the higher-root spectra.

## Prime-equidistribution 4.95

- [x] Prove that a uniform bound on every positive power sum of two complex
  numbers forces the corresponding individual norm bounds.
- [x] Prove the recurrence identifies every literal Legendre extension
  correlation with the canonical-root power sum.
- [x] Prove the canonical-root `√p` condition is equivalent to the literal
  sharp Weil bounds in all extension degrees.
- [x] Record unconditional algebraic integrality of both canonical roots.
- [x] Restate the complete three-root residual using only the literal Weil
  bound and recurrence, with no root or coefficient predicates.
- [x] Carry the completely literal residual through the public Theorem 1.7
  endpoint.
- [ ] Prove the literal all-extension Weil bound and recurrence, and construct
  the higher-root spectra.

## Prime-equidistribution 4.96

- [x] Evaluate Newton's identities on arbitrary finite complex multisets.
- [x] Prove that cardinality and all positive power sums determine a complex
  multiset with multiplicity.
- [x] Prove that two higher-root spectrum records for the same literal
  correlation sequence are equal.
- [x] Install the higher-root spectrum type as a subsingleton and define its
  canonical value from any existence witness.
- [x] Restate higher-root existence as unique existence and carry the
  canonical residual through the public Theorem 1.7 endpoint.
- [ ] Prove the literal Legendre all-extension Weil bound and recurrence, and
  prove existence of the uniquely determined higher-root spectra.

## Prime-equidistribution 4.97

- [x] Define a terminating Newton recursion for elementary symmetric
  coefficients from an arbitrary complex power-sum sequence.
- [x] Prove the recursion recovers multiset elementary symmetric sums.
- [x] Construct the higher-root Newton polynomial from the first finitely
  many literal extension correlations.
- [x] Prove this polynomial is monic of degree `R.toFinset.card-1`.
- [x] Define its canonical complex root multiset and prove the exact
  cardinality unconditionally.
- [x] Prove every admissible spectrum has exactly this polynomial and root
  multiset.
- [x] Replace higher-root spectrum existence by fixed-root integrality,
  weight, and trace conditions and carry them to Theorem 1.7.
- [ ] Prove the literal Legendre Weil bound/recurrence and the canonical
  higher-root integrality, weight, and trace conditions.

## Prime-equidistribution 4.98

- [x] Prove that the power sums of all roots of a degree-`n` polynomial
  satisfy its order-`n` characteristic recurrence.
- [x] Prove uniqueness of a sequence satisfying a monic recurrence from its
  first `n` values.
- [x] Replace the canonical higher-root all-extension trace identities by
  finitely many initial identities and the Newton recurrence.
- [x] Carry the recurrence residual through the full Frobenius system,
  Burgess certificate, and public Theorem 1.7 endpoint.
- [ ] Prove the finite initial identities automatically from the Newton
  construction, then prove the remaining integrality, weight, and recurrence
  conditions together with the literal Legendre Weil bound/recurrence.

## Prime-equidistribution 4.99

- [x] Extract every Newton polynomial coefficient in signed elementary-
  symmetric form.
- [x] Identify the elementary symmetric sums of the canonical roots with the
  recursively constructed Newton coefficients.
- [x] Prove inverse Newton identities for arbitrary complex sequences.
- [x] Deduce all finite initial canonical power-sum identities automatically.
- [x] Reduce the higher-root trace boundary to the literal characteristic
  recurrence and carry the result through Theorem 1.7.
- [ ] Prove canonical-root integrality and `√p` weight, the higher-root
  literal recurrence, and the Legendre literal Weil bound/recurrence.

## Prime-equidistribution 5.00

- [x] Prove that a monic split complex polynomial has integral roots exactly
  when all of its coefficients are integral.
- [x] Restrict Newton-polynomial coefficient integrality to its exact finite
  degree range.
- [x] Identify finite coefficient integrality with integrality of the
  recursively constructed Newton elementary coefficients.
- [x] Replace rootwise integrality in the higher-root residual and carry the
  finite form through the Frobenius system and Theorem 1.7.
- [ ] Prove finite Newton-coefficient integrality, canonical-root `√p` weight,
  and the literal characteristic recurrence, together with the Legendre
  literal Weil bound/recurrence.

## Prime-equidistribution 5.01

- [x] Prove uniform Newton coefficient bounds from uniformly bounded power
  sums for an arbitrary complex sequence.
- [x] Apply Cauchy's root bound to every powered finite multiset.
- [x] Prove that all positive power-sum bounds are equivalent to individual
  finite-multiset norm bounds, including radius zero.
- [x] Replace canonical higher-root weight by the literal sharp
  all-extension Weil bound.
- [x] Carry the fully literal weight residual through the Frobenius system,
  Burgess certificate, and public Theorem 1.7 endpoint.
- [ ] Prove finite Newton-coefficient integrality and the literal higher-root
  and Legendre Weil bounds/characteristic recurrences.

## Prime-equidistribution 5.02

- [x] Generalize the quadratic Frobenius-orbit decomposition from the
  Legendre weight to every explicit root-multiset Kummer weight.
- [x] Compare it with the coordinate-swap decomposition of the squared base
  correlation and prove the second Newton numerator integral.
- [x] Prove Newton elementary integrality in degrees zero, one, and two for
  every prime root-multiset input, with no spectral assumptions.
- [ ] Prove the remaining finite Newton integrality in degrees at least three
  and the literal higher-root and Legendre Weil bounds/recurrences.

## Prime-equidistribution 5.03

- [x] Prove a general weighted sum decomposition for an automorphism of order
  three into fixed points and three-element orbits.
- [x] Identify cubic Frobenius fixed points, norm invariance, and norm-lifted
  root-multiset weights over the cubic finite-field extension.
- [x] Prove integrality of the degree-two and degree-three complete
  homogeneous expressions by finite induction.
- [x] Deduce unconditional integrality of Newton elementary degree three.
- [ ] Prove the remaining finite Newton integrality in degrees at least four
  and the literal higher-root and Legendre Weil bounds/recurrences.

## Prime-equidistribution 5.04

- [x] Decompose the full quartic Frobenius locus into four-element orbits.
- [x] Identify the two-step fixed locus with the quadratic subfield and prove
  that quartic norm-lifted weights there are squares of quadratic weights.
- [x] Prove integrality of the degree-four complete homogeneous expression by
  finite induction.
- [x] Deduce unconditional integrality of Newton elementary degree four.
- [ ] Prove the remaining finite Newton integrality in degrees at least five
  and the literal higher-root and Legendre Weil bounds/recurrences.

## Prime-equidistribution 5.06 (historical)

- [x] Embed arbitrary divisor-degree finite fields and identify Frobenius fixed loci.
- [x] Prove partial-norm descent, orbit invariance, and repeated-period power identities.
- [x] Prove the weighted divisor-sum formula for every finite permutation.
- [x] Construct integral formal Euler factors and prove their differential equation.
- [x] Compare formal coefficients with the exact Newton recursion in every degree.
- [x] Prove all-degree Kummer Newton integrality and canonical-root integrality.
- [x] Remove integrality from the literal residual consumed by Theorem 1.7.
- [x] Eliminate the three inherited contour `ring` diagnostics.
- [ ] Prove the remaining literal higher-root and Legendre Weil bounds/recurrences.
- [ ] Prove Proposition 2.3(ii)/BHP and finish the combined main-theorem release.

## Prime-equidistribution 5.05 (historical)

- [x] Prove a general weighted order-five orbit decomposition.
- [x] Identify quintic Frobenius fixed points and norm-lifted weights.
- [x] Prove integrality of the degree-five complete homogeneous expression by
  finite induction.
- [x] Assemble the fifth Newton numerator from the earlier aggregate residuals
  and the quintic orbit sum.
- [x] Deduce unconditional integrality of Newton elementary degree five.
- [ ] Prove the remaining finite Newton integrality in degrees at least six
  and the literal higher-root and Legendre Weil bounds/recurrences.

## Prime-equidistribution 4.41

- [x] Prove the selected HT shift tends below every positive fixed target.
- [x] Fit the full small-beta depth `beta+eta<=3*eta` inside the native VK
  region at the actual translated height.
- [x] Package the exact two-pole decomposition uniformly for
  `0<beta<=2*eta` and the full HT frequency range.
- [x] Identify the packaged origin residue with the physical
  `-zeta'/zeta(1-beta+it)`.
- [x] Prove the sharp `C+1/beta` origin-residue bound at bounded height.
- [x] Prove the high-height `O(D(A)*loglog(A))` origin-residue bound and
  absorb it into `O(1/beta)` on the small-beta scale.
- [ ] Absorb the negative-left three-edge contribution.

## Prime-equidistribution 4.42

- [x] Place the source coordinate inside a fixed-radius variable VK disk.
- [x] Prove normalized analyticity, zero-freeness, and emptiness of the disk
  zero set.
- [x] Bound the center reciprocal by the Euler product and the disk maximum
  by the frozen Pintz zeta window.
- [x] Apply the frozen disk logarithmic-derivative bound and transport it to
  the physical source point.
- [x] Reduce the disk logarithmic majorant to `O(loglog(A))` at native VK
  width.
- [x] Combine high and bounded heights and prove the uniform eventual
  `K/beta` origin-residue estimate.
- [ ] Absorb the negative-left three-edge contribution.

## Prime-equidistribution 4.10

- [x] Prove every fixed finite indexed-shell sum tends to zero.
- [x] Diagonalize a norm bound for the complete prefix rather than its
  coordinates separately.
- [x] Retain all shellwise cosine-loss assertions on the selected prefix.
- [x] Obtain a depth tending to infinity whose moving prefix vanishes.
- [ ] Telescope the finite sum into one contiguous physical Perron segment.
- [ ] Control the infinite line beyond the moving terminal height.

## Prime-equidistribution 4.11

- [x] Prove exact addition of adjacent normalized symmetric Perron shells.
- [x] Telescope every finite indexed prefix to one contiguous segment.
- [x] Transfer the vanishing slow diagonal to that physical segment.
- [x] Make the terminal shell index tend to infinity.
- [ ] Prove the post-terminal outer Perron line tends to zero.
- [ ] Feed the completed outer-line estimate into the sharp saddle asymptotic.

## Prime-equidistribution 4.05

- [x] Characterize survival through `k` iterated natural square roots by
  `a^(2^k) <= y`.
- [x] Prove eventual terminal noncollapse at every fixed depth.
- [x] Prove the indexed logarithmic rounding criterion eventually at every
  fixed depth.
- [x] Package both ideal scale bounds for each fixed finite shell prefix.
- [ ] Choose one admissible depth tending to infinity.
- [ ] Sum its indexed shell envelopes and control the residual tail.

## Prime-equidistribution 4.06

- [x] Choose a positive fixed exponent adapted to each shell index.
- [x] Prove the critical Rankin ratio is eventually at most the square root
  of the corresponding iterated prime scale.
- [x] Discharge the CEP/PNT/saddle hypotheses at every fixed index `k >= 2`.
- [x] Obtain the full accumulated cosine loss throughout each fixed shell.
- [ ] Make the estimate uniform along a depth tending to infinity.
- [ ] Sum the indexed shell integrals and close the residual outer tail.

## Prime-equidistribution 4.07

- [x] Package the full pointwise assertion for one indexed shell.
- [x] Intersect the estimates over every fixed finite index prefix.
- [x] Select a single shell depth tending to infinity by countable
  diagonalization.
- [x] Obtain simultaneous loss bounds for all `2 <= k <= K(n)`.
- [ ] Derive a uniform normalized integral envelope for this moving family.
- [ ] Sum the controlled prefix and bound the post-terminal tail.

## Prime-equidistribution 4.08

- [x] Define the positive indexed exponent `(4/5)*2^(-k)`.
- [x] Transfer its Rankin-ratio power to the iterated prime scale at the
  saddle.
- [x] Absorb the CEP cofactor cutoff with the universal displacement penalty.
- [x] Prove the explicit loss scale bounds every fixed indexed shell.
- [x] Prove this loss scale tends to infinity for every fixed index.
- [ ] Integrate the fixed-index envelope and diagonalize its finite sum.

## Prime-equidistribution 4.09

- [x] Prove positive-power exponential decay absorbs `sqrt(u)`.
- [x] Extend the indexed loss envelope to both frequency signs.
- [x] Compute the exact width of every indexed symmetric shell.
- [x] Prove each fixed indexed Perron contribution tends to zero.
- [ ] Select a growing depth whose complete finite contribution sum vanishes.
- [ ] Control the infinite Perron tail beyond that terminal height.

## Prime-equidistribution 4.12

- [x] Concatenate the first, extended, and second outer pieces into one
  pre-indexed Perron segment.
- [x] Prove the complete pre-indexed segment tends to zero.
- [x] Define the exact infinite remainder after the pre-indexed and moving
  indexed segments.
- [x] Prove its decay is equivalent to decay of the infinite outer line.
- [x] Reduce the critical smooth-saddle asymptotic to this named remainder.
- [ ] Prove the post-terminal remainder tends to zero by a second
  high-frequency mechanism.
- [ ] Feed the resulting saddle asymptotic into the unconditional Theorem
  1.7 endpoint.

## Prime-equidistribution 4.13

- [x] Convert terminal iterated-scale survival to `4^(2^k) <= y`.
- [x] Bound every admissible indexed physical endpoint by
  `3*pi/(2*log 4)`.
- [x] Prove an eventually admissible growing depth has bounded height.
- [x] Prove such a height cannot tend to infinity.
- [ ] Develop a non-indexed high-frequency estimate for the post-terminal
  Perron remainder.

## Prime-equidistribution 4.14

- [x] Define the exact HT loss `u*t^2/((1-sigma)^2+t^2)`.
- [x] Prove nonnegativity, sign symmetry, and radial monotonicity.
- [x] State HT Lemma 8(ii) as a finite-range characteristic contract.
- [x] Transfer that contract to the normalized physical Perron integrand.
- [x] Integrate a finite symmetric shell at its left-endpoint loss.
- [ ] Prove the minor-arc contract from the Mangoldt cosine sum.
- [ ] Formalize the smoothed short-interval and finite-truncation estimates.

## Prime-equidistribution 4.15

- [x] Define the finite HT complex Mangoldt transform.
- [x] Define its weighted Mangoldt cosine sum.
- [x] Prove the exact real-part subtraction identity.
- [x] Define the source-shaped complex and cosine main terms.
- [x] Prove two complex errors `<=E` give cosine error `<=2E`.
- [ ] Prove the uniform complex transform approximation by Abel–PNT.

## Prime-equidistribution 4.16

- [x] Define the exact HT ceiling `exp((log y)^(3/2-epsilon))`.
- [x] Define the equation-(3.10) transform-error shape.
- [x] State the full uniform HT Lemma 6 proposition with its literal
  epsilon-dependent implied constant.
- [x] Compute the main term at frequency zero, its real part, and its norm.
- [x] Compute the Cartesian weighted-cosine main term.
- [x] Derive the cosine corollary from the uniform transform proposition.
- [ ] Prove the proposition by shifted Perron inversion and the zero-free region.

## Prime-equidistribution 4.17

- [x] Split the HT Mangoldt cosine sum into prime and non-prime parts.
- [x] Identify the prime part using `Λ(p)=log p`.
- [x] Bound the prime part by `log y` times the Euler-product cosine loss.
- [x] Bound the prime-power cosine tail by twice its nonoscillatory mass.
- [x] Derive the explicit cosine-loss lower bound from HT Lemma 6.
- [x] Prove the source-strength HT Lemma 5 bound for the remainder in the
  saddle range `sigma >= 1/2`.
- [ ] Lower-bound the elementary cosine main term in the Lemma 8 range.

## Prime-equidistribution 4.18

- [x] Decompose the non-prime Mangoldt remainder exactly by prime-power
  exponent.
- [x] Prove the `k=1` slice vanishes.
- [x] Dominate every `k>=2` slice by a geometric coefficient times the
  weighted prime logarithm sum when `sigma>=1/2`.
- [x] Sum the geometric coefficients with an explicit constant.
- [x] Apply the Chebyshev bound to obtain the explicit `O(log y)` remainder.
- [x] Combine the remainder with a lower bound for the cosine main term.

## Prime-equidistribution 4.19

- [x] Prove the uniform quadratic lower bound for the Cartesian HT cosine
  main term.
- [x] Insert the explicit prime-power remainder bound into the Lemma 6 bridge.
- [x] Compare the main coefficient with the Rankin ratio under the canonical
  saddle-cutoff hypothesis.
- [ ] Prove the named Lemma 6 transform proposition analytically.

## Prime-equidistribution 4.20

- [x] Bound each saddle prime term by `5 log(y) p^(-sigma)`.
- [x] Apply the canonical finite Abel prime-sum estimate.
- [x] Derive the explicit Rankin-ratio/main-coefficient comparison.
- [x] Obtain the source-shaped rational HT loss from the cosine main term.
- [x] Record that the cutoff is not expected in the critical regime and
  replace this route by a uniform theta-Abel estimate in release 4.21.

## Prime-equidistribution 4.21

- [x] Prove the exact Abel identity for `sum log(p)p^(-sigma)` using theta.
- [x] Bound it by `log(4)y^(1-sigma)/(1-sigma)` for `0<=sigma<1`.
- [x] Deduce the cutoff-free `smoothSaddlePhiOne` main-scale estimate.
- [x] Insert the exact saddle equation and derive the rational HT main-term
  loss with constant `5 log(4)`.
- [ ] Prove the named HT Lemma 6 transform proposition analytically.

## Prime-equidistribution 4.22

- [x] Rewrite the HT transform as `sum Lambda(n)n^(-s)` at
  `s=1-beta+i*t`.
- [x] Rewrite the source main term as `y^(1-s)/(1-s)`.
- [x] Prove the source shifted-Perron contract equivalent to the Lemma-6
  transform contract.
- [x] Prove the exact finite Abel identity against Chebyshev's `psi`.
- [ ] Prove the shifted contour estimate from the zeta logarithmic derivative
  and frozen zero-free rectangle.

## Prime-equidistribution 4.23

- [x] Prove absolute convergence and termwise integration on the shifted
  initial Perron line `1 < Re(s)+c`.
- [x] Identify the normalized logarithmic-derivative integral with the
  source-weighted frozen sharp-Perron kernels.
- [x] Identify the exact shifted cutoff series with the source Dirichlet sum.
- [x] Prove the termwise cutoff-error identity at `s=1-beta+i*t` for
  `beta<c`.
- [ ] Shift the contour, extract `y^(1-s)/(1-s)`, and bound the remaining
  edges from the frozen zero-free region.

## Prime-equidistribution 4.24

- [x] Define the translated zeta-surrogate Perron integrand.
- [x] Prove it equals the literal shifted logarithmic-derivative integrand at
  regular points.
- [x] Prove the simple-pole residue at `z=1-s` is `y^(1-s)/(1-s)`.
- [x] Decompose the initial right line into the source main term and the
  three other rectangle edges.
- [x] Specialize the exact rectangle identity to `s=1-beta+i*t`.
- [ ] Derive the required rectangle zero-freeness and quantitative edge
  estimates uniformly in the HT parameter range.

## Prime-equidistribution 4.25

- [x] Translate the shifted rectangle to physical zeta coordinates.
- [x] Bound every translated imaginary part by `|t|+T`.
- [x] Derive surrogate nonvanishing from the rectangle-uniform
  Vinogradov--Korobov width condition.
- [x] Insert that result into the exact shifted contour identity.
- [x] Extract positive native rectangle constants from the proved Ford
  zero-free theorem.
- [ ] Choose uniform HT contour parameters and bound all three remaining
  edges by the equation-(3.10) error.

## Prime-equidistribution 4.26

- [x] Fix the source shift `2*(log y)^(epsilon/2-1)` and prove its exact
  equation-(3.10) decay identity.
- [x] Fix height `2Y_epsilon(y)` and prove it contains every allowed
  frequency, with translated height at most `3Y_epsilon(y)`.
- [x] Fix the initial line `beta+1/log y` and prove its physical real part
  and exact `exp(1)y^beta` power cost.
- [x] Assemble the contour and sharp-Perron identities into one exact
  transform-error decomposition and norm reduction.
- [ ] Prove the selected shift satisfies the native VK width eventually.
- [ ] Bound the contour-edge and Perron-truncation remainders, including the
  complementary small-beta range.

## Prime-equidistribution 4.27

- [x] Compute the VK denominator exactly at the HT frequency ceiling.
- [x] Reduce the shift-denominator product to a negative power of `log y`
  times a `log log y` factor.
- [x] Prove that product tends to zero by log-versus-power asymptotics.
- [x] Transfer the width through the frozen factor-three height comparison.
- [x] Obtain the literal width uniformly at every translated requested
  height and instantiate native Ford constants.
- [ ] Bound the three contour edges and finite-height Perron error.
- [ ] Close the complementary `beta<=eta` range from the `1/beta` budget.

## Prime-equidistribution 4.28

- [x] Compute the exact norm of the shifted von Mangoldt coefficient.
- [x] Prove cancellation to the optimized sharp-Perron exponent.
- [x] Bound every below-cutoff, endpoint, and above-cutoff term.
- [x] Package the bounds in a nonnegative scalar majorant.
- [x] Prove the infinite majorant is summable.
- [x] Bound the full truncation-error norm by its majorant `tsum`.
- [ ] Estimate that `tsum` explicitly at height `2Y_epsilon(y)`.
- [ ] Bound the displaced contour edges and close the small-beta range.

## Prime-equidistribution 4.00

- [x] Define the third iterated natural square-root prime scale.
- [x] Bound its logarithm between `1/9*log(y)` and `1/8*log(y)`.
- [x] Put the retained CEP alphabet above `1/12*log(y)`.
- [x] Prove unit cosine loss on `[6*pi/log(y), 12*pi/log(y)]`.
- [x] Prove the accumulated eighth-root-alphabet loss.
- [x] Verify its critical-regime cofactor range.
- [ ] Convert the loss to a divergent Rankin-ratio scale and integrate it.
- [ ] Abstract and aggregate the continuing shell family.

## Prime-equidistribution 4.01

- [x] Convert the fourth-shell loss to `u^(1/9)/log(u)`.
- [x] Prove divergence and exponential saddle-normalization absorption.
- [x] Establish the signed physical envelope.
- [x] Integrate the exact shell through `12*pi/log(y)`.
- [ ] Abstract and aggregate all subsequent shells.
- [ ] Pass the aggregate to the infinite outer Perron line.

## Prime-equidistribution 4.02

- [x] Define arbitrary iterated natural square-root prime scales.
- [x] Prove recursive lower and upper logarithmic bounds.
- [x] Solve both envelopes in closed form.
- [x] Recover the existing three rescaled alphabets exactly.
- [x] Define indexed physical upper heights and prove exact doubling.
- [ ] Prove uniform indexed phase loss and shell envelopes.
- [ ] Sum the indexed shells and identify the infinite outer line.

## Prime-equidistribution 4.03

- [x] Prove the indexed endpoint/support coefficient identities.
- [x] Derive retained CEP support from a uniform `4/5` scale bound.
- [x] Prove the exact indexed nonpositive-cosine phase window.
- [x] Prove the generic accumulated indexed-shell loss.
- [ ] Establish the required scale hypotheses uniformly over a growing range.
- [ ] Sum the normalized indexed shells and pass to infinite height.

## Prime-equidistribution 4.04

- [x] Prove iterated prime scales are antitone in the index.
- [x] Reduce all intermediate largeness hypotheses to terminal noncollapse.
- [x] Convert the closed-form rounding error to a four-fifths scale bound.
- [x] Package the explicit condition `10*(2^k-1)*log(2) <= log(y)`.
- [ ] Choose a growing terminal index satisfying both range conditions.
- [ ] Sum its indexed shell envelopes and control the residual tail.

## Prime-equidistribution 3.98

- [x] Define the twice-iterated natural square-root prime scale.
- [x] Prove its logarithm lies between `1/5*log(y)` and `1/4*log(y)` on an
  explicit tail.
- [x] Put the retained CEP alphabet above `1/6*log(y)`.
- [x] Place all retained phases in the nonpositive-cosine window on
  `[3*pi/log(y), 6*pi/log(y)]`.
- [x] Prove the accumulated fourth-root-alphabet cosine-loss lower bound.
- [x] Verify its cofactor-range hypotheses in every critical regime.
- [ ] Convert the explicit third-shell loss to a divergent Rankin-ratio
  scale and integrate the normalized shell.
- [ ] Extend coverage beyond `6*pi/log(y)`.

## Prime-equidistribution 3.99

- [x] Compare the fourth-root cofactor power with a `1/5` power of the
  Rankin ratio.
- [x] Prove the resulting `u^(1/5)/log(u)` loss tends to infinity.
- [x] Prove its exponential envelope absorbs the saddle normalization.
- [x] Extend the envelope to both frequency signs.
- [x] Integrate the exact symmetric shell from `3*pi/log(y)` through
  `6*pi/log(y)`.
- [x] Prove the normalized third-shell contribution tends to zero.
- [ ] Recover uniform loss beyond `6*pi/log(y)`.
- [ ] Assemble all remaining bands into the infinite outer Perron line.
