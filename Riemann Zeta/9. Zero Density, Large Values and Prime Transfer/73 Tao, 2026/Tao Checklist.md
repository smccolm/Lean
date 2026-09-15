# Tao 2026 Checklist

This is the detailed readiness and future completion ledger for node 73.
Checked groundwork and input items do not imply that a public theorem from the
paper has been formalized.

## Groundwork completed

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

## Formalization - active

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
- [ ] Recursively formalize the Erdős--Selfridge no-perfect-power theorem
  (at minimum its square specialization) in the residual short range
  `3≤H<N`; instantiating the proved consequence then gives the two-element
  fiber bound used in Theorem 1.10.
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
  the quantitative Type I/II estimates. Its full
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
- [ ] Formalize the Baker--Harman--Pintz bound in Proposition 2.3(ii). The
  pinned paper is provenance only and is not proof evidence. The exact
  backward-to-forward endpoint and finite-exception transfer is proved; the
  source theorem's analytic sieve argument remains.
- [ ] Prove the selected release scope without `sorry`, `admit`, project
  postulates, or unsafe proof bypasses.
- [x] Add an executable development `Audit.lean` covering every current Tao
  theorem declaration.
- [x] Extend the development verifier with real source, import, diagnostic,
  frozen-hash, file-set, and axiom contracts.
- [ ] Promote the development verifier to a proof-release verifier only when
  all four public theorem endpoints exist.

## Release acceptance - future

- [ ] Every claimed result has an exact source crosswalk.
- [ ] Every vendored or copied dependency has immutable provenance.
- [ ] The production root builds with zero project diagnostics.
- [ ] Public endpoints pass a transitive axiom audit.
- [ ] Source hashes and frozen dependency boundaries pass.
- [ ] README claims match the executable audit and reproduction manifest.
- [ ] The architecture dashboard reflects actual, not aspirational, status.

## Current stop line

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
The unrestricted Sylvester--Schur theorem itself still has a finite bounded
residual rectangle, now restricted to `H>=101`. However, a separate theorem
proves one start cutoff beyond which its conclusion holds for every length.
Admissible starts escape that cutoff with the dyadic scale, so unrestricted
Sylvester--Schur is no longer an input to Theorem 1.7. The exact Theorem 1.7
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
