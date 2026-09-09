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
- [x] Freeze its exact recursive source import closure: 852 Gafni--Tao, 291
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
- [x] Prove that largest-index projection maps the finite factorial-square
  triple set exactly onto `F₃∩[1,x]`, yielding the lower-count transfer
  `#F₃(x) ≤ #triples(x)` used in Theorem 1.10.
- [x] Characterize `F₃¹` as square multiples of factorial squarefree
  components and prove the unconditional `⌊√x⌋-1` lower bounds for both
  `F₃¹`, `F₃` endpoints, and factorial-square triples, including the explicit
  triple `1! (q²-1)! (q²)! = (q (q²-1)!)²`.
- [x] Lift the finite square-family bounds to the reverse-big-O half of the
  `x^(1/2+o(1))` contracts for `F₃¹`, `F₃`, and Theorem 1.10's triple count.
- [x] Pin Erdős--Selfridge and prove the exact factorial-fiber reduction:
  equal squarefree components are equivalent to the intervening consecutive
  product being a square; adjacent repetition is exactly at a square index.
- [ ] Recursively formalize the Erdős--Selfridge no-perfect-power theorem
  (at minimum its square specialization) and derive the two-element fiber
  bound used in Theorem 1.10.
- [x] Sharpen the proved square-root power scale to the source's
  `ζ(3/2)/ζ(3) √x` asymptotic for `VB¹` from the exact sum.
- [x] Prove the elementary `H<N` conclusion of Lemma 3.1 for `N≥1`, by
  extracting a Bertrand prime that divides the interval product exactly once;
  record that the literal `N=0,H=1` interval is an exception to the paper's
  unrestricted natural-number wording.
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
- [ ] Prove the remaining Theorem 2.5 analytic chain: Vinogradov/Weyl
  cancellation, the paper's precise polylogarithmic Vaughan family count, and
  quantitative Type I/II estimates. The canonical Vaughan coefficient
  envelopes and their support cutoffs are now proved. The
  two-dimensional slice/Fubini assembly, directional bounds, radial arithmetic,
  automatic smooth-periodic derivative chains, and unconditional `taoC3Norm`
  coefficient estimate are now proved. Identification of the summable
  Fourier series with the original periodic weight is now proved. The
  compiled contract and exact weighted
  Vaughan identity are not proof of this estimate.
- [ ] Prove Lemma 3.1's subexponential bound
  `H ≤ exp(log^(2/3+o(1)) N)` from Theorem 2.5.
- [x] Build Lemma 3.2's canonical exponent-one/powerful-core factorization;
  prove its coefficient squarefree, supported on primes `≤H`, and dividing
  `H!`, and derive the exact two-position relation `an+h=bm`.
- [x] Complete Lemma 3.2's averaging step selecting two distinct positions
  whose coefficients are each `H^O(1)`.
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
- [ ] Formalize Proposition 2.1's analytic smooth-number estimates and use
  them to prove Lemma 1.6; the exact finite identity alone is not the
  asymptotic.
- [x] Pin and hash the Baker--Harman--Pintz primary source, with exact theorem
  and proof locators.
- [ ] Formalize the Baker--Harman--Pintz bound in Proposition 2.3(ii). The
  pinned paper is provenance only and is not proof evidence.
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
zeta-ratio asymptotic, the positive-start elementary clause of Lemma 3.1, and
the complete polynomial-coefficient relation of Lemma 3.2. It also includes
the exact Theorem 2.5 interface, reciprocal-phase calculus and character
variation, bidirectional finite partial-summation/log-weight reductions, and
the low-frequency Abel reduction and the frozen qualitative PNT's uniform
dyadic and fixed-bounded-frequency `o(P)` consequences, but not the stronger
arbitrary-logarithmic-saving PNT bound or the full prime exponential-sum
estimate.
It does not prove any of Theorems 1.7--1.10. Do not mark a later crosswalk,
proof, or release item complete merely because one of its inputs builds.
