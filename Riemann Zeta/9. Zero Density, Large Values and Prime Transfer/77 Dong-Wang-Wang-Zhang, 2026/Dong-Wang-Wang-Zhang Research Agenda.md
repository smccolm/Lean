# Research agenda and current status

**4 October 2026 — ACTIVE DEVELOPMENT; 7/20 implementation gates complete (DWWZ-01/03/05/06/07/08/10).** The owner explicitly activated the whole-proof goal. The exact actual-sum contract and compatible package/BAT graph pass. The consumed phase-specialized mean-value/comparison/Lipschitz inputs and full same-witness Lemma 2.2 have passed both BATs and their semantic acceptance tests.

## Work completed in this setup

Identified and read the primary paper's five sections and reference list using its HTML and frozen TeX, including both full theorem statements, all seven lemmas and Proposition 4.1. Archived the original PDF and source archive with extracted source. Examined the cited Granville–Soundararajan mean-value and zero-forcing inputs in journal/preprint versions and located the author-hosted exponential-sum chapter. Searched current paper metadata, author publications, web and GitHub implementation evidence, three live upstream repositories, and relevant local interfaces. Prepared the scaffold, inactive goal prompt and source-integrity runner.

This is a literature/interface investigation, not a complete semantic audit of existing libraries or a new proof. The [Sources](Dong-Wang-Wang-Zhang%20Sources.md) document records limits and dated negative results.

## First analytic priority

The initially missing uniform mean-value/twist/Lipschitz package needed for **Lemma 2.2** is now proved at its consumed phase specialization. Its outputs drive the Gaussian lower bound and hence the main inverse theorem. No equivalent theorem was located in the searched local or public Lean sources. This is a search result, not a claim that the theorem is inaccessible or impossible to formalize.

Aim first at the smallest genuine specialization for the completely multiplicative function `n ↦ n^(it)`, with the actual maximizing twist. DWWZ-05 must supply the analytic reason a large sum varies slowly after twisting; DWWZ-06 then assembles the exact uniform estimates. Do not settle for a generic implication assuming those estimates.

Independent branches with useful existing infrastructure are: zeta/xi zero sums (DWWZ-04/08/09/11), the Gaussian identity including its pole (DWWZ-07/10), and the classical large-x estimate (DWWZ-15). Reusing those branches should avoid reproving foundations, but they do not eliminate the need for DWWZ-05.

The uniform zeta consumer is now accepted: `norm_zeta_left_strip_le`
proves Lemma 3.1 with constant 8, from the installed explicit-pole continuation.
Four new boundary/contract regressions, both BATs and the dependency/semantic
audit pass. DWWZ-07 is DONE.

## Minimal remaining-obligation DAG

1. DWWZ-02/04: exact public Lean statements and faithful zero objects; DWWZ-01/03 are DONE.
2. DWWZ-05 → 06: analytic mean-value inputs → actual twist selection, global-in-y Lipschitz and comparison.
3. DWWZ-04 → 08 → 09/11: multiplicity-faithful xi product/convergence → zeta growth from zeros and weighted-zero upper bound; DWWZ-07 supplies the small-height bound.
4. DWWZ-03/07 → 10: actual shifted-series Gaussian identity with positive residue is DONE, by proved regularized Mellin continuation and Gaussian Fubini.
5. DWWZ-06/07/09/10 → 12: weighted-zero forcing from the original large sum.
6. DWWZ-04/11/12 → 13 → 14: actual near/far split → T1 with a common center.
7. DWWZ-03 → 15; DWWZ-14/15 → 16: large-x cancellation plus local-window contradiction → full T2.
8. DWWZ-17/18/19/20: exact regressions, dependency/coverage audits, both BATs and synchronized release evidence.

These obligations are now active. The node-73 survey is recorded in Crosswalk, with no import selected. The actual positive-index sum, unit bound, multiplicativity, conjugation and convergent spectral-shift identity are proved. The compact maximizing twist exists. The GS03 Lemma 7.1 chain now includes the exact Möbius convolution, uniform power-sum error, coefficient mean from the logarithmic convolution and Mathlib Chebyshev, reciprocal tail from Abel summation, finite Euler product and optimized short/long split. `norm_normalized_mean_comparison_le` proves (2.2) for the actual phases with constant `42(2(log 4+4)+1) exp(8)`, for all real twists and `x>1`. The original general statement remains frozen; the specialization is explicitly identified in Crosswalk.

DWWZ-07 is complete via the installed Euler–Maclaurin continuation with its pole explicit. DWWZ-10 is now complete via the actual power-sum remainder's convergent-transform route. DWWZ-08's xi divisor and real log derivative are now complete. The next terminal analytic obligations are **DWWZ-09/11, quantitative zero repulsion and the zero-sum upper bound**. The completed Lemma 2.2 now feeds the Gaussian lower-bound branch. The xi/divisor identities are proved; the residue-bearing Gaussian identity is proved. Full source (2.1) remains an unproved reference generality, not an assumed input or a rewritten contract.

The transform entry is now proved for both the original sum and its logarithmically weighted coefficients: Mathlib's `LSeries_eq_mul_integral` and `LSeries_deriv` feed exact Laplace/Fourier formulas `ζ(s−it)/s` and `−ζ′(s−it)/s`, followed by genuine `L¹ ∩ L²` Parseval with all convergence obligations discharged. The controlled frequency regions and one-point Euler-product/finite-distance bound are proved as described below. Ordinary pointwise/parameter integration is now assembled directly on the full series, with no smooth-number adapter needed for that estimate. Neither Parseval identity alone establishes Halász or Lipschitz. The existing foundation's Schwartz Parseval consumers require smooth test functions and do not directly apply to these floor-cutoff sums; Mathlib's distributional `L²` Fourier interface supplies the bridge without importing another extension.

The near-frequency branch now has a proved von Mangoldt/logarithmic-derivative mean square, exact factorization with nonvanishing, and an actual-maximizer consumer on the source line `σ=1+1/log x`. Its explicit constant is recorded in Crosswalk. The far-frequency branch now imports the foundation's continuous Montgomery theorem through a four-file local closure. Exact derivative-series coefficient blocks, shifted-interval mean squares, both signed shells, and convergent two-sided tails for each block are proved.

The sharp full-series coefficient/frequency sub-obligation is now closed by Gaussian averaging, rather than an infinite triangle sum of block norms. Exact logarithmic Gaussian Gram rows, their symmetric quadratic-form bound and dominated convergence give the index-weighted full-series mean square. The actual derivative coefficients have square sums bounded by `48` and `8/(σ−1)^3`; `zeta_deriv_far_tail` proves the two-sided bound `192 sqrt(π) exp(5/4)[1/T+1/((σ−1)^3 T²)]`, uniformly in the twist, for `1<σ≤2`, `T≥4`, with integrability. The inspected local prefix/Gaussian estimates did not supply this sharp bound; their scoped non-reuse finding is in Crosswalk.

The source-line maximum now has a proved rightward transport mechanism: half-plane Poisson reproduction, unit mass and the explicit complementary-frequency tail. For the actual zeta series, one original maximizer controls all positive rightward shifts on the half-sized window. Combining this with the near/far bounds and Parseval gives `exists_maximizingTwist_weighted_mean_square`; its complete ranges and constants are in Crosswalk. This closes that maximum-transport sub-obligation, not the pointwise mean-value theorem or the whole smooth-number/Euler-product convention bridge.

The difference-factor variant of Poisson transport is also proved, with arbitrary bounded complex multiplier and the initial damping retained. Exact ordinary/weighted dilation Laplace identities connect that factor to the original cutoff sums. The two-point prime/Euler-product estimate and same-maximizer off-frequency consumer are now proved below. The optimized dilation factor and rightward transport are proved. The actual weighted-difference Parseval/mean-square consumer is now proved. Difference smoothing with a dilation-independent arithmetic error is now proved. Parameter-integration assembly and its uniform power-loss evaluation are now proved. Scalar exponent absorption, all-real cutoff assembly and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance; the transform identities do not establish the desired exponent by themselves. A targeted GS03 Lemma 2.1 input inspection found incomplete strong-PNT/Dusart declarations at the installed PNT+ pin; neither was imported. The ordinary pointwise smoothing input is now proved by a valid alternate sieve argument, as described below.

The one-point Euler input is proved: `MeanValueEuler` gives `|ζ(twistZetaPoint x t u)| ≤ (1+L) exp(4C−M_x(t−u))` and `Σ_{p≤x}1/p ≤ log(1+L)+2C`, for `L=log x≥1`, `C=log 4+4`. The source comparison depends only on the actual prime distance and cutoff. A short branch-free proof was adapted from inspected node-74 `FordEulerProduct`; no node-74 dependency was added. These estimates are now consumed by the large-sum distance theorem below.

`MeanValueSmoothing` closes the ordinary pointwise-to-average sub-obligation using installed Brun–Titchmarsh on quartic cells. It proves `|S(x,t)|/x ≤ (2048/log x)∫₀^(log x) exp(−v)|S(exp v,t)|dv + 952321/log x`, uniformly for `x>1` and real `t`, with actual Mangoldt convolution, Abel weighting and all floor/prime-power errors discharged. This sufficient absolute-constant auxiliary estimate is not a claim to GS03's coefficient-one version or to Halász itself. The six-file installed sieve closure and the later scoped node-73 non-reuse decision are documented.

`MeanValueAssembly` now completes ordinary damping-parameter integration: logarithmic-weight removal, finite absolutely integrable Fubini, weighted Cauchy–Schwarz, the minimum of the transported maximum and the trivial series bound, and exact splitting of its parameter integral. `exists_maximizingTwist_mean_value_bound` gives a pointwise ordinary maximum-form estimate with explicit absolute constants and no residual integral; Crosswalk states the formula. This consumes the actual sum and one source maximizer and needs no smooth-number replacement. It is not yet the hybrid source (2.1).

The Euler substitution now gives `exists_maximizingTwist_prime_distance_mean_bound`, with ordinary majorant `D[(M+1)exp(−M)+(1+log L)/L]` and a proved absolute `D`. `exists_large_sum_prime_distance_bound` absorbs its error uniformly over `1≤N≤L^(1/100)` and proves the source's `M≤(1/100)log L+log log L+C` from `|S|=x/N`, at one actual maximizing twist. The reciprocal-prime estimate controls `M+1` before taking logarithms, preserving the exact leading coefficient. All constants precede the height, scale and `N` quantifiers.

The remaining terminal DAG is now: **completed xi/divisor identities (08) → zero repulsion/zero-sum bounds (09/11), with count bridges (04) open; completed Gaussian identity with residue (10) + completed Lemma 2.2 + these inputs → forcing (12) → near/far count (13) → T1 (14); large-x bound (15) + T1 → T2 (16)**. `exists_large_sum_twist_bounds` completes the ordinary-mean-value alternate deduction of the three non-Lipschitz clauses. Its comparison majorant is uniformly at most `L^(-4/5)`; this gives `1+|t₀|≤4N`, and multiplication by the exact inverse comparison factor yields the required `L^(-3/4)` error. All constants precede height, scale and N. This is not a claim to full hybrid (2.1) or a source repair. DWWZ-05/06 are DONE; the count is 7/20.

## Route selection and stopping source searches

The two-frequency input now follows the proved installed `MediumPNT` → actual `θ` logarithmic error → exact prime Abel summation → three-frequency absolute-cosine majorant with mean `75/113<2/3` → actual distance/zeta pair → same-maximizer off-frequency bound. The prime scale is chosen internally as `exp(max(B,1/|y|,L^(1/A)))`. Crosswalk states the exact quantified consumer. A later survey found the relevant stronger node-73 quantitative PNT, but the smaller installed closure suffices, so no node-73 import was added. Multiplication by the damped difference factor and rightward transport are now proved with a bound uniform in frequency and translation. The actual weighted-difference Parseval and full near/far mean-square consumer are now proved. Difference-sum smoothing is now proved with an active-cell error independent of dilation; the mean-square bound now retains the reciprocal cap. Damping-parameter assembly and its power-loss evaluation are now proved. Scalar exponent absorption, all-real cutoff assembly and full Lemma 2.2 are kernel-checked. The next obligations are the Gaussian and zeta/zero inputs to Proposition 4.1.

Primary route: the paper's adaptation of Granville–Soundararajan. For DWWZ-05, compare the journal's Theorems 2b/4 and Lemma 7.1 with the precise Section 2 restatement in the later zero-forcing paper. The two versions' maxima and Euler-product conventions require a bridge, not textual substitution.

If formalizing the general multiplicative-function theory becomes disproportionate, investigate a direct proof of the needed specialized twist/Lipschitz estimate. For DWWZ-10, a vertical-line Mellin/contour argument is a possible alternative to parameter continuation, provided it proves the exact same integrals and residue. For DWWZ-15, a finite third-derivative estimate can replace the exponent-pair abstraction if its uniform range is proved. These are prospective alternatives, not proved repairs.

Do not continue broad source hunting merely because a proof is difficult. Reopen it for a newly identified theorem, a concrete missing cited input, or a newer primary revision. Work on actual analytic bounds and consumers. Bibliography growth, scalar comparisons, fresh module families and conditional wrappers are not replacements for closing gates.

### Gaussian branch now assembled

The actual power-sum remainder bound supplies Mellin convergence and analytic
continuation. The positive/negative half-line pole fractions cancel in the
regularized transform. Gaussian Fubini and restoration of the explicit
exponential now prove the exact Lemma 3.3 identity, including both source
integrals' convergence and the positive residue. Five regressions compile;
DWWZ-10 is DONE after combined BAT/audit and semantic acceptance. The next independent mathematical
branch is the actual xi zero divisor, summability and real log derivative
(DWWZ-04/08 → 09/11), followed by actual forcing.

### Xi branch now assembled

`XiZeros` proves actual zeta-zero identification, exact fiber multiplicity,
critical-strip bounds, local finiteness and multiplicity-preserving reflection.
`XiLogDerivative` consumes the proved installed genus-one factorization,
derives its real exponential-factor cancellation, and proves both the real
resolvent identity and exact zeta/gamma decomposition. The shifted inverse-square
kernel is summable. Seven new regressions and both BATs pass. DWWZ-08 is accepted as DONE;
 DWWZ-04 retains the missing disk/window/rectangle and
conjugation bridges. The next analytic obligations are the xi ratio bound and
uniform gamma/log-derivative estimates for DWWZ-09/11, then forcing.

## Regression design to retain

Test the `n=0` exclusion; floor endpoints; `x<1`; both signs of `t`; repeated zeros; pole exclusion; `λ=1/2`; unbounded `a`; the open disk versus closed window; a single `φ` before all `L`; empty admissible intervals; the exact residue sign/denominator; Gaussian parameter distinct from height; small versus large x at `sqrt T`; nonintegral dyadic endpoints; `ε` strictness; and `K(A)` independent of `δ`. Preserve any counterexample or source correction as a permanent regression.

## Acceptance authority

The [Checklist](Dong-Wang-Wang-Zhang%20Checklist.md), [Architecture](Dong-Wang-Wang-Zhang%20Architecture.md) and this agenda must always report the same gate statuses. Source Contract controls mathematical outputs. Reproduction Manifest controls evidence claims. The ready [Goal Prompt](Dong-Wang-Wang-Zhang%20Goal%20Prompt.md) includes maintenance of the paper BAT and foundation BAT. Recovery-record files are never a task dependency.
