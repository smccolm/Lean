# Research agenda and current status

**5 October 2026 — PROJECT COMPLETE; 20/20 implementation gates complete (DWWZ-01–20).** The owner explicitly activated the whole-proof goal. The exact actual-sum contract and compatible package/BAT graph pass. The consumed phase-specialized mean-value/comparison/Lipschitz inputs and full same-witness Lemma 2.2 have passed both BATs and their semantic acceptance tests.

## Historical planning survey

Identified and read the primary paper's five sections and reference list using its HTML and frozen TeX, including both full theorem statements, all seven lemmas and Proposition 4.1. Archived the original PDF and source archive with extracted source. Examined the cited Granville–Soundararajan mean-value and zero-forcing inputs in journal/preprint versions and located the author-hosted exponential-sum chapter. Searched current paper metadata, author publications, web and GitHub implementation evidence, three live upstream repositories, and relevant local interfaces. Prepared the scaffold, inactive goal prompt and source-integrity runner.

That historical setup was a literature/interface investigation, not a proof claim. Implementation after activation is recorded below. The [Sources](Dong-Wang-Wang-Zhang%20Sources.md) document records limits and dated negative results.

## Initial analytic priority, now closed

The initially missing uniform mean-value/twist/Lipschitz package needed for **Lemma 2.2** is now proved at its consumed phase specialization. Its outputs drive the Gaussian lower bound and hence the main inverse theorem. No equivalent theorem was located in the searched local or public Lean sources. This is a search result, not a claim that the theorem is inaccessible or impossible to formalize.

The adopted route proves the needed specialization for the completely multiplicative function `n ↦ n^(it)`, with the actual maximizing twist. DWWZ-05 supplies the analytic reason a large sum varies slowly after twisting; DWWZ-06 assembles the exact uniform estimates. Neither conclusion is supplied as an assumed estimate.

The independently developed branches are also complete: zeta/xi zero sums (DWWZ-04/08/09/11), the Gaussian identity including its pole (DWWZ-07/10), and the classical large-x estimate (DWWZ-15). Their selected foundation reuse and actual consumers are recorded in Dependencies and Crosswalk.

The uniform zeta consumer is now accepted: `norm_zeta_left_strip_le`
proves Lemma 3.1 with constant 8, from the installed explicit-pole continuation.
Four new boundary/contract regressions, both BATs and the dependency/semantic
audit pass. DWWZ-07 is DONE.

## Completed obligation DAG

The Gaussian evaluation sub-obligation of DWWZ-12 now compiles in
`GaussianConcentration`: actual same-maximizer continuity, convergent
Gaussian rescaling and exact main/error normalization yield the source
one-sixth saving. `GaussianLowerBound` now consumes the actual large-sum
comparison and proves the exact lower bound `π exp(λ log x/2)/N`, with
one maximizing twist before every admissible λ. That lower bound alone is not
a standalone proof of Proposition 4.1. `GaussianFrequency` and
`WeightedZeroForcing` now assemble residue removal, both frequency tails,
the actual frequency witness and multiplicity-preserving conjugation into
`exists_large_sum_weighted_zero_forcing`. The full consumer compiles;
combined BAT/audit and semantic acceptance passed (DWWZ-12 DONE).
The final gate count is 20/20; dated receipts distinguish the forcing checkpoint from final full-proof verification.

1. DWWZ-02 is DONE: both exact public theorems and their exact-type regressions passed final combined acceptance. DWWZ-01/03/04, including the faithful zero objects and count bridges, are DONE.
2. DWWZ-05/06: analytic mean-value inputs and full same-witness Lemma 2.2 are DONE.
3. DWWZ-08/11 are DONE: actual xi product/convergence and uniform zero-sum bound. DWWZ-09 is also DONE: actual xi quotient, gamma cancellation and all-height source zero repulsion.
4. DWWZ-03 and the DWWZ-05 power-sum/transform inputs → 10: actual shifted-series Gaussian identity with positive residue is DONE, by proved regularized Mellin continuation and Gaussian Fubini. Lemma 3.1 (DWWZ-07) enters the later frequency-tail bound, not this identity.
5. DWWZ-04/06/07/09/10 → 12: weighted-zero forcing from the original large sum, including multiplicity-preserving conjugation, is DONE.
6. DWWZ-04/11/12 → 13 → 14: actual near/far split and full T1 with a common center now compile; combined BAT/semantic acceptance passed.
7. DWWZ-03 → 15; DWWZ-14/15 → 16 are DONE: large-x cancellation plus local-window contradiction → full T2, including exact public-contract regressions; combined BAT/audit and semantic acceptance passed.
8. DWWZ-17/18/19/20 are DONE: exact regressions, dependency/coverage audits, both BATs and synchronized release evidence.

The final integrated BAT/audit, semantic review and documentation gates passed. All mathematical consumers and all twenty acceptance gates are complete. The node-73 survey is recorded in Crosswalk, with no import selected. The actual positive-index sum, unit bound, multiplicativity, conjugation and convergent spectral-shift identity are proved. The compact maximizing twist exists. The GS03 Lemma 7.1 chain now includes the exact Möbius convolution, uniform power-sum error, coefficient mean from the logarithmic convolution and Mathlib Chebyshev, reciprocal tail from Abel summation, finite Euler product and optimized short/long split. `norm_normalized_mean_comparison_le` proves (2.2) for the actual phases with constant `42(2(log 4+4)+1) exp(8)`, for all real twists and `x>1`. The original general statement remains frozen; the specialization is explicitly identified in Crosswalk.

DWWZ-07 is complete via the installed Euler–Maclaurin continuation with its pole explicit. DWWZ-10 is now complete via the actual power-sum remainder's convergent-transform route. DWWZ-08's xi divisor and real log derivative are now complete. DWWZ-09 and DWWZ-11 have passed both BATs and exact semantic review. DWWZ-12's actual weighted forcing is accepted; the actual near/far count and full T1 now compile; both BATs and exact semantic acceptance passed. **DWWZ-15/16, large-x cancellation and T2, now compile**, with DWWZ-04's conjugation/count bridges now accepted. The completed Lemma 2.2 now feeds the Gaussian lower-bound branch. The xi/divisor identities are proved; the residue-bearing Gaussian identity is proved. Full source (2.1) remains an unproved reference generality, not an assumed input or a rewritten contract.

The transform entry is now proved for both the original sum and its logarithmically weighted coefficients: Mathlib's `LSeries_eq_mul_integral` and `LSeries_deriv` feed exact Laplace/Fourier formulas `ζ(s−it)/s` and `−ζ′(s−it)/s`, followed by genuine `L¹ ∩ L²` Parseval with all convergence obligations discharged. The controlled frequency regions and one-point Euler-product/finite-distance bound are proved as described below. Ordinary pointwise/parameter integration is now assembled directly on the full series, with no smooth-number adapter needed for that estimate. Neither Parseval identity alone establishes Halász or Lipschitz. The existing foundation's Schwartz Parseval consumers require smooth test functions and do not directly apply to these floor-cutoff sums; Mathlib's distributional `L²` Fourier interface supplies the bridge without importing another extension.

The near-frequency branch now has a proved von Mangoldt/logarithmic-derivative mean square, exact factorization with nonvanishing, and an actual-maximizer consumer on the source line `σ=1+1/log x`. Its explicit constant is recorded in Crosswalk. The far-frequency branch now imports the foundation's continuous Montgomery theorem through a four-file local closure. Exact derivative-series coefficient blocks, shifted-interval mean squares, both signed shells, and convergent two-sided tails for each block are proved.

The sharp full-series coefficient/frequency sub-obligation is now closed by Gaussian averaging, rather than an infinite triangle sum of block norms. Exact logarithmic Gaussian Gram rows, their symmetric quadratic-form bound and dominated convergence give the index-weighted full-series mean square. The actual derivative coefficients have square sums bounded by `48` and `8/(σ−1)^3`; `zeta_deriv_far_tail` proves the two-sided bound `192 sqrt(π) exp(5/4)[1/T+1/((σ−1)^3 T²)]`, uniformly in the twist, for `1<σ≤2`, `T≥4`, with integrability. The inspected local prefix/Gaussian estimates did not supply this sharp bound; their scoped non-reuse finding is in Crosswalk.

The source-line maximum now has a proved rightward transport mechanism: half-plane Poisson reproduction, unit mass and the explicit complementary-frequency tail. For the actual zeta series, one original maximizer controls all positive rightward shifts on the half-sized window. Combining this with the near/far bounds and Parseval gives `exists_maximizingTwist_weighted_mean_square`; its complete ranges and constants are in Crosswalk. This closes that maximum-transport sub-obligation, not the pointwise mean-value theorem or the whole smooth-number/Euler-product convention bridge.

The difference-factor variant of Poisson transport is also proved, with arbitrary bounded complex multiplier and the initial damping retained. Exact ordinary/weighted dilation Laplace identities connect that factor to the original cutoff sums. The two-point prime/Euler-product estimate and same-maximizer off-frequency consumer are now proved below. The optimized dilation factor and rightward transport are proved. The actual weighted-difference Parseval/mean-square consumer is now proved. Difference smoothing with a dilation-independent arithmetic error is now proved. Parameter-integration assembly and its uniform power-loss evaluation are now proved. Scalar exponent absorption, all-real cutoff assembly and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance; the transform identities do not establish the desired exponent by themselves. A targeted GS03 Lemma 2.1 input inspection found incomplete strong-PNT/Dusart declarations at the installed PNT+ pin; neither was imported. The ordinary pointwise smoothing input is now proved by a valid alternate sieve argument, as described below.

The one-point Euler input is proved: `MeanValueEuler` gives `|ζ(twistZetaPoint x t u)| ≤ (1+L) exp(4C−M_x(t−u))` and `Σ_{p≤x}1/p ≤ log(1+L)+2C`, for `L=log x≥1`, `C=log 4+4`. The source comparison depends only on the actual prime distance and cutoff. A short branch-free proof was adapted from inspected node-74 `FordEulerProduct`; no node-74 dependency was added. These estimates are now consumed by the large-sum distance theorem below.

`MeanValueSmoothing` closes the ordinary pointwise-to-average sub-obligation using installed Brun–Titchmarsh on quartic cells. It proves `|S(x,t)|/x ≤ (2048/log x)∫₀^(log x) exp(−v)|S(exp v,t)|dv + 952321/log x`, uniformly for `x>1` and real `t`, with actual Mangoldt convolution, Abel weighting and all floor/prime-power errors discharged. This sufficient absolute-constant auxiliary estimate is not a claim to GS03's coefficient-one version or to Halász itself. The six-file installed sieve closure and the later scoped node-73 non-reuse decision are documented.

`MeanValueAssembly` now completes ordinary damping-parameter integration: logarithmic-weight removal, finite absolutely integrable Fubini, weighted Cauchy–Schwarz, the minimum of the transported maximum and the trivial series bound, and exact splitting of its parameter integral. `exists_maximizingTwist_mean_value_bound` gives a pointwise ordinary maximum-form estimate with explicit absolute constants and no residual integral; Crosswalk states the formula. This consumes the actual sum and one source maximizer and needs no smooth-number replacement. It is not yet the hybrid source (2.1).

The Euler substitution now gives `exists_maximizingTwist_prime_distance_mean_bound`, with ordinary majorant `D[(M+1)exp(−M)+(1+log L)/L]` and a proved absolute `D`. `exists_large_sum_prime_distance_bound` absorbs its error uniformly over `1≤N≤L^(1/100)` and proves the source's `M≤(1/100)log L+log log L+C` from `|S|=x/N`, at one actual maximizing twist. The reciprocal-prime estimate controls `M+1` before taking logarithms, preserving the exact leading coefficient. All constants precede the height, scale and `N` quantifiers.

The now-implemented mathematical DAG is: **completed xi/divisor identities (08), zero-sum bound (11) and zero repulsion (09), with count bridges (04) accepted; completed Gaussian identity with residue (10) + completed Lemma 2.2 + these inputs → forcing (12) → near/far count (13) → T1 (14); large-x bound (15) + T1 → T2 (16)**. `exists_large_sum_twist_bounds` completes the ordinary-mean-value alternate deduction of the three non-Lipschitz clauses. Its comparison majorant is uniformly at most `L^(-4/5)`; this gives `1+|t₀|≤4N`, and multiplication by the exact inverse comparison factor yields the required `L^(-3/4)` error. All constants precede height, scale and N. This is not a claim to full hybrid (2.1) or a source repair. DWWZ-05/06 are DONE; the count is 20/20.

## Route selection and stopping source searches

The two-frequency input now follows the proved installed `MediumPNT` → actual `θ` logarithmic error → exact prime Abel summation → three-frequency absolute-cosine majorant with mean `75/113<2/3` → actual distance/zeta pair → same-maximizer off-frequency bound. The prime scale is chosen internally as `exp(max(B,1/|y|,L^(1/A)))`. Crosswalk states the exact quantified consumer. A later survey found the relevant stronger node-73 quantitative PNT, but the smaller installed closure suffices, so no node-73 import was added. Multiplication by the damped difference factor and rightward transport are now proved with a bound uniform in frequency and translation. The actual weighted-difference Parseval and full near/far mean-square consumer are now proved. Difference-sum smoothing is now proved with an active-cell error independent of dilation; the mean-square bound now retains the reciprocal cap. Damping-parameter assembly and its power-loss evaluation are now proved. Scalar exponent absorption, all-real cutoff assembly and full Lemma 2.2 are kernel-checked. The Gaussian/zero inputs and full Proposition 4.1 are accepted; the exact T1 chain now compiles. Lemma 5.1 and exact T2 now compile; no analytic obligation remains in the twenty-gate contract.

The adopted primary route follows the paper's adaptation of Granville–Soundararajan. The journal's Theorems 2b/4 and Lemma 7.1 were compared with the precise Section 2 restatement in the later zero-forcing paper. The implemented phase-specialized consumers preserve the required maximum and Euler-product conventions; the generic statements are not inferred by textual substitution.

The completed alternatives are recorded in Crosswalk: phase-specialized mean value/Lipschitz in place of unnecessary generic multiplicative-function theory, regularized Mellin/Gaussian Fubini in place of moving-contour continuation, and finite A/B/first-derivative large-x estimates in place of an exponent-pair abstraction. They prove the required exact conclusions without source repairs. None remains a pending route-selection task.

Do not continue broad source hunting merely because a proof is difficult. Reopen it for a newly identified theorem, a concrete missing cited input, or a newer primary revision. Work on actual analytic bounds and consumers. Bibliography growth, scalar comparisons, fresh module families and conditional wrappers are not replacements for closing gates.

### Gaussian branch now assembled

The actual power-sum remainder bound supplies Mellin convergence and analytic
continuation. The positive/negative half-line pole fractions cancel in the
regularized transform. Gaussian Fubini and restoration of the explicit
exponential now prove the exact Lemma 3.3 identity, including both source
integrals' convergence and the positive residue. Five regressions compile;
DWWZ-10 is DONE after combined BAT/audit and semantic acceptance. The actual xi zero divisor, summability and real log derivative are now proved
(DWWZ-08 DONE). Quantitative zero repulsion and zero-sum bounds feed actual forcing.

### Xi branch now assembled

`XiZeros` proves actual zeta-zero identification, exact fiber multiplicity,
critical-strip bounds, local finiteness and multiplicity-preserving reflection.
`XiLogDerivative` consumes the proved installed genus-one factorization,
derives its real exponential-factor cancellation, and proves both the real
resolvent identity and exact zeta/gamma decomposition. The shifted inverse-square
kernel is summable. Seven new regressions and both BATs pass. DWWZ-08 is accepted as DONE;
DWWZ-04's disk/window/rectangle and conjugation bridges have passed combined acceptance. The xi ratio and gamma cancellation now close DWWZ-09; actual forcing is accepted and T1 now compiles. The uniform digamma and zeta
log-derivative bounds now prove exact DWWZ-11; both BATs and semantic acceptance pass.

### Source zero repulsion assembled

The actual xi quotient, horizontal gamma quotient, rational factors and
lower real logarithmic derivative now give exact Lemma 3.2 in
`exists_source_zero_repulsion`. Height growth cancels with its exact
coefficient, and Lemma 3.1 covers small heights. Six additional regressions
retain the full source statement and boundaries. DWWZ-09 is DONE after both BATs and semantic acceptance. The near/far split (13) and full T1 (14) now compile, with both BATs and exact semantic acceptance passed; the complete weighted-forcing consumer (12) is accepted. The multiplicity-preserving conjugation/count bridges (04) are now accepted.

## Regression coverage to retain

Test the `n=0` exclusion; floor endpoints; `x<1`; both signs of `t`; repeated zeros; pole exclusion; `λ=1/2`; unbounded `a`; the open disk versus closed window; a single `φ` before all `L`; empty admissible intervals; the exact residue sign/denominator; Gaussian parameter distinct from height; small versus large x at `sqrt T`; nonintegral dyadic endpoints; `ε` strictness; and `K(A)` independent of `δ`. Preserve any counterexample or source correction as a permanent regression.

## Acceptance authority

The [Checklist](Dong-Wang-Wang-Zhang%20Checklist.md), [Architecture](Dong-Wang-Wang-Zhang%20Architecture.md) and this agenda must always report the same gate statuses. Source Contract controls mathematical outputs. Reproduction Manifest controls evidence claims. The completed [Goal Prompt](Dong-Wang-Wang-Zhang%20Goal%20Prompt.md) includes maintenance of the paper BAT and foundation BAT. Recovery-record files are never a task dependency.
