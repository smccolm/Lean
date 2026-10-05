# Source-to-Lean planning crosswalk

**PLANNING ONLY. No imports or Lean declarations added.** All proposed modules are unimplemented. Read literal theorem types, not only names. The machine-readable local inventory records source SHA-256, imports and declaration signatures at the setup checkout; it is not an exhaustive transitive axiom audit.

## Source result mapping

| Source / label | Proposed proof gate / consumer | Main semantic risk |
|---|---|---|
| Lemma 1 `lem:harmonic-lead`; Appendix Lemma 11 `lemma_bnd_sum_nu_powers` | DKKH-03 → 08/09 | Digamma at δ, exact rational corrections, all denominator domains. |
| Lemma 2 `lem:geometric`, `def-Sxy` | DKKH-04 → 05/08 | General x versus integer/half-integer x, finite versus limiting sums. |
| Lemma 3 `lemma_bnd_S_plus_minus` | DKKH-05 → 09 | Convergent oscillatory tails, correct half-integer cancellations and shifted derivative. |
| Lemma 4 `Lemma 2 arias`; Lemma 5 `lem:u-s`, `def-intJabm` | DKKH-06 → 11/14 | Weighted actual integral, endpoint contributions, branch and stationary phase. |
| Lemmas 6–7 `lem:bndchi-Simonic`, `lem:gamma-chi2` | DKKH-07 → 14/15 | Precise χ convention; C₀–C₃ and negative-height phase. |
| Theorem 8 `thm-VDC` and four `def-TNab...` displays | DKKH-08/09 → 10/12/14 | Full g,N and endpoint generality, derivative hypotheses, explicit error constants. |
| Corollaries 0.1 / 8.1 `cor-VDC`, `cor-thmVDC-partII` | DKKH-10 | g=1 lies on the boundary of printed positivity assumptions. |
| Corollary 0.2 `Explicit_B_estimate` | DKKH-11 | The true dual-sum identity and all constants, not an exponent-pair declaration. |
| Theorem 9 `thm-AFE1`, `def-m-AEF1` | DKKH-12 | Missing n=1 term in display; proof's x>1 assumption; conjugation of positive-log phase. |
| Corollary 0.3 `cor:all_t`, `eq:def-c0` | DKKH-13 | Sharp floor transfer, uniform σ and 14.13472 threshold, rigorous decimals. |
| Theorem 10 `thm-AFE2`, `bnd-E-all-x-y`, `def-E0-all-x-y` | DKKH-14/15 | Reversed E₀ branches, |t| powers, σ=1 dual endpoint, actual remainder. |
| Corollary 0.4 `cor-AFE2`, `def:epsilon0-delta0`, Table 1 | DKKH-16 | Maxima over [1/2,1], correct three branch cases, exact 2π. |
| Corollary 0.5 `cor-k-AFE2`, `def:epsilonk`, Tables 2–3 | DKKH-17 | Finite k range, outward rounding, h_k floor, constant-6 consequence. |
| `eq:ek-largeK`, `eq:AFE2-simple`, comparison Table 4 | DKKH-17 | Uniform bounds versus approximate explanatory values; cited comparison attribution. |

## Existing local proofs and required adapters

The setup inspected the current status documentation for nodes 63, 71, 73, 74 and 77, searched all local Lean paths for relevant primitives, and read selected exact statements and proof bodies. The table deliberately records mismatches: existing sophisticated machinery should be reused without claiming that an unrelated stronger-sounding theorem already proves the required explicit inequality.

| Existing source and declaration | Obligation shortened | Precise fit / gap |
|---|---|---|
| [SecondDerivative.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/71%20Guth-Maynard%2C%202026/GuthMaynard/SecondDerivative.lean) : `vanDerCorput_B_process` (line 398) | DKKH-06/11 | Discrete second-difference upper bound for a finite sum; does not give the stationary dual-sum identity or DKKH constants. |
| [TypeIReflection.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/71%20Guth-Maynard%2C%202026/GuthMaynard/TypeIReflection.lean) : `mediumTypeIExactBProcess_native` (line 1988) | DKKH-08/09 | Actual smoothed Poisson split and quantitative far tail; smooth weights/dual truncation require proof before replacing sharp endpoints. |
| [ZetaTruncation.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/71%20Guth-Maynard%2C%202026/GuthMaynard/ZetaTruncation.lean) : `riemannZeta_truncation` (line 563) | DKKH-12/14 | Exact Euler–Maclaurin identity, 0<Re(s), s≠1 and integer cutoff; must bridge half-integer sharp cutoffs and explicit remainder constants. |
| [ContinuousSecondDerivative.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang%2C%202025/Extension/TaoTrudgianYang2025/ContinuousSecondDerivative.lean) : `continuous_second_derivative_bound` (line 18) | DKKH-06/11 | Continuous F,F′,F″ input on a longer interval, α>0 and α≤1; useful derivative control but constants 12 and its scale differ. |
| [ExponentPairBProcess.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang%2C%202025/Extension/TaoTrudgianYang2025/ExponentPairBProcess.lean) : `ExponentPair.bProcess` (line 32) | DKKH-11 | Already proved exponent-pair B transform; asymptotic closure does not retain the explicit finite DKKH remainder. |
| [ZetaDigammaLog.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang%2C%202025/Extension/TaoTrudgianYang2025/ZetaDigammaLog.lean) : `norm_digamma_sub_log_le` (line 172) | DKKH-03/07 | Concrete bound 4/|Im z| for Re z>0, |Im z|≥1. Not the real-small-δ digamma estimate nor automatically sharp enough for C₀. |
| [ZetaSharpTruncation.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang%2C%202025/Extension/TaoTrudgianYang2025/ZetaSharpTruncation.lean) : `norm_zeta_le_sharp_sum_add` (line 10) | DKKH-12 | Actual sharp zeta partial sum with additive 150; useful object/cutoff bridge, not the c₀·t^(−σ) target. |
| [FordDadaroTruncation.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao%2C%202026/Extension/GafniTao/FordDadaroTruncation.lean) : `riemannZeta_eq_fordFiniteApproximation_sub_terms` (line 103) | DKKH-12/14 | Actual zeta and finite approximation identity; retain cutoff/pole terms and exact dependency closure. |
| [FordRiemannDadaroTruncation.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao%2C%202026/Extension/GafniTao/FordRiemannDadaroTruncation.lean) : `riemannZeta_eq_fordPartialSum_sub_terms` (line 115) | DKKH-12/14 | Sharp partial-sum identity with explicit Dadaro terms; inspect branch conventions and interval adapters. |
| [PintzDigammaSharp.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao%2C%202026/Extension/GafniTao/PintzDigammaSharp.lean) : `exists_re_digamma_le_log_add` (line 25) | DKKH-03/07 | Existing logarithmic gamma growth input; existential additive constant is not an explicit numeric certificate. |
| [PintzGammaHorizontalSharp.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao%2C%202026/Extension/GafniTao/PintzGammaHorizontalSharp.lean) : `exists_norm_Gamma_right_displacement_le` (line 107) | DKKH-07 | Horizontal gamma control; requires domain and numerical-strength comparison. |
| [StationaryFourierSourceBlock.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/73%20Tao%2C%202026/Extension/Tao2026/StationaryFourierSourceBlock.lean) : `norm_fourierModeIntegral_Ico_le_stationary_optimized_dyadic` (line 1797) | DKKH-06 | Actual oscillatory integral bounds from node 73; different phase/scale, so selected only if the adapter shortens a proof. |
| [GammaLogBounds.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/77%20Dong-Wang-Wang-Zhang%2C%202026/Extension/DongWangWangZhang2026/GammaLogBounds.lean) : `re_digamma_source_upper` (line 123) | DKKH-03/07 | Node 77 explicit digamma upper bound on a scaled shifted argument. Useful proof pattern; constants and domain differ. |
| [GammaRatioBounds.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/77%20Dong-Wang-Wang-Zhang%2C%202026/Extension/DongWangWangZhang2026/GammaRatioBounds.lean) : `norm_Gamma_source_ratio_le` (line 117) | DKKH-07 | Actual gamma quotient inequalities; cannot relabel as the full C₀–C₃ estimate. |
| [LogarithmicDerivativeBounds.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/77%20Dong-Wang-Wang-Zhang%2C%202026/Extension/DongWangWangZhang2026/LogarithmicDerivativeBounds.lean) : `source_logarithmic_prefix_second_derivative` (line 172) | DKKH-06/11 | Recently completed actual logarithmic-prefix bound with source derivative adapters; no need to rediscover this infrastructure. |
| [ZetaSum.lean](../../9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/77%20Dong-Wang-Wang-Zhang%2C%202026/Extension/DongWangWangZhang2026/ZetaSum.lean) : `tsum_zetaTerm_div_cpow` (line 133) | DKKH-02 | Actual finite/infinite Dirichlet-term and cpow normalization; DKKH uses negative phase and σ-dependent weights, so adapt explicitly. |

Full selected signatures/imports and file hashes: `Tools/local_reuse_inventory.json`. Wider filename candidates included stationary-phase, gamma, AFE, second-derivative and Poisson modules; the selected inventory does not certify every proof in those trees.

## Installed library interfaces

At installed Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, `Complex.digamma_one`, `Complex.digamma_one_half` and `Complex.digamma_apply_add_one` already provide source special values/recurrence. `Real.tsum_eq_tsum_fourier` and `SchwartzMap.tsum_eq_tsum_fourier` provide actual Poisson identities under their exact continuity/summability or Schwartz hypotheses. The sharp piecewise interval weight needs an endpoint argument; it is not automatically Schwartz. `riemannZeta_one_sub` and `completedRiemannZeta_one_sub` are available with their real domains/conventions, and gamma reflection/duplication, integrals and complex powers should be searched before reimplementation.

The installed PNT+ `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/DigammaSeries.lean` contains `hasSum_digamma`, `digamma_eq_tsum`, positive-half-plane differentiability and logarithmic growth bounds. Node 77 already used this exact installed file with a recorded one-file non-Mathlib closure. Do not vendor a second digamma-series proof or pull newer upstream simply because it was found online.

The foundation's smooth zeta-square AFE, quantitative smooth reflection, zero-density and mean-value chains are completed local resources. Their smoothing, powers, constants and domains differ from this paper. Full source equality and normalization consumers are separate proof obligations. No density theorem, RH verification assertion or epsilon-power estimate substitutes for a fixed explicit constant.
