# Source-to-formalization crosswalk

4 October 2026. **PLANNING ONLY. Every node-77 Lean result below is unimplemented.** Labels refer to the [frozen TeX](Sources/DongWangWangZhang-v1-source/main.tex); proposed module names are not claims that files or declarations exist.

| Source | TeX label | Owning gates / proposed module | Required mathematical bridge |
|---|---|---|---|
| (1.1), shifted Dirichlet series | `eq:def-S` | DWWZ-03 / `ZetaSum` | Positive naturals, floor cutoff, exp/log and complex-power identity, `ζ(s−it)` in Re s>1. |
| Theorem 1.1 | `thm:main` | DWWZ-02,14 / `MainTheorems` | Exact T1 in Source Contract; consume actual forcing and disk count with a center independent of L. |
| Theorem 1.2 | `thm:corollary` | DWWZ-02,16 / `LocalZeroCriterion` | Exact T2; small and large x, closed zero window, all nearby centers, constants uniform as specified. |
| Lemma 2.1, (2.1)–(2.3) | `lem:standard-mean` | DWWZ-05 / `MultiplicativeMeanValues` | Genuine Halász hybrid estimate, twisted-mean comparison and Lipschitz estimate, not Hilbert-space large-values machinery. |
| Lemma 2.2, (2.6)–(2.9) | `lem:t0` | DWWZ-06 / `TwistSelection` | Argmax of actual shifted zeta on `[-log x,log x]`; `|t₀|≪N`; `M≤(log₂ x)/100+log₃ x+O(1)`; all-real-y exponent 1/3; full comparison with exponent 3/4. |
| Lemma 3.1 | `lem:zeta-crude` | DWWZ-07 / `ZetaUniformBounds` | `|ζ(1−λ+iv)|≪(2+|v|)^λ/λ`, uniformly `0<λ≤1/2`; no lost small-height or pole case. |
| Lemma 3.2 | `lem:zero-bound` | DWWZ-04,08,09 / `ZeroRepulsion` | `|ζ(1−λ+iu)|≪λ⁻¹ exp(Σρ 2λ²/|1+λ+iu−ρ|²)`; xi factorization and cancellation of gamma growth with the real zero sum. |
| Lemma 3.3 | `lem:gaussian` | DWWZ-10 / `GaussianTransform` | Both real-line integrals and exact residue (see below); prove Fubini and contour/continuation, not just a Gaussian identity in isolation. |
| Lemma 3.4 | `lem:zero-sum-upper` | DWWZ-11 / `ZeroLogDerivative` | `Σρ Re(1/(1+a+iv−ρ))≤(1/2)log(2+a+|v|)+1/a+O(1)`, uniformly in `a>0, |v|≥2`. |
| Proposition 4.1 | `prop:forcing` | DWWZ-12 / `WeightedZeroForcing` | For `c₀N⁶/y₀≤λ≤1/2`, derive `∃η, |η|≤2λ√(log T/y₀)` and `Σρ λ/|1+λ+i(t−t₀+η)−ρ|²≥y₀/4`. |
| Proof of Theorem 1.1 | `eq:outer-zero`, `eq:outer-contribution` | DWWZ-13 / `DiskZeroForcing` | Linked `λ=L/(40y₀)`, `a=20λQ/y₀`, `Q=log T`; actual infinite near/far split and multiplicity consumer. |
| Lemma 5.1 | `lem:large-x` | DWWZ-15 / `LargeXBound` | `S(x,t)≪xT^(-1/13)` for all `x≥√T`; high-frequency pair `(1/6,2/3)` and low-frequency first derivative, arbitrary terminal subintervals. |
| Proof of Theorem 1.2 | `eq:L-choice` | DWWZ-16 / `LocalZeroCriterion` | `L=δε² log T`, lower/upper L bounds, radius≤δ, center in allowed family, `L/360>L/400`; large-x bound converted using `x≤T^A`. |

## Gaussian normalization to preserve

For real `τ`, `V>0`, `0<λ≤1/2`, Lemma 3.3 requires

\[
\sqrt{2\pi V}\int_{\mathbb R}S(e^y,\tau)
 e^{(\lambda-1)y-Vy^2/2}\,dy
=\int_{\mathbb R}\frac{\zeta(1-\lambda+i(\xi-\tau))}{1-\lambda+i\xi}
 e^{-\xi^2/(2V)}\,d\xi
+\frac{2\pi}{1+i\tau}e^{(\lambda+i\tau)^2/(2V)}.
\]

Here `V` is the paper's `𝒯`, **not** height `T`. It becomes `λ/log x` in Proposition 4.1. The moving zeta pole is `ξ=τ−iλ`; the denominator's pole stays in the upper half-plane. With Fourier kernel `exp(−iξy)`, the residue is positive and contains `2π/(1+iτ)`. Mathlib conventions must be bridged explicitly. The source's entire continuation in the auxiliary parameter is a proof obligation, not a permission to treat a divergent unsmoothed integral as an identity.

## Consumer checkpoints

- Lemma 2.2 fixes the maximizing twist at `x`; do not reselect it as `y` varies.
- Proposition 4.1 first obtains frequency `ξ−τ`; conjugation, with multiplicity, gives `τ+η` with `η=−ξ`.
- For T1 choose `φ=t−t₀`, not `φ=t−t₀+η(L)`. The latter choice would lose the common center.
- The outer-zero comparison gives `5λ Σρ |1+a+iφ−ρ|⁻²`; Lemma 3.4 bounds this by `5y₀/36`. The remainder is at least `y₀/9`; each zero copy contributes at most `1/λ`. Thus the count is `≥λy₀/9=L/360`.
- Lemma 5.1 needs a finite **uniform** exponential-sum estimate. An asymptotic exponent-pair object with epsilon loss is only useful after specifying a loss budget inside `1/12−1/13=1/156` and proving every scale conversion. The regime near `X≈|t|` cannot be dropped between high- and low-frequency lemmas.

## Existing code candidates, not accepted imports

| Location inspected | Actual interface found | Remaining node-77 work |
|---|---|---|
| Node 71 `GuthMaynard/ZeroCount.lean` | `analyticVanishingOrder`, `zerosInRect`, `zeroCountRect`, `zeroCountRect_mono`, `analyticVanishingOrder_conj` | Exclude trivial zeros/pole correctly; build open-disk and closed-window counts and match infinite divisor indexing. |
| Installed Mathlib `NumberTheory/LSeries/RiemannZeta.lean` | `zeta_eq_tsum_one_div_nat_cpow`, `riemannZeta_residue_one`, analytic continuation | Prove the shifted series and the exact Gaussian integrand/residue consumer. |
| Installed Mathlib `Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`, `Analysis/MellinTransform.lean`, `Analysis/MellinInversion.lean` | Gaussian Fourier and transform infrastructure | Audit hypotheses and normalize `2π`; Gaussian transform infrastructure alone is not Lemma 3.3. |
| Node 74 `Dependencies/PrimeNumberTheoremAndClean/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean` | `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq`, `riemannXi_hadamard_factorization`, `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` | Minimal compatible import closure; identify zero copies with zeta multiplicities; derive real-part normalization and gamma bounds. |
| Same dependency, `IEANTN/HadamardLogDerivative.lean` | `Kadiri` algebraic factor/log-derivative bridges | Distinguish finite identities from complete analytic product consumers. |
| Node 63 `ExponentPairAProcess.lean`, `ExponentPairBProcess.lean` | `ExponentPair.aProcess`, proved nonasymptotic A-process interface | Obtain the classical pair, normalize logarithmic phase, budget epsilon losses and sum dyadically. |
| Node 63 `ExponentPairLowFrequency.lean` | `norm_exponentialSumAt_le_firstDerivative` with `T≤N/4` and model-phase assumptions | Check parameter normalization; bridge the omitted transition range rather than assuming this theorem applies for every `X≥|t|`. |
| Node 63 frozen ANTEDB / current upstream | Phase, exponential-sum and Euler–Maclaurin infrastructure | No discovered implementation of this paper or its pretentious mean-value/Lipschitz chain. |

The node-63 `GafniTaoNative` derivative subset does **not** contain the whole node-74 PNT+/Hadamard tree. Do not infer those imports from its name. Read [Dependencies](Dependencies/README.md) before deciding which boundary to reuse.
