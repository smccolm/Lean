# Source-to-formalization crosswalk

4 October 2026. **ACTIVE DEVELOPMENT.** Labels refer to the [frozen TeX](Sources/DongWangWangZhang-v1-source/main.tex). `ZetaSum`, `TwistSelection`, `MeanComparison`, `PowerSumEstimate`, `CoefficientMean`, `MeanValueTransform`, `MeanValueFrequency`, `MeanValueMaximum`, `MeanValueEuler`, `MeanValueSmoothing`, `MeanValueAssembly`, `TwistBounds`, `TwoPointEuler`, `DilationMeanSquare`, `DilationSmoothing`, `DilationAssembly`, `DilationLipschitz`, `ZetaUniformBounds`, `RegularizedTransform`, `GaussianTransform`, `XiZeros`, `XiLogDerivative`, `SemanticRegression` and `Audit` are integrated. The two-frequency prime/zeta input and its actual-maximizer consumer are proved; other module names below remain proposals. T1 and T2 are unproved.

| Source | TeX label | Owning gates / proposed module | Required mathematical bridge |
|---|---|---|---|
| (1.1), shifted Dirichlet series | `eq:def-S` | DWWZ-03 / `ZetaSum` | Positive naturals, floor cutoff, exp/log and complex-power identity, `ζ(s−it)` in Re s>1. |
| Theorem 1.1 | `thm:main` | DWWZ-02,14 / `MainTheorems` | Exact T1 in Source Contract; consume actual forcing and disk count with a center independent of L. |
| Theorem 1.2 | `thm:corollary` | DWWZ-02,16 / `LocalZeroCriterion` | Exact T2; small and large x, closed zero window, all nearby centers, constants uniform as specified. |
| Lemma 2.1, (2.1)–(2.3) | `lem:standard-mean` | DWWZ-05 / `MeanComparison`, `PowerSumEstimate`, `CoefficientMean` | Phase-specialized source-form (2.2) proved with an absolute constant; generic hybrid (2.1) and optimal (2.3) remain unproved reference generality; the faithful phase-specialized inputs consumed by Lemma 2.2 are proved below (DWWZ-05 DONE). |
| Lemma 2.2, (2.6)–(2.9) | `lem:t0` | DWWZ-06 / `TwistSelection` | Argmax of actual shifted zeta on `[-log x,log x]`; `|t₀|≪N`; `M≤(log₂ x)/100+log₃ x+O(1)`; all-real-y exponent 1/3; full comparison with exponent 3/4. |
| Lemma 3.1 | `lem:zeta-crude` | DWWZ-07 / `ZetaUniformBounds` | `|ζ(1−λ+iv)|≪(2+|v|)^λ/λ`, uniformly `0<λ≤1/2`; no lost small-height or pole case. |
| Lemma 3.2 | `lem:zero-bound` | DWWZ-04,08,09 / `ZeroRepulsion` | `|ζ(1−λ+iu)|≪λ⁻¹ exp(Σρ 2λ²/|1+λ+iu−ρ|²)`; xi factorization and cancellation of gamma growth with the real zero sum. |
| Lemma 3.3 | `lem:gaussian` | DWWZ-10 / `GaussianTransform` | Both real-line integrals and exact residue (see below); prove Fubini and contour/continuation, not just a Gaussian identity in isolation. |
| Lemma 3.4 | `lem:zero-sum-upper` | DWWZ-11 / `ZeroLogDerivative` | `Σρ Re(1/(1+a+iv−ρ))≤(1/2)log(2+a+|v|)+1/a+O(1)`, uniformly in `a>0, |v|≥2`. |
| Proposition 4.1 | `prop:forcing` | DWWZ-12 / `WeightedZeroForcing` | For `c₀N⁶/y₀≤λ≤1/2`, derive `∃η, |η|≤2λ√(log T/y₀)` and `Σρ λ/|1+λ+i(t−t₀+η)−ρ|²≥y₀/4`. |
| Proof of Theorem 1.1 | `eq:outer-zero`, `eq:outer-contribution` | DWWZ-13 / `DiskZeroForcing` | Linked `λ=L/(40y₀)`, `a=20λQ/y₀`, `Q=log T`; actual infinite near/far split and multiplicity consumer. |
| Lemma 5.1 | `lem:large-x` | DWWZ-15 / `LargeXBound` | `S(x,t)≪xT^(-1/13)` for all `x≥√T`; high-frequency pair `(1/6,2/3)` and low-frequency first derivative, arbitrary terminal subintervals. |
| Proof of Theorem 1.2 | `eq:L-choice` | DWWZ-16 / `LocalZeroCriterion` | `L=δε² log T`, lower/upper L bounds, radius≤δ, center in allowed family, `L/360>L/400`; large-x bound converted using `x≤T^A`. |

## Implemented uniform zeta continuation consumer

`DongWangWangZhang2026.norm_zeta_left_strip_le` proves
`‖ζ(1−λ+iv)‖ ≤ 8(2+|v|)^λ/λ` for every real `v` and
`0<λ≤1/2`. It consumes installed `Zeta0EqZeta` and
`ZetaBnd_aux1b`, keeping the pole separate in
`norm_zeta_sub_sum_pole_le`. Finite power-sum comparison and the natural
cutoff `ceil(2+|v|)` discharge every remaining premise. Neither a large-height
assumption nor an unspecified analytic remainder is retained. Four regressions
freeze the source bound, zero height, the closed half endpoint and explicit pole.
Both BATs and the exact consumer audit pass; DWWZ-07 is DONE.

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

## Implemented residue-bearing Gaussian consumer

`RegularizedTransform` proves the actual bounded remainder's Mellin
continuation on `Re(s)>0`. For `c=1+it`, the positive-half-line transform is
`ζ(s−it)/s − 1/[c(s−c)]`; the negative half-line contributes
`+1/[c(s−c)]`. Absolute convergence holds on `0<Re(s)<1`.
Thus `integral_zetaExpRemainder` supplies the actual full-line shifted zeta
quotient without assuming an analytic transform formula in the strip.

`DongWangWangZhang2026.source_gaussian_identity` in `GaussianTransform` proves
exactly the displayed Lemma 3.3 formula for every real twist, every `V>0` and
`0<λ≤1/2`. Its immediate consumers are `regularized_source_gaussian_identity`,
`integrable_source_gaussian_remainder`, and `integral_source_gaussian_pole`.
The joint Fourier integrand and both original integrals have separate proved
absolute-convergence interfaces. Restoring the subtracted exponential gives
the positive residue, with `sqrt(2πV)sqrt(2π/V)=2π` proved exactly.

This is a faithful alternate proof of the frozen identity, not a source repair.
Its proved Mellin continuation replaces moving-contour continuation; there is
no contour limiting step left as a hypothesis. No extra analytic or height
premise is added. Node-74's `PintzGaussianBareShift` and
`PintzGaussianKernel` were inspected: their bare-kernel shift on fixed lines
does not supply this shifted-zeta consumer, so no node-74 import was added.
The existing power-sum error bound and foundation pole-removal theorem suffice.
Five new regressions and both BATs pass. Semantic review accepts DWWZ-10 as DONE.

## Actual xi/divisor and real logarithmic-derivative consumers

`XiZeros` consumes the pinned installed PNT+ entire xi and genus-one
Hadamard library. Each `XiZero` is a sigma/finite multiplicity index of
the actual divisor, not an unweighted set or an assumed enumeration.
`xiZeroPoint_zeta_zero`, `xiZeroPoint_re` and
`xi_zero_fiber_card` prove the genuine zeta zero, strict critical strip
and exact analytic multiplicity of the whole fiber. Gamma and rational
factors are proved analytic units, so neither poles nor trivial zeros
enter the index. Bounded index sets are finite.

`xiZeroReflectEquiv` preserves both the point reflection `ρ ↦ 1−ρ`
and every multiplicity label. `summable_xiZero_norm_inv_sq` consumes
the proved order-one divisor theorem. `XiLogDerivative` proves absolute
convergence of the real reciprocal and resolvent sums. Evaluating one
actual Hadamard polynomial at zero and one, and reindexing by reflection,
derives the cancellation of its real linear coefficient.

`re_xi_logDeriv_eq_tsum_of_one_le_re` consequently proves
`Re(ξ′/ξ)(s)=Σρ Re(1/(s−ρ))` for every `Re(s)≥1`, with summability
and no zero-avoidance or factorization premise. The stronger off-zero
identity is also proved. `tsum_xiZero_re_eq_zeta_gamma` gives the exact
rational, `−log π/2`, gamma and zeta logarithmic-derivative expression
for `Re(s)>1`. `summable_xiZero_inverse_square` proves convergence of
the actual shifted kernel used in Lemma 3.2.

Seven regressions retain actual zeros, full multiplicity fibers, reflection
labels, genus-one convergence, the real identity, the exact source
decomposition and inverse-square convergence. Focused builds pass;
DWWZ-08 is DONE after combined BAT/audit and semantic acceptance. DWWZ-04 remains
OPEN for disk/window/rectangle and conjugation bridges. No gamma asymptotic,
zero-repulsion estimate or zero-sum upper bound is claimed yet.

Reuse survey: the installed `RiemannZetaHadamard` already supplies the
genuine factorization and convergence. The matching node-74 family was
inspected; importing its separate package is unnecessary. Installed
`IEANTN.Kadiri`'s named real Hadamard identities have unfinished proof
bodies, so they were not imported or assumed. The clean underlying
Hadamard theorem plus the new reflection proof discharges the identity.
Dependencies records the selected 61-file source closure and hashes.

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

### Node-73 survey before implementation — inspected, no relevant reuse

On activation, searched the node-73 Lean tree for mean-value, twist, Lipschitz, pretentious, Mertens and exponential-sum interfaces, and inspected the actual interfaces in `Asymptotics.lean`, `LargeSieveGlobal.lean`, `ExceptionalCharacterBHM.lean`, `LowFrequency.lean`, `LowFrequencyIntegral.lean`, `SmallPrimeMertens.lean`, `SmoothNumberSaddlePhase.lean` and `VinogradovPhase.lean`. The finite `bombieri_halasz_montgomery_inequality` concerns Gram energies, not the multiplicative mean-value estimate. The low-frequency interfaces concern reciprocal prime phases and PNT discrepancy; the small-prime interface concerns fifty-tuple Mertens weights, not the needed reciprocal-prime estimate. The sequence uniformization helper does not shorten the direct real-parameter compactness argument.

**Outcome: “inspected, no relevant reuse” for the initial DWWZ-03/05/06 obligation.** No node-73 import or dependency was added. This is a scoped interface survey, not a claim that every theorem in node 73 is irrelevant to every later obligation. Any later reuse still requires a named exact declaration, the DWWZ obligation materially shortened, compatible audited import closure, and genuine input adapters.

### Implemented entry consumers

`zetaSum_eq_sum_exp`, `norm_zetaTerm`, `zetaTerm_mul`, `zetaSum_neg`, `norm_zetaSum_le`, `summable_zetaTerm_div_cpow` and `tsum_zetaTerm_div_cpow` in `ZetaSum.lean` implement the positive-index/floor convention and the actual introduction's absolutely convergent shifted series. `exists_maximizingTwist` in `TwistSelection.lean` proves compact maximum attainment of the actual zeta norm for every `x>1`, with the entire interval checked for avoidance of the pole. `prime_phase_deviation_le` proves the exact weighted prime Cauchy–Schwarz step for the actual spectral difference. The downstream quantitative displacement/distance/comparison consumers are recorded below; the initial interfaces alone do not establish them.

`MeanComparison.lean` implements the GS03 Lemma 7.1 reduction using the actual coefficient `phaseMobiusCoeff = μ * phaseArithmetic`. `phaseMobiusCoeff_prime_pow` and `norm_phaseMobiusCoeff_prime_pow` give its exact prime-power values and norms. `zetaSum_eq_mobius_twisted_sum` proves the finite twisted convolution at the original real cutoff, directly consuming Mathlib's `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`; no new hyperbola reindexing infrastructure is needed.

`PowerSumEstimate.lean` proves `norm_zetaSum_sub_powerMain_le_min`: for every real `α` and `x≥1`, the error in `S(x,α) − x^(1+iα)/(1+iα)` is at most `min(4(1+α²),2x)`. Its proof uses actual complex integration by parts twice on each unit cell, the bound `(α²+|α|)/x²` for the second derivative, Mathlib's `sum_Ioo_inv_sq_le`, telescoping, and the final fractional interval. This is a proved uniform analytic input, not a citation or assumed error estimate.

`norm_mean_comparison_le_mobius_error` consumes this result and bounds the actual error by `Σ_{d≤x} |(μ*f)(d)| min(5(1+α²),2x/d)`, with the correct source prefactor `x^(iα)/(1+iα)`.

`CoefficientMean.lean` discharges this coefficient error. The exact logarithmic Dirichlet-convolution identity and Mathlib's `Chebyshev.psi_le_const_mul_self` give `sum_phaseMobiusAbs_le` with constant `C = 2(log 4+4)+1`. Abel summation gives `sum_phaseMobiusWeight_tail_le`, with integrability and every endpoint checked. The finite smooth-number Euler-product theorem, exact prime-power geometric series and a summable higher-power correction give `sum_phaseMobiusWeight_le_exp_prime`; unrestricted convergence at one is not assumed. Splitting at `x/(1+α²)` and treating the complementary large-twist range proves `norm_mean_comparison_le_prime_error`.

The public consumer `norm_normalized_mean_comparison_le` proves **the paper's (2.2) for `f(n)=n^(it)`**, for every `x>1` and every real `t,t₀`, with explicit absolute error constant `42(2(log 4+4)+1) exp(8)`, spectral difference `t−t₀`, the source's `log(e+|t₀|)/log x` and its exact prime-exponential factor. This faithful specialization follows the GS03 Lemma 7.1 proof path; it is not a proof for arbitrary multiplicative functions. No source correction is involved. Generic hybrid (2.1) and optimal (2.3) remain unproved; their consumed phase specialization is proved below. The quantitative prime-distance, displacement and final comparison clauses are now proved below.

`MeanValueTransform.lean` implements the actual summatory transform on `Re s>1`: `integral_zetaSum_exp_univ` gives the full-line Laplace integral `ζ(s−it)/s`; `fourier_dampedZetaSum` gives Mathlib's exact `2πξ` normalization; `integral_zeta_quotient_sq_eq_sum_sq` gives Parseval with weight `exp(-2σu)`. Measurability at floor jumps, absolute convergence, the logarithmic Jacobian, vanishing below cutoff one, `L²` membership and spectral-square integrability are proved. The generic `L¹ ∩ L²` bridge is derived from Mathlib's distributional Fourier agreement using smooth test functions, not an assumed Parseval formula.

The same module now supplies the actual logarithmically weighted coefficients `logZetaSum x t = Σ_{1≤n≤x} log(n)n^(it)`. `LSeries_logZetaTerm`, `integral_logZetaSum_exp_univ` and `fourier_dampedLogZetaSum` identify the transform as `−ζ′(s−it)/s`, including its sign; `integral_zeta_deriv_quotient_sq_eq_logSum_sq` proves the weighted Parseval identity. Arbitrarily small power-loss bounds justify absolute convergence throughout `Re s>1`, not merely `Re s>2`. Both sides are genuinely square integrable.

The near-frequency estimate is proved: `zeta_logDeriv_quotient_mean_square_le` uses Mathlib's exact von Mangoldt logarithmic derivative, the actual twisted coefficients, Chebyshev and the summatory Parseval argument to give the uniform constant `(log 4+4)²/[2(σ−1)]`. `zeta_deriv_near_frequency_le` factors the derivative with nonvanishing proved; `exists_maximizingTwist_near_mean_square` consumes the actual source maximizer at `σ=1+1/log x`, over `|2πξ|≤log x`, with explicit right side `|ζ(s₀−it)|²(log 4+4)² log x/2`. This is not yet the global Halász estimate.

For the far-frequency work, `MeanValueFrequency.lean` imports the exact continuous theorem `RiemannZeta.GuthMaynard.integral_norm_sq_dirichletTime_le`; its four-file local closure and hashes are in Dependencies. `zetaLogBlock_eq_LSeries_terms` identifies actual derivative-series coefficients on `(N,2N]`. The phase/translated-interval adapter proves the mean square with factor `(b−a+2(5π+1)N)`. Positive and negative shells are summed with convergence to `zetaLogBlock_far_tail`: the two-sided tail outside `|y|≤T` is at most `4(T+2(5π+1)N) Σ(log n·n^(−σ))²/T²`, uniformly in real `t`, for `N>0`, `σ,T>0`.

The sharp full-series coefficient assembly is now proved by a different route in the same module. Before implementing it, inspected node 63's `DirichletMeanSquareTranslation`, `DirichletPrefixMeanSquare`, `GaussianPrefixMean` and `DirichletPrefixBounded`: the available prefix bounds carry a logarithmic loss and do not discharge the needed sharp infinite-series estimate. Node 73's `SmoothNumberCEPBootstrap` uses a Hildebrand density input, not the relevant Hilbert/mean-square inequality. No new extension import was selected.

`sum_logGaussianKernel_le` bounds each logarithmic Gaussian Gram row by `exp(1/4)(1+6n/T)`, for `T≥4`, using proved lower/upper power-sum integral comparisons. The exact identity `integral_gaussian_logFrequencySum`, a symmetric quadratic-form estimate and a Gaussian majorant prove `integral_norm_sq_logFrequencySum_le` with absolute constant `sqrt(π) exp(5/4)` and diagonal weights `T+6n`. Dominated convergence proves `integral_norm_sq_tsum_logFrequency_le`; no infinite coefficient-block triangle estimate is assumed.

`tsum_zetaLogCoeff_phase` identifies the actual absolutely convergent series with `−ζ′(σ+i(y−t))`. Its ordinary coefficient-square sum is at most `48`, and its index-weighted square sum is at most `8/(σ−1)^3` for `1<σ≤2`. The resulting shifted-interval mean square has constant `48 sqrt(π) exp(5/4)`. Both signed frequency tails are summed with integrability proved. The public consumer `zeta_deriv_far_tail` gives

`∫_{|y|>T} |ζ′(σ+i(y−t))/(σ+iy)|² dy ≤ 192 sqrt(π) exp(5/4) [1/T + 1/((σ−1)^3 T²)]`

for every real `t`, `1<σ≤2` and `T≥4`. This closes the sharp **full-series frequency/coefficients** sub-obligation. Ordinary parameter assembly and the large-sum-to-small-distance implication are proved below; full hybrid Halász remains a reference target; phase-specialized Lipschitz and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance. DWWZ-05/06 are DONE; the total is **7/20**. This Gaussian majorant is not the continued DWWZ-10 identity with its pole residue. Ninety-three semantic consumers and the module-origin transitive audit cover the implemented scope; the reproduction manifest distinguishes integrated checkpoints from later additions.

`MeanValueMaximum.lean` implements the half-plane Poisson mechanism of GS03 Lemma 2.2 for absolutely convergent logarithmic-frequency series. The kernel `Kα(u)=α/[π(α²+u²)]` has proved positivity, unit mass, Fourier identity and tail integral at most `2α/(πT)`. `poissonLine_zeta` gives the actual zeta reproduction identity with absolute integrability. For `L=log x>0`, the actual source-line maximizer `t₀` and `Z=|ζ(1+1/L+i(t₀−t))|` satisfy

```text
|ζ(1+1/L+α+i(y−t))| ≤ Z + (1+L)4α/(πL),  α>0, |y|≤L/2.
```

The same point is selected before all shifts. No shifted-line maximality is assumed. `zeta_deriv_quotient_mean_square_le` combines the proved near and far integrals with the exact Fourier scaling. `exists_maximizingTwist_weighted_mean_square` then applies Parseval: for `L≥8`, `δ=1/L+α≤1`, `α>0`, and `B=Z+(1+L)4α/(πL)`,

```text
∫ℝ exp(−2(1+δ)u) |Σ_{1≤n≤exp u} log(n)n^(it)|² du
  ≤ B²(log 4+4)²/(2δ)
    + [192 sqrt(π) exp(5/4)/(2π)] [2/L+4/(δ³L²)].
```

This is a full-series weighted mean-square consumer, not by itself GS03 Proposition 1, Halász or Lipschitz. Its actual pointwise/parameter-integration consumer and prime-distance deduction are proved below, preserving the source maximum and prime-distance conventions.

Scoped reuse inspection for this step: Mathlib's `Analysis/Complex/Poisson` concerns the disk; `Probability/Distributions/Cauchy` supplies the real kernel mass/integrability but not its Fourier transform. Installed Fourier inversion and half-line exponential integrals supply the latter. Local node-63 `PointMeanLemmaThreeTail/Edges`, foundation `LargeValuesAffine/Iteration` and the inspected Hughes–Young contour-tail interfaces did not furnish the required half-plane maximum transport. No extension dependency was added.

The Lipschitz difference factor is now retained exactly as well. `poissonLine_frequency_series` proves reproduction with arbitrary real frequencies and absolute integrability; translating the actual frequencies by `b≥0` gives `poissonLine_zeta_difference` for `ζ(σ+iy−it)(1−c exp(−iby))`. For `|c|≤1`, `norm_shifted_zeta_difference_rightward_le` bounds the shifted expression by its original-line local bound plus `(1+1/(σ−1))4α/(πT)`, uniformly in `b,c,t`. With `c=exp(−(σ−1)b)`, `poissonLine_zeta_dilation_difference` keeps the initial damping; it does not replace it by one.

`laplace_zetaSum_dilation` and `laplace_logZetaSum_dilation` prove the actual ordinary and logarithmically weighted dilation transforms, for every real `b,t` and `Re s>1`, including integrability. The ordinary left-hand function is `[S(exp u,t)−exp(b)S(exp(u−b),t)] exp(−su)`; its integral is `[ζ(s−it)/s][1−exp((1−s)b)]`. The weighted version replaces `S` by its actual log-weighted sum and `ζ` by `−ζ′`. This proves the scale/sign bridge behind the Lipschitz factor. The two-point prime/Euler-product input is separately proved below; these identities do **not** supply the final pointwise Lipschitz exponent.

Targeted inspection of the GS03 Lemma 2.1 arithmetic input found that installed PNT+ `StrongPNT.lean` has only a commented final strong-PNT statement, with incomplete intermediate declarations, and `IEANTN/Dusart.theorem_3_3` is incomplete. Neither was imported. The pointwise smoothing input has now been proved by the sieve route below, without requiring those declarations. The inspected node-73 smooth-number `psiNat` results concern a different counting function, not Chebyshev's `ψ`.

`MeanValueEuler.lean` closes the one-point Euler-product/finite-distance sub-obligation. The convergent identity for `log |ζ(s)|` and the nonnegative prime-power deficits give `D(s) ≤ log|ζ(Re s)|−log|ζ(s)|`, with coefficient exactly one. Chebyshev and the existing Abel adapter control the damping loss. For `L=log x≥1`, `C=log 4+4`, every real `t,u`, and the actual finite distance `M_x`,

```text
|ζ(twistZetaPoint x t u)| ≤ (1+L) exp(4C−M_x(t−u)),
Σ_{p≤x} 1/p ≤ log(1+L)+2C.
```

Consequently `norm_normalized_mean_comparison_le_distance` replaces the auxiliary prime-exponential in (2.2) by `exp sqrt(2M_x(t−t₀)[log(1+L)+2C])`, keeping its original prefactor. These are unconditional estimates for the actual phases and assume no PNT. The large-sum-to-small-distance consumer is now proved below. The two-point Euler input is now proved below; difference smoothing is proved below and the final Lipschitz assembly is kernel-checked and passed combined BAT/audit acceptance; the actual weighted-difference mean square is proved below.

Scoped reuse: node-74 `GafniTao/FordEulerProduct.lean` provides a useful short branch-free logarithmic proof. Its entry was adapted directly against installed Mathlib; the unrelated Fourier-kernel import chain and node-74 package were not imported. Dependencies records the inspected source hash. The subsequent prime-power positivity, finite-distance comparison and reciprocal-prime consumers are local proofs.

`MeanValueSmoothing.lean` proves the actual pointwise arithmetic input by a different argument. Installed `BrunTitchmarsh.primesBetween_le`, with sieve level `k`, controls primes in `(k⁴,(k+1)⁴]`; Mathlib's `psi_sub_theta_le` controls higher powers. The resulting bound is `Σ Λ(n) ≤ 2048 k³` for every integer `k≥1`. The actual cutoff sum satisfies `|S(b,t)−S(a,t)|≤b−a+1` for `0≤a≤b`. Averaging within each cell, summing its inverse-square variation error, and choosing the cell by double integer square roots gives an arbitrary-real-cutoff estimate. Exact logarithmic convolution, Abel summation and monotone substitution then prove, for `x>1`, `L=log x`, every real `t`,

```text
|S(x,t)|/x ≤ (2048/L) ∫₀ᴸ exp(−v)|S(exp v,t)| dv + 952321/L.
```

All integrability, floor jumps and higher prime powers are retained. This is a proved absolute-constant replacement for the **auxiliary smoothing input**, not a claim to GS03 Lemma 2.1's coefficient-one form, a source error, or a repair of either frozen main statement. The ordinary damping-parameter assembly is now proved below. The Lipschitz difference-smoothing variant is now proved below, with its cutoff errors retained.

`MeanValueAssembly.lean` consumes those actual objects through logarithmic-weight removal, a bounded damping interval, absolutely integrable Fubini and weighted Cauchy–Schwarz. It retains the minimum of the transported maximum and `1+1/δ`, rather than losing an extra logarithm. Splitting the elementary minimum at `δ=2/(Z+4)` evaluates the parameter integral. For `L=log x≥8`, every real `t`, `exists_maximizingTwist_mean_value_bound` returns one original maximizer `t₀` and, with `Z=|ζ(twistZetaPoint x t t₀)|`, proves

```text
B = (log 4 + 4) + 192 sqrt(pi) exp(5/4)/(2 pi) + 2,
|S(x,t)|/x <=
  [2048 * (1 + log L + 36 B * ((Z+4)*(1+log(2L/(Z+4)))+2)) + 952321] / L.
```

`B` is the positive absolute `meanValueAssemblyConstant`; all maxima, convergence, near/far estimates, prime-power smoothing and cutoff conventions are discharged. There is no residual analytic integral or assumed mean-value bound. This is the **ordinary maximum-form** result, not the hybrid source (2.1). The full-series route avoids a smooth-number adapter for this ordinary estimate; it makes no such claim for the remaining Lipschitz work. Four regressions cover damping reconstruction, actual weighted Cauchy–Schwarz, minimum evaluation and the full actual-maximizer consumer.

The Euler substitution is now consumed by `exists_maximizingTwist_prime_distance_mean_bound`. With the same actual maximizing witness and `M=M_x(t−t₀)`, for `L≥8` it proves

```text
D = 1000000 * (1+B) * exp(4*(log 4+4)+2),
|S(x,t)|/x <= D * ((M+1)*exp(-M) + (1+log L)/L).
```

`exists_large_sum_prime_distance_bound` then proves **the distance clause of Lemma 2.2**: there are absolute `C>0`, `x₀≥3` such that, for every `x≥x₀`, real height `t`, `1≤N≤(log x)^(1/100)` and `|S(x,t)|=x/N`, one actual source maximizer satisfies `M≤(1/100)log log x+log log log x+C`. The proof absorbs the uniform error using the proved threshold and bounds `M+1` by the reciprocal-prime estimate before taking logarithms. The exact coefficient and both height signs are retained. Four further regressions cover the distance-form mean value, crude distance, uniform error threshold and exact source-clause consumer.

This is an alternate ordinary-mean-value deduction of that supporting clause, not a proof of full hybrid (2.1) or a source repair.

`exists_large_sum_twist_bounds` (namespace `DongWangWangZhang2026`, module `TwistBounds`) now consumes the actual distance witness and (2.2). For absolute `C>0,x₀≥3`, every `x≥x₀`, real `t` and `1≤N≤(log x)^(1/100)` with `|S(x,t)|=x/N`, it produces **one** actual source maximizer satisfying all three non-Lipschitz clauses:

- `|t₀|≤4N`;
- `M≤(1/100)log log x+log log log x+C`;
- `|S(x,t−t₀)−(1+it₀)x^(−it₀)S(x,t)|≤4x/(log x)^(3/4)`.

The uniform distance majorant gives forward normalized error `≤L^(-4/5)`; comparison-factor decay gives `1+|t₀|≤4N`. The exact inverse factor then supplies the reversed error with exponent `3/4`. No displacement or error bound is assumed. Two new regressions check the inverse identity and the full same-witness consumer. Uniform Lipschitz and the full same-witness Lemma 2.2 are proved below; DWWZ-05/06 are DONE.

The six-file installed PNT+ sieve closure is listed in Dependencies. Node-73 `SelbergPrimeWeights` was inspected for this new obligation; its prefix-weight bound is less direct than the installed interval-prime theorem, so no node-73 import was selected. This scoped later inspection does not change the recorded initial survey.

### Two-frequency analytic consumer

`TwoPointEuler.lean` consumes the installed, proved `MediumPNT`, not the incomplete strong-PNT/Dusart declarations. `exists_theta_logarithmic_error` gives `|θ(x)−x|≤x/(log x)^A` eventually for each fixed natural `A`. Exact finite-cutoff Abel summation gives reciprocal-prime cosine error at most `(|β|+4)/(log a)^A`. The trigonometric majorant

```text
|cos u| <= 75/113 + (175/452)cos(2u) - (5/113)cos(4u) + (5/452)cos(6u)
```

is proved by a nonnegative polynomial identity. `exists_prime_absolute_cosine_bound` then proves, uniformly for `X(A)≤a≤x`, `1≤|β|log a`, `|β|≤(log a)^A`,

```text
sum_{a<p<=x} |cos(beta log(p)/2)|/p <= (75/113)(log log x-log log a)+8.
```

It feeds the actual source distances, giving `M_x(τ)+M_x(υ)≥(76/113)(log log x−log log a)−24`. `exists_two_point_zeta_bound` consumes the one-point Euler inequalities at `σ=1+1/log x`: the actual product of zeta norms is at most `(1+log x)^2 exp(8(log 4+4)+24−(76/113)(log log x−log log a))`. No prime correlation, Euler estimate or PNT remains an assumed input.

`exists_maximizingTwist_uniform_frequency_bound` applies this at the actual source maximizer. For each `A≥1` it chooses an absolute `B≥1`. If `L=log x≥B`, `|t₀|≤L/2` and `1/L≤|y|≤L/2`, put `H=max(B,1/|y|,L^(1/A))`; then

```text
|zeta(twistZetaPoint x t (t0+y))| <= (1+L) exp(4(log 4+4)+12-(38/113)(log L-log H)).
```

The proof chooses `a=exp H` internally and discharges every PNT scale/frequency restriction. The source maximum, not just a small distance, supplies the square-root improvement. Four regressions fix the actual theta, prime-correlation, zeta-product and same-maximizer contracts. Difference-factor optimization is now proved below; difference smoothing is proved below; parameter integration is evaluated below, while final exponent absorption and all-real cutoff assembly are kernel-checked and passed combined BAT/audit acceptance; the actual weighted-difference mean square is proved below. The margin `75/113<2/3` is sufficient for the intended `1/3` specialization after losses are proved; this is not a claim to the original optimal `2/π` estimate or to either main theorem.

This later quantitative-PNT survey also found the exact stronger node-73 `Tao2026.classicalChebyshevPsiDeLaValleePoussin_native`. It was not selected: the installed `MediumPNT` has a smaller compatible closure and suffices. Dependencies records the exact interfaces, hashes and fourteen-file installed closure; the initial scoped non-reuse survey remains historical, not a blanket negative claim.

`exists_maximizingTwist_dilation_factor_bound` now optimizes the frequency-dependent cutoff against the actual damped factor. With the same maximizing twist, `L≥B(A)`, `|t₀|≤L/2`, every `b≥0` and `|y|≤L/2`, put

```text
M_A(L,b) = 4 exp(4(log 4+4)+12) (1+L) [max(B(A),b,L^(1/A))/L]^(38/113).
```

The actual product `ζ(1+1/L+i(y−(t−t₀)))(1−exp(−b/L−iby))` has norm at most `M_A(L,b)`. Zero frequency, small frequency and arbitrarily large translations are included; the initial damping is not discarded. `exists_maximizingTwist_dilation_rightward_bound` feeds this into the proved Poisson transport. For every `α>0`, `|y|≤L/4`, the corresponding product on `σ=1+1/L+α`, with factor `1−exp(−(1/L+α)b−iby)`, is bounded by `M_A(L,b)+(1+L)16α/(πL)`. Two further regressions retain these exact consumers. The weighted-difference mean-square consumer is now proved below. Floor-sensitive difference smoothing is now proved below; parameter integration is evaluated below. Final uniform `1/3` loss absorption, all-real cutoff assembly and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance.

`DilationMeanSquare.lean` proves integrability, square integrability, Fourier normalization and Parseval for the actual weighted difference `W_b(u)=logS(exp u,τ)−exp(b)logS(exp(u−b),τ)`, with no cutoff replacement. Its transform is `[−ζ′(σ+i(2πξ−τ))/(σ+i2πξ)] [1−exp(−(σ−1)b−i2πbξ)]`. Near-frequency factorization consumes the proved von Mangoldt logarithmic-derivative mean square; the far contribution is bounded by four times the sharp actual derivative tail.

The public `exists_maximizingTwist_weighted_dilation_mean_square` consumes the optimized same-maximizer bound. For `L≥max(16,B(A))`, `|t₀|≤L/2`, `τ=t−t₀`, every `b≥0`, `α>0` and `δ=1/L+α≤1`, put `R=M_A(L,b)+(1+L)16α/(πL)`; then

```text
integral_R exp(-2(1+delta)u) |W_b(u)|^2 du
 <= R^2 (log 4+4)^2/(2 delta)
    + 4/(2 pi) * 192 sqrt(pi) exp(5/4) * [4/L+16/(delta^3 L^2)].
```

There is no residual local-zeta-bound or mean-square premise. Two exact regressions fix Parseval and this actual consumer; the original maximizing condition is retained to use the same witness returned by `TwistBounds`. No package/dependency change is needed beyond the already recorded closure. This closes the weighted-difference mean-square input. Difference smoothing is now proved below; the damping-parameter integral is now evaluated below; Lipschitz and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance; both main theorems remain open.

The proved `exists_maximizingTwist_weighted_dilation_mean_square_min` strengthens the usable majorant by taking `R=min(M_A(L,b)+16,4/δ)` in the same inequality and ranges. Both branches are derived from the actual zeta product. Retaining this cap is needed for uniform parameter integration when the translation grows with the logarithmic scale.

`DilationSmoothing` defines the actual difference `D_w(x)=S(x,τ)−w S(x/w,τ)`, not a surrogate. Its exact Mangoldt convolution, log-weight removal, cell averaging and active-cutoff summation prove, for every real height, `b≥0` and `Y>0`,

```text
exp(−Y)|S(exp Y,τ)−exp(b)S(exp(Y−b),τ)|
 ≤ (2048/Y) ∫[0,Y] exp(−u)|S(exp u,τ)−exp(b)S(exp(u−b),τ)| du
   +(1904642+b)/Y.
```

The second floor error vanishes on cells whose lower endpoint exceeds `x/w`; its summed cost is at most `465x`, independent of `w`. This is an actual-difference smoothing input, not yet the uniform Lipschitz theorem. Four additional exact regressions preserve the capped mean square, original-sum convolution, active floor cost and exponential-cutoff smoothing. The translation-scale split and capped mean-square integration are now proved below, keeping the original source line and maximizer. Scalar loss absorption to the exact `1/3` exponent and all-real cutoff comparison are kernel-checked below. DWWZ-05/06 are DONE; the total is 7/20.

`DilationAssembly` now proves translation-scale log-weight removal, weighted Cauchy–Schwarz, fixed-source-line reconstruction up to `Y≤2L`, and absolutely integrable Fubini. The source line remains `1+1/L` and the same maximizing twist is retained, including for cutoffs above the base scale.

Its public `exists_maximizingTwist_dilation_power_bound` has the same source-maximizer hypotheses as above, with `b≥0`, `b+1≤Y≤2L` and any `0<q<1`. Put `R=M_A(L,b)+16` and let `C=meanValueAssemblyConstant>0`. For the original sum it proves

```text
exp(−Y)|S(exp Y,τ)−exp(b)S(exp(Y−b),τ)|
 ≤ (2048/Y) [2(b+1)+(2+b)log(Y/(b+1))
      +1296 C ((R+4)^q 2^(1−q) L^(1−q)/(1−q)+2)]
   +(1904642+b)/Y.
```

There is no residual analytic integral, assumed local zeta bound, or upper-size premise on `R`. The power-loss evaluation uses `min(a,b)≤a^q b^(1−q)` and a convergent improper power integral; comparison to the already proved ordinary damping majorant reuses its near/far calculation. Four new exact regressions retain translation-scale splitting, doubled-horizon fixed-line reconstruction, uniform-size parameter evaluation and the actual-maximizer end consumer. The scalar and cutoff steps are kernel-checked below, along with full Lemma 2.2. DWWZ-05/06 are DONE after both BATs and the semantic audit passed.

## Full Lemma 2.2 consumer

`DongWangWangZhang2026.exists_large_sum_maximizing_twist` in `DilationLipschitz.lean` is kernel-checked and passed both BATs. It quantifies absolute `C>0` and `x₀≥3` before `x,t,N`, uses the original large-sum premise and `1≤N≤(log x)^(1/100)`, and returns one actual maximizer with all four source clauses:

- `|t₀|≤C N`;
- `M≤(1/100)log log x+log log log x+C`;
- for every real `y`, the original normalized-sum difference is at most `C((1+|y−log x|)/log x)^(1/3)`;
- reversed comparison error at most `C x/(log x)^(3/4)`.

The source line, sign `τ=t−t₀`, floor cutoffs, same witness and uniform constants are preserved. Numerical choices `A=1000`, `q=199/200` leave `(38/113)q(999/1000)>1/3`; all arithmetic and loss absorption are proved, not informal asymptotic substitutions. The near-cutoff proof handles both sides by taking the larger cutoff as `Y`; distant and negative cutoffs use the proved unit bound. Combining with `TwistBounds` derives `|t₀|≤(log x)/2` internally.

This is a faithful specialization/alternate route to the exact Lemma 2.2 conclusions. It does not prove or modify the frozen generic hybrid (2.1) or optimal `1−2/π` estimate. The existing DWWZ-05 acceptance explicitly permits the specialization consumed by Lemma 2.2. Four new regressions freeze the exponent arithmetic, exact normalization, all-real estimate and full same-witness statement. DWWZ-05/06 are DONE after both BATs and semantic acceptance; no source contract or acceptance text is weakened.
