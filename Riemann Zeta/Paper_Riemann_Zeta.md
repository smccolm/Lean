---
title: "Mechanized Formalization of Finite Dirichlet Polynomial Conjugation Dualities, Fourfold Completed Zeta Orbits, and Complex-Valued Hardy-Type Normalization Identities in Lean 4"
author: "S. McColm"
date: "August 3, 2026"
abstract: |
  We present a Lean 4 library (pinned to Lean `v4.30.0` and Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`) of finite positive-index Dirichlet-polynomial conjugation lemmas, elementary products-of-norms identities, and coordinate wrappers for existing Mathlib theorems about the completed Riemann Zeta function. We also define a complex-valued Hardy-type phase normalization on the critical line and prove norm and zero equivalence with the Riemann Zeta function. A two-reflection theorem packages the functional-equation images of two assumed conjugate zeros. The library does not yet prove the interior classical zero-density endpoints, the Guth–Maynard large-values theorem, a one-zero fourfold orbit, real-valuedness of the classical Hardy Z-function, or new zero-free regions. Verification details are tied to the repository release and its continuous integration audit.
---

# 1. Introduction & Contextualization

The distribution of non-trivial zeros of the Riemann Zeta function:

$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s} \quad (\operatorname{Re}(s) > 1)$$

governs prime number asymptotics. In analytic number theory, finite Dirichlet polynomials:

$$A(s) = \sum_{n \in S} a_n n^{-s} \quad (S \subset \mathbb{N}_{\ge 1})$$

serve as essential approximations, mollifiers, and large-value estimators. Recent developments by Larry Guth and James Maynard (2026) established new large-value estimates for Dirichlet polynomials, deriving the zero-density bound $N(\sigma, T) \le T^{\frac{30(1-\sigma)}{13} + o(1)}$ [1].

In this work, we formalize finite Dirichlet polynomial conjugation identities, coordinate wrappers around Mathlib's completed Zeta symmetries, a complex-valued Hardy-type phase normalization, and provisional interfaces for the Guth–Maynard zero-density architecture [2, 3]. The F-01 through F-10 transfer is kernel-checked conditionally from ten explicit primitive inputs. Local zero multiplicity, Montgomery mean value, beta removal, divisor count, ordered-factorization count, the finite classical Montgomery–Halász–Huxley large-values theorem, Appendix C contour coverage, and the Type-II fourth-moment reduction are proved. The false historical decoupling model has been deleted and replaced by source-facing shared-language, matrix/trace, and Fourier/Poisson packages. These now include the exact operator-norm conclusions of Guth–Maynard Lemmas 4.1–4.2, the first-trace expansion, the exact Lemma 4.5 cubic Poisson expansion with its diagonal `Oε(T⁻¹⁰⁰)` remainder, the `S₁/S₂/S₃` partition, and Proposition 5.1 with `S₁ = Oε(T⁻¹⁰)`. The exact-$\sigma$ classical density transfer, twisted fourth moment, and the remaining `S₂/S₃` and energy portion of the Guth–Maynard large-values proof remain open.

## Contribution Taxonomy & Originality Disclosure
The mathematical content of this package is structured into four distinct layers:

1. **Finite Sum Dualities (New Definitions)**: Formalization of positive-index Dirichlet polynomials over $\mathbb{N}_+$ (`dirichletPoly`), conjugate coefficient sequences (`conjCoeff`), and cross-norm evaluation products (`crossNormProduct`).
2. **Coordinate Wrappers (Local Packaging)**: Repackaging Mathlib's `completedRiemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re` into coordinate representations over evaluation points $s(\sigma, t) = \sigma + i t$.
3. **Complex Phase Normalization (New Definitions)**: Formalization of $H(t) = e^{i \theta(t)} \zeta(1/2 + i t)$ as a complex-valued phase normalization ($H : \mathbb{R} \to \mathbb{C}$).
4. **Inherited Analytic Foundations**: The completed Zeta functional equation and boundary non-vanishing are inherited directly from Mathlib 4.

## AI Tool Disclosure & Human Review Statement
All Lean 4 proof developments, manuscript drafts, and verification steps were assisted by AI coding agents (Antigravity/Gemini). S. McColm performed overall mathematical oversight, project specification, design review, and accepts full responsibility for the mathematical content.

---

# 2. Finite Dirichlet Polynomial Conjugation Dualities

Let $S \subset \mathbb{N}_{+}$ be a finite index set of positive naturals ($n \ge 1$), eliminating the $n=0$ branch.

## Definition 1 (Positive-Index Dirichlet Polynomial)
For $s \in \mathbb{C}$, the finite Dirichlet polynomial $A(s)$ is defined by:

$$A(s) = \sum_{n \in S} a_n n^{-s}$$

## Definition 2 (Conjugate Coefficient Sequence)
The conjugate coefficient sequence $a^* : \mathbb{N}_{+} \to \mathbb{C}$ is defined by $a_n^* = \overline{a_n}$.

## Theorem 1 (Conjugation Invariance)
For all $s \in \mathbb{C}$:

$$\overline{A(s)} = A^*(\overline{s})$$

*Proof.* Expanding $\overline{A(s)} = \sum_{n \in S} \overline{a_n} \cdot \overline{n^{-s}}$. For $n \in \mathbb{N}_{+}$, $n > 0$ is real and positive, so $\overline{n^{-s}} = n^{-\overline{s}}$. Thus $\overline{A(s)} = \sum_{n \in S} a_n^* n^{-\overline{s}} = A^*(\overline{s})$. $\quad \square$

## Definition 3 (Cross-Norm Product)
For evaluation parameters $\sigma_1, \sigma_2, t \in \mathbb{R}$, the cross-norm product $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t)$ is defined by:

$$\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1 + i t)\| \cdot \|A^*(\sigma_2 - i t)\|$$

## Theorem 2 (Factor Swap Invariance)
For all $\sigma_1, \sigma_2, t \in \mathbb{R}$:

$$\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \text{crossNormProduct}(a^*, S, \sigma_2, \sigma_1, -t)$$

## Theorem 3 (Evaluation Product Real-Part Upper Bound)
For all $\sigma_1, \sigma_2, t \in \mathbb{R}$:

$$\left|\operatorname{Re}\left( A(\sigma_1 + i t) \cdot A^*(\sigma_2 - i t) \right)\right| \le \text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t)$$

## Theorem 4 (Cross-Norm Product Zero Characterization)
For all $\sigma_1, \sigma_2, t \in \mathbb{R}$:

$$\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = 0 \iff A(\sigma_1 + i t) = 0 \lor A^*(\sigma_2 - i t) = 0$$

---

# 3. Completed Zeta Reflection & Fourfold Zero Orbit

Away from $s = 0$ and $s = 1$, Mathlib's completed Riemann Zeta function agrees with the classical expression $\Lambda(s) = \pi^{-s/2} \Gamma(s/2) \zeta(s)$. At $s = 0$ and $s = 1$, Mathlib assigns totalized values.

## Theorem 5 (Functional Equation Reflection)
For all $\sigma, t \in \mathbb{R}$, $\Lambda(\sigma + i t) = \Lambda((1 - \sigma) - i t)$.

## Theorem 6 (Fourfold Zero Orbit / Two-Reflection Pair Theorem)
If completed Riemann Zeta vanishes at both $\sigma + i t$ and $\sigma - i t$, then by functional equation reflection it vanishes at all four symmetry points:

1. $\sigma + i t \quad (\text{assumed zero } h_1)$
2. $(1 - \sigma) - i t \quad (\text{via functional equation reflection of } h_1)$
3. $(1 - \sigma) + i t \quad (\text{via functional equation reflection of } h_2)$
4. $\sigma - i t \quad (\text{assumed zero } h_2)$

*Point Collision Note*: On symmetry loci ($t = 0$ or $\sigma = 1/2$), these four evaluation points may coincide.

---

# 4. Complex-Valued Hardy-Type Phase Normalization

## Definition 4 (Riemann-Siegel Theta Function)
For $t \in \mathbb{R}$, the Riemann-Siegel theta function $\theta(t)$ is defined using Mathlib's principal branch:

$$\theta(t) = \operatorname{im}\left( \log \Gamma\left( \frac{1}{4} + i \frac{t}{2} \right) \right) - \frac{t}{2} \log \pi$$

## Definition 5 (Complex Hardy-Type Normalization)
For $t \in \mathbb{R}$, the complex-valued Hardy-type normalization $H(t)$ is defined by:

$$H(t) = e^{i \theta(t)} \zeta\left( \frac{1}{2} + i t \right)$$

*Real-Valuedness Disclaimer*: The present library defines $H : \mathbb{R} \to \mathbb{C}$ as a complex-valued phase normalization. It does not establish that $H(t)$ is real-valued for real $t$ or identify it fully with the classical real Hardy Z-function.

## Theorem 7 (Norm Equivalence)
For all $t \in \mathbb{R}$, $|H(t)| = |\zeta(1/2 + i t)|$.

## Theorem 8 (Zero Equivalence)
For all $t \in \mathbb{R}$, $H(t) = 0 \iff \zeta(1/2 + i t) = 0$.

## Theorem 9 (Conditional Hardy Norm Parameter Symmetry)
For all $t \in \mathbb{R}$, provided $\|\zeta(1/2 - i t)\| = \|\zeta(1/2 + i t)\|$ ($h_{\text{symm}}$), we have:

$$\|H(-t)\| = \|H(t)\|$$

---

# 5. Boundary Non-Vanishing & Pole Disclosures

## Theorem 10 (Classical Boundary Non-Vanishing for $t \neq 0$)
For all $t \in \mathbb{R}$ with $t \neq 0$:

$$\zeta(1 + i t) \neq 0$$

*Pole Disclosure Note*: At $t = 0$, $s = 1$, where $\zeta(s)$ possesses a simple pole. Mathlib totalizes $\zeta(1) \neq 0$ as a junk value. Restricting $t \neq 0$ guarantees true classical nonvanishing on $\operatorname{Re}(s) = 1$.

---

# 6. Guth-Maynard Target Infrastructure & Formal Statements

The primary long-term objective of this project is the zero-density bound of Guth and Maynard (2026). The conclusion-equivalent transfer axiom has been deleted. Its replacement `conditionalZeroDensityTransfer` is a kernel-checked primitive-input theorem: it derives separated extraction, powered-coefficient control, the complete central Type-I estimate, the residual Type-II estimate, the positive-slab partition, the F-01 dyadic-to-global reduction, and Huxley's high-$\sigma$ branch from individually named analytic/arithmetic inputs. Five of those inputs are now discharged: `localZeroMultiplicityBound_native` proves the Jensen local-zero estimate, `montgomery_mean_value_native` proves the base-interval Montgomery estimate, `beta_dependence_removal` proves the pointwise fixed-line detector shift, and `divisorCountBound_native` plus `factorizationCountBound_native` prove the two arithmetic estimates.

The detector layer implements the exact truncated Möbius divisor sum. In addition to the cutoff support and magnitude results, `detectorDivisors_subset_divisors`, `norm_mobius_sum_le_divisors_card`, and `norm_detectorCoeff_le_divisors_card` bound the construction by the full divisor count independently of `T`. `uniformDetectorCoeffBound_of_divisorCount` then proves the source-uniform `UniformDetectorCoeffBoundProp` from the explicit classical epsilon-power divisor estimate `DivisorCountBoundProp`, which is now proved by `divisorCountBound_native`.

For polynomial powers, `FactorizationCountBoundProp` places its constant before the target integer `m`, and `PowCoeffBoundProp` places its constant before `N`, `m`, and `T`. The kernel-checked theorem `powCoeff_bound_of_uniform_detector_and_factorization` combines a `T`-uniform detector input with the uniform factorization-count input. `factorizationCountBound_native` bounds ordered factorizations by a power of the divisor count and invokes `divisorCountBound_native` at a divided epsilon; `powCoeffBound_native` then specializes the powered-coefficient result with no arithmetic premise. Independently of those estimates, `polynomial_power_identity` expands `powPoly` exactly as the finite sum of `powCoeff N k m T · m^{-s}` for `N^k ≤ m ≤ (2N)^k`. Its proof expands the finite power over `Fin k` tuples, proves the product support, uses natural-cast complex-power multiplicativity, and regroups by product fibers; it includes `k = 0`.

For Type II zeros, `FiniteTypeICoverProp` now matches the asymptotic setting: it requires coverage only eventually in the height parameter and only in the source range `7/10 ≤ σ ≤ 4/5`. The theorem `finiteTypeICover_of_typeIContourTypeII` derives this finite-family coverage for `zerosInRect σ 1 T (2T)` from the source-facing `TypeIContourTypeIICoverProp`. The exact identity `weightedResidualCount_dyadicZetaZeros_eq` connects the generic real-valued weighted sum to `residualZeroCount` with analytic multiplicity. Consequently `residualZeroBound_of_contourTypeII_reduction_and_fourthMoment` proves the concrete `ResidualZeroBoundProp` from the coverage, Appendix C reduction, and twisted fourth-moment inputs. `typeIContourTypeIICoverOn_native` and `typeIIFourthMomentReduction_native` discharge the first two inputs; only the twisted fourth moment remains unproved.

For Type I extraction, `LocalZeroMultiplicityBoundProp` states an ordinary multiplicity-weighted `O(log T)` bound in unshifted unit-height intervals. `typeI_unit_bin_sum_le_jensen` proves the pointwise bin estimate on pole-safe concentric discs and bridges Jensen divisors to `analyticVanishingOrder`; `localZeroMultiplicityBound_native` discharges the proposition. `BetaDependence.lean` applies a rational localizer and Mathlib's right-half-plane Phragmén–Lindelöf theorem to prove `beta_dependence_removal : DetectorBetaShiftProp` with the exact $T^\delta$ displacement and $1/(4\log T)$ threshold. This is an alternative complex-analytic realization of the source's smooth Fourier-localization step. The theorem `extractSeparated_native` combines both inputs with shifted covering, translation into `[0,3T]`, phase preservation, and epsilon-loss absorption, so the extraction chain is unconditional.

The mean-value layer is also unconditional. `MeanValueProof.lean` establishes exact continuous Dirichlet-polynomial mean square, a finite reciprocal-log Hilbert inequality, and a local Sobolev sample bound; together these prove `montgomery_mean_value_native`. The wrapper `halasz_montgomery_lemma_native` specializes the finite large-value count without an analytic premise.

`ClassicalDensity.lean` supplies the initial classical-density layer: exact finite Möbius mollifier convolution and cancellation, a globally analytic pole-free Ingham detector, zeta-zero multiplicity inheritance, a detector-to-Jensen divisor bridge, full unit-bin control down to $\sigma=1/2$, dyadic $O(T\log T)$ and symmetric exponent-one bounds, Ingham at $\sigma=1/2,1$, and Huxley at $\sigma=1$. `ClassicalMoments.lean` now proves the exact continuous mean-square estimate on the full coefficient interval $1\le n\le X$ and specializes it to the actual Möbius mollifier:
$$
\int_0^T\left|M_X\left(\frac12+it\right)\right|^2dt
\le \left(T+2(2\pi+1)X\right)(1+\log X).
$$
This has the `(T+O(X)) log X` strength of the critical-line mollifier input used in the source argument. Shitlist #15 nevertheless remains open because the exact-$\sigma$ density transfer and concrete endpoint assembly remain unproved.

The rectangle argument-principle core is now kernel-checked. The project ports the PNT+ rectangle geometry, finite divisor-support, and residue calculus to Lean 4.30, then proves that the normalized contour integral of `logDeriv f` equals the finite sum of meromorphic orders in the rectangle. `ClassicalArgumentPrinciple.lean` specializes this result to the globally analytic pole-free Ingham detector while retaining finite-order and boundary-nonvanishing hypotheses explicitly. It also derives the concrete classical-strip growth bound `‖ζ(s)‖ ≤ 20 |Im(s)|` for `1/2 ≤ Re(s) < 3` and `|Im(s)| ≥ 1`. Weighted Littlewood, boundary perturbation, Gabriel interpolation, the standalone zeta fourth moment, and the remaining edge estimates are unfinished optional extensions; they are not on the selected #15 critical path.

The selected remaining interior engine is a finite zero-density-from-large-values route. The sharp approximation, dichotomy, exact powering infrastructure, coefficient growth, MHH/Weyl estimates, endpoint arithmetic, and terminal restriction are proved. The new Type-I modules prove the exact source-faithful smooth partition and common-scale extraction, literal smooth Poisson summation, the corrected stationary point and dual window at scale `T/N`, and Fourier deweighting of both the short and reflected amplitudes to coefficient-one shifted polynomials. The remaining medium theorem is the uniform stationary leading term with a summed remainder smaller than the detector witness. The earlier `100\sqrt t` estimate is valid but cannot replace it: at `σ=3/4`, `N=T^(2/3)`, its weighted size is of order one. The source/Lean correspondence and normalization correction are recorded in `Type I Reflection Proof Bijection.md`.
$$R\ll_\varepsilon T^\varepsilon\left(N^2V^{-2}+T\min(NV^{-2},N^4V^{-6})\right).$$
The theorem `classical_montgomery_halasz_huxley_native` proves this estimate for bounded coefficients on a dyadic interval and a finite one-separated set in $[0,T]$, with an explicit positive constant and the exact minimum of the second- and sixth-power branches. The final transfer must now derive Ingham's exponent $3(1-\sigma)/(2-\sigma)$ and Huxley's exponent $3(1-\sigma)/(3\sigma-1)$ over their full intervals and specialize the positive-ordinate-to-symmetric bridge. At $\sigma=3/4$ the two exponents both equal $3/5$, so the Huxley boundary follows from Ingham and is not a separate analytic obstruction. Neither fully quantified endpoint proposition is currently a Lean theorem for the project's symmetric multiplicity-weighted `N`.

The selected #18 route follows Maynard–Pratt Appendix C [5]. Uniform arbitrary-order Gamma decay, honest contour integrability, and the native coverage theorem are proved. The coverage proof establishes Mellin inversion for the exponentially smoothed Möbius detector, removes the apparent singularity at $s=0$, shifts the rectangle, computes the sole residue at $s=1-\rho$, controls all tails quantitatively, and assembles the exact dyadic Type-I/contour-Type-II dichotomy. The native fourth-moment reduction constructs multiplicity-preserving ordinate fibers and representative zeros, performs Jensen-controlled growing-scale extraction, proves the exact contour-to-critical-line Gamma convolution and weighted fourth-power Hölder inequalities, absorbs the Gamma tail quantitatively, converts the translated windows by bounded overlap to $[T/2,3T]$, and assembles the final epsilon loss. The identity $|M\zeta|^4=|\zeta|^4|M^2|^2$ puts the squared mollifier at length $T^{1/50}$, within the $T^{1/11-\varepsilon}$ range of Hughes–Young [6]. Formalizing the required upper-bound corollary still requires an approximate functional equation for $\zeta^2$, diagonal evaluation, and quadratic-divisor/off-diagonal control.

For #19, the false interval-free incidence and off-by-one block contracts have been deleted. The source-faithful Guth–Maynard route [1] now has its affine/approximate-energy language, exact sampling-matrix trace-dispersion reduction through Lemmas 4.1–4.2, the complete first-trace Poisson expansion, arbitrary-order uniform two-parameter Fourier decay, the exact cubic expansion and frequency partition of Lemma 4.5/equation (5.5), Proposition 5.1 for $S_1$, and a kernel-checked Section 6 smooth-reflection module. `gmCubicZeroMode_main_term` identifies the diagonal cubic zero mode with an $O_\varepsilon(T^{-100})$ remainder, while `gmCubicS1_estimate` proves $S_1=O_\varepsilon(T^{-10})$ under the source $T^\varepsilon$ separation. The remaining chain is the $S_2$ and $S_3$ estimates, the Heath–Brown difference-set mean-square estimate, Proposition 9.1, and the final GCD/spacing assembly. Mathlib's exact additive energy is connected to the tolerance-one real energy through the proved seven-bin floor bridge.

## Theorem 11 (Large Values Estimate Target Statement)
**Status**: Unproved (Target Specification).
For any $\varepsilon > 0$, there exists a constant $C$ such that for a sequence $b_n \in \mathbb{C}$ with $\|b_n\| \le 1$, and a $1$-separated set $W \subset [0, T]$ satisfying $\|D_N(t)\| \ge V$ for all $t \in W$, the cardinality is bounded by:
$$ |W| \le C T^\varepsilon \left( N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4} \right) $$

## Theorem 12 (Zero Density Deduction Target Statement)
**Status**: Conditionally proved from ten explicit primitive analytic/arithmetic inputs by `conditionalZeroDensityTransfer`.
For the concrete multiplicity-weighted zeta-zero count $N(\sigma, T)$ and $7/10 \le \sigma \le 1$:
$$ N(\sigma, T) = O_\varepsilon\left(T^{\frac{15(1-\sigma)}{3+5\sigma} + \varepsilon}\right) $$

## Corollary 1 (Combined Zero Density Exponent)
**Status**: Unproved (Target Specification).
Combining with assumed Ingham bounds for $\sigma \le 7/10$, for $\sigma \ge 1/2$:
$$ N(\sigma, T) = O_\varepsilon\left(T^{\frac{30(1-\sigma)}{13} + \varepsilon}\right) $$

---

# 7. Audited Declarations & Mathlib Dependencies

`RiemannZeta/Audit.lean` explicitly lists all 1112 exported source-level theorems across the production modules and computes their transitive axioms with `Lean.collectAxioms`. The explicit list matches the discovered theorem set and every existing declaration passes with only `propext`, `Classical.choice`, and `Quot.sound`. A separate named-output gate rejects the seven absent #15/#18/#19 end theorems, so the executable audit remains nonzero until the research agenda is complete. No direct project axiom remains.

Every intended production module is imported through the default `RiemannZeta` library root. The runner also builds `DyadicTransfer`, `CentralTypeI`, `HalaszMontgomery`, `ClassicalArgumentPrinciple`, the large-values definition/matrix/trace modules, and `LargeValues` explicitly as a redundant coverage check.

| Theorem Name | Lean 4 Declaration | Submodule File | Mathlib Basis / Dependency |
| :--- | :--- | :--- | :--- |
| Conjugation | `dirichletPoly_conj` | `FiniteDirichletPolynomial.lean` | `cpow_conj`, `map_sum` |
| Norm Conjugation | `dirichletPoly_norm_conj` | `FiniteDirichletPolynomial.lean` | `norm_star` |
| Norm-Square Line | `dirichletNormSquare_conj_line` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_norm_conj` |
| Threshold Iff | `threshold_conj_line_iff` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_norm_conj` |
| Zero Conjugation | `dirichletPoly_zero_conj` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_conj`, `star_zero` |
| Zero Conj Iff | `dirichletPoly_zero_conj_iff` | `FiniteDirichletPolynomial.lean` | `star_eq_zero` |
| Nonnegative | `crossNormProduct_nonneg` | `CrossNormProduct.lean` | `mul_nonneg`, `norm_nonneg` |
| Involution | `conjCoeff_conjCoeff` | `CrossNormProduct.lean` | `star_star` |
| Factor Swap | `crossNormProduct_swap` | `CrossNormProduct.lean` | `mul_comm` |
| Real-Part Bound | `realPart_abs_le_crossNormProduct` | `CrossNormProduct.lean` | `abs_re_le_norm`, `norm_mul` |
| Zero Left | `crossNormProduct_eq_zero_of_left` | `CrossNormProduct.lean` | `norm_zero`, `zero_mul` |
| Zero Right | `crossNormProduct_eq_zero_of_right` | `CrossNormProduct.lean` | `norm_zero`, `mul_zero` |
| Zero Iff | `crossNormProduct_eq_zero_iff` | `CrossNormProduct.lean` | `mul_eq_zero`, `norm_eq_zero` |
| Reflection | `completedRiemannZeta_reflection` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_one_sub` |
| Zero Reflection | `completedRiemannZeta_zero_reflection_iff` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_one_sub` |
| 4-Fold Orbit | `completedRiemannZeta_fourfold_zero_orbit` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_reflection` |
| Hardy Norm Eq | `hardyZ_norm_eq_riemannZeta_norm` | `HardyZ.lean` | `norm_mul`, `norm_exp` |
| Hardy Zero Iff | `hardyZ_zero_iff_riemannZeta_zero` | `HardyZ.lean` | `exp_ne_zero`, `mul_eq_zero` |
| Hardy Neg Norm | `hardyZ_neg_norm` | `HardyZ.lean` | `hardyZ_norm_eq_riemannZeta_norm`, `h_symm` |
| 1-Line Nonvanishing | `riemannZeta_ne_zero_on_one_line` | `Nonvanishing.lean` | `riemannZeta_ne_zero_of_one_le_re` |
| Totalized Nonvanishing | `riemannZeta_ne_zero_totalized` | `Nonvanishing.lean` | `riemannZeta_ne_zero_of_one_le_re` |
| Epsilon-Power Asymptotics | `EpsilonPowerBound` | `GuthMaynard/Asymptotics.lean` | `IsBigO` |
| Epsilon-Power Refl | `EpsilonPowerBound.refl` | `GuthMaynard/Asymptotics.lean` | `IsBigO.of_bound` |
| Epsilon-Power Trans | `EpsilonPowerBound.trans` | `GuthMaynard/Asymptotics.lean` | `IsBigO.mul` |
| Detector Support | `detectorDivisors_subset_range` | `GuthMaynard/ZeroDetector.lean` | `Nat.mem_divisors`, `Nat.lt_floor_add_one` |
| Detector Cutoff Bound | `norm_detectorCoeff_le_cutoff` | `GuthMaynard/ZeroDetector.lean` | `abs_moebius_le_one`, `norm_sum_le`, `exp_smoothing_bound` |
| Detector Epsilon Bound | `detectorCoeff_bound` | `GuthMaynard/ZeroDetector.lean` | `norm_detectorCoeff_le_cutoff`, `Real.one_le_rpow` |
| Detector Divisor-Card Bound | `norm_detectorCoeff_le_divisors_card` | `GuthMaynard/ZeroDetector.lean` | Full-divisor support, `abs_moebius_le_one`, exponential smoothing |
| Conditional Uniform Detector Bound | `uniformDetectorCoeffBound_of_divisorCount` | `GuthMaynard/ZeroDetector.lean` | Explicit `DivisorCountBoundProp` input |
| Compact Zeta-Zero Finiteness | `riemannZeta_finite_zeros_in_rect` | `GuthMaynard/ZeroCount.lean` | `IsCompact.inter_riemannZetaZeros_finite` |
| Weighted Separated Selection | `weighted_separated_selection` | `GuthMaynard/Separated.lean` | Finite even/odd unit-bin decomposition |
| Polynomial Phase Translation | `dirichletPoly_translate`, `norm_phaseShiftCoeffs` | `GuthMaynard/DirichletPolynomial.lean` | Finite sums, complex powers, positive dyadic indices |
| Shifted-Bin Covering | `shifted_bin_weight_le_of_unit_bin_weight` | `GuthMaynard/ExtractSeparated.lean` | Integer floors, finite interval cardinality, weighted fiber decomposition |
| Raw Conditional Type-I Extraction | `rawExtractSeparated_of_beta_shift_and_local_multiplicity` | `GuthMaynard/ExtractSeparated.lean` | Explicit beta-shift/unit-zero inputs, weighted pigeonholing, covering, and selection |
| Normalized Conditional Type-I Extraction | `extractSeparated_of_beta_shift_and_local_multiplicity` | `GuthMaynard/ExtractSeparated.lean` | Raw extraction, exact phase translation, `[0,3T]` interval control, and epsilon-loss absorption |
| Native Beta Removal | `beta_dependence_removal` | `GuthMaynard/BetaDependence.lean` | Rational localizer, detector coefficient-mass bounds, boundary decay, and right-half-plane Phragmén–Lindelöf |
| Unconditional Type-I Extraction | `extractSeparated_native` | `GuthMaynard/BetaDependence.lean` | Native beta removal, native Jensen multiplicity, and the normalized extraction theorem |
| Conditional Powered-Coefficient Bound | `powCoeff_bound_of_uniform_detector_and_factorization` | `GuthMaynard/PolynomialPowers.lean` | Explicit detector/factorization inputs, `norm_sum_le`, `Real.finset_prod_rpow` |
| Divisor-to-Powered-Coefficient Bound | `powCoeff_bound_of_divisor_and_factorization` | `GuthMaynard/PolynomialPowers.lean` | Explicit divisor-count/factorization inputs and the uniform-detector deduction |
| Polynomial-Power Coefficient Expansion | `polynomial_power_identity` | `GuthMaynard/PolynomialPowers.lean` | `Finset.sum_pow'`, product support, complex powers of natural products, finite fiber regrouping |
| Montgomery Mean Value | `montgomery_mean_value_native` | `GuthMaynard/MeanValueProof.lean` | Continuous mean-square identity, reciprocal-log Hilbert inequality, Sobolev sampling |
| Native Large-Value Count | `halasz_montgomery_lemma_native` | `GuthMaynard/HalaszMontgomery.lean` | Proved Montgomery mean value and finite-sum inequalities |
| Classical MHH Large Values | `classical_montgomery_halasz_huxley_native` | `GuthMaynard/ClassicalLargeValues.lean` | Logarithmic-kernel bounds, Gram duality, separated harmonic shells, absorption, subdivision, and energy inequalities |
| Initial-Interval Mean Square | `integral_norm_sq_dirichletTimeUpTo_le` | `GuthMaynard/ClassicalMoments.lean` | Exact continuous expansion, reciprocal-log Hilbert inequality, kernel comparison |
| Critical-Line Mollifier Moment | `integral_norm_sq_zetaMollifier_criticalLine_le` | `GuthMaynard/ClassicalMoments.lean` | Initial-interval mean square, exact critical-line phase identity, Möbius bound, harmonic-number estimate |
| Zeta Truncation | `riemannZeta_truncation` | `GuthMaynard/ZetaTruncation.lean` | Project Abel continuation, Mathlib finite Abel summation, complex-power interval integral |
| Truncation at a Zeta Zero | `zeta_zero_truncation`, `norm_zeta_zero_truncation_error_le` | `GuthMaynard/ZetaTruncation.lean` | Exact truncation identity and the proved variable-tail norm bound |
| Huxley Left Boundary from Ingham | `huxley_zero_density_at_three_quarters_of_ingham` | `GuthMaynard/InghamBound.lean` | Arithmetic normalization of both exponents to `3/5` |
| Powered Block Preparation | `exists_dyadic_block_and_subset` | `GuthMaynard/PolynomialPowers.lean` | Kernel-checked lower-endpoint removal, normalized translated blocks, and simultaneous fixed-block selection |
| Primitive-Input Conditional Transfer | `conditionalZeroDensityTransfer` | `GuthMaynard/Transfer.lean` | Audit-clean full deduction from ten named analytic/arithmetic inputs |
| Contour Type II Condition | `IsContourTypeIIZero` | `GuthMaynard/TypeIIZeros.lean` | Short Möbius polynomial, Gamma factor, and `riemannZeta` contour integral |
| Type II Analytic Inputs | `typeIContourTypeIICoverOn_native`, `typeIIFourthMomentReduction_native`, `TwistedZetaFourthMomentProp` | `GuthMaynard/TypeIICoverage.lean`, `TypeIIFourthMomentReduction.lean`, `TypeIIZeros.lean` | Native coverage and reduction; explicit remaining twisted-moment specification |
| Conditional Residual-Zero Bound | `residual_zero_bound_of_cover_reduction_and_fourth_moment` | `GuthMaynard/TypeIIZeros.lean` | Audit-clean deduction from the three explicit Type II inputs over generic finite weighted data |
| Concrete Conditional Residual-Zero Bound | `residualZeroBound_of_contourTypeII_reduction_and_fourthMoment` | `GuthMaynard/TypeIIZeros.lean` | Eventual contour coverage bridge, exact weighted/concrete count identity, Appendix C reduction and fourth-moment inputs |
| Separated Sets | `IsSeparated` | `GuthMaynard/Separated.lean` | `Metric.dist` |
| Target Interval | `InTargetInterval` | `GuthMaynard/Separated.lean` | `Set.Icc` |
| Base Interval | `InBaseInterval` | `GuthMaynard/Separated.lean` | `Set.Icc` |
| Set Translation | `translateSet` | `GuthMaynard/Separated.lean` | `Finset.image` |
| Separated Translation | `isSeparated_translate` | `GuthMaynard/Separated.lean` | `dist_sub_sub` |
| Interval Translation | `inBaseInterval_translate` | `GuthMaynard/Separated.lean` | `Set.mem_Icc` |
| Large Values Estimate | `GuthMaynardLargeValues` | `GuthMaynard/Statements.lean` | Target Specification |
| Zero-Density Deduction | `GuthMaynardZeroDensity` | `GuthMaynard/Statements.lean` | Target Specification |
| Combined Exponent | `CombinedZeroDensity` | `GuthMaynard/Statements.lean` | Target Specification |

---

# 8. Reproducibility & Verification Metadata

The formalization relies on the following exact environment:
- **Lean Toolchain**: `leanprover/lean4:v4.30.0`
- **Mathlib Revision**: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- **Package Version**: `0.1.0`
- **Principal Verification Command**: `run_lake_build.bat`
- **Noninteractive Verification Command**: `run_lake_build.bat --no-pause`
- **Principal Runner Coverage**: five warning-failing stages covering the default production graph, explicit production-module redundancy, both retained examples, and the transitive axiom audit
- **Focused Axiom/Output Audit Command**: `lake env lean RiemannZeta/Audit.lean` (1112/1112 existing dependency checks pass; the command exits nonzero on seven missing research outputs)

---

# 9. Conclusion & Future Work

We have constructed a machine-checked Lean 4 library of finite Dirichlet polynomial conjugation identities, coordinate packaging for Mathlib's completed Zeta functional equation, and a complex-valued Hardy-type phase normalization.

**Future Technical Extensions**:
1. Formalizing continuous branch choices for $\theta(t)$ to prove that $H(t)$ is real-valued.
2. Completing #15's Type-I smoothing, stationary `T/N` B-process and reflected deweighting, actual-`X` Type-II powered MHH application, branch-to-slab reduction, and concrete Ingham/Huxley endpoints.
3. Proving the Hughes–Young-range twisted fourth moment required by #18; the Maynard–Pratt Type-I/Type-II cover and contour-to-twisted-fourth-moment reduction are complete.
4. Completing the source Guth–Maynard proof after the proved matrix/dispersion, first- and cubic-trace Poisson, `S₁`, uniform Fourier-decay, and smooth-reflection layers: the remaining `S₂/S₃`, Heath–Brown, affine transformation, energy, and final integration.

---

# 10. References

1. Larry Guth and James Maynard, *"New large value estimates for Dirichlet polynomials,"* **Annals of Mathematics**, vol. 203, no. 2, pp. 623-675, 2026. DOI: 10.4007/annals.2026.203.2.6.
2. David Loeffler and Michael Stoll, *"Formalizing zeta and L-functions in Lean,"* **Annals of Formalized Mathematics**, vol. 1, 2025. DOI: 10.46298/afm.15328. arXiv:2503.00959.
3. The Lean Community, *"Mathlib 4: The Lean 4 Mathematical Library,"* 2026. Pinned commit `c5ea00351c28`. https://leanprover-community.github.io/mathlib4_docs/
4. A. E. Ingham, *"On the Estimation of N(σ, T),"* **The Quarterly Journal of Mathematics**, os-11(1), pp. 201-202, 1940. DOI: 10.1093/qmath/os-11.1.201.
5. James Maynard and Kyle Pratt, *"Half-isolated zeros and zero-density estimates,"* arXiv:2206.11729, 2022. https://arxiv.org/abs/2206.11729
6. C. P. Hughes and Matthew P. Young, *"The twisted fourth moment of the Riemann zeta function,"* **Journal für die reine und angewandte Mathematik**, vol. 641, pp. 203-236, 2010. DOI: 10.1515/CRELLE.2010.034; arXiv:0709.2345.
