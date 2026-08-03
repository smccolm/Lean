---
title: "Mechanized Formalization of Finite Dirichlet Polynomial Conjugation Dualities, Fourfold Completed Zeta Orbits, and Hardy Z-Function Identities in Lean 4"
author: "Scott McColm (with AI Proof Assistance)"
date: "August 2, 2026"
abstract: |
  We present a Lean 4 library (toolchain `v4.30.0-rc2`, version `0.1.0`) of finite positive-index Dirichlet-polynomial conjugation identities and coordinate corollaries of Mathlib's completed Riemann Zeta symmetries. The library defines finite Dirichlet polynomials over $\mathbb{N}+$, proves conjugation and norm invariance, packages a product-of-norms API with elementary factor-swap and zero-factor lemmas, and derives the four standard symmetry evaluations associated with a zero of the completed Zeta function. We also define a complex-valued Hardy-type normalization on the critical line and prove that it has the same norm and zeros as the Riemann Zeta function there. These results do not formalize zero-density estimates, do not rule out off-line zeros, and do not establish that the Hardy-type normalization is real-valued. Verification details are tied to local commit `d6c7c51` and its continuous integration audit.
---

# 1. Introduction & Contextualization

The distribution of non-trivial zeros of the Riemann Zeta function:

$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s} \quad (\operatorname{Re}(s) > 1)$$

governs prime number asymptotics. In analytic number theory, finite Dirichlet polynomials:

$$A(s) = \sum_{n \in S} a_n n^{-s} \quad (S \subset \mathbb{N}_{\ge 1})$$

serve as essential approximations, mollifiers, and large-value estimators. Recent developments by Larry Guth and James Maynard (2026) established new large-value estimates for Dirichlet polynomials, deriving the zero-density bound $N(\sigma, T) \le T^{\frac{30(1-\sigma)}{13} + o(1)}$ [1].

In this work, we do not formalize the analytic measure bounds or zero-density counting theorems of Guth-Maynard. Instead, we establish a clean, machine-checked foundational library in **Lean 4** covering finite Dirichlet polynomial conjugation identities, coordinate symmetries of the completed Zeta function, and the classical Hardy Z-function [2, 3].

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

*Proof.* Follows from double conjugation $(a^*)^* = a$ and real multiplication commutativity $x \cdot y = y \cdot x$. $\quad \square$

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

## Theorem 6 (Full Fourfold Zero Orbit)
If $\Lambda(\sigma + i t) = 0$ and $\Lambda(\sigma - i t) = 0$, then $\Lambda(s)$ vanishes at all four symmetry points:

1. $\sigma + i t$
2. $(1 - \sigma) - i t \quad (\text{via Mathlib functional equation})$
3. $(1 - \sigma) + i t \quad (\text{via functional equation reflection})$
4. $\sigma - i t \quad (\text{via parameter negation})$

*Point Collision Note*: On symmetry loci ($t = 0$ or $\sigma = 1/2$), these four evaluation points may coincide.

---

# 4. Classical Hardy Z-Function Properties

## Definition 4 (Riemann-Siegel Theta Function)
For $t \in \mathbb{R}$, the Riemann-Siegel theta function $\theta(t)$ is defined using Mathlib's principal branch:

$$\theta(t) = \operatorname{im}\left( \log \Gamma\left( \frac{1}{4} + i \frac{t}{2} \right) \right) - \frac{t}{2} \log \pi$$

## Definition 5 (Complex Hardy-Type Normalization)
For $t \in \mathbb{R}$, the complex-valued Hardy-type normalization $H(t)$ is defined by:

$$H(t) = e^{i \theta(t)} \zeta\left( \frac{1}{2} + i t \right)$$

## Theorem 7 (Norm Equivalence)
For all $t \in \mathbb{R}$, $|H(t)| = |\zeta(1/2 + i t)|$.

## Theorem 8 (Zero Equivalence)
For all $t \in \mathbb{R}$, $H(t) = 0 \iff \zeta(1/2 + i t) = 0$.

## Theorem 9 (Hardy Norm Parameter Negation Symmetry)
For all $t \in \mathbb{R}$, $|H(-t)| = |H(t)|$ under critical line norm symmetry.

---

# 5. Boundary Non-Vanishing & Pole Disclosures

## Theorem 10 (Classical Boundary Non-Vanishing for $t \neq 0$)
For all $t \in \mathbb{R}$ with $t \neq 0$:

$$\zeta(1 + i t) \neq 0$$

*Pole Disclosure Note*: At $t = 0$, $s = 1$, where $\zeta(s)$ possesses a simple pole. Mathlib totalizes $\zeta(1) \neq 0$ as a junk value. Restricting $t \neq 0$ guarantees true classical nonvanishing on $\operatorname{Re}(s) = 1$.

---

# 6. Complete Formalization Mapping & Mathlib Dependencies

All 21 canonical declarations across 5 mathematical submodules in package `RiemannZeta` (pinned to Lean `v4.30.0-rc2`) have been verified with **0 errors, 0 warnings, and 0 `sorryAx` dependencies**.

| Mathematical Theorem | Formal Lean 4 Declaration | Module File | Mathlib Basis / Dependency | Audit Status |
| :--- | :--- | :--- | :--- | :--- |
| $\overline{A(s)} = A^*(\overline{s})$ | `dirichletPoly_conj` | `FiniteDirichletPolynomial.lean` | `cpow_conj`, `map_sum` | Verified (No `sorryAx`) |
| $\|A(s)\| = \|A^*(\bar{s})\|$ | `dirichletPoly_norm_conj` | `FiniteDirichletPolynomial.lean` | `norm_star` | Verified (No `sorryAx`) |
| $\|A(\sigma+it)\|^2 = \|A^*(\sigma-it)\|^2$ | `dirichletNormSquare_conj_line` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_norm_conj` | Verified (No `sorryAx`) |
| $V \le \|A(\sigma+it)\| \iff V \le \|A^*(\sigma-it)\|$ | `threshold_conj_line_iff` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_norm_conj` | Verified (No `sorryAx`) |
| $A(\sigma+it)=0 \implies A^*(\sigma-it)=0$ | `dirichletPoly_zero_conj` | `FiniteDirichletPolynomial.lean` | `dirichletPoly_conj`, `star_zero` | Verified (No `sorryAx`) |
| $A(\sigma+it)=0 \iff A^*(\sigma-it)=0$ | `dirichletPoly_zero_conj_iff` | `FiniteDirichletPolynomial.lean` | `star_eq_zero` | Verified (No `sorryAx`) |
| $\text{crossNormProduct} \ge 0$ | `crossNormProduct_nonneg` | `CrossNormProduct.lean` | `mul_nonneg`, `norm_nonneg` | Verified (No `sorryAx`) |
| $(a^*)^* = a$ | `conjCoeff_conjCoeff` | `CrossNormProduct.lean` | `star_star` | Verified (No `sorryAx`) |
| Factor Swap Invariance | `crossNormProduct_swap` | `CrossNormProduct.lean` | `mul_comm` | Verified (No `sorryAx`) |
| $|\operatorname{Re}(A A^*)| \le \text{crossNormProduct}$ | `realPart_abs_le_crossNormProduct` | `CrossNormProduct.lean` | `abs_re_le_norm`, `norm_mul` | Verified (No `sorryAx`) |
| $A(\sigma_1+it)=0 \implies \text{crossNormProduct}=0$ | `crossNormProduct_eq_zero_of_left` | `CrossNormProduct.lean` | `norm_zero`, `zero_mul` | Verified (No `sorryAx`) |
| $A^*(\sigma_2-it)=0 \implies \text{crossNormProduct}=0$ | `crossNormProduct_eq_zero_of_right` | `CrossNormProduct.lean` | `norm_zero`, `mul_zero` | Verified (No `sorryAx`) |
| $\text{crossNormProduct}=0 \iff A=0 \lor A^*=0$ | `crossNormProduct_eq_zero_iff` | `CrossNormProduct.lean` | `mul_eq_zero`, `norm_eq_zero` | Verified (No `sorryAx`) |
| $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ | `completedRiemannZeta_reflection` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_one_sub` | Verified (No `sorryAx`) |
| $\Lambda(\sigma+it)=0 \iff \Lambda(1-\sigma-it)=0$ | `completedRiemannZeta_zero_reflection_iff` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_one_sub` | Verified (No `sorryAx`) |
| Full 4-Fold Zero Orbit | `completedRiemannZeta_fourfold_zero_orbit` | `CompletedZetaSymmetry.lean` | `completedRiemannZeta_reflection` | Verified (No `sorryAx`) |
| $\|H(t)\| = \|\zeta(1/2+it)\|$ | `hardyZ_norm_eq_riemannZeta_norm` | `HardyZ.lean` | `norm_mul`, `norm_exp` | Verified (No `sorryAx`) |
| $H(t)=0 \iff \zeta(1/2+it)=0$ | `hardyZ_zero_iff_riemannZeta_zero` | `HardyZ.lean` | `exp_ne_zero`, `mul_eq_zero` | Verified (No `sorryAx`) |
| $\|H(-t)\| = \|H(t)\|$ | `hardyZ_neg_norm` | `HardyZ.lean` | `riemannZeta_conj`, `norm_star` | Verified (No `sorryAx`) |
| $\forall t \neq 0, \zeta(1+it) \neq 0$ | `riemannZeta_ne_zero_on_one_line` | `Nonvanishing.lean` | `riemannZeta_ne_zero_of_one_le_re` | Verified (No `sorryAx`) |
| Totalized $\zeta(1+it) \neq 0$ | `riemannZeta_ne_zero_totalized` | `Nonvanishing.lean` | `riemannZeta_ne_zero_of_one_le_re` | Verified (No `sorryAx`) |

---

# 7. References

1. Larry Guth and James Maynard, *"New large value estimates for Dirichlet polynomials,"* **Annals of Mathematics**, vol. 203, no. 2, pp. 623-675, 2026. DOI: 10.4007/annals.2026.203.2.6.
2. David Loeffler and Michael Stoll, *"Formalizing zeta and L-functions in Lean,"* **Annals of Formalized Mathematics**, vol. 1, 2025. DOI: 10.46298/afm.15328. arXiv:2503.00959.
3. The Lean Community, *"Mathlib 4: The Lean 4 Mathematical Library,"* 2026. https://leanprover-community.github.io/mathlib4_docs/
4. A. E. Ingham, *"On the Estimation of N(σ, T),"* **The Quarterly Journal of Mathematics**, os-11(1), pp. 201-202, 1940. DOI: 10.1093/qmath/os-11.1.201.
