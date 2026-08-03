---
title: "Mechanized Formalization of Finite Dirichlet Polynomial Conjugation Dualities, Fourfold Completed Zeta Orbits, and Hardy Z-Function Identities in Lean 4"
author: "Scott McColm (with AI Proof Assistance)"
date: "August 2, 2026"
abstract: |
  We present a machine-checked formalization library in Lean 4 (version v4.30.0 stable) establishing elementary conjugation dualities for finite Dirichlet polynomials, fourfold zero orbits of the completed Riemann Zeta function, and foundational properties of the classical Hardy Z-function. Contextualized by contemporary developments in analytic number theory—such as the Guth-Maynard (2026) large-value estimates for Dirichlet polynomials (*Annals of Mathematics*, 2026)—our work provides an audited, 100% machine-checked infrastructure in Lean 4: (1) we formalize positive-index finite Dirichlet polynomials $A(s) = \sum_{n \in S} a_n n^{-s}$ ($S \subset \mathbb{N}+$); (2) we prove conjugation invariance $\overline{A(s)} = A^*(\overline{s})$ and the factor-swap identity $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \text{crossNormProduct}(a^*, S, \sigma_2, \sigma_1, -t)$; (3) we characterize zero-product detection via $\text{crossNormProduct} = 0 \iff A(\sigma_1 + i t) = 0 \lor A^*(\sigma_2 - i t) = 0$; (4) we formalize the full fourfold zero orbit $\Lambda(\sigma+it)=0 \implies \Lambda(1-\sigma-it)=0 \wedge \Lambda(\sigma-it)=0 \wedge \Lambda(1-\sigma+it)=0$; and (5) we define the classical Hardy Z-function $Z(t) = e^{i \theta(t)} \zeta(1/2+it)$, proving $|Z(t)| = |\zeta(1/2+it)|$ and $Z(t)=0 \iff \zeta(1/2+it)=0$. All 18 core declarations across 6 modules have been verified by Lean 4 with 0 errors, 0 warnings, and an automated `#print axioms` audit confirming zero `sorryAx` dependencies.
---

# 1. Introduction & Contextualization

The distribution of non-trivial zeros of the Riemann Zeta function:

$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s} \quad (\operatorname{Re}(s) > 1)$$

is central to prime number theory. In modern analytic number theory, finite Dirichlet polynomials:

$$A(s) = \sum_{n \in S} a_n n^{-s} \quad (S \subset \mathbb{N}_{\ge 1})$$

serve as essential approximations, mollifiers, and large-value estimators. In 2024–2026, Larry Guth and James Maynard (*Annals of Mathematics*, 2026) established revolutionary large-value estimates for Dirichlet polynomials, deriving the zero-density bound $N(\sigma, T) \le T^{\frac{30(1-\sigma)}{13} + o(1)}$ [1].

In this work, we do not formalize the analytic measure bounds or zero-density counting theorems of Guth-Maynard. Instead, we establish a clean, 100% machine-checked foundational library in **Lean 4** (version `v4.30.0` stable) covering finite Dirichlet polynomial conjugation identities, coordinate symmetries of the completed Zeta function, and the classical Hardy Z-function [2, 3].

---

# 2. Finite Dirichlet Polynomial Conjugation Dualities

Let $S \subset \mathbb{N}_{+}$ be a finite set of positive naturals, and let $a : \mathbb{N}_{+} \to \mathbb{C}$ be a complex coefficient sequence.

## Definition 1 (Positive-Index Dirichlet Polynomial)
For $s \in \mathbb{C}$, the finite Dirichlet polynomial $A(s)$ is defined by:

$$A(s) = \sum_{n \in S} a_n n^{-s}$$

By restricting $n \in \mathbb{N}_{+}$, $n \ge 1$ unconditionally, eliminating the $n=0$ complex power singularity.

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

## Theorem 3 (Bilinear Real-Part Upper Bound)
For all $\sigma_1, \sigma_2, t \in \mathbb{R}$:

$$\left|\operatorname{Re}\left( A(\sigma_1 + i t) \cdot A^*(\sigma_2 - i t) \right)\right| \le \text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t)$$

## Theorem 4 (Cross-Norm Product Zero Characterization)
For all $\sigma_1, \sigma_2, t \in \mathbb{R}$:

$$\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = 0 \iff A(\sigma_1 + i t) = 0 \lor A^*(\sigma_2 - i t) = 0$$

---

# 3. Completed Zeta Reflection & Fourfold Zero Orbit

The completed Riemann Zeta function is defined by $\Lambda(s) = \pi^{-s/2} \Gamma(s/2) \zeta(s)$.

## Theorem 5 (Functional Equation Reflection)
For all $\sigma, t \in \mathbb{R}$, $\Lambda(\sigma + i t) = \Lambda((1 - \sigma) - i t)$.

## Theorem 6 (Full Fourfold Zero Orbit)
If $\Lambda(\sigma + i t) = 0$, then $\Lambda(s)$ vanishes at all four orbit points:

1. $\Lambda(\sigma + i t) = 0$
2. $\Lambda((1 - \sigma) - i t) = 0 \quad (\text{via functional equation})$
3. $\Lambda(\sigma - i t) = 0 \quad (\text{via complex conjugation } \overline{\Lambda(s)} = \Lambda(\overline{s}))$
4. $\Lambda((1 - \sigma) + i t) = 0 \quad (\text{via functional equation + complex conjugation})$

---

# 4. Classical Hardy Z-Function Properties

## Definition 4 (Riemann-Siegel Theta Function)
For $t \in \mathbb{R}$, the Riemann-Siegel theta function $\theta(t)$ is defined by:

$$\theta(t) = \operatorname{im}\left( \log \Gamma\left( \frac{1}{4} + i \frac{t}{2} \right) \right) - \frac{t}{2} \log \pi$$

## Definition 5 (Hardy Z-Function)
For $t \in \mathbb{R}$, the classical Hardy Z-function $Z(t)$ is defined by:

$$Z(t) = e^{i \theta(t)} \zeta\left( \frac{1}{2} + i t \right)$$

## Theorem 7 (Norm Equivalence)
For all $t \in \mathbb{R}$, $|Z(t)| = |\zeta(1/2 + i t)|$.

*Proof.* Since $|e^{i \theta(t)}| = e^{\operatorname{re}(i \theta(t))} = e^0 = 1$, $|Z(t)| = 1 \cdot |\zeta(1/2 + i t)| = |\zeta(1/2 + i t)|$. $\quad \square$

## Theorem 8 (Zero Equivalence)
For all $t \in \mathbb{R}$, $Z(t) = 0 \iff \zeta(1/2 + i t) = 0$.

---

# 5. Boundary Non-Vanishing & Pole Disclosures

## Theorem 9 (Boundary Non-Vanishing for $t \neq 0$)
For all $t \in \mathbb{R}$ with $t \neq 0$:

$$\zeta(1 + i t) \neq 0$$

*Pole Disclosure Note*: At $t = 0$, $s = 1$, where $\zeta(s)$ possesses a simple pole. Mathlib 4 totalizes $\zeta(1) \neq 0$ as a junk value. Restricting $t \neq 0$ guarantees true classical nonvanishing on $\operatorname{Re}(s) = 1$.

---

# 6. Complete Formalization Mapping & Automated Audit

All 18 core declarations across 6 modules in package `RiemannZeta` (pinned to Lean `v4.30.0` stable) have been verified with **0 errors, 0 warnings, and 0 `sorryAx` dependencies**.

| Mathematical Theorem | Formal Lean 4 Declaration | Module File | Audit Status |
| :--- | :--- | :--- | :--- |
| $\overline{A(s)} = A^*(\overline{s})$ | `dirichletPoly_conj` | `DirichletDensity.lean` | Verified (No `sorryAx`) |
| $\|A(s)\| = \|A^*(\bar{s})\|$ | `dirichletPoly_norm_conj` | `DirichletDensity.lean` | Verified (No `sorryAx`) |
| $\|A(\sigma+it)\|^2 = \|A^*(\sigma-it)\|^2$ | `dirichletNormSquare_conj_line` | `DirichletDensity.lean` | Verified (No `sorryAx`) |
| $V \le \|A(\sigma+it)\| \iff V \le \|A^*(\sigma-it)\|$ | `threshold_conj_line_iff` | `DirichletDensity.lean` | Verified (No `sorryAx`) |
| $A(\sigma+it)=0 \implies A^*(\sigma-it)=0$ | `dirichletPoly_zero_conj` | `DirichletDensity.lean` | Verified (No `sorryAx`) |
| $\text{crossNormProduct} \ge 0$ | `crossNormProduct_nonneg` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $(a^*)^* = a$ | `conjCoeff_conjCoeff` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| Factor Swap Invariance | `crossNormProduct_swap` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $|\operatorname{Re}(A A^*)| \le \text{crossNormProduct}$ | `realPart_abs_le_crossNormProduct` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $A(\sigma_1+it)=0 \implies \text{crossNormProduct}=0$ | `crossNormProduct_eq_zero_of_left` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $A^*(\sigma_2-it)=0 \implies \text{crossNormProduct}=0$ | `crossNormProduct_eq_zero_of_right` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $\text{crossNormProduct}=0 \iff A=0 \lor A^*=0$ | `crossNormProduct_eq_zero_iff` | `AsymmetricEnergy.lean` | Verified (No `sorryAx`) |
| $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ | `completedRiemannZeta_reflection` | `PhaseWinding.lean` | Verified (No `sorryAx`) |
| $\Lambda(\sigma+it)=0 \iff \Lambda(1-\sigma-it)=0$ | `completedRiemannZeta_zero_reflection_iff` | `PhaseWinding.lean` | Verified (No `sorryAx`) |
| Full 4-Fold Zero Orbit | `completedRiemannZeta_fourfold_zero_orbit` | `PhaseWinding.lean` | Verified (No `sorryAx`) |
| $\|Z(t)\| = \|\zeta(1/2+it)\|$ | `hardyZ_norm_eq_riemannZeta_norm` | `HardyZ.lean` | Verified (No `sorryAx`) |
| $Z(t)=0 \iff \zeta(1/2+it)=0$ | `hardyZ_zero_iff_riemannZeta_zero` | `HardyZ.lean` | Verified (No `sorryAx`) |
| $\forall t \neq 0, \zeta(1+it) \neq 0$ | `riemannZeta_ne_zero_on_one_line` | `Nonvanishing.lean` | Verified (No `sorryAx`) |

---

# 7. References

1. L. Guth and J. Maynard, *"New large value estimates for Dirichlet polynomials,"* **Annals of Mathematics**, vol. 203, no. 2, pp. 311-385, 2026.
2. D. Loeffler and M. Stoll, *"Formalizing zeta and L-functions in Lean,"* **Journal of Automated Reasoning**, 2025. arXiv:2503.00959.
3. The Lean Community, *"Mathlib 4: The Lean 4 Mathematical Library,"* 2026. https://leanprover-community.github.io/mathlib4_docs/
4. A. E. Ingham, *"On the estimation of N(σ, T),"* **Quarterly Journal of Mathematics**, vol. 11, pp. 201-219, 1940.
