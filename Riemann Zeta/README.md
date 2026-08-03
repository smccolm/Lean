# Riemann Zeta Formalization in Lean 4

[![Riemann Zeta Lean CI](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml/badge.svg)](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml)

Mechanized formalization of finite Dirichlet polynomial conjugation dualities, fourfold completed Zeta function orbits, and complex-valued Hardy-type phase normalization identities in **Lean 4** (pinned to toolchain `leanprover/lean4:v4.30.0-rc2`, package version `0.1.0`).

Author: **S. McColm**

---

## Package Structure

- **[`RiemannZeta/FiniteDirichletPolynomial.lean`](RiemannZeta/FiniteDirichletPolynomial.lean)**: Finite Dirichlet polynomials over positive naturals $\mathbb{N}_+$, conjugation invariance $\overline{A(s)} = A^*(\overline{s})$, norm equality, threshold equivalence, and two-way zero conjugation.
- **[`RiemannZeta/CrossNormProduct.lean`](RiemannZeta/CrossNormProduct.lean)**: Cross-norm product quantity $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1+it)\| \cdot \|A^*(\sigma_2-it)\|$, factor swap invariance, real-part upper bound, and zero-factor characterization.
- **[`RiemannZeta/CompletedZetaSymmetry.lean`](RiemannZeta/CompletedZetaSymmetry.lean)**: Coordinate representation of Mathlib's completed Riemann Zeta functional equation $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ and fourfold zero orbit under two assumed conjugate zeros.
- **[`RiemannZeta/HardyZ.lean`](RiemannZeta/HardyZ.lean)**: Classical Riemann-Siegel theta angle $\theta(t)$, complex-valued Hardy-type phase normalization $H(t) = e^{i\theta(t)}\zeta(1/2+it)$, norm equivalence $\|H(t)\| = \|\zeta(1/2+it)\|$, zero equivalence $H(t)=0 \iff \zeta(1/2+it)=0$, and conditional norm parameter negation symmetry $\|H(-t)\| = \|H(t)\|$.
- **[`RiemannZeta/Nonvanishing.lean`](RiemannZeta/Nonvanishing.lean)**: Classical non-vanishing along $\mathrm{Re}(s) = 1$ for $t \neq 0$ excluding the pole at $s = 1$, with Mathlib totalization disclosure.
- **[`RiemannZeta/GuthMaynard/Asymptotics.lean`](RiemannZeta/GuthMaynard/Asymptotics.lean)**: Asymptotic relations matching the Guth-Maynard epsilon-power convention $T^{o(1)}$, equipped with `EpsilonPowerBound` defining properties.
- **[`RiemannZeta/GuthMaynard/Separated.lean`](RiemannZeta/GuthMaynard/Separated.lean)**: Properties and translation symmetries for bounded 1-separated sets over explicit frequency intervals.
- **[`RiemannZeta/GuthMaynard/Statements.lean`](RiemannZeta/GuthMaynard/Statements.lean)**: Exact kernel-checked propositions mapping the Guth-Maynard Large Values Estimate and Zero-Density exponents over polynomial bases.
- **[`RiemannZeta/GuthMaynard/ZeroCount.lean`](RiemannZeta/GuthMaynard/ZeroCount.lean)**: Interface tying exact multiplicity counts of `riemannZeta` zeros to topological regions, parameterized finiteness, and dyadic reduction properties.
- **[`RiemannZeta/GuthMaynard/ExponentArithmetic.lean`](RiemannZeta/GuthMaynard/ExponentArithmetic.lean)**: Zero-`sorry` formulation of exact rational inequalities, integer parameter bounds, and rational exponent limits utilized in Section 13.1.
- **[`RiemannZeta/GuthMaynard/ZeroDetector.lean`](RiemannZeta/GuthMaynard/ZeroDetector.lean)**: Abstract formalization of the Zero Detector Dirichlet polynomial, Type I classification, and Type II bounds hypotheses.
- **[`RiemannZeta/GuthMaynard/PolynomialPowers.lean`](RiemannZeta/GuthMaynard/PolynomialPowers.lean)**: Formulation of Dirichlet polynomial exponentiation and relations between large base values and powered values.
- **[`RiemannZeta/GuthMaynard/Transfer.lean`](RiemannZeta/GuthMaynard/Transfer.lean)**: Conditional zero-density transfer theorem parameterizing the final exponent over explicit hypotheses from F-01 through F-10.
- **[`RiemannZeta/Audit.lean`](RiemannZeta/Audit.lean)**: Dedicated automated audit file executing `#print axioms` across all 50 core declarations.

---

## Verification & Axiom Audit

To verify the package locally using `lake`:
```bash
lake build
lake env lean RiemannZeta/Audit.lean
```

All 50 audited declarations depend exclusively on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) with **0 `sorryAx` dependencies**.

---

## Contribution Taxonomy & AI Tool Disclosure

- **Contribution Layers**:
  1. *New Definitions & Finite Dualities*: `dirichletPoly`, `conjCoeff`, `crossNormProduct`, conjugation invariance.
  2. *Coordinate Wrappers*: Packaging Mathlib's `completedRiemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re` into coordinate representations.
  3. *Complex Phase Normalization*: Formalizing $H(t) = e^{i \theta(t)} \zeta(1/2 + i t)$ as a complex-valued phase normalization ($H : \mathbb{R} \to \mathbb{C}$).
  4. *Inherited Analytic Foundations*: Functional equation and boundary non-vanishing inherited directly from Mathlib 4.
  5. *Guth-Maynard Target Infrastructure*: Statement formulations and explicit asymptotic machinery required for the zero-density deduction sequence.

- **AI Tool Disclosure**: All Lean 4 proof developments, manuscript drafts, and verification steps were assisted by AI coding agents (Antigravity/Gemini). S. McColm performed overall mathematical oversight, project specification, design review, and accepts full responsibility for the mathematical content.

---

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.