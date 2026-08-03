# Riemann Zeta Formalization in Lean 4

This repository contains a mechanized formalization of finite Dirichlet polynomial conjugation dualities, fourfold completed Zeta function orbits, and complex-valued Hardy Z-function identities in **Lean 4** (pinned to toolchain `leanprover/lean4:v4.30.0-rc2`, package version `0.1.0`).

## Package Structure

- **`RiemannZeta/FiniteDirichletPolynomial.lean`**: Finite Dirichlet polynomials over positive naturals $\mathbb{N}+$, conjugation invariance $\overline{A(s)} = A^*(\overline{s})$, norm equality, threshold equivalence, and two-way zero conjugation.
- **`RiemannZeta/CrossNormProduct.lean`**: Cross-norm product quantity $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1+it)\| \cdot \|A^*(\sigma_2-it)\|$, factor swap invariance, real-part upper bound, and zero-factor characterization.
- **`RiemannZeta/CompletedZetaSymmetry.lean`**: Coordinate representation of Mathlib's completed Riemann Zeta functional equation $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ and full 4-fold zero orbit $\Lambda(s) = 0 \implies \Lambda$ vanishes at all 4 symmetry evaluations.
- **`RiemannZeta/HardyZ.lean`**: Classical Riemann-Siegel theta angle $\theta(t)$, complex-valued Hardy-type normalization $H(t) = e^{i\theta(t)}\zeta(1/2+it)$, norm equivalence $\|H(t)\| = \|\zeta(1/2+it)\|$, zero equivalence $H(t)=0 \iff \zeta(1/2+it)=0$, and norm parameter negation symmetry $\|H(-t)\| = \|H(t)\|$.
- **`RiemannZeta/Nonvanishing.lean`**: Classical non-vanishing along $\operatorname{Re}(s) = 1$ for $t \neq 0$ excluding the pole at $s=1$, with Mathlib totalization disclosure.
- **`RiemannZeta/Audit.lean`**: Dedicated automated audit file executing `#print axioms` across all 21 core declarations.

## Verification & Audit

To verify the package locally:
```bash
lake build
lake env lean RiemannZeta/Audit.lean
```
All 21 audited declarations depend exclusively on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) with **0 `sorryAx` dependencies**.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.