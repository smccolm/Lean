# Riemann Zeta - Machine-Checked Formalization in Lean 4

This repository contains a machine-checked formalization of finite Dirichlet polynomial conjugation identities, fourfold completed Riemann Zeta zero orbits, and classical Hardy Z-function properties in **Lean 4** (pinned to stable version `v4.30.0`).

## Package Structure

- **`RiemannZeta/HardyZ.lean`**: Classical Hardy Z-function $Z(t) = e^{i \theta(t)} \zeta(1/2 + i t)$, proving $|Z(t)| = |\zeta(1/2 + i t)|$ and $Z(t) = 0 \iff \zeta(1/2 + i t) = 0$.
- **`RiemannZeta/Nonvanishing.lean`**: Non-vanishing of the classical Riemann Zeta function along $\text{Re}(s) = 1$ for $t \neq 0$ (excluding the pole at $s = 1$).
- **`RiemannZeta/PhaseWinding.lean`**: Coordinate identities and full 4-point zero orbit $\Lambda(\sigma+it)=0 \implies \Lambda(1-\sigma-it)=0 \wedge \Lambda(\sigma-it)=0 \wedge \Lambda(1-\sigma+it)=0$.
- **`RiemannZeta/DirichletDensity.lean`**: Finite Dirichlet polynomial evaluation over positive naturals $\mathbb{N}+$, proving $\overline{A(s)} = A^*(\overline{s})$, norm invariance, threshold equivalence, and zero preservation.
- **`RiemannZeta/AsymmetricEnergy.lean`**: Cross-norm product $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1+it)\| \|A^*(\sigma_2-it)\|$, factor swap invariance, bilinear real-part bound, and zero detection characterization.
- **`RiemannZeta/Audit.lean`**: Automated axiom audit script executing `#print axioms` across all 18 core declarations.

## Building and Verification

### Prerequisites
- Lean 4 toolchain manager (`elan`).

### Commands

To build and verify the package locally:

```cmd
cd "Riemann Zeta"
lake build
```

To run the full automated diagnostic audit:

```cmd
.\lean_build_diag.cmd
```

## Scope Boundaries & Disclosures

1. **Finite Algebraic Identities**: All Dirichlet polynomial declarations operate on finite sums $\sum_{n \in S} a_n n^{-s}$ ($S \subset \mathbb{N}+$). They are exact algebraic identities, not analytic zero-density measure bounds ($N(\sigma, T)$).
2. **Symmetry vs. Non-Existence**: The fourfold zero orbit proves where zeros must lie if they exist; it does not rule out off-line zeros.
3. **Pole Totalization**: The classical zeta function possesses a simple pole at $s=1$. Mathlib totalizes $\zeta(1) \neq 0$ as a junk value. For classical nonvanishing, $t \neq 0$ is required.

## License

MIT License. See [LICENSE](LICENSE).