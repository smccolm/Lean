# Lean 4 Mathematical Formalizations Workspace

[![Riemann Zeta Lean CI](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml/badge.svg)](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml)

Welcome to the **Lean 4** research workspace! This repository contains Lean 4 formalizations of classical mathematical theorems, Dirichlet polynomial dualities, completed Riemann Zeta symmetries, compactified graph theory subprojects, interactive 3D WebGL visualization tools, and formal paper manuscripts.

Author: **S. McColm**

---

## 📁 Repository Overview

```text
Lean/
├── Riemann Zeta/        # Formalization of Dirichlet polynomials & completed Zeta symmetries
├── EllipsePerimeter/    # Formalized proof of complete elliptic perimeter series in Lean 4
├── EllipseLab/          # Development laboratory and step-by-step proof iterations
├── Compacted Graphs/    # Subproject formalizing compactified graphs and cylindrical topology
└── visualizer/          # Reusable 3D WebGL & 2D Python interactive visualization suite
```

---

## 🧮 Subprojects & Formalizations

### 1. Riemann Zeta Formalization (`Riemann Zeta/`)
Mechanized Lean 4 formalization of finite positive-index Dirichlet polynomial conjugation identities, coordinate packaging for Mathlib's completed Riemann Zeta functional equation, and complex-valued Hardy-type phase normalization.

- **Toolchain**: Lean 4 `v4.30.0-rc2` & Mathlib `5450b53e5d`
- **Submodules**:
  - `FiniteDirichletPolynomial.lean`: Positive-index Dirichlet polynomials over $\mathbb{N}_+$, conjugation invariance $\overline{A(s)} = A^*(\overline{s})$, and two-way zero conjugation.
  - `CrossNormProduct.lean`: Product-of-norms quantity $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1+it)\| \cdot \|A^*(\sigma_2-it)\|$, factor swap invariance, and zero-factor characterization.
  - `CompletedZetaSymmetry.lean`: Coordinate packaging of completed Zeta functional equation $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ and fourfold zero orbit under two assumed conjugate zeros.
  - `HardyZ.lean`: Complex-valued Hardy-type phase normalization $H(t) = e^{i\theta(t)}\zeta(1/2+it)$, norm equivalence $\|H(t)\| = \|\zeta(1/2+it)\|$, zero equivalence $H(t)=0 \iff \zeta(1/2+it)=0$, and conditional norm negation symmetry.
  - `Nonvanishing.lean`: Classical boundary nonvanishing along $\mathrm{Re}(s) = 1$ for $t \neq 0$ with Mathlib totalization disclosure.
  - `Audit.lean`: Automated `#print axioms` audit across all 21 core declarations (0 `sorryAx` dependencies).

### 2. Ellipse Perimeter Formalization (`EllipsePerimeter/`)
A mechanized Lean 4 proof of the classical infinite-series formula for the perimeter of an ellipse with semiaxes $A = \max(a,b)$ and $B = \min(a,b)$:

$$P(a,b) = 4A E(e) = 2\pi A \sum_{n=0}^{\infty} \left(\frac{(2n)!}{2^{2n}(n!)^2}\right)^2 \frac{e^{2n}}{1-2n}, \qquad e = \sqrt{1 - \frac{B^2}{A^2}}$$

- **Modules**:
  - `Wallis.lean`: Combinatorics of Wallis sequences and ratio recurrences.
  - `Binomial.lean`: Real binomial expansion $\sqrt{1-x}$ and series summability.

### 3. Compacted Graphs (`Compacted Graphs/`)
A dedicated Lean 4 project for formalizing compactified topological graphs, single-valued fiber bundle projections, and cylindrical coordinate mappings $(r, \theta, z)$.

---

## 🎨 Interactive 3D WebGL Visualization Suite (`visualizer/`)

Includes a Python visualization engine for interactive 3D WebGL exploration in your browser:
- **3D Cylindrical Compactification**: Visualizes $3\text{D}$ cylindrical spirals $(r(\theta), \theta, z)$ alongside their compactified torus ($S^1 \times S^1$) embeddings.
- **Riemann Zeta Critical Line Trajectory**: Animates $\zeta(\frac{1}{2} + it)$ for $t \in [0, 40]$, showing 3D spatial origin-axis collapses at nontrivial zeros and 2D complex plane origin-crossing loops.

### Running the Visualizer
```bash
python visualizer/visualizer.py
```
Or start the local server:
```bash
python visualizer/server.py
```

---

## 🛠️ Local Build & Verification

```bash
# Verify Riemann Zeta
cd "Riemann Zeta"
lake build
lake env lean RiemannZeta/Audit.lean

# Verify EllipsePerimeter
cd "../EllipsePerimeter"
lake build

# Verify Compacted Graphs
cd "../Compacted Graphs"
lake build
```

---

## 📄 License

This repository is licensed under the MIT License - see the [LICENSE](Riemann%20Zeta/LICENSE) file for details.
