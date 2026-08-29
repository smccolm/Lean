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
Mechanized Lean 4 formalization of the Guth--Maynard large-values and zero-density chain and its selected analytic inputs. The project contains frozen publication-facing contracts for Guth--Maynard Theorems 1.1 and 1.2, Ingham, Huxley, and the combined exponent $30(1-\sigma)/13$. It also retains the earlier finite Dirichlet-polynomial, completed-zeta, and Hardy-type infrastructure.

**Claim boundary:** the exact contracts are kernel-checked and project-integrated, with no project axiom or admitted proof in the audited tree. The DFI theorem is the localized signed dyadic specialization needed by the consumer, and the twisted-fourth-moment theorem is the mollifier-specific upper bound, not the full Hughes--Young asymptotic. Independent semantic review, publication of this formalization, and community canonicalization are not claimed.

- **Toolchain**: Lean 4 `v4.30.0`; Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`.
- **Publication contracts**: `RiemannZeta/PublicationContract.lean` proves the exact five source-facing contracts, including the closed-support/source-only coefficient form of Theorem 1.1 and the full range $1/2\le\sigma\le1$ of Theorem 1.2.
- **Verification**: `scripts/verify_release.ps1` is the canonical local/CI verifier. It classifies every project Lean file, enforces exact theorem types, builds the full graph, runs the exhaustive axiom audit and all linters, scans for proof escapes, records provenance, and fails on project diagnostics. `run_lake_build.bat` is its Windows wrapper.
- **Source freeze and review packet**: see `Riemann Zeta/verification/SOURCE_FREEZE.md` and `Riemann Zeta/Publication Readiness and Semantic Audit.md`.

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
pwsh -NoProfile -File scripts/verify_release.ps1

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
