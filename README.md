# Lean 4 Mathematical Formalizations Workspace

Welcome to the **Lean 4** research workspace! This repository contains Lean 4 formalizations of classical mathematical theorems, Dirichlet polynomial dualities, completed Riemann Zeta symmetries, post-Guth--Maynard exceptional-interval results and route analyses, compactified graph theory subprojects, interactive 3D WebGL visualization tools, and formal paper manuscripts.

Author: **S. McColm**

---

## 📁 Repository Overview

```text
Lean/
├── Riemann Zeta/        # Frozen Guth--Maynard foundation and earlier zeta infrastructure
│   └── PostGM/          # Isolated Gafni--Tao and Prime Shell projects
├── EllipsePerimeter/    # Formalized proof of complete elliptic perimeter series in Lean 4
├── EllipseLab/          # Development laboratory and step-by-step proof iterations for the Ellipse project
├── Compacted Graphs/    # Subproject formalizing compactified graphs and cylindrical topology
├── visualizer/          # Reusable 3D WebGL & 2D Python interactive visualization suite
└── Article/             # Formal paper manuscripts and drafts (e.g., Ellipse Perimeter paper)
```

---

## 🧮 Subprojects & Formalizations

### 1. Riemann Zeta Formalization (`Riemann Zeta/`)
Mechanized Lean 4 formalization of the Guth--Maynard large-values and zero-density chain and its selected analytic inputs. The project contains frozen publication-facing contracts for Guth--Maynard Theorems 1.1 and 1.2, Ingham, Huxley, and the combined exponent $30(1-\sigma)/13$. It also retains the earlier finite Dirichlet-polynomial, completed-zeta, and Hardy-type infrastructure.

**Claim boundary:** the exact contracts are kernel-checked and project-integrated, with no project axiom or admitted proof in the audited tree. The DFI theorem is the localized signed dyadic specialization needed by the consumer, and the twisted-fourth-moment theorem is the mollifier-specific upper bound, not the full Hughes--Young asymptotic. Independent semantic review, publication of this formalization, and community canonicalization are not claimed.

- **Toolchain**: Lean 4 `v4.30.0`; Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`.
- **Publication contracts**: `RiemannZeta/PublicationContract.lean` proves the exact five source-facing contracts, including the closed-support/source-only coefficient form of Theorem 1.1 and the full range $1/2\le\sigma\le1$ of Theorem 1.2.
- **Verification**: `scripts/verify_release.ps1` is the canonical verifier. Exact commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, published annotated tag `gm-foundation-freeze-v1.0.1`, passed it from a fresh short-path clone. It classifies every project Lean file, enforces exact theorem types, builds the full graph, runs the exhaustive axiom audit and all linters, scans for proof escapes, records provenance, and fails on project diagnostics. `run_lake_build.bat` is its Windows wrapper. Hosted CI is an optional mirror and has not produced a successful artifact.
- **Source freeze and review packet**: see `Riemann Zeta/verification/SOURCE_FREEZE.md` and `Riemann Zeta/Publication Readiness and Semantic Audit.md`.

#### Isolated post-Guth--Maynard work (`Riemann Zeta/PostGM/`)

The post-GM projects remain outside the frozen foundation's import graph and use their own pinned packages and verification procedures.

- **[Gafni--Tao exceptional intervals](Riemann%20Zeta/PostGM/GafniTao/README.md)**: A kernel-checked formalization of the release-scope results in Gafni--Tao, *Primes in almost all short intervals* (`arXiv:2505.24017v1`). The public root proves the general Theorems 1.1--1.3 and the two displayed Section 3 sample inequalities, including the specialization of Theorem 1.1 using the frozen Guth--Maynard density theorem. The latest recorded isolated run passed on 2026-09-07: all 3,592 local PNT+ jobs and 10,344 Gafni--Tao jobs completed with zero diagnostics, and the audit reported only `propext`, `Classical.choice`, and `Quot.sound`. The release does not claim the full best-known numerical curve, Ford's optimized constants, external review, or new mathematics.
- **[Prime Shell](Riemann%20Zeta/PostGM/PrimeShell/README.md)**: This completed experiment reached its permitted **ROUTE DISPROVED** endpoint. Lean proves that every faithful separated amplitude in the modeled explicit-formula range has `3 < kappaXi`, so the exact Zeta23 output `2 - kappaXi` cannot improve `2/3` by any positive amount, even under perfect arithmetic control. The endpoint `primeShell_universal_no_gain_native` is non-vacuous and its audit reports only the standard logical dependencies above. It proves no new theorem about zeta zeros and does not rule out connected positive-valley windows, other source constructions, or approaches outside `FaithfulAmplitudeShell`.

### 2. Ellipse Perimeter Formalization (`EllipsePerimeter/` & `Article/`)
A mechanized Lean 4 proof of the classical infinite-series formula for the perimeter of an ellipse with semiaxes $A = \max(a,b)$ and $B = \min(a,b)$:

$$P(a,b) = 4A E(e) = 2\pi A \sum_{n=0}^{\infty} \left(\frac{(2n)!}{2^{2n}(n!)^2}\right)^2 \frac{e^{2n}}{1-2n}, \qquad e = \sqrt{1 - \frac{B^2}{A^2}}$$

- **Modules**:
  - `Binomial.lean`: Real binomial expansion $\sqrt{1-x}$ and series summability.
  - `Boundary.lean`: Endpoint evaluations and limit squeezes for the degenerate case $e=1$.
  - `EllipticE.lean`: Definition and properties of the complete elliptic integral $E(e)$ and coefficient sequences.
  - `Geometry.lean`: Full-loop parametric arc-length and its relationship to the quadrant integral.
  - `Wallis.lean`: Combinatorics of Wallis sequences and ratio recurrences for the trigonometric integrals.
- **Paper**: A draft manuscript detailing the derivation alongside the Lean formalization is available in the `Article/` directory. `EllipseLab/` contains the intermediate iterative states of the proof development.

### 3. Compacted Graphs (`Compacted Graphs/`)
A dedicated Lean 4 project for formalizing compactified topological graphs, single-valued fiber bundle projections, and cylindrical coordinate mappings $(r, \theta, z)$. (Currently in early stages of development.)

---

## 🎨 Interactive 3D WebGL Visualization Suite (`visualizer/`)

Includes a Python visualization engine for interactive 3D WebGL exploration in your browser via `dashboard.html`:
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

# Verify the isolated Gafni--Tao release
cd "PostGM/GafniTao"
cmd /c run_gafni_tao_build.bat --no-pause

# Reproduce the isolated Prime Shell project
cd "../PrimeShell/Extension"
lake update
lake build
lake env lean PrimeShell/Audit.lean

# Verify EllipsePerimeter
cd "../../../../EllipsePerimeter"
lake build

# Verify Compacted Graphs
cd "../Compacted Graphs"
lake build
```

---

## 📄 License

This repository is licensed under the MIT License - see the [LICENSE](Riemann%20Zeta/LICENSE) file for details.
