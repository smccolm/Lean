# Lean 4 Formalizations & Compacted Graphs Workspace

Welcome to the **Lean** research workspace! This repository contains Lean 4 formalizations of classical mathematical theorems, compactified graph theory subprojects, interactive 3D WebGL visualization tools, and formal paper drafts.

---

## 📁 Repository Overview

```text
Lean/
├── EllipsePerimeter/    # Formalized proof of complete elliptic perimeter series in Lean 4
├── EllipseLab/          # Development laboratory and step-by-step proof iterations
├── Compacted Graphs/    # Subproject formalizing compactified graphs and cylindrical topology
├── visualizer/          # Reusable 3D WebGL & 2D Python interactive visualization suite
├── Article/             # Formal paper drafts and document exports
└── logs/                # Sequential project execution logs (#001 - #013)
```

---

## 🧮 Mathematical Projects

### 1. Ellipse Perimeter Formalization (`EllipsePerimeter`)
A mechanized Lean 4 proof of the classical infinite-series formula for the perimeter of an ellipse with semiaxes $A = \max(a,b)$ and $B = \min(a,b)$:

$$P(a,b) = 4A E(e) = 2\pi A \sum_{n=0}^{\infty} \left(\frac{(2n)!}{2^{2n}(n!)^2}\right)^2 \frac{e^{2n}}{1-2n}, \qquad e = \sqrt{1 - \frac{B^2}{A^2}}$$

- **Toolchain**: Lean 4 `v4.30.0-rc2` & Mathlib `v4.30.0-rc2`
- **Modules**:
  - `Wallis.lean`: Combinatorics of Wallis sequences and ratio recurrences.
  - `Binomial.lean`: Real binomial expansion $\sqrt{1-x}$ and series summability.

### 2. Compacted Graphs (`Compacted Graphs`)
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

## 🛠️ Build & Verification

### Building Lean Projects
```bash
# Build EllipsePerimeter
cd EllipsePerimeter
lake build

# Build Compacted Graphs
cd "../Compacted Graphs"
lake build
```

---

## 📜 Project Logging
All development steps, prompts, file updates, and verification outputs are tracked in sequence under `logs/#<seq>_<timestamp>_<topic>.md`.
