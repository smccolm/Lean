# Project Log #003: Discussion - Compacted Graphs in Cylindrical Coordinates

**Timestamp**: 2026-08-02T15:17:12-07:00  
**Log Sequence**: #003  

---

## 1. User Request Recorded
- **User Prompt**: "Discussion Mode: image a family of functions that plotted in a cylindrical coordinate system have a uniqe height relative to the starting plane for every incremental degree of roation (Theta) such that coordinate z is a function of r. Then, consider the comacted graphs of such functions. A true function of a graph would be rendered through compactification as a circle."

---

## 2. Theoretical Analysis & Mathematical Breakdown

### A. Cylindrical Coordinate Mapping & Functional Coupling
- **Cylindrical System**: $(r, \theta, z)$ where $r \in [0, \infty)$, $\theta \in [0, 2\pi) \cong S^1$, $z \in \mathbb{R}$.
- **Uniqueness Condition**: For each angle $\theta$, there is a unique height $z(\theta)$.
- **Radial Coupling**: Given $z = f(r)$ and $z = Z(\theta)$, this implies a functional relation $r(\theta) = f^{-1}(Z(\theta))$ (assuming invertibility of $f$ on its range), yielding a space curve $\gamma(\theta) = (r(\theta), \theta, f(r(\theta)))$.

### B. Topological Compactification
- **Domain/Codomain Compactification**: 
  - Standard graphs in $\mathbb{R}^3$ are non-compact because $z \in \mathbb{R}$ or $\theta \in \mathbb{R}$.
  - Under periodic angular identification ($\theta \sim \theta + 2\pi$) and codomain compactification (such as stereographic projection/one-point compactification of the height axis $\mathbb{R} \cup \{\infty\} \cong S^1$, or periodic quotienting $z(0) \sim z(2\pi)$), the unbounded graph $\Gamma = \{(r(\theta), \theta, f(r(\theta)))\}$ wraps smoothly into a closed 1-manifold homeomorphic to $S^1$ (a circle).
- **Geometric Interpretation**:
  - Helical/spiral graphs on cylindrical surfaces transform under compactification into closed knots or loops $S^1 \hookrightarrow \mathbb{T}^2 \subset \mathbb{R}^3$.

### C. Implications for Formalization in `Compacted Graphs`
- In Lean 4 (`CompactedGraphs`), this model can be formalized as:
  1. A continuous embedding $\gamma: S^1 \to M$ into a compact cylindrical manifold $M = S^1 \times S^1$ or $D^2 \times S^1$.
  2. A topological graph / fiber bundle projection $\pi: \Gamma \to S^1$ where each fiber $\pi^{-1}(\theta)$ is a single point, proving $\Gamma \cong S^1$.
