# Research Organization

The research tree mirrors the nine corridors in [`The RH Map - Aug 30, 2026 - Mermaid Diagram.txt`](The%20RH%20Map%20-%20Aug%2030,%202026%20-%20Mermaid%20Diagram.txt):

1. `1. Classical Analytic Foundations/`
2. `2. Computation and Explicit Zero-Free Control/`
3. `3. Quantum Chaos, Random Matrices and Spectral Physics/`
4. `4. Equivalent Criteria and Functional-Analytic Reformulations/`
5. `5. Critical Line, Mollifiers and Proportions/`
6. `6. de Bruijn-Newman Heat-Flow Route/`
7. `7. Weil, Arithmetic Geometry and Noncommutative Geometry/`
8. `8. Pair Correlation, Zero Statistics and Weil-Form Methods/`
9. `9. Zero Density, Large Values and Prime Transfer/`

Each corridor contains numbered node directories matching the map. These are stable homes for source material, research notes, and Lean packages as each line of work matures. The placeholders do not claim that their corresponding results have been formalized.

## Current formalizations

- The frozen [Guth--Maynard foundation](9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/71%20Guth-Maynard,%202026/README.md) occupies node 71. Its `GuthMaynard/`, collision-safe `GuthMaynardExternal/`, and support modules sit directly in that node, while the project-root Lake package and verifier use it as their source root.
- The isolated [Gafni--Tao release](9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao,%202026/README.md) occupies node 74 in the same corridor.

## Investigations outside the map

Cross-node synthesis and experiments that do not correspond to a single map node live in [`Investigations/`](Investigations/README.md):

- [`Inference (63, 71, 73, 74)`](Investigations/Inference%20%2863,%2071,%2073,%2074%29/) contains the provisional cross-node inference agenda.
- [`PrimeShell`](Investigations/PrimeShell/README.md) contains the completed separated-amplitude route analysis and its isolated Lean package.

The Guth--Maynard foundation remains frozen at commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`. Map-aligned work and investigations must remain outside that frozen import graph unless a future migration is separately designed and verified.

Exceptional-set, density-one, computational, and route-analysis results are not described as proofs of the Riemann Hypothesis.
