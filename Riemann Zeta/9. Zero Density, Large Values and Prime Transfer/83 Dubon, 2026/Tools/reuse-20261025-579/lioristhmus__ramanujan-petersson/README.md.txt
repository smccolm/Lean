# A Rank-Two Witness Reduction of the Ramanujan–Petersson Bound (after Deligne)

This repository contains the source note and a Gauss-managed Lean formalization companion for the
Ramanujan–Petersson argument recorded in `ramanujan-petersson.md`.

## Abstract

> We give a short derivation of the Ramanujan-Petersson bound for normalized holomorphic newforms by isolating a rank-two witness whose Frobenius trace equals the Hecke eigenvalue at unramified primes, and then applying a one-line squeeze using purity. An appendix records the standard geometric input: realization of the witness in étale cohomology of modular curves with symmetric-power local systems (or via Kuga–Sato varieties), the Hecke–Frobenius compatibility giving the local Euler factor, and the purity statement used in the squeeze. This note is expository: we do not reprove Deligne’s construction of $\rho_{f,\ell}$ or Weil II; we only isolate the minimal inputs needed for the bound.

## Introduction Snapshot

> A common arithmetic pattern is to realize a scalar quantity as the trace of an operator acting on a small-dimensional space and then bound the trace by controlling the spectral radius. In the modular setting, the Hecke eigenvalue $a_p$ at an unramified prime $p$ is the trace of Frobenius acting on a rank-two $\ell$-adic Galois representation. Deligne's purity theorem forces both Frobenius eigenvalues to have absolute value $p^{(k-1)/2}$, and the Ramanujan-Petersson bound follows immediately from the triangle inequality. The proof thus decomposes into (i) existence and Hecke-Frobenius compatibility of the representation, and (ii) purity. We refer to this three-step reduction (rank-two witness, purity, and the elementary trace bound) as a witness–squeeze argument.

## Layout

- `ramanujan-petersson.md`: source Markdown
- `ramanujan-petersson.pdf`: source PDF
- `lean/`: Lean 4 project
- `lean/README.md`: public statement of the current formalization boundary

## Lean Companion

The Lean project exposes a paper-facing public layer for the main statements together with
supporting companion documents:

- `lean/blueprint.md`
- `lean/claims.yaml`

The private review queue `paper_patch.md` is intentionally not included in this public snapshot.

## Build

```bash
cd lean
lake update
lake build
```

The exported project is pinned to `leanprover/lean4:v4.26.0` and references `mathlib4` by git
revision so that the public snapshot can be built outside the private research environment.
