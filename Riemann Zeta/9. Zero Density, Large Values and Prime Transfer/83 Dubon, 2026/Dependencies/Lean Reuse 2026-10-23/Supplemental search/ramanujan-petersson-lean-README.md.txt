# Lean Formalization Scope

This repository contains a Lean formalization companion to the source note, not a claim that every
deep input has already been fully internalized in Lean.

## Current Public Endpoint

The exported Lean project provides a paper-facing public layer for the main results:

- Theorem 3.1
- Theorem 4.1
- Theorem 2.1
- Corollary 5.3 (prime-power clause)
- Corollary 5.3 (coprime-index clause)

These public declarations live in the Lean companion and are supported by internal reduction and
interface layers documented in `blueprint.md` and `claims.yaml`.

## Remaining Abstraction Boundaries

The current snapshot still treats some deep inputs as abstract interfaces rather than deriving them
fully inside Lean. In particular, the present public endpoint does not yet fully internalize:

- Deligne's representation-theoretic construction
- the purity input behind the Frobenius eigenvalue bounds
- the full Hecke multiplicativity / Euler-product infrastructure

That means this repository is best described publicly as a **Lean formalization companion** or a
**paper-facing Lean formalization**, rather than a complete end-to-end internal derivation of every
background theorem used by the note.
