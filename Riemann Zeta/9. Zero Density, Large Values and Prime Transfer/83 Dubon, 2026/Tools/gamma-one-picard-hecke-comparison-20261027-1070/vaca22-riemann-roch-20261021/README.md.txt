# Riemann–Roch for Function Fields, in Lean 4

A complete, kernel-checked formalization of the **Riemann–Roch theorem** for algebraic function
fields of one variable, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The public API is **coordinate-free**: divisors are indexed by *intrinsic places* — discrete
rank-one valuation subrings of the function field that contain the constants — rather than by a
choice of coordinate. The development is **axiom-clean** (every headline theorem depends only on
`[propext, Classical.choice, Quot.sound]`) and contains **zero** `sorry` / `admit`.

## Main results

For a function field `K` over its field of constants `k`, in the `FunctionField` namespace:

- **`riemann_roch`** — for a canonical divisor `W` and any divisor `D`,
  `ℓ(D) = deg D + 1 − g + ℓ(W − D)`.
- **`duality`** — `ℓ(W − D) = i(D)`, the index of specialty.
- **`clifford`** — Clifford's inequality for special divisors.
- **`riemann_ineq`** — Riemann's inequality `ℓ(D) ≥ deg D + 1 − g`.
- Corollaries **C1–C6** — dimension and degree of canonical divisors, nonspeciality of
  large-degree divisors, existence of a nonspecial divisor, and more.
- The building blocks: **`genus`**, **`RRspace`** (`L(D)`), **`ell`** (`ℓ(D)`),
  **`indexOfSpecialty`** (`i(D)`), **`IsCanonical`** (a divisor is canonical exactly when it is the
  divisor of a nonzero Weil differential), the intrinsic **`WeilDifferential`**, and the intrinsic
  **`AdeleSpace`**.

Independently useful supporting pieces:

- **`IsDedekindDomain.Divisor`** / **`FractionalIdeal.divisorEquiv`** — the divisor group of a
  Dedekind domain as the free abelian group on its height-one prime ideals, with multiplication of
  fractional ideals corresponding to addition of divisors.
- **`FunctionField.Place`** and **`chartToPlace`** — the intrinsic place abstraction and its
  equivalence with a two-chart coordinate model, established via Ostrowski's theorem.

### Worked application: elliptic curves

On a Weierstrass elliptic curve (`WeierstrassCurve.Affine`) the development derives that the
**genus is one** (`genus_eq_one`) and identifies the degree-one places with the class group / Picard
torsor, compatibly with the elliptic group law (`picTorsor_compat_groupLaw`). A concrete end-to-end
regression instantiates the entire hypothesis tower on `y² = x³ − x` over `AlgebraicClosure ℚ`.

## Building

Requires [`elan`](https://github.com/leanprover/elan). Mathlib is pinned via `lake-manifest.json`
(`lean-toolchain` fixes the Lean version — currently Lean 4 / Mathlib `v4.31.0`).

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # build the library
```

## Verifying the proofs

- **No placeholders.** The library contains no `sorry`, `admit`, or unexplained `opaque`.
- **Axiom audit.** `AxiomCheck.lean` prints the axiom dependencies of the headline theorems:

  ```bash
  lake env lean AxiomCheck.lean
  ```

  Every declaration reports `[propext, Classical.choice, Quot.sound]` — the standard classical-logic
  axioms — with no `sorryAx`.
- **Continuous integration.** GitHub Actions builds the library, runs the Mathlib linter, checks the
  import umbrella (`mk_all`), and rejects any proof placeholder (`.github/workflows/lean.yml`).

## Repository layout

| Path | Contents |
|---|---|
| `RiemannRoch/Place.lean`, `PlaceEquiv.lean` | intrinsic places and the coordinate equivalence |
| `RiemannRoch/RRspace/`, `AdeleSpace/`, `Genus/` | Riemann–Roch spaces, adeles, genus, Riemann inequality |
| `RiemannRoch/WeilDifferential/` | Weil differentials, canonical class, duality |
| `RiemannRoch/RiemannRochTheorem/` | the theorem, Clifford, and corollaries |
| `RiemannRoch/CoordinateFree/` | the intrinsic (coordinate-free) public API, transported |
| `RiemannRoch/EllipticCurve/` | the elliptic-curve application |
| `AxiomCheck.lean` | axiom-dependency audit of the headline theorems |

## Status

The mathematics is complete and kernel-checked. Upstreaming these results into Mathlib — as a
sequence of small, independently reviewable pieces — is in progress.

## AI assistance

This project was developed with substantial assistance from AI coding tools for proof drafting,
search, and documentation. Every proof is checked by the Lean kernel; correctness does not depend on
the tooling.

## License

Released under the Apache 2.0 license (see [`LICENSE`](LICENSE)). © 2026 Guanghao Li.
