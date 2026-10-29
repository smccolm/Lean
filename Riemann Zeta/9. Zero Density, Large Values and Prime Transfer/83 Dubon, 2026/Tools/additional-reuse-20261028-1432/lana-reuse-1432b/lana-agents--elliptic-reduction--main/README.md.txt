# elliptic-reduction

Elliptic curve reduction theory beyond Mathlib.

## Status

**Not started.** The repository is the initial project scaffold (a single commit,
2026-07-20). The library `EllipticReduction` contains only the placeholder module
`EllipticReduction/Basic.lean`, which has no declarations: there are no definitions or theorems yet
(and so no `sorry`, `axiom` or `admit`). Everything under *Goals* below is planned, not
formalised.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

`iut` no longer has a `ReductionCertificate` interface waiting for this repository. Its
tower arithmetic of IUT IV Theorem 1.10, `Iut.TowerArithmetic`, is proved for the tripod
(`Iut.Tripod.towerArithmetic_of_towerLocalHyp`, with the local facts proved as
`Iut.Tripod.towerLocalHyp`), and the stable reduction of the tripod curves is proved there
(`Iut/Tripod/StableOdd.lean`, `StableTwo.lean`). A general reduction theory for elliptic curves, as listed under *Goals*, is still
missing.

## Goals

Develop general reduction theory for elliptic curves, the theory behind IUT IV Proposition 1.8(v)–(vii). (It was planned to discharge a `ReductionCertificate` interface of `iut`; see *Status*.)

In scope, none of which is packaged in Mathlib v4.32.0:

* semistable and Néron models;
* moduli with level structure;
* inertia actions;
* Galois descent for elliptic curves;
* Serre-type criteria via polarized abelian varieties and Tate modules.

This is a standalone arithmetic-geometry project.

## Related repositories

Planned to discharge reduction-theory inputs of `iut`; `iut` does not use it (see
*Status*). Overlaps with `elliptic-curves`, which already has one direction of
Néron–Ogg–Shafarevich, the formal group, Weil pairing and Tate module, and `j`-invariant
criteria for the reduction type. Distinct from `tate-curves-theta`, which concerns Tate
uniformization and the theta function.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `EllipticReduction/`, and every file must be imported from
the root module `EllipticReduction.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib EllipticReduction --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#5](https://taxis.lana.merten.dev/issues/5)

License: Apache 2.0 (see LICENSE).
