# Tao--Trudgian--Yang 2025 formalization

This directory is the planning and source-control baseline for a Lean 4
formalization of Terence Tao, Tim Trudgian, and Andrew Yang,
*New exponent pairs, zero density estimates, and zero additive energy
estimates: a systematic approach*, arXiv `2501.16779v1` (2025).

**Current status:** research and architecture scaffold only. No theorem from
the paper is claimed formalized here yet. The neighboring Guth--Maynard and
Tao projects are completed foundations; this directory does not inherit their
completion status merely by referring to them.

## Exact intended outputs

The initial completion contract covers all results advertised by the paper as
new:

1. the four exponent pairs in `new-exp-pair`;
2. the improved Heath--Brown zero-density theorem `hb-density2`;
3. the improved Bourgain density-hypothesis bound
   `bourgain-density-improved`;
4. the eight-piece optimized Bourgain zero-density bound
   `bourgain-zero-density-optimized`; and
5. all nine clauses of the additive-energy theorem `Add-est`.

The exact statements and rational endpoints are frozen in
[`Tao-Trudgian-Yang Crosswalk.md`](Tao-Trudgian-Yang%20Crosswalk.md). A
release is not complete until the public Lean statements match those formulas,
the source-to-Lean dependency edges are proved, and every theorem passes the
project integrity and semantic audits.

## Main research finding

The live [ANTEDB repository](https://github.com/teorth/expdb) now has a real
Lean library. At commit
`088040634e8300f87e80f431d8bdc38c42cc8e11` it contains proved foundations for
cheap asymptotic notation, automatic uniformity, model phase functions,
exponential sums, the exponent-sum growth function, Euler--Maclaurin, and
Fourier/L2 estimates. It does **not** yet contain Lean modules for exponent
pairs, large-value exponents, zero-density exponents, or additive-energy
exponents.

That upstream is therefore the natural starting point, but not a complete
formalization of this paper. Its current Lean toolchain is `v4.32.0`; the
completed local Guth--Maynard foundation is on `v4.30.0`. Resolving that
compatibility boundary is Checklist item EPZAE-01 and must precede production
code.

## Layout

- `Tao-Trudgian-Yang Goal Prompt.md` -- immutable whole-project contract.
- `Tao-Trudgian-Yang Research Agenda.md` -- staged implementation plan and
  risk register.
- `Tao-Trudgian-Yang Architecture.md` -- dependency graph with checklist
  ownership.
- `Tao-Trudgian-Yang Checklist.md` -- acceptance tests for every work package.
- `Tao-Trudgian-Yang Crosswalk.md` -- paper labels, formulas, and planned Lean
  consumers.
- `Tao-Trudgian-Yang Sources.md` -- literature, repositories, and reuse survey.
- `Tao-Trudgian-Yang Reproduction Manifest.md` -- pins and verification policy.
- `Sources/` -- the primary paper, source archive, figures, and frozen ANTEDB
  snapshots.
- `Dependencies/` -- dependency decision record; no multi-gigabyte tree is
  copied here during planning.
- `Extension/` -- proposed Lean package and module layout.
- `Tools/` -- source-integrity and future build-runner notes.
- `run_tao_trudgian_yang_build.bat` -- human-facing verification runner; currently reports
  a planning-scaffold result and activates Lean build/audit gates when the
  unified package is installed.

## Recommended first implementation slice

Start with a compatibility spike, not a theorem stub:

1. select one Lean/mathlib version for both the local Guth--Maynard source and
   the ANTEDB foundations;
2. import ANTEDB's existing asymptotic and phase-function API without copying
   definitions under new names;
3. formalize the paper's `ExponentPair` predicate and the
   exponent-pair/`beta` duality interface;
4. build an exact rational certificate checker for piecewise-affine bounds;
5. certify one small convex-hull calculation before tackling any analytic
   process theorem.

This order separates exact finite optimization from the deep analytic inputs
and gives an early, auditable end-to-end artifact.

## Non-claims

- ANTEDB's Python output is discovery evidence, not Lean proof evidence.
- A checked rational inequality is not a proof that its analytic input is an
  exponent pair or a large-value theorem.
- The completed Guth--Maynard theorem does not automatically prove every
  large-value inequality used in this paper; each interface requires an exact
  source-convention bridge.
- A theorem parameterized by the desired exponent-pair, density, or energy
  conclusion is conditional and cannot satisfy the release contract.
- The source paper itself describes its computation as not formally
  certified. This project must replay every optimization through
  kernel-checked certificates.

## Repository synchronization

Use the repository-root `push_to_github.bat` only when deliberately requested.
Do not add a second synchronization workflow here. A suitable future commit
message for this scaffold is:

`plan Tao-Trudgian-Yang 2025 formalization and pin primary sources`
