# Tao--Trudgian--Yang 2025 formalization

This directory is the planning and source-control baseline for a Lean 4
formalization of Terence Tao, Tim Trudgian, and Andrew Yang,
*New exponent pairs, zero density estimates, and zero additive energy
estimates: a systematic approach*, arXiv `2501.16779v1` (2025).

**Current status:** the unified package, audited dependency bridges, exact
certificate kernel, analytic exponent-pair semantics, exact Guth--Maynard
large-value bridge, and additive-energy foundations are installed and pass
the principal runner. The energy layer includes the extended-real general
and zeta comparisons `2LV ≤ LV* ≤ 3LV` and the corresponding necessary region
constraints. No advertised theorem from the paper is claimed
formalized yet; the four exponent pairs, density bounds, and energy bounds
still require their analytic derivations.

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

That upstream is therefore a foundation, not a complete formalization of this
paper. Its upstream Lean toolchain is `v4.32.0`; the completed local
Guth--Maynard foundation is on `v4.30.0`. EPZAE-01 resolved that boundary by
compiling an attributed, hash-pinned subset of ANTEDB on the local Lean 4.30
graph.

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
- `Dependencies/` -- attributed frozen ANTEDB compatibility subset and
  dependency decision record.
- `Extension/` -- unified Lean package and production modules.
- `Tools/` -- source-integrity, build, regression, and audit implementation.
- `run_tao_trudgian_yang_build.bat` -- principal human-facing verification
  runner; it builds the unified package and runs every currently installed
  integrity, regression, and audit gate.

## Current implementation frontier

EPZAE-00--05, EPZAE-07--08, EPZAE-16--17, EPZAE-20, EPZAE-22--23,
EPZAE-25, and EPZAE-31 are complete. The next analytic
frontier is EPZAE-09: the remaining endpoint/reflection and converse direction
of beta/exponent-pair duality.
The initial deterministic certificate extractor is in the principal runner;
EPZAE-06 remains open until it reproduces every optimization witness rather
than only the four output coordinates.

## Non-claims

- ANTEDB's Python output is discovery evidence, not Lean proof evidence.
- A checked rational inequality is not a proof that its analytic input is an
  exponent pair or a large-value theorem.
- The completed Guth--Maynard theorem supplies `guth-maynard-lvt` only through
  the explicit, kernel-checked support, reflection, phase, coefficient, and
  epsilon-loss conversions in `GuthMaynardBridge.lean`; it does not
  automatically prove the other large-value inequalities used in the paper.
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
