# Gafni-Tao exceptional intervals

Status: architecture and research contract only. No Gafni-Tao theorem is yet
claimed in Lean.

This directory is the isolated post-Guth-Maynard program for formalizing Ayla
Gafni and Terence Tao's paper *On the number of exceptional intervals to the
prime number theorem in short intervals* (arXiv:2505.24017v1).

The intended mathematical output is the paper's exact zero-density-to-
exceptional-set transfer, including its fourth-moment refinement, followed by
the native consequences obtained from the frozen Guth-Maynard zero-density
theorem and the required zero-additive-energy estimates. It is not a path to
the Riemann Hypothesis, and no new theorem is claimed merely because this plan
exists.

## Isolation boundary

- Frozen foundation commit: `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`
- Frozen foundation tag: `gm-foundation-freeze-v1.0.1`
- Foundation Lean version: `v4.30.0`
- Current planning commit when this directory was created:
  `3e1eff79810846335386c2f4bc0ec1957272e301`
- All future Lean source for this program must live below
  `PostGM/GafniTao/Extension/` in a separate Lake package pinned to the frozen
  foundation.
- Do not edit `RiemannZeta/`, weaken its public contracts, or import the
  experiment into `RiemannZeta.lean`.

## Documents

- [Gafni-Tao Sources.md](Gafni-Tao%20Sources.md): authoritative sources,
  reusable Lean infrastructure, and gaps found by research.
- [Gafni-Tao Architecture.md](Gafni-Tao%20Architecture.md): numbered Mermaid
  dependency graph and proposed module layout.
- [Gafni-Tao Research Agenda.md](Gafni-Tao%20Research%20Agenda.md): exact
  mathematical route and execution order.
- [Gafni-Tao Shitlist.md](Gafni-Tao%20Shitlist.md): exhaustive acceptance
  checklist.
- [Gafni-Tao Goal Prompt.md](Gafni-Tao%20Goal%20Prompt.md): copyable persistent
  goal for the implementation turn.
- `push_to_github.bat`: deliberately simple owner-operated stage, commit, and
  push script. It does not run builds or CI.

## Claim discipline

The principal source theorem is stronger than the already frozen
Guth-Maynard density bound. A clean implementation must still formalize:

1. the exact exceptional set and its Lebesgue measure exponent;
2. the truncated explicit formula with the paper's endpoints and errors;
3. the Vinogradov-Korobov and near-one zero-density input used in Lemma 2.1;
4. the paper's `L-infinity`, `L2`, and `L4` estimates;
5. the multiplicity-weighted four-zero quantity `N*` and its exponent `A*`;
6. the finite-strip, Markov, and limiting assembly of Theorems 1.2 and 1.3;
7. the native Guth-Maynard and Heath-Brown numerical consumers.

Until the exact public theorems, audits, and isolated runner pass, the correct
status is **planned**, not **formalized**.

## Commit-message practice

Do not hard-code a historical commit message into the push script. After each
substantive milestone, update the `Suggested commit message` line in the
research agenda and pass that text to `push_to_github.bat`, for example:

```bat
push_to_github.bat "PostGM Gafni-Tao: establish explicit-formula bridge"
```

The project owner runs the script; agents must not run it unless separately
instructed.
