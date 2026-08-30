# Verification evidence

`scripts/verify_release.ps1` is the canonical verifier for the frozen
Guth--Maynard foundation. It produces a complete log and a JSON manifest tied
to the tested Git commit, verifier hash, contract version, toolchain, and
dependency revisions.

Local development runs write ignored evidence under `logs/`. The accepted
internal freeze evidence is a release-mode run from a clean checkout of exact
commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, published as annotated tag
`gm-foundation-freeze-v1.0.1`. This directory stores the contract-version
identifier and reproduction instructions, not a self-referential manifest that
would alter the commit it claims to describe.

The fixed paper editions, theorem-display conventions, classical citations,
ANTEDB snapshot, dependency revisions, and the boundary between internal
verification and external review are recorded in [`SOURCE_FREEZE.md`](SOURCE_FREEZE.md).

Run locally from the project directory:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify_release.ps1
```

For a release candidate, the tree must be clean:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify_release.ps1 -Mode release
```

Release mode must be run from a clean checkout of the exact candidate commit.
It classifies every `RiemannZeta/**/*.lean` file mechanically as root-graph or
explicit regression coverage, scans the full Lean tree for prohibited proof
shortcuts, builds the root, checks the five exact publication contracts, runs
both retained regressions, executes the exhaustive dependency audit, and runs
all project linters. Any Lean warning, tactic suggestion, linter finding,
unclassified file, failed output gate, or nonzero stage fails the run.

The optional CI workflow uses two `ubuntu-24.04` jobs with actions pinned to
immutable commits. The first builds the DFI-heavy prefix under an exact-SHA
cache key; the dependent job is intended to invoke the same release script and
upload a SHA-named log and JSON manifest. Runs `33258211182` and `33278864901`
both ended with external exit `143` before artifact upload. No hosted PASS or
artifact is claimed. This missing supplemental evidence does not change the
exact-SHA local verifier result, and hosted CI is not a prerequisite for the
internal foundation freeze or PostGM work.
