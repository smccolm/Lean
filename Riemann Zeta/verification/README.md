# Verification evidence

`scripts/verify_release.ps1` is the canonical verifier for the frozen
Guth--Maynard foundation. It produces a complete log and a JSON manifest tied
to the tested Git commit, verifier hash, contract version, toolchain, and
dependency revisions.

Local development runs write ignored evidence under `logs/`. Release evidence
is produced by CI from a clean checkout of an exact commit and uploaded as an
artifact named with that commit SHA. This directory stores the contract-version
identifier and the reproduction instructions, not a self-referential manifest
that would alter the commit it claims to describe.

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

The CI workflow uses two `ubuntu-24.04` jobs with actions pinned to immutable
commits. The first builds the DFI-heavy prefix and saves `.lake` under the
exact commit-SHA cache key. The dependent job restores that exact cache and
invokes this same, unchanged release script; it then uploads the log and JSON
manifest under an artifact name containing `${{ github.sha }}`. This split is
an execution-resource measure, not a reduction of the verifier's stages. A
local tag is not evidence that CI ran; the SHA-bound CI artifact and successful
workflow must be inspected after the candidate is pushed. The initial remote
attempt of 29 August 2026 ended with runner exit `143` before artifact upload
and is not release evidence.
