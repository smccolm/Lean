# Prime Shell

This directory is the isolated planning and future implementation area for the Prime Shell research program.

## Boundary

- Frozen GM source: commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`.
- Zeta23 source selected for reproduction: Anthropic `formal-math` tag `v1.0`, commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
- The two projects have different toolchains. Zeta23 must first be reproduced as its own Lake project. No Zeta23 import is to be added to `RiemannZeta.lean`, and no frozen GM Lean file is to be edited, until the analytic feasibility gates pass and an explicit integration decision is recorded.
- This directory currently contains research documents only. It proves no new mathematical result.

## Program objective

Determine whether unconditional prime information beyond the classical support-one scale can be consumed by the exact Alpoge-Furman/Zeta23 prime-side trace calculation, initially through a disconnected high-frequency shell. The first candidate input is the Guth-Maynard almost-all short-interval prime theorem; the Matomaki-Radziwill-Tao almost-all shifted von Mangoldt theorem is the fallback.

The objective is not described as a route to RH. The first deliverable is a falsifiable kernel-compatibility verdict.

## Documents

- [Prime Shell Architecture](Prime%20Shell%20Architecture.md): dependency graph and numbered execution steps.
- [Prime Shell Research Agenda](Prime%20Shell%20Research%20Agenda.md): corrected mathematical program, source analysis, scale ledger, and kill rules.
- [Prime Shell Source Ledger](Prime%20Shell%20Sources.md): pinned repositories, primary papers, and the precise use of each source.
- [Prime Shell Shitlist](Prime%20Shell%20Shitlist.md): exhaustive local acceptance checklist.
- [Prime Shell Goal Prompt](Prime%20Shell%20Goal%20Prompt.md): exact bounded prompt for the next persistent goal.
- `push_to_github.bat`: stages the repository, commits pending changes, and pushes `HEAD` directly to `origin/main`; it does not run builds or CI.

Update the default commit message near the top of the local push script periodically so it accurately describes the work being pushed. The script also accepts a commit message as its first command-line argument.

The local Shitlist is authoritative only for this subproject. It does not alter the completed theorem statuses in the frozen GM proof architecture.
