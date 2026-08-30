# Prime Shell

This directory is the isolated research and implementation area for the Prime Shell program.

## Boundary

- Frozen GM source: commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`.
- Zeta23 source selected for reproduction: Anthropic `formal-math` tag `v1.0`, commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
- The two projects have different toolchains. Zeta23 must first be reproduced as its own Lake project. No Zeta23 import is to be added to `RiemannZeta.lean`, and no frozen GM Lean file is to be edited, until the analytic feasibility gates pass and an explicit integration decision is recorded.
- `Extension/` is a separately pinned Zeta23-compatible Lake project. Its manifest fetches the exact Zeta23 commit into the ignored `.lake` dependency cache. It does not import the frozen GM project and is not imported by `RiemannZeta.lean`.

## Program objective

Determine whether unconditional prime information beyond the classical support-one scale can be consumed by the exact Alpoge-Furman/Zeta23 prime-side trace calculation, initially through a disconnected high-frequency shell. The first candidate input is the Guth-Maynard almost-all short-interval prime theorem; the Matomaki-Radziwill-Tao almost-all shifted von Mangoldt theorem is the fallback.

The objective is not described as a route to RH. Phase I is complete with a negative kernel-compatibility verdict for the proposed **collapsed GM-prefix interface**. This does not prove a new zero theorem and does not decide the later disconnected-shell question.

The precise result is narrower than “GM cannot help.” The literal dyadic kernel depends on both the base point and the shift. A cumulative estimate after summing away the base point controls the anchored scalar part by Abel summation, but it does not control the separately exposed two-variable variation remainder. The extension proves the corresponding finite information-loss theorem and states the exact stronger remainder input that would suffice.

## Documents

- [Prime Shell Architecture](Prime%20Shell%20Architecture.md): dependency graph and numbered execution steps.
- [Prime Shell Research Agenda](Prime%20Shell%20Research%20Agenda.md): corrected mathematical program, source analysis, scale ledger, and kill rules.
- [Prime Shell Source Ledger](Prime%20Shell%20Sources.md): pinned repositories, primary papers, and the precise use of each source.
- [Prime Shell Shitlist](Prime%20Shell%20Shitlist.md): exhaustive local acceptance checklist.
- [Prime Shell Goal Prompt](Prime%20Shell%20Goal%20Prompt.md): exact bounded prompt for the next persistent goal.
- [Prime Shell Phase I Report](Prime%20Shell%20Phase%20I%20Report.md): pins, reproduction results, source crosswalk, theorem inventory, F1 verdict, and nonclaims.
- `push_to_github.bat`: stages the repository, commits pending changes, and pushes `HEAD` directly to `origin/main`; it does not run builds or CI.

Supply an explicit, current commit message when running the push script. Agents do not run it as part of verification.

The local Shitlist is authoritative only for this subproject. It does not alter the completed theorem statuses in the frozen GM proof architecture.
