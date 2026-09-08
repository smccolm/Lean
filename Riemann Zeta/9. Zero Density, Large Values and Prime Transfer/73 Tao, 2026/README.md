# Tao 2026 formalization

This directory is the active formalization project for Terence Tao,
*Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`. The paper and its TeX source are pinned under `Sources/`.

**Status:** initial definitions milestone. No theorem from the paper has been
proved or claimed here. The isolated `Extension/` package now contains the
compiled arithmetic-anatomy, interval, counting, and asymptotic-language
definitions required to state the source results.

Node 73 keeps the human-readable location assigned by the RH Map. An initial
source and local-library survey confirms that node 74 contains the intended
Guth--Maynard-driven almost-all short-interval PNT input. The exact node-73
snapshot and the bridge to Tao's exceptional-measure formulation remain to be
frozen and proved.

## Layout

- `Sources/`: exact paper artifacts, version pins, provenance, and hashes.
- `Dependencies/`: reserved for deliberate, immutable dependency snapshots.
  It is intentionally empty of code until the required node-71/node-74
  theorem boundary has been established.
- `Extension/`: isolated Lean package named `Tao2026`, pinned to the exact
  Mathlib revision used by node 74.
- `Tools/`: evolving warning-failing project verification. It is not yet the
  final proof-release verifier.

## Current verification

From this directory, run:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The runner checks source hashes, the raw Mermaid contract, Lean and Mathlib
pins, direct production-root coverage, forbidden proof shortcuts, and the
warning-free Lake build. Its current success certifies only the initial
definitions milestone.

## Project-control documents

The node follows the useful role separation established in node 74:

- `README.md`: public status, layout, and entry points.
- `Tao Architecture.md`: raw Mermaid planning dashboard; no Markdown wrapper.
- `Tao Checklist.md`: detailed readiness and future completion ledger.
- `Tao Goal Prompt.md`: activation contract for the future implementation
  agent.
- `Tao Research Agenda.md`: source-first sequencing and scope controls.
- `Tao Crosswalk.md`: active paper-to-Lean mapping and semantic-gap ledger.
- `Tao Sources.md` and `Sources/`: source policy, artifacts, pins, and hashes.
- `Tao Reproduction Manifest.md`: what can truthfully be reproduced now.

## Next legitimate step

Turn the initial source study recorded in `Tao Goal Prompt.md` and
`Tao Architecture.md` into authoritative row-by-row entries in
`Tao Crosswalk.md`, then freeze the exact dependency snapshots and Lean
statement contracts before starting proof modules.

## Deliberate non-claims

This scaffold does not claim a proof of any result in the paper, a formal
connection to nodes 71 or 74, publication readiness, external review, or a
route to the Riemann Hypothesis.

## Repository synchronization

`push_to_github.bat` is the existing owner-operated repository synchronization
script. It is not called by the build or scaffold verifier.
