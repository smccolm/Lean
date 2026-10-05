# Reproduction manifest

**PLANNING ONLY — GOAL INACTIVE — 0/20 proof gates complete.**
Prepared 5 October 2026 at checkout `baef1ac59f8ded380b91dda2b5a04a5468f798a8`; working tree was clean before setup. Changes belong to node 78 plus its category README entry. No Lean source/package/configuration change, goal activation, dependency update, commit or push is included.

## Immutable and observed inputs

- Primary edition: arXiv:2609.00537v1, submitted 2026-09-01 01:21:11 UTC, 37 PDF pages.
- Root Lean: `leanprover/lean4:v4.30.0`; Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`.
- Original source archive, seven extracted files, reference PDFs and web/API snapshots: `Sources/SHA256SUMS.txt` and PINS.
- Full node-77 inventory: 199 physical files, 87 retained; `Tools/template_inventory.json` includes exact paths/hashes.
- Node-63 `push_to_github.bat`: exact SHA-256 `9dd7c9f61aeb2704832c897475a76d471f855150ff6cde03e08cee141a090114`. Copied, not run.
- Parent `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: unchanged hashes in `Tools/scaffold.json`.
- Newer upstream observations are discovery evidence only; exact SHA/toolchain metadata in `Tools/upstream_snapshot.json`.

## Setup checks

The principal node-78 entry point is:

```powershell
cmd /c run_dhiman_kadiri_quesada_herrera_build.bat --no-pause
```

The BAT validates only the scaffold, source pins, inventory, all-open status, template/source anchors, links, unchanged root pin files and owner script. Eight source-verifier tests reject missing/changed/extra/duplicate/escaping/empty/malformed ledgers and accept the valid fixture. Any `.lean` or Lake package file is rejected in this planning mode. There is no new theorem to build or audit.

An optional replay command is `python Tools/reproduce_author_code.py`. The first research replay of unmodified AFE2 returned 0 under Python 3.13.5, NumPy 1.26.4, SciPy 1.17.1. Table 1 displays matched; nearest rounding and domain issues remain open. AFE1 was inspected but not run (Sage absent). This is computational observation, not formal certification. Exact author-code evidence is recorded in `Tools/author_code_observation.json`.

## Source inspection evidence

Primary PDF rendered and checked at printed pp.22 and 25 against TeX. The omitted n=1 and reversed E₀ branches occur in the actual PDF. All source-file bytes are preserved. Bibliography and both programs were inspected. Source issues E01–E09 and proposed contract resolutions are recorded; none is a Lean implementation.

## Final execution receipts

Final setup/foundation verifier receipts, log names and hashes are appended after execution. A historical PASS from node 77 is not evidence for node 78. A foundation PASS verifies its existing scope and does not prove any DKKH theorem.

## Future release gate

After activation: freeze accepted repairs, create the package, classify every module, build all production/regression targets, run exact source-contract tests, explicit and exhaustive transitive axiom audits, zero-warning/linter and integrity checks, verify dependency pins and run foundation/paper BATs sequentially. Record exact checkout, sources, runtime, toolchains, commands, exits, diagnostics and complete logs. Complete all twenty gates before claiming the whole-paper contract; distinguish internal completion from external review.

### Scaffold verification checkpoint — 5 October 2026

- Paper BAT returned exit 0: SCAFFOLD PASS - LEAN CONVERSION NOT STARTED. It checked 60 retained files, 25 source artifacts, seven exact extracted archive members, seven valid PDFs, 205 source-label locations and 34 existing local Markdown targets.
- All eight source-verifier fixtures passed. Ten additional isolated-copy validator checks passed: valid scaffold accepted; missing BAT, extra file, new Lean file, wrong mode, DONE gate, changed source-label index, broken link, changed parent pin and changed owner BAT rejected. Fixtures did not alter the real sources.
- git diff --check passed. Node-63 synchronization BAT remained byte-identical. Parent pin/configuration files and every existing Lean file were left unchanged.
- Raw parent hashes describe the setup bytes. Canonical-LF comparison hashes also permit Git line-ending conversion on another checkout while rejecting content drift. The copied owner BAT has -text attributes to preserve its exact original bytes.

### Final sequential receipts — 5 October 2026

1. From the root Riemann Zeta package: cmd /c run_lake_build.bat --no-pause returned **exit 0, FINAL RESULT: PASS** in development mode at the recorded dirty setup checkout. Root build: 8,857 jobs; classification: 301 root-graph modules plus two explicit regressions; transitive audit: all 14,290 discovered nonprivate project theorems, 7,636 explicitly registered declarations; publication contracts, retained regressions, integrity scans and linter gates passed. Zero project Lean warnings, tactic suggestions or linter failures; no failed stage. This confirms the existing foundation, not a DKKH theorem.

   Log: ../../logs/foundation_freeze_20261005_033026.log; SHA-256 51a6834e941ad0a428c797fa63dbd4856580efb4098eaa9ffe24a6198e56b4a1. Structured receipt: ../../logs/foundation_freeze_20261005_033026.json.

2. After foundation completion, the paper BAT was invoked by absolute path from E:/Lean, returned **exit 0, SCAFFOLD PASS - LEAN CONVERSION NOT STARTED**, and passed every source/status/coverage/link check and all eight source-verifier fixtures. This also verifies arbitrary-caller-directory operation. Unknown argument test separately returned the required exit 2.

   Log: logs/dhiman-kadiri-quesada-herrera-scaffold-20261005-033800-919.log; SHA-256 33b090e842df100a7118ba89acc72f0f64f750b938761714c5ff2dd0db8ee20a. These ignored logs remain on this workstation; the receipt records their exact identity without fabricating a release archive.

3. Unmodified AFE2 replay: exit 0, no stderr; versions/output hashes in Tools/author_code_observation.json. AFE1 Sage replay remains not run. No numerical result is counted as a proof.

All 20 DKKH gates remain OPEN. No Lean source or package was created, and no existing Lean source or dependency pin changed. No commit, staging, Git synchronization or push was performed.
