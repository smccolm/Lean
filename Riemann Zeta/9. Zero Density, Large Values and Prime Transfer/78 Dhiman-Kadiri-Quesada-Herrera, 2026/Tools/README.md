# Scaffold and research tooling

Current mode: **planning-only**, 0/20 proof gates. Use `cmd /c ..\run_dhiman_kadiri_quesada_herrera_build.bat --no-pause` from this directory. The wrapper works from any caller directory and rejects unknown arguments. It checks the source ledger, exhaustive scaffold file list, no-Lean/no-package boundary, required inactive-goal markers, all twenty OPEN statuses in JSON/checklist/Mermaid, exact label index, local Markdown targets, parent file hashes/pins and node-63 BAT identity. It runs eight source-verifier negative/positive tests and writes its own timestamped log. It does not fetch, activate a goal, replay author programs, run Lean or invoke Git synchronization.

`verify_sources.ps1` and `test_source_verifier.ps1` were copied verbatim from node 77. `verify_scaffold.py` uses Python standard library only. PowerShell runner propagates nonzero Python/stage status and ends with `SCAFFOLD PASS — LEAN CONVERSION NOT STARTED` only on success. Logs are ignored generated files; the complete retained inventory lives in `scaffold.json`.

`reproduce_author_code.py` is a separate optional numerical replay and records its actual runtime versions; it is not a proof gate. `source_labels.json` records active original-TeX labels and line numbers. `local_reuse_inventory.json` records selected existing theorem signatures and file hashes, not a promise to install their imports. `template_inventory.json` accounts for every file in node 77, including classified generated state. `upstream_snapshot.json` records live external observations without changing dependency pins.

The exact self-contained `../push_to_github.bat` comes from node 63. No `push_to_github.ps1` helper is required or substituted. Build/scaffold tools never call this owner interface.

The frozen owner BAT is marked `-text` so Git preserves its original LF bytes.
Parent configuration and the external node-63 reference also have canonical-LF
comparison hashes to tolerate Git checkout line-ending conversion. Their
non-line-ending content, package revisions and the archived BAT bytes remain checked.

When conversion is explicitly activated, replace the inactive scaffold mode with actual package coverage/build/audit/semantic-regression checks; update every status document in the same change. No excluded Lean files, linter suppression or success labels masking missing proof work are allowed. Run foundation and paper proof verifiers sequentially, preserve all prior accepted contracts and report diagnostics accurately.
