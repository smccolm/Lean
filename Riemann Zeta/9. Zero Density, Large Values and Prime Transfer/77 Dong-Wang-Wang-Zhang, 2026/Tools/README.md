# Scaffold tooling

Run `cmd /c ..\run_dong_wang_wang_zhang_build.bat --no-pause` from this folder. The BAT resolves its own directory, returns the PowerShell exit code, rejects unknown arguments, and pauses in double-click mode.

Current scope: **offline planning/scaffold verification**, not a Lean build. `scaffold.json` is the exhaustive file inventory and parent-pin baseline. `verify_sources.ps1` rejects missing, changed, extra, duplicate, malformed, empty and nonlocal artifact pins. The main PowerShell runner additionally checks no Lean/package files were accidentally created, status consistency, required inactive-prompt markers, primary result labels and local Markdown link targets. Logs are generated under `../logs/`.

`upstream_snapshot.json` records external observations, not installed dependencies. Verification performs no Python replay, certificate generation, source download, telemetry, recovery-record maintenance, commit or push operation.

`push_to_github.ps1` implements the separate folder-local `../push_to_github.bat` owner interface. It accepts a positional commit message (otherwise prompts) and optional `-NoPause`, enters the resolved Git root, requires branch `main`, rejects an empty/whitespace message before staging, runs repository-wide `git add -A`, commits only when the staged diff has changes, and pushes `origin main`. All Git exit codes are checked, including the distinct diff outcomes 0/1/error. There is no automatic pull/rebase, force-push, tag push or default commit message. Normal double-click use pauses on completion or failure. Agents must not execute it without separate explicit instruction. Scaffold verification checks that these files exist; it never executes synchronization.

`test_source_verifier.ps1` runs isolated generated-fixture regressions for source-pin validation; it never edits the frozen sources. These are tooling tests, not mathematical regressions.

Upon later authorized conversion, upgrade this same paper BAT and runner to complete package build/coverage, axiom audit, semantic regression and zero-Lean-diagnostic gates. Update the inventory and mode explicitly. Keep the foundation BAT intact and run both interfaces sequentially after relevant changes. Until that upgrade, the only valid success label is **SCAFFOLD PASS — NOT A LEAN PROOF PASS**.
