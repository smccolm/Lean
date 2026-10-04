# Reproduction manifest

4 October 2026. **PLANNING ONLY; Lean conversion and proof goal not started.** This manifest separates setup verification from future proof evidence.

## Baseline and immutable inputs

Template/reference checkout: `56fcb266457d6097f87e38ca7d45eef3231cc145`. The working tree was clean before this setup. Node 63 was inventoried, not modified or rebuilt as part of node-77 implementation. The parent package files and all existing Lean source remain unchanged.

The candidate foundation baseline is Lean `leanprover/lean4:v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. These existing pins are checked by the scaffold runner; no claim is made that the incompatible newer upstream observations are installed.

Nine archived source artifacts, versions and rights notices are enumerated in [Sources/PINS.md](Sources/PINS.md) and [SHA256SUMS.txt](Sources/SHA256SUMS.txt). Original source extraction used `tar -tf` to inspect the archive, then `tar -xf` into the dedicated source folder. No extraction or compilation of third-party code is performed by the verifier.

## Setup commands

From this paper directory:

```powershell
cmd /c run_dong_wang_wang_zhang_build.bat --no-pause
powershell.exe -NoProfile -ExecutionPolicy Bypass -File Tools/test_source_verifier.ps1
```

The paper BAT must work from an arbitrary caller directory as well. Unsupported arguments must exit 2, not report success. It uses process-local execution-policy bypass, not a machine-wide policy change. Every source check reads UTF-8 explicitly.

From the `Riemann Zeta/` root, the existing foundation gate remains:

```powershell
cmd /c run_lake_build.bat --no-pause
```

Run foundation and paper evaluation sequentially. A foundation PASS tests its existing scope and does not establish either new theorem. The scaffold runner never starts a Lean build itself.

## Initial setup verification record (35-file scaffold)

Executed on 4 October 2026, local Pacific time, on the deliberately dirty setup worktree based on the reference commit above:

| Check | Actual result |
|---|---|
| Paper BAT invoked by full path from `E:/Lean`, with `--no-pause` | **SCAFFOLD PASS**, exit 0: 35 files, nine complete source pins, baseline parent pins, twenty OPEN gates, ten frozen source result labels, 34 local links. No Lake invocation. |
| Source-verifier fixture suite | **8/8 PASS**, process exit 0: valid fixture accepted; changed, missing, extra, duplicate, nonlocal, empty and malformed inputs rejected. No frozen source modified. |
| Paper BAT `--invalid` and `--no-pause unexpected` | Both returned the expected child exit **2**, with usage text and no success claim. |
| Deliberately unclassified temporary marker | Paper BAT visibly reported **SCAFFOLD FAIL**, child exit **1**. Only the test's own marker was then removed; actual sources and documents were untouched. This is expected negative-test evidence, not a remaining failure. |
| Foundation `cmd /c run_lake_build.bat --no-pause` | **PASS**, exit 0: 8,857 build jobs; 301 root modules and two retained regressions; 7,636 explicit / 14,290 discovered-theorem audits; exact publication/output gates and 16 linters; zero Lean errors, warnings, tactic suggestions or linter findings. |
| Existing-source check | No diff in node 63, any existing Lean source, or parent package/toolchain/manifest. |
| Repository-wide lexical integrity checks, excluding generated `.lake`/logs | No `sorry`/`admit`/`sorryAx` or unsafe-bypass matches. Sixteen `axiom/constant` lexical matches were fourteen comment lines and two existing rational structure fields, not postulates; the canonical parser-aware gate also passed. |
| New PowerShell scripts | All three parsed with zero syntax errors. |

Initial scaffold log, relative to this directory:
`logs/dong-wang-wang-zhang-scaffold-20261004-111446-271.log`.
SHA-256: `e20958834c2d631b00e6195604041e35d9f4f2c9b992da8180420857bd712057`.

After foundation evaluation, expected failure testing, fixture removal and
documentation synchronization, the paper-directory command passed again,
exit 0, with the same 35-file / nine-pin / 34-link counts:
`logs/dong-wang-wang-zhang-scaffold-20261004-111904-312.log`, SHA-256
`a531ca422d0bbf8bfec86e7643215b0224cec3db334adf424157b20ea670480a`.
The receipt text itself was appended afterward; no source pin or runner changed.
`git diff --check` also exited 0, and new authored text had no trailing-whitespace findings.

Foundation evidence, relative to `Riemann Zeta/`:
`logs/foundation_freeze_20261004_111449.log`, SHA-256
`1b1a7b50a5a925faf2e2e66c34ddcd26976f23107358166f719cf794cb872f2e`;
`logs/foundation_freeze_20261004_111449.json`, SHA-256
`af2eb0a0a8d66405aaaba74b27cc38f54ea66454475cf96951160496d0479114`.
The receipt explicitly records a **DIRTY development worktree**, not a clean-release revision.

Expected inventory-rejection log:
`logs/dong-wang-wang-zhang-scaffold-20261004-111749-561.log`.
Fixture outputs are retained under `logs/source-verifier-tests-20261004-111447-233/`.
Generated logs/fixtures are ignored, not tracked source artifacts. Git emitted ordinary LF-to-CRLF working-copy notices during diff inspection; those are not Lean diagnostics or failed proof gates.

These results validate setup tooling and the unchanged existing foundation only. **Node 77 remains 0/20; no paper theorem, Lean package or conversion goal has been started.**

## Folder-local synchronization follow-up (37-file scaffold)

4 October 2026: added the initially omitted `push_to_github.bat` and its
`Tools/push_to_github.ps1` implementation. Updated README, Tools README, template
mapping, inactive goal prompt and exhaustive file inventory. Re-enumerated all
1,993 tracked node-63 paths, including all fifteen root interfaces/documents and
nine Tools files: no other missing planning role was found. The deliberate
non-copies/deferred proof infrastructure are listed in Template Inventory.

The owner-only synchronization script was **not executed**. Static review checked
root resolution/entry, main-branch guard, explicit or prompted nonblank commit
message, repository-wide staging, distinct staged-diff exit handling, checked
commit/push exits, and absence of force-push, automatic rebase, tag push or a
hard-coded message. All four PowerShell files parsed with zero syntax errors;
the BAT's script-relative dispatch and exit propagation were checked statically.
This is not a claim of a successful live Git synchronization.

The paper BAT was rerun by full path from `E:/Lean`: **SCAFFOLD PASS**, exit 0,
37 files, nine source pins, twenty OPEN gates, ten source labels and 34 local
links. Log: `logs/dong-wang-wang-zhang-scaffold-20261004-112731-408.log`;
SHA-256: `54202b4dfea6433e8f84f069c190b26fd025e919bbee8f0cd12e69358bd80c17`.
Source-verifier fixture tests again passed **8/8**, exit 0, under
`logs/source-verifier-tests-20261004-112732-352/`.
Authored-text whitespace checks passed. Repository-wide lexical scans again
found no placeholder or unsafe-bypass matches; the sixteen postulate-pattern
matches remained the same comments and rational structure fields described
above. No existing Lean, parent package/toolchain/manifest or node-63 file changed.

Fresh foundation verification, `cmd /c run_lake_build.bat --no-pause`, also
returned **PASS**, exit 0: 8,857 build jobs, complete production/regression
coverage, all 14,290 discovered-theorem dependency audits, exact publication
and output gates, and all sixteen linters passed with zero Lean warnings,
errors, tactic suggestions or linter findings. No failed stage remained.
Evidence relative to `Riemann Zeta/`:
`logs/foundation_freeze_20261004_112745.log`, SHA-256
`dbd6227cd7a50e07d0b49944364c794babff80a3110728b68e2b9ac784ace1cc`;
`logs/foundation_freeze_20261004_112745.json`, SHA-256
`48953ed08d00f9adfd0a4ec10b9d3d66278029b90401775d3a5c41d37d279632`.
This remains a dirty development-checkout receipt for the existing foundation,
not node-77 proof evidence. `git diff --check` exited 0; its only notices were
the existing LF-to-CRLF working-copy notices described in the initial record.

No staging, commit, push, recovery-record maintenance or goal activation occurred.
The project remains **planning only, 0/20 proof gates complete**.

## Future proof-mode evidence requirements

After explicit activation, record exact repository revision and dirty/clean status, toolchain/manifest/source hashes, all module classifications, actual imports, explicit and exhaustive transitive audits, semantic/exact-type regressions, full BAT commands, stage results, exit codes, logs and hashes. No copied historical receipt, focused build alone or scaffold PASS can satisfy DWWZ-18/19.

Both public theorem statements and all consuming bridges must pass semantic review in addition to Lean's dependency checks. Independent external review and publication remain distinct. No recovery-record file is required or maintained.
