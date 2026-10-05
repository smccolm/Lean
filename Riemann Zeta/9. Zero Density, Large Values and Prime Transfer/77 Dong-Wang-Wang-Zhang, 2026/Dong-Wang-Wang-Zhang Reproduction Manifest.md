# Reproduction manifest

5 October 2026. **INTERNAL PROJECT COMPLETE; 20/20 accepted gates.** Both frozen main contracts and their analytic inputs are kernel-checked, integrated and audited. The sequential mathematical acceptance checkpoint below passed with zero Lean diagnostics. Final project-complete-mode verification also passed after status/tooling synchronization. Historical receipts retain their original scope and status; none is retroactively promoted.

## Documentation consistency audit — 5 October 2026

Reviewed all sixteen node-77 Markdown documents, the root and corridor README
references, the stable-node note, source/dependency ledgers, package metadata,
both BAT interfaces and their helpers. This is a documentation-consistency
review against the existing Lean consumers and frozen TeX, not a new literature
survey or independent mathematical review. The 4 October external snapshot
remains explicitly dated; external URLs were not re-fetched.

Corrected the corridor's stale 7/20/open-theorem summary, the agenda's pending
acceptance wording, module-versus-namespace theorem references, the Lemma 2.2
consumer location, and the selected-versus-historical reuse descriptions.
The architecture now shows conjugation feeding weighted forcing, the proved
power-sum/transform input feeding the Gaussian identity, and the zero-sum upper
bound feeding the later near/far count rather than weighted forcing. README
links lead directly to both public theorem files. The checklist explains the
accepted Mellin/Fubini alternative without changing its original acceptance
rows. Historical receipts, frozen specifications and scoped node-73 survey
findings remain distinct from current status.

Read-only checks passed: all 103 dependency/source-code hash entries, all 93
previously recorded evidence-file hash entries, the three activation-package
hashes, the 44-module README inventory and the 135 regression declarations.
All 95 local links across the paper/root/corridor READMEs resolve. The paper
BAT separately checks every local Markdown link in this node (36 after adding
the two public theorem links). All four PowerShell helpers parse. The owner
synchronization interface was inspected, not executed.

Checkout remains `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, branch `main`,
DIRTY, with the unchanged Lean/Mathlib/PNT pins. The commands below used
process-local `ELAN_HOME=C:/Users/Naraphim/.elan`, ran sequentially, and had
no intervening source, tooling or documentation edits:

- Foundation, from `Riemann Zeta/`:
  `cmd /c run_lake_build.bat --no-pause` — **PASS**, exit 0.
  All 8,857 jobs, 301 production modules and two regressions, publication
  contracts, 7,636 explicit / 14,290 discovered theorem audits, repository
  integrity scans and sixteen linters passed with zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261005_023639.log`, SHA-256
  `239026cc969f864c46f4417249201c5b9f8e2d773a26b028f8e205734b404c4f`;
  JSON `../../logs/foundation_freeze_20261005_023639.json`, SHA-256
  `3a7b1084442389a41aa962ab7eb3999e97a59902b6ae28c95e9eaf8d15ed9297`.
- Paper BAT, invoked by full path from `E:/Lean` with `--no-pause`:
  **PROOF PASS - BOTH FROZEN MAIN CONTRACTS VERIFIED; 20/20 GATES**, exit 0.
  All 87 classified files, 44 production and two verification modules,
  3,872 jobs, 135 regressions, 1,149 discovered project theorems, 677 required
  consumers, nine source pins, ten source labels and 36 local links passed.
  Sixteen linters checked 749 declarations plus 452 generated declarations;
  zero Lean errors, warnings, tactic suggestions or linter findings remain.
  Log `logs/dong-wang-wang-zhang-build-20261005-024228-912.log`, SHA-256
  `de66f1a525f20464e295141a43726d82a325177536fc3793e1d3a56d32720b06`.

All 58 proof/package/tooling hashes still match
`logs/proof-inputs-20261005-003207-332.json`, before and after these runs.
The Source Contract document and all twenty acceptance rows are unchanged
by this audit. No Lean source, script, pin, frozen source artifact, foundation
or other completed node was edited. No failed verification stage remains.
An initial direct PowerShell source-verifier invocation was blocked by the
host execution policy; the BAT's documented process-local bypass then ran
that verifier successfully, without changing machine policy.
`git diff --check` passed. Only this receipt was appended after the checks;
no recovery-record maintenance, staging, commit, pull or push occurred.

## Final release-mode verification — 5 October 2026

The synchronized `project-complete` checkout passed the two BATs again,
**sequentially**, with no edits during either run. Same HEAD, DIRTY status,
toolchain and dependency pins as the mathematical checkpoint below;
`ELAN_HOME=C:/Users/Naraphim/.elan` was explicit for both commands.

- Foundation, from `Riemann Zeta/`:
  `cmd /c run_lake_build.bat --no-pause` — **PASS**, exit 0.
  Full 8,857-job / 301-production-module / two-regression scope,
  7,636 explicit and 14,290 discovered theorem audits, exact publication
  and output checks, all sixteen linters; zero Lean errors, warnings,
  tactic suggestions or linter findings.
  Log `../../logs/foundation_freeze_20261005_002856.log`,
  SHA-256 `9b4be6dc40b9dedf759fe7ed0fb9576d6ca33c17587dfe5f2997b8b88769fb25`;
  JSON `../../logs/foundation_freeze_20261005_002856.json`,
  SHA-256 `57774cb092ef0f70db4a7403eb9276a583a8d59e39fb8217173803f66f808489`.
- Paper, invoked by full path from `E:/Lean` with `--no-pause`:
  **PROOF PASS - BOTH FROZEN MAIN CONTRACTS VERIFIED; 20/20 GATES**,
  exit 0. All 87 classified files, 44 production and two verification
  modules, 3,872 jobs, 135 semantic regressions, 1,149 discovered
  project theorems and 677 required audit consumers passed.
  All sixteen linters passed (749 declarations plus 452 generated).
  Nine source pins, 34 local links and all twenty status checks passed.
  Zero Lean errors, warnings, tactic suggestions or linter findings;
  no failed stage remains.
  Log `logs/dong-wang-wang-zhang-build-20261005-003207-332.log`,
  SHA-256 `f7ddc24e8cbaafa6b9059e2b63ae61b0f445da26e36455ac829a4e0b3b4142c4`.

All 58 proof/package/tooling input hashes were compared before and after
this final verification and were identical. The exact byte-hash list is
`logs/proof-inputs-20261005-003207-332.json`,
SHA-256 `5afe510e11905769892097aba1b246da66fa6764d7b3203254bd41dfa649d8ff`.
This generated evidence is not a clean-commit claim or a source archive.

The goal is internally complete. The original end statements, source pins,
existing foundations and node-63 counterexamples are preserved.
Node 73 was inspected with the scoped outcomes recorded in Crosswalk;
no node-73 import was needed. Owner synchronization remains unexecuted.
No staging, commit, pull, push or recovery-record operation occurred.
At this checkpoint, the only post-verification edit was this receipt/status
bookkeeping; no proof, package pin, runner, gate status or owner script changed.
Later documentation-only checks are recorded separately.
`git diff --check` passed (ordinary Git line-ending notices only).

## Complete mathematical acceptance checkpoint — 5 October 2026

All twenty original gates are accepted after exact consumer review and the
sequential checks below. No frozen mathematical end statement or source byte
changed. The six final production modules prove the linked local-window scale,
small-range contradiction, finite derivative prefixes, actual all-large-x
estimate and exact T2. Both main theorem types are explicit regression consumers.
The canonical source objects are the positive-index finite sum and the actual
xi divisor with analytic zeta multiplicity, proved finite in the relevant regions.

Checkout: `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, branch `main`,
**DIRTY development worktree**, not a clean committed release.
Lean `leanprover/lean4:v4.30.0`; Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; PNT+
`4ecb950126c4290293c5662dfe0e884123171df5`, unchanged.
Commands used explicit process-local
`ELAN_HOME=C:/Users/Naraphim/.elan`.

1. From `Riemann Zeta/`: `cmd /c run_lake_build.bat --no-pause`:
   **PASS**, exit 0, 8,857 jobs, 301 production modules and two retained
   regressions; 7,636 explicit and 14,290 discovered theorem audits;
   exact publication/output gates and all sixteen linters.
   Zero Lean warnings, errors, tactic suggestions or linter findings.
   Log `../../logs/foundation_freeze_20261005_001757.log`,
   SHA-256 `0c9bb00985cbf13be530edfe18bab46a2bf92a1a163a630dbf379621507fe43a`;
   JSON `../../logs/foundation_freeze_20261005_001757.json`,
   SHA-256 `062f11831794caf8a9297d68fdcbda4ebf9480ff8445e21ccbc43c033939bb9e`.
2. After foundation completion, invoked the paper BAT by full path from
   `E:/Lean` with `--no-pause`: **DEVELOPMENT PASS — BOTH MAIN
   CONTRACTS VERIFIED; RELEASE GATES OPEN**, exit 0.
   Covered 87 classified files, 44 production modules, both verification
   modules, 3,872 jobs, 135 semantic regressions, 1,149 discovered theorem
   declarations and 677 required consumers. All sixteen linters passed:
   749 declarations plus 452 automatically generated ones, zero findings.
   Nine source pins and 34 local links passed.
   Log `logs/dong-wang-wang-zhang-build-20261005-002122-324.log`,
   SHA-256 `b0745dba7b799eac1273cb32a23a9ba5287cfb8df5a1f21198833e061d0eec1b`.

No file edits occurred during these two runs. The status check saw the
pre-acceptance 13/20 state; the final seven gates were accepted afterward on
their unchanged tests, with the exact semantic record in Checklist/Crosswalk.
Only `propext`, `Classical.choice`, `Quot.sound` are permitted logical
dependencies; no project postulate or proof placeholder was found.

The source-verifier fixture suite passed 8/8, exit 0, under
`logs/source-verifier-tests-20261005-001733-656/`. Invalid and extra BAT
arguments returned expected child exit 2. Repository-wide lexical scans found
no admitted/unsafe proof words; the sixteen postulate-pattern matches were
the previously reviewed comments and two rational structure fields, not
postulates. `git diff --check` passed; Git's LF-to-CRLF notices are not
Lean diagnostics. Parent package files and nodes 63/71/73/74 had no diff.

Post-checkpoint maintenance changes: synchronized all current statuses to
20/20 and selected `project-complete` mode, whose separate final receipt
must be recorded after verification. The owner BAT's existing rebase behavior
is preserved through the checked helper's `-RebaseBeforePush` switch,
adding main-branch/whitespace-message guards, distinct diff error handling and
checked root entry/native exits. All four PowerShell scripts parse cleanly.
This is static tooling verification only: no owner synchronization script,
staging, commit, pull, push or recovery-record maintenance was executed.
Historical no-rebase template receipts describe their then-current scripts,
not the present owner-selected workflow.

## Historical setup baseline and immutable inputs

Template/reference checkout: `56fcb266457d6097f87e38ca7d45eef3231cc145`. The working tree was clean before this setup. Node 63 was inventoried, not modified or rebuilt as part of node-77 implementation. The parent package files and all existing Lean source remain unchanged.

The candidate foundation baseline is Lean `leanprover/lean4:v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. These existing pins are checked by the scaffold runner; no claim is made that the incompatible newer upstream observations are installed.

Nine archived source artifacts, versions and rights notices are enumerated in [Sources/PINS.md](Sources/PINS.md) and [SHA256SUMS.txt](Sources/SHA256SUMS.txt). Original source extraction used `tar -tf` to inspect the archive, then `tar -xf` into the dedicated source folder. No extraction or compilation of third-party code is performed by the verifier.

## Current verification commands

The recorded runs use process-local `ELAN_HOME=C:/Users/Naraphim/.elan`.
On another machine, use that installation's actual elan directory; do not change
the pinned Lean toolchain. No machine-wide environment change is required.

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

Run foundation and paper evaluation sequentially. A foundation PASS tests its existing scope and does not establish either new theorem. The historical scaffold runner did not start Lean; the current `project-complete` runner builds and audits the entire node-77 package and requires all twenty accepted gates.

## Historical checkpoint records

The dated entries below retain their then-current counts, ACTIVE/OPEN statuses
and runner modes; they do not reopen the completed goal. Foundation paths written
as `logs/foundation_freeze_...` are relative to `Riemann Zeta/`; paper paths written
as `logs/dong-wang-wang-zhang-...` are relative to this paper directory. Paths
starting `../../logs/` resolve to that same foundation log directory.

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

These results validated setup tooling and the unchanged existing foundation only. **At this historical setup receipt, node 77 was 0/20 and no paper theorem, Lean package or conversion goal had been started.** Later activation is recorded separately below.

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

No staging, commit, push, recovery-record maintenance or goal activation occurred
in that follow-up. Its historical status was **planning only, 0/20 proof gates complete**.

## Goal activation and first arithmetic reduction

The owner explicitly activated `Dong-Wang-Wang-Zhang Goal Prompt.md` on
4 October 2026. The product goal is ACTIVE, without a token budget. Development
is on a **DIRTY** worktree based on `92f2304f630cbed3b76818a7f649e34b98cea209`.
No staging, commit, push or recovery-record maintenance occurred. The owner's
pre-existing `push_to_github.bat` edit is preserved and that interface was not run.

The isolated `Extension/` package requires the unchanged foundation by local
path and shares its Mathlib/PNT dependency revisions. No node-63/73/74 extension
is imported. The scoped node-73 survey and no-reuse decision are in Crosswalk.
No end statement or frozen source was changed. The nine artifact pins pass.

Package SHA-256 values at activation:

- `Extension/lean-toolchain`: `54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325`.
- `Extension/lakefile.toml`: `f85c69dac07d2b1063a162defb05dbb061aad395ea646a1aad136606c986ada4`.
- `Extension/lake-manifest.json`: `3bd32f161ed185489ce80a96804a0265aa25976396fac9d84dbb2a28e7ee64b2`.

Fresh foundation command, from `Riemann Zeta/`:
`cmd /c run_lake_build.bat --no-pause`.
Result: **PASS**, exit 0; 8,857 build jobs; 301 production modules and two retained
regressions; 7,636 explicit / 14,290 discovered-theorem audits; exact publication
and agenda outputs; all sixteen declaration linters; zero Lean diagnostics.
Log: `logs/foundation_freeze_20261004_124125.log`, SHA-256
`e0dca5ba33ca89f4149a5c3f7ad5c8d0896dbb446162227bc9be9b6a6b685bd0`;
manifest: `logs/foundation_freeze_20261004_124125.json`, SHA-256
`693d42c272515b9b1c77c808a833c1adec0998ca6edd5bde4ec394ea04cf7e57`.

Then, sequentially from the paper directory:
`cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`.
Result: **DEVELOPMENT PASS — CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS
INCOMPLETE**, exit 0. This receipt covers 46 classified files; three production
modules (`ZetaSum`, `TwistSelection`, `MeanComparison`) in the root graph; both
verification modules; 3,526 build jobs; nine semantic regression consumers;
56 discovered project theorems including private/generated declarations;
29 required audit consumers; all sixteen linters; nine source pins and 34 local
links. No Lean errors, warnings, tactic suggestions or linter findings remained.
Log: `logs/dong-wang-wang-zhang-build-20261004-125041-178.log`, SHA-256
`17b21824255bf57931981d33a86e3487e3098038cf2b72d4f3457259906b3fe3`.

The status scan in that run preceded promotion of DWWZ-01/03 from OPEN to DONE.
The promotion reflects their exact contract review and the two independent BAT
receipts, not completion of DWWZ-05/06 or of the release gates. The next power-sum
analytic work is **not** covered by this receipt; it requires fresh verification.

## Uniform power-sum and finite mean-comparison verification

Fresh sequential verification on the same dirty baseline, 4 October 2026:

1. From `Riemann Zeta/`, `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0,
   unchanged 8,857-job / 301-production-module / two-regression foundation scope,
   all 14,290 discovered-theorem audits, exact publication/output checks and
   sixteen linters. No Lean diagnostics or failed stages. Foundation log
   `logs/foundation_freeze_20261004_131139.log`, SHA-256
   `926b2ea6826b8b4e7bbe3566ac315d680bd8b762608842045f0954d0c87756ce`;
   manifest `logs/foundation_freeze_20261004_131139.json`, SHA-256
   `c6b00fe398b042e7e15445d07a0ced59351b8e08d8e949d0576a0bb5614f0a92`.
2. After that process completed, invoked the paper BAT by full path from
   `E:/Lean` with `--no-pause`: **DEVELOPMENT PASS — CURRENT MODULES VERIFIED;
   MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. All 47 classified files, four
   production modules, both verification modules, 3,527 build jobs, eleven
   semantic regressions, 85 discovered project theorems, 41 required audit
   consumers, sixteen linters, nine source pins and 34 local links passed.
   The status scan agreed on **2/20**, DWWZ-01/03 DONE. No Lean errors, warnings,
   tactic suggestions or linter findings. Log
   `logs/dong-wang-wang-zhang-build-20261004-131648-336.log`, SHA-256
   `df3275cac8487b46c1d2256bb4d2d7eb46dd8afae39515ad2d660badbb1261e8`.

This historical checkpoint includes `PowerSumEstimate` and the actual finite
coefficient-error bound in `MeanComparison`. It does not cover the coefficient
mean/tail or Euler-product estimates added later, nor Halász, Lipschitz or either
main contract.
The source-verifier fixture suite passed 8/8 again, exit 0, under
`logs/source-verifier-tests-20261004-131148-584/`. Invalid BAT arguments returned
the expected child exit 2. `git diff --check` passed; only Git's existing
LF-to-CRLF notices were printed, not Lean diagnostics. No foundation pins or
node-63/73/74 files changed. The receipt was appended after the verified run.

## Source-form mean-comparison verification

4 October 2026, same dirty baseline and unchanged pins; the two BATs ran sequentially.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production modules plus two regressions, 7,636 explicit and 14,290 discovered
  theorem audits, all sixteen linters and exact publication/output checks. Zero
  Lean diagnostics. Log `logs/foundation_freeze_20261004_134452.log`, SHA-256
  `2398567d60df7a8c9b348c0e16e5c578c502e4c9d6ef5540dc7ec1d6b478d97d`;
  JSON `logs/foundation_freeze_20261004_134452.json`, SHA-256
  `cf9fb4aa74a4e92600118e04587ed2922d8de0122526fc0334fd2bffe793e9a0`.
- Paper BAT invoked by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. Covered
  48 classified files, five production modules including `CoefficientMean`, two
  verification modules, 3,545 jobs, fourteen semantic regressions, 162 discovered
  project theorems, 73 required consumers, all sixteen linters, nine source pins
  and 34 links. Status agreement remains **2/20**. No Lean diagnostics or failed
  stages. Log `logs/dong-wang-wang-zhang-build-20261004-134751-893.log`, SHA-256
  `f1b0c7464f0d48d0bf77d3ab9360fac2693ef94027ac6239ff3934caf5a65279`.

This checkpoint covers the exact coefficient mean/tail/Euler-product estimates
and the complete phase-specialized comparison (2.2), including the original
normalized sum, real cutoff, twist sign, prime factor and explicit absolute
constant. Halász, Lipschitz and both main contracts remain open. A preliminary
focused build produced one unnecessary-sequence-focus style warning; it was
fixed in the source before the clean audit and these BAT runs. `git diff --check`
passed, with only Git line-ending notices. No recovery record or synchronization
operation was performed. This receipt was appended after verification and does
not cover subsequent transform work.

## Ordinary and logarithmically weighted transform verification

4 October 2026, unchanged pins and dirty baseline; both BATs ran sequentially.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production modules plus two retained regressions, 7,636 explicit and 14,290
  discovered theorem audits, exact publication/output checks and sixteen linters.
  Zero Lean diagnostics. Log `logs/foundation_freeze_20261004_141939.log`, SHA-256
  `47bcec02700d1b569bf09ffd2d83fa086227a64f963b89cd0cb3a5f994acf399`;
  JSON `logs/foundation_freeze_20261004_141939.json`, SHA-256
  `0e32d9e3419c9110a5dc159780e3500c500c4777eed12d152559848d6eb20fdd`.
- Paper BAT invoked by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. Covered
  49 classified files, six production and two verification modules, 3,562 jobs,
  twenty semantic regressions, 216 discovered project theorems, 113 required
  consumers, all sixteen linters (152 declarations plus 83 automatic), nine
  source pins and 34 local links. Status agreement remains **2/20**. Zero Lean
  diagnostics. Log `logs/dong-wang-wang-zhang-build-20261004-142238-371.log`, SHA-256
  `bab0c15fd44a0778b9e0184a3c1f44733cab2697b8579aea305b5dd8388ce060`.

This checkpoint covers exact ordinary and logarithmically weighted Laplace,
Fourier and Parseval identities, including floor cutoffs, the spectral shift,
`2π` normalization, negative derivative sign, absolute convergence and both
square-integrability obligations. It does not prove Halász, Lipschitz, the
frequency-region bounds, a smooth-number adapter, the continued Gaussian
identity or either main theorem. `git diff --check` passed (Git line-ending
notices only). No recovery-record or synchronization operation was performed.
This receipt was appended after verification; later analytic additions require
their own verification record.

## Near-frequency and actual-block far-tail verification

4 October 2026, unchanged pins and dirty baseline; both BATs again ran sequentially.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production modules plus two regressions; 7,636 explicit and 14,290 discovered
  theorem audits, exact output checks and sixteen linters. Zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_144905.log`, SHA-256
  `20df64987d4c85cef5136661fb6e75252043c9e8b110def4ddcde9a5bfa8f74e`;
  JSON `logs/foundation_freeze_20261004_144905.json`, SHA-256
  `1104e55eb1225b304c34fc9553046cf45686499511512065713502facc2949a7`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS — CURRENT
  MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. Covered 50 files,
  seven production and two verification modules, 3,578 jobs, 26 regressions,
  270 discovered project theorems and 139 required consumers. All sixteen
  linters passed (179 declarations plus 111 automatic), as did nine source pins,
  34 links and **2/20** status agreement. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-145225-916.log`, SHA-256
  `6b6326bad852a49206e16652fa1e9c0081b00d82c8e54948cfc3a7500e2854d2`.

This checkpoint includes the actual twisted von Mangoldt mean square, exact
near-frequency bound with the source maximizer, and foundation-backed translated
mean squares and convergent two-sided far tails for each differentiated-series
coefficient block. The four-file foundation import closure is recorded in
Dependencies. Sharp infinite-coefficient assembly, Halász/Lipschitz and both main
contracts remain open. Preliminary focused attempts had tactic diagnostics;
these were repaired before the clean build/audit and both BAT runs. No diagnostic
was suppressed. `git diff --check` passed (Git line-ending notices only).
No recovery record or Git synchronization was touched. Receipt appended after
verification; later mathematical additions are not covered by this checkpoint.

## Sharp full-series frequency verification

4 October 2026, unchanged pins and dirty baseline; both BAT interfaces ran
sequentially after the new Gaussian/full-series mathematical batch.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production modules and two regressions, 7,636 explicit/14,290 discovered
  theorem audits, exact source outputs and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_153126.log`, SHA-256
  `9197f5bbb9efe44133d2e3cc74fb6d4d0a19bb515fdd1ac43f0348e4f2bcc18e`;
  JSON `logs/foundation_freeze_20261004_153126.json`, SHA-256
  `ac7c412f091a66d2acae6ee86a8f3b3c15cd593df293a1b700752b8385e8c898`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS — CURRENT
  MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. Covered 50 files,
  seven production/two verification modules, 3,579 jobs, 31 semantic regressions,
  359 discovered project theorems and 184 required consumers. All sixteen linters
  passed (227 declarations plus 155 automatic); nine source pins, 34 local links
  and the **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-153455-215.log`, SHA-256
  `ff2c7024d0154db2bde2ad3ca4c744eb83e10818de0f555568a738f87a42b9e7`.

The earlier paper run `logs/dong-wang-wang-zhang-build-20261004-153431-014.log`
correctly exited 1 at the conservative text scanner: a prose comment began with
the reserved declaration word `constant`. Reworded the comment; no proof or
scanner was weakened. Preliminary focused proof diagnostics were fixed before
the clean integrated runs. `git diff --check` passed (Git line-ending notices only).

This checkpoint covers the exact Gaussian Gram identity, sharp index-weighted
finite/full-series mean square, actual derivative coefficient convergence and
square sums, and the uniform two-sided full-series far tail recorded in Crosswalk.
It closes that analytic sub-obligation, not Halász/Lipschitz, DWWZ-05/06 or T1/T2.
No foundation source/pin, frozen paper statement, recovery record or owner Git
synchronization interface was changed by this batch. Receipt appended after
verification; later analytic additions require their own evidence.

## Poisson maximum transport and full weighted mean-square verification

4 October 2026, unchanged pins and dirty baseline. Both BAT interfaces ran
sequentially after adding the eighth production module, `MeanValueMaximum`,
its actual consumers and four semantic regressions.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production modules/two regressions, 7,636 explicit and 14,290 discovered
  theorem audits, exact source contracts and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_160452.log`, SHA-256
  `aebd6c907c500ffa1350265c4dde1cf664871ee4d01a0c835be62e09ce338293`;
  JSON `logs/foundation_freeze_20261004_160452.json`, SHA-256
  `681d660f6526d85c40ef6e42192c7ce16c0562eab99d64872dd2889fd8db3714`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0. Covered
  51 classified files, eight production/two verification modules, 3,581 jobs,
  35 semantic regressions, 421 discovered project theorems and 220 required
  consumers. All sixteen linters passed (266 declarations plus 181 automatic);
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-160756-402.log`, SHA-256
  `b9a7643c57b6f4d079c866a7d40ec6236ea1c705cc3588f8fa3226f1911998c0`.

This checkpoint covers the Poisson Fourier identity and unit mass, actual zeta
reproduction with absolute integrability, the explicit tail, original-maximizer
rightward transport, full near/far spectral assembly and the weighted-summatory
mean-square consumer recorded in Crosswalk. All focused tactic diagnostics and
two missing-definition-docstring linter findings were fixed before the clean
integrated runs; no checks were disabled. `git diff --check` passed (Git
line-ending notices only). The unchanged frozen main contracts, Halász,
Lipschitz and DWWZ-05/06 remain open. No recovery record or owner synchronization
interface was edited or executed. Receipt appended after verification; later
analytic additions are not covered by this checkpoint.

## Lipschitz difference-factor verification

4 October 2026, same pins and dirty baseline. Both BATs ran sequentially after
the difference-factor Poisson and ordinary/weighted dilation Laplace additions.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production/two regression modules, 7,636 explicit/14,290 discovered
  theorem audits and all exact-output/linter gates; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_162216.log`, SHA-256
  `b7406bcbfc77584274c36cd11fcc92e74577dc80f8f6d44120d4146c2f2b3c25`;
  JSON `logs/foundation_freeze_20261004_162216.json`, SHA-256
  `ff5c39ad375dc7c0dd90d77b3e8fc4800674b1dc58b8c231abcbd87081d33d45`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 51 files, eight production/two verification modules, 3,581 jobs,
  39 regressions, 435 discovered theorems and 232 required consumers.
  All sixteen linters passed (278 declarations plus 183 automatic); nine
  source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-162524-713.log`, SHA-256
  `e20c4f4c50810eb2eb6dd12d7e735615913028a13022b71fac3ed5a4b694c7e2`.

The identities retain the actual sums, derivative sign, denominator, spectral
shift, initial dilation damping and all integrability hypotheses. The transport
bound is uniform in the nonnegative translation and bounded complex multiplier.
The pointwise Lipschitz theorem and prime/Euler-product estimates remain open;
this checkpoint does not close DWWZ-05/06 or either public contract. One focused
translation-rewrite diagnostic was fixed before the clean builds; no diagnostic
was suppressed. `git diff --check` passed (Git line-ending notices only).
No foundation/pin, frozen source, recovery record or owner synchronization
interface was changed. Later additions require a fresh verification receipt.

## Euler-distance and reciprocal-prime verification

4 October 2026, same pins and dirty baseline. Both BATs ran sequentially after
adding `MeanValueEuler`, its 22 public audit consumers and four regressions.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production/two regression modules, 7,636 explicit/14,290 discovered
  theorem audits, exact outputs and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_164921.log`, SHA-256
  `3937641ae99b3c865a842df43de38351ef92fd3130cd2ed84b9d62579ba7d1d2`;
  JSON `logs/foundation_freeze_20261004_164921.json`, SHA-256
  `26330362303c8cfbfdb7e5e31d3bcff606cb1b1fa9834dc7ba35ea4fb1c04292`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 52 files, nine production/two verification modules, 3,584 jobs,
  43 regressions, 466 discovered theorems and 258 required consumers.
  All sixteen linters passed (305 declarations plus 188 automatic); nine
  source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-165220-746.log`, SHA-256
  `b9fef919735009f6c53c926bccc1c7244f4145a30ded2dcc5a541a9894c63927`.

This covers the convergent Euler distance with coefficient one, the finite
source-distance bound, reciprocal primes and the actual distance-form mean
comparison. Focused elaboration diagnostics were fixed before integrated
verification; no check was weakened. `git diff --check` passed (Git line-ending
notices only). Pointwise Halász/Lipschitz, DWWZ-05/06 and T1/T2 remain open.
No foundation/pin, frozen source, recovery record or owner synchronization
interface was changed. Later analytic additions require fresh verification.

## Quartic-cell pointwise smoothing verification

4 October 2026, same pins and dirty baseline. Both BATs ran sequentially after
adding `MeanValueSmoothing`, its 28 public consumers and four regressions.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production/two regression modules, 7,636 explicit/14,290 discovered
  theorem audits, exact outputs and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_171847.log`, SHA-256
  `dc90a206e5acdc93e186ec4456ca313f062a9678b7b9a2fc222da1f4278ff9d4`;
  JSON `logs/foundation_freeze_20261004_171847.json`, SHA-256
  `001a7a7dc8aca5b9490a5e3dd40af6bbe39a039cc79c0d091db395a2e08c77b9`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 53 files, ten production/two verification modules, 3,595 jobs,
  47 regressions, 528 discovered theorems and 290 required consumers.
  All sixteen linters passed (337 declarations plus 218 automatic); nine
  source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-172524-191.log`, SHA-256
  `9ed91d3a822bea9d6dc109ebc12a53e66faad849317ef5d07165dd0d129a5a31`.

This proves the ordinary pointwise-to-average smoothing input by an alternate
quartic-cell sieve argument using the installed, audited Brun–Titchmarsh
closure. It includes prime powers, floor jumps, convolution, Abel weighting
and the real-cutoff substitution. Its absolute coefficients are not the
coefficient-one GS03 lemma, and no source contract is relabelled as proved.
Focused elaboration diagnostics were repaired before these clean builds.
Halász parameter assembly, Lipschitz, DWWZ-05/06 and T1/T2 remain open.
No source freeze, foundation, pin, recovery record or owner synchronization
interface was changed. Later analytic additions require fresh verification.

## Ordinary maximum-form mean-value verification

4 October 2026, same pins and dirty baseline. Both BATs ran sequentially after
adding `MeanValueAssembly`, twenty public consumers and four regressions.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production/two regression modules, 7,636 explicit/14,290 discovered
  theorem audits, exact outputs and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_174854.log`, SHA-256
  `3efc627decadd3f556d54e9d0f4f9e9455f8d0a04354a6019f2e741b0d10ceda`;
  JSON `logs/foundation_freeze_20261004_174854.json`, SHA-256
  `0f243d2bf10f082c81b99b3b0eaa05c2962149d84b2283f9bcdc09d9a8c994b2`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 54 files, eleven production/two verification modules, 3,597 jobs,
  51 regressions, 566 discovered theorems and 314 required consumers.
  All sixteen linters passed (363 declarations plus 232 automatic); nine
  source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-175149-509.log`, SHA-256
  `2461fa6c227fa469b9e5d6978f7fa3d291a6e32e1a0167fb77cd976eb42a6f0f`.

The checkpoint includes actual-sum logarithmic-weight removal, bounded
damping reconstruction, absolute integrability for Fubini, weighted
Cauchy–Schwarz, the near/far maximum consumer and elementary evaluation of
the minimum integral. `exists_maximizingTwist_mean_value_bound` is an ordinary
maximum-form theorem with explicit absolute constants and no remaining
analytic integral. It is not yet source (2.1), Lipschitz or Lemma 2.2.
Focused proof/tactic diagnostics were repaired before clean verification;
no checks were suppressed. `git diff --check` passed (Git line-ending notices
only). No source freeze, foundation, pin, recovery record or owner
synchronization interface changed. Later prime-distance deductions are not
covered by this receipt and require fresh verification.

## Source large-sum prime-distance verification

4 October 2026, same pins and dirty baseline. Both BATs ran sequentially after
the Euler substitution and exact Lemma 2.2 distance-clause consumer.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0, 8,857 jobs,
  301 production/two regression modules, 7,636 explicit/14,290 discovered
  theorem audits, exact outputs and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_180419.log`, SHA-256
  `f5d5b5695083bdc4c6999a57b7a0e0074e0eb1afa9618345c0d314ead87e7fb9`;
  JSON `logs/foundation_freeze_20261004_180419.json`, SHA-256
  `0f262067d674bf41643d6435ee361d54d1d4a60c62f9ebf63c4d850138417454`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 54 files, eleven production/two verification modules, 3,597 jobs,
  55 regressions, 587 discovered theorems and 324 required consumers.
  All sixteen linters passed (374 declarations plus 243 automatic); nine
  source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-180750-024.log`, SHA-256
  `0aa3fb6bc1382cd0c86602bc36acddba72781be72b99a41b21b5bcc208dd2cec`.

`exists_large_sum_prime_distance_bound` consumes the actual large sum and
produces an actual source maximizer with the exact `1/100` leading coefficient,
absolute threshold and both signs of height. It uses the ordinary mean-value
theorem, Euler distance, a uniform error threshold and reciprocal-prime
control. It does not claim the remaining displacement, comparison-error or
Lipschitz clauses, full hybrid (2.1), or either main theorem. Focused arithmetic
and tactic-style diagnostics were fixed before clean verification, with no
suppression. `git diff --check` passed (Git line-ending notices only).
No source freeze, foundation, pin, recovery record or owner synchronization
interface changed. Subsequent twist-bound additions require fresh verification.

## Same-witness twist-bound verification

4 October 2026, unchanged pins and dirty baseline. Both BATs ran sequentially,
with no source edits during either run, after adding `TwistBounds`.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0,
  8,857 jobs, 301 production/two regression modules, 7,636 explicit/14,290
  discovered theorem audits and sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_181916.log`, SHA-256
  `3683d41109179b7f7a9b65d239c9e93f779fce5b4388e21d204eeaf7880fee2b`;
  JSON `logs/foundation_freeze_20261004_181916.json`, SHA-256
  `b9d7c4e6c5b9958d0dbfea59f57adb6bdc72dce3fa22e37fab94ce29b99cabc7`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  Covered 55 files, twelve production/two verification modules, 3,598 jobs,
  57 regressions, 595 discovered theorems and 331 required consumers.
  All sixteen linters passed (381 declarations plus 244 automatic);
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-182248-403.log`, SHA-256
  `06f337e7c02101dbcd215834757000efc3eeeaeb6be672f2995c0b346086a01d`.

The actual large-sum consumer now returns a single source maximizer with
displacement `≤4N`, the exact source M bound and reversed comparison error
`≤4x/(log x)^(3/4)`. The same-witness regression and inverse-factor identity
are audited. Lipschitz remains unproved; no aggregate gate or frozen source
statement changed. A focused multiplication-by-one type mismatch was fixed
before the successful integrated checks. No recovery record, foundation,
pin or owner synchronization interface changed. Subsequent two-frequency
work is outside this receipt.

## Two-frequency prime/zeta and maximizer verification

4 October 2026, same pins and dirty baseline. The foundation and paper BATs
ran sequentially, with no source edits during either run, after integrating
`TwoPointEuler` through its internally chosen prime-scale consumer.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered theorem audits, sixteen linters, zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_185111.log`, SHA-256
  `acd942b4dda8a9632a2a75da2b6ee297c69aa5df033def7f8e4b762397c294c2`;
  JSON `logs/foundation_freeze_20261004_185111.json`, SHA-256
  `abbcbd666e7fbefc365700c38e836b66624963d5c5ec6cb720015d8d5f09c705`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  56 files, thirteen production/two verification modules, 3,659 jobs,
  61 regressions, 658 discovered theorems, 357 required consumers.
  Sixteen linters passed on 409 declarations plus 281 automatic declarations;
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-185404-765.log`, SHA-256
  `782d8ac7ed9a2a544f8ced2456e8e2b272485466fca67eeed4690ef0f4c7b092`.

The proved installed `MediumPNT` and its fourteen-file closure are recorded
in Dependencies; all fourteen ledger hashes were rechecked. It supplies the
actual theta error, prime cosine bound of mean `75/113`, actual two-point
zeta bound and same-source-maximizer off-frequency consumer. Four exact
regressions and every public theorem are in the transitive audit. Focused
type mismatches, one unused simplifier argument and one missing definition
comment were fixed before the clean integrated run. No pin, foundation,
frozen source, recovery record or owner synchronization interface changed.
Neither Lipschitz nor either main theorem is proved. Subsequent difference-factor
optimization additions are outside this receipt.

## Optimized dilation and weighted-difference verification

4 October 2026, unchanged pins and dirty baseline. The two BATs ran
sequentially, without source edits during either run, after integrating
the optimized factor/rightward estimates and `DilationMeanSquare`.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered theorem audits, sixteen linters; zero Lean diagnostics.
  Log `logs/foundation_freeze_20261004_191342.log`, SHA-256
  `6a913767988424791a8857ed62c378a8bdac9224fd180738637c516023f67b7c`;
  JSON `logs/foundation_freeze_20261004_191342.json`, SHA-256
  `eefaf3745a964fc54a6c5bc82fd21a5c97de85938fe615b610b022ee0266b75f`.
- Paper BAT by full path from `E:/Lean`, `--no-pause`: **DEVELOPMENT PASS —
  CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  57 files, fourteen production/two verification modules, 3,660 jobs,
  65 regressions, 685 discovered theorems, 374 required consumers.
  All sixteen linters passed on 427 declarations plus 291 automatic;
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-191717-870.log`, SHA-256
  `9a22c0fbcf01f776b26bf3dfcce8c49a5d41aa9fe24f2b1e28f302420aa3c391`.

The actual source maximizer now controls the damped zeta dilation factor,
uniformly over the local frequency window and every nonnegative translation.
Its rightward transport feeds genuine weighted-difference Parseval and
near/far mean-square assembly for the original sums. Four new exact consumers
cover the factor, rightward transport, Parseval and weighted mean square.
All public declarations are audited. Focused cast, algebra-normalization,
negative-product rewriting and implicit-set inference failures were fixed
before the successful integrated checks. `git diff --check` passed, with
Git line-ending notices only. No frozen source, foundation, pin, recovery
record or owner synchronization interface changed. Lipschitz, difference
smoothing and both main theorems remain unproved. Subsequent capped-maximum
and smoothing work is outside this receipt.

## Capped mean square and actual-difference smoothing verification

4 October 2026, same dirty checkout and unchanged package pins. Both BATs ran
sequentially with no source edits during either run.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_194144.log`, SHA-256
  `fc784d026859ba5046253b5c4e210e8a347c155fbc03ba782cf39d8c9bb8b1af`;
  matching JSON SHA-256
  `c8de760eff0ddb031146413646d550a4fc178d1c5e376a4997d541ed1a003ea6`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  58 files, fifteen production/two verification modules, 3,661 jobs,
  69 regressions, 738 discovered theorems and 405 required consumers.
  All 16 linters passed on 460 declarations plus 313 automatic;
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-194439-661.log`, SHA-256
  `76dd8136605ff52474a4d920da581f8d4f9369298d284bb86abf2dcd9db167b9`.

This receipt covers the capped actual weighted-difference mean square and
all of `DilationSmoothing`: exact convolution, active-cell variation,
log-weight removal and pointwise-to-logarithmic-average bound. Four new
regressions preserve those actual-object contracts. The initial natural/
real inference errors in filtered cell sets were fixed before verification.
`git diff --check` passed, with Git line-ending notices only. No source freeze,
foundation, pin, recovery record or owner synchronization interface changed.
The final Lipschitz parameter assembly, exponent absorption and both main
theorems remain unproved; subsequent parameter-assembly work is outside this receipt.

## Evaluated dilation-parameter verification

4 October 2026, unchanged pins and same dirty checkout. Both BATs ran sequentially
without source edits during either run.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_200841.log`, SHA-256
  `47b7e7e2f6d5fd53b9f93db5317ecab8717f6975a74ad8ba71dcf7f3675937d8`;
  matching JSON SHA-256
  `a8c946a6aa3bf0ea0a3c247e984d7c185e3b36897dc243bffc793e3f50434713`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0.
  59 files, sixteen production/two verification modules, 3,662 jobs,
  73 regressions, 766 discovered theorems and 426 required consumers.
  All 16 linters passed on 482 declarations plus 320 automatic;
  nine source pins, 34 links and **2/20** status agree. Zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-201145-555.log`, SHA-256
  `b0b285c125234fc78aec8f1c2d0c4cd02101dd1651b69d66599acc76c79e6949`.

This covers all of `DilationAssembly`: translation-scale log-weight removal,
weighted Cauchy–Schwarz, reconstruction up to twice the base logarithmic
cutoff, justified Fubini, capped integral evaluation, and the actual
same-maximizer consumer with no residual analytic integral or upper-size
premise on the maximum. Four new regressions and every public theorem are
audited. An unnecessary interval assumption, tactic sequencing diagnostic,
power-continuity inference, reciprocal normalization and constant-integrand
inference were corrected before the clean integrated runs.
`git diff --check` passed with Git line-ending notices only. No frozen source,
foundation, package pin, recovery record or owner synchronization interface
changed. Scalar absorption to the exact `1/3` exponent, all-real cutoff
assembly, full Lemma 2.2 and both main theorems remain open. Subsequent
Lipschitz work is outside this receipt.

## Full Lemma 2.2 acceptance

4 October 2026, unchanged pins and dirty checkout at
`92f2304f630cbed3b76818a7f649e34b98cea209`. Both BATs ran sequentially,
with no source or documentation edits during either run.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_203103.log`, SHA-256
  `ef371d74bcc67300e03c0522a023b6d01fc8622d0e47ae82ded1d79c7db46cb0`;
  matching JSON SHA-256
  `d27527126b84094423f9c56fc09f2bef59a42ead5b0b1d2b42c5f6931e4b1468`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  60 files, seventeen production/two verification modules, 3,663 jobs,
  77 regressions, 798 discovered theorems and 442 required consumers.
  All 16 linters passed on 500 declarations plus 336 automatic;
  nine source pins and 34 links passed, with zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-203716-719.log`, SHA-256
  `9923b9076ed5a2cbd54764b505d7c7268bbbbbd9e489eac84259f303d953dfc8`.

The run used the pre-acceptance status 2/20. Semantic review of
`DongWangWangZhang2026.exists_large_sum_maximizing_twist` confirms absolute
constants before all physical parameters, the actual maximizing condition,
one witness for displacement/distance/all-real continuity/reversed comparison,
and exact source exponents and signs. Its upstream consumers are
`exists_large_sum_twist_bounds` and `exists_maximizingTwist_uniform_lipschitz`;
the latter consumes the actual dilation mean square and smoothing chain.
No analytic conclusion is supplied as a premise.

Accordingly DWWZ-05 and DWWZ-06 are accepted under their unchanged criteria,
bringing the total to **4/20**. DWWZ-05 is the explicitly permitted consumed
phase specialization, not a claim to generic hybrid (2.1) or optimal GS03
generality. Frozen source statements remain unchanged. Both main theorems and
release gates remain open. Status-only synchronization is verified separately
below; subsequent zeta-bound work is outside this receipt.

### Post-acceptance status verification

The unchanged Lean sources passed the paper BAT again after status-only
synchronization: **DEVELOPMENT PASS**, exit 0, **4/20** status agreement,
the same 60 files/17 production modules/77 regressions/798 discovered
theorems/442 consumers, all 16 linters, and zero Lean diagnostics.
Log `logs/dong-wang-wang-zhang-build-20261004-204320-588.log`, SHA-256
`03ba9936ad697bb9aa464a0f755da92c74d435e168306c984b29c5a6b332acdd`.
No source edits occurred during this run. The preceding foundation receipt
applies to this unchanged proof/import/package scope.

## Uniform zeta Lemma 3.1 acceptance

4 October 2026, unchanged pins and dirty checkout. Sequential runs, with no
source/documentation changes during either:

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_205109.log`, SHA-256
  `680e84d57fb523e6c40103cd21a3d921bdda7e08161b566124b6db763bec06b2`;
  matching JSON SHA-256
  `01eb8913fa55cfa699271be64cce0af64ee0ea33b42c395fef5b34a799a8dd6e`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  61 files, eighteen production/two verification modules, 3,664 jobs,
  81 regressions, 810 discovered theorems and 451 required consumers.
  All 16 linters passed on 509 declarations plus 339 automatic;
  nine source pins, 34 links and pre-acceptance **4/20** status passed.
  Zero Lean diagnostics. Log
  `logs/dong-wang-wang-zhang-build-20261004-205353-504.log`, SHA-256
  `1b094d4bd066af69c2ec6b241d3efc8a91f6cd92e50c1a8581a9c08eb202539c`.

Semantic acceptance: `norm_zeta_left_strip_le` proves the actual zeta bound
with the fixed constant 8 for every real height and every `0<λ≤1/2`.
The proof consumes the installed Euler–Maclaurin identity and genuine
integrable remainder bound; its pole stays explicit in the truncation theorem.
The cutoff is selected internally as `ceil(2+|v|)`. Four regressions retain
the exact source form, zero height, closed endpoint and explicit-pole estimate.
No size assumption on the height or conclusion-shaped premise is present.
After acceptance DWWZ-07 is DONE and the total is **5/20**. Subsequent
regularized-transform implementation is outside this receipt.

## Exact Gaussian Lemma 3.3 acceptance

4 October 2026, unchanged pins and dirty checkout. Both BATs ran sequentially
with no source/documentation edits during either run.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_210850.log`, SHA-256
  `e249a8cf737e13c87c377a8d516910f6755d69816377e1bc5b01f472e8a91212`;
  matching JSON SHA-256
  `9a132898d8477ca876ba9155cf802709b639818eaeed99d01c5f4f7f937ffa1d`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  63 files, twenty production/two verification modules, 3,694 jobs,
  86 regressions, 881 discovered theorems and 491 required consumers.
  All 16 linters pass on 552 declarations plus 370 automatic;
  nine source pins, 34 links and pre-acceptance **5/20** status pass.
  Zero Lean diagnostics. Log
  `logs/dong-wang-wang-zhang-build-20261004-211249-672.log`, SHA-256
  `5d255839660f5a799eecc5ea1ccd43712f80c53ad7fe8fe4e95fc24b504294e4`.

Semantic acceptance: `source_gaussian_identity` consumes the actual power
sum for all real twists, `V>0` and `0<λ≤1/2`, with the exact shifted
zeta quotient and positive `2π/(1+it) exp((λ+it)²/(2V))` term.
The original scale and frequency integrals are proved absolutely convergent.
The actual bounded remainder is continued by Mellin uniqueness, its full-line
Laplace transform is proved, and justified Gaussian Fubini plus explicit
exponential restoration assemble the displayed source identity. No analytic
identity, convergence claim or pole correction is assumed.

This faithful alternate replaces moving-contour continuation; no contour
limit remains undischarged. It changes neither the frozen statement nor
the acceptance requirement. The five new regressions include the zero-twist
positive residue, both convergences and the exact full formula.
DWWZ-10 is accordingly DONE: **6/20**. Both main contracts remain open.
Subsequent xi/divisor work is outside this receipt.

## Actual xi/divisor and real logarithmic-derivative acceptance

4 October 2026, unchanged pins and dirty checkout. Both BATs ran sequentially
with no source/documentation edits during either run.

- Foundation `cmd /c run_lake_build.bat --no-pause`: **PASS**, exit 0;
  8,857 jobs, 301 production/two regression modules, 7,636 explicit and
  14,290 discovered-theorem audits, 16 linters, zero Lean diagnostics.
  Log `../../logs/foundation_freeze_20261004_212721.log`, SHA-256
  `8daf7443011db807093fd1ce9cfb8d4533b4eb6029e8c87ae6f4690498391ac4`;
  matching JSON SHA-256
  `a5f67437197fbfb993b820727065436f3c50a9d700af239bfeeca5e580dee3f2`.
- Paper `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`:
  **DEVELOPMENT PASS — MAIN PAPER CONTRACTS INCOMPLETE**, exit 0;
  65 files, twenty-two production/two verification modules, 3,815 jobs,
  93 regressions, 931 discovered theorems and 525 required consumers.
  All 16 linters pass on 590 declarations plus 386 automatic;
  nine source pins, 34 links and pre-acceptance **6/20** status pass.
  Zero Lean diagnostics. Log
  `logs/dong-wang-wang-zhang-build-20261004-213012-827.log`, SHA-256
  `9c3aeee5a347b3d5f50685017f2d7c779e474358e1d631124f0990c892c45b74`.

Semantic acceptance: `re_xi_logDeriv_eq_tsum` actually consumes the proved
installed `riemannXi_hadamard_factorization_no_monomial` and its
logarithmic-derivative theorem. No product or Hadamard coefficient is a
premise of the public consumer. Xi nonvanishing at zero/one, the strict
zero strip, inverse-square convergence and multiplicity-preserving reflection
derive cancellation of the real linear coefficient. Real zero sums are
absolutely convergent; no conditionally convergent complex reciprocal sum
is separated illicitly.

`xi_analyticOrder_eq_zeta` and `xi_zero_fiber_card` prove exact zeta
multiplicities through analytic units. `tsum_xiZero_re_eq_zeta_gamma`
supplies the exact rational/gamma/zeta expression for every `Re(s)>1`;
the shifted inverse-square kernel is summable. Seven new regressions and
all explicit/exhaustive audits retain these contracts.

DWWZ-08 is accordingly DONE: **7/20**. Its divisor/fiber entry is proved
even though DWWZ-04's additional disk/window/rectangle and conjugation
bridges remain open. No quantitative gamma asymptotic, zero-repulsion bound
or zero-sum upper bound is claimed by this gate. Both main theorems remain
open. Subsequent coefficient-one digamma work is outside this receipt.

## Exact Lemma 3.4 acceptance — 4 October 2026

Tested checkout: `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, main,
DIRTY; unchanged Lean/Mathlib/PNT pins above. No source or documentation
edits occurred during either sequential BAT run.

- Foundation: `cmd /c run_lake_build.bat --no-pause`, PASS, exit 0.
  8,857 jobs; 301 production and two regression modules; 7,636 explicit
  declarations and 14,290 discovered theorems; all sixteen linters;
  zero Lean diagnostics. Log `logs/foundation_freeze_20261004_215003.log`,
  SHA-256 `665b1ed00adf801b5f61d7d4ef363cd241e790cc1cf57c38abe9ab8871f672c4`;
  JSON `logs/foundation_freeze_20261004_215003.json`,
  SHA-256 `36b8ee7769fc64b2aacd3a6abcf7f57a573bf56d7451e422552898a99235b272`.
- Paper: `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`,
  DEVELOPMENT PASS, exit 0. 68 classified files, 25 production and two
  verification modules, 3,821 jobs, 98 semantic regressions, 949 discovered
  theorems and 543 required consumers. Sixteen linters checked 608
  declarations plus 386 automatic declarations. Nine source pins,
  34 local links and complete coverage passed; zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-215304-015.log`,
  SHA-256 `908bedaddc82c4812bc865da62993ac2b33f7793fecdd009e3396738c6d85319`.

Semantic acceptance: `exists_source_zero_sum_upper` consumes actual
`XiZero` multiplicity indices, their proved convergence and the exact
xi/zeta/gamma identity. The actual digamma series gives coefficient-one
logarithmic growth on the unbounded half-plane. The nonnegative Mangoldt
series and actual pole removal give the uniform coefficient-one pole
bound. Rational factors are bounded from the source height assumption.
The conclusion is exactly Lemma 3.4, with one absolute remainder constant,
every positive a, both height signs and the closed endpoints ±2.
No analytic estimate, factorization, convergence or zero-sum bound is a
theorem premise. Five new regressions retain the source and boundary types.

DWWZ-11 is therefore DONE after this pre-acceptance 7/20 test: **8/20**.
The status-only updates follow this receipt. Subsequent `XiRepulsion`
work is outside its tested scope. Both main source contracts remain open.

## Exact Lemma 3.2 acceptance — 4 October 2026

Tested checkout: `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, main,
DIRTY, unchanged toolchain/dependency pins. An initial foundation invocation
failed before verification because its process lacked ELAN_HOME. The retry
explicitly set `ELAN_HOME=C:/Users/Naraphim/.elan`; both runs below passed
sequentially, with no intervening source/documentation edits.

- Foundation: `cmd /c run_lake_build.bat --no-pause`, PASS, exit 0.
  8,857 jobs, 301 production and two regression modules, 7,636 explicit
  public declarations, 14,290 discovered theorems, sixteen linters and
  zero Lean diagnostics. Log `logs/foundation_freeze_20261004_221301.log`,
  SHA-256 `26cfba46bad29848a24fc58b007152659603a659943545443ed7dc84699f2367`;
  JSON `logs/foundation_freeze_20261004_221301.json`,
  SHA-256 `569f61230c347321207dcc963ca2bb3020056e1136db3e711412bae9a79c56a4`.
- Paper: `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`,
  DEVELOPMENT PASS, exit 0. 71 classified files, 28 production and two
  verification modules, 3,824 jobs, 104 semantic regressions, 979 discovered
  theorems, 565 required consumers. Sixteen linters checked 630 declarations
  plus 394 automatic declarations. Complete coverage, nine source pins,
  34 local links and integrity checks passed; zero Lean diagnostics.
  Log `logs/dong-wang-wang-zhang-build-20261004-221602-166.log`,
  SHA-256 `fcb6eea6195ee4f79a86ed050b077b4126a4fbe57daae3e4b67eba6e7b76028f`.

Semantic acceptance: `exists_source_zero_repulsion` proves the exact
all-real-height Lemma 3.2 for 0<λ≤1/2, with one positive absolute C/λ
prefactor and the convergent actual multiplicity-indexed kernel
Σρ 2λ²/|1+λ+iu−ρ|². The actual canonical product and degree-one
Hadamard polynomial are consumed, including possible zeros at the left
evaluation point. The gamma quotient has exact exponent λ; the
coefficient-one-half lower real logarithmic derivative cancels its
height growth. Rational factors and the right-half-plane zeta estimate
are proved; the uniform Lemma 3.1 consumer supplies all small heights.
No product, gamma, convergence, zero-sum or terminal growth assumption
remains. Six regressions freeze this contract and its zero/half endpoints.

DWWZ-09 is DONE after this pre-acceptance 8/20 test: **9/20**.
The status-only updates and subsequent `XiConjugation` work are outside
this receipt. Both frozen main source contracts remain open.

## Proof acceptance evidence requirements

### Exact Theorem 1.1 acceptance — 4 October 2026

Checkout `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, main, DIRTY;
unchanged Lean 4.30.0, Mathlib/PNT/package/source pins. Both BATs used
`ELAN_HOME=C:/Users/Naraphim/.elan`, sequentially with no intervening
file edits.

- Foundation: `cmd /c run_lake_build.bat --no-pause`, PASS, exit 0.
  8,857 jobs, 301 production and two regression modules, 7,636 explicit
  declarations and 14,290 discovered theorems; sixteen linters, zero
  Lean diagnostics. Log `logs/foundation_freeze_20261004_233821.log`,
  SHA-256 `bf1376b30830e6c51aea3a36a5c646ed6e268059c37f24548d8002db62eb9591`;
  JSON `logs/foundation_freeze_20261004_233821.json`, SHA-256
  `eb59b349cefab21fbacfbd574ca05ecdac74350ff8d77945143b4d5dae68ce9c`.
- Paper: `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`,
  DEVELOPMENT PASS, exit 0. 81 classified files, 38 production and two
  verification modules, 3,837 jobs, 127 semantic regressions, 1,107
  discovered theorems and 653 required consumers. Sixteen linters checked
  725 declarations plus 434 automatic declarations. Full root coverage,
  nine source pins, 34 local links and integrity checks passed; zero Lean
  diagnostics. Log `logs/dong-wang-wang-zhang-build-20261004-234118-655.log`,
  SHA-256 `711b0f6e6c305bed1f9406bad2c0a2d98bc4c4e0f9179cb88af3398a203f3b7a`.

Semantic acceptance: `large_zeta_sum_forces_zero_disk` has exactly the
frozen T1 quantifier order and input ranges. One maximizing twist defines
φ=t−t₀ before every L. Absolute c is enlarged once, jointly controlling
displacement and the N⁶ cutoff; one absolute height threshold absorbs
Lemma 3.4's remainder. The linked scales λ=L/(40 log x),
a=20λ log T/log x give the actual far sum ≤5 log x/36, near sum
≥log x/9 and open-disk multiplicity count ≥L/360. The finite near
set and absolutely convergent complement partition the actual divisor.
Boundary zeros stay in the far sum; both height signs and empty scale
intervals are retained. No product, count, Gaussian, convergence, forcing
or terminal analytic estimate is a public premise. Five new regressions
include the complete exact T1 type. The frozen source is unchanged.

DWWZ-13/14 are DONE after this pre-acceptance 11/20 test: **13/20**.
DWWZ-02 still needs the actual T2 public theorem and exact-type regression.
Subsequent status documentation, the neutral development-runner banner
correction, and `LocalWindowScale` development are outside this receipt.
The old runner's initial plural-unproved banner was stale; its final
incomplete-paper label was and remains correct. T2 and whole-paper
completion are not claimed.


### Proposition 4.1 acceptance — 4 October 2026

Checkout `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, main, DIRTY;
unchanged package/source pins. Both commands below used explicit
`ELAN_HOME=C:/Users/Naraphim/.elan` and ran sequentially without source
or documentation edits between them.

- Foundation: `cmd /c run_lake_build.bat --no-pause`, PASS, exit 0.
  8,857 jobs, 301 production and two regression modules, 7,636 explicit
  declarations and 14,290 discovered theorems; sixteen linters, zero
  Lean diagnostics. Log `logs/foundation_freeze_20261004_231355.log`,
  SHA-256 `5851f89329e04841773849040ecba4fb03b777f2a4327059c994b28f86e74099`;
  JSON `logs/foundation_freeze_20261004_231355.json`, SHA-256
  `af71621e97325ffb36b245331e4114e68fe4f28db1478f96659d34ca6a6b0a59`.
- Paper: `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`,
  DEVELOPMENT PASS, exit 0. 77 classified files, 34 production and two
  verification modules, 3,833 jobs, 122 semantic regressions, 1,082
  discovered theorems and 636 required consumers. Sixteen linters checked
  708 declarations plus 426 automatic declarations. Complete root coverage,
  nine source pins, 34 local links and all integrity scans passed; zero
  Lean diagnostics. Log `logs/dong-wang-wang-zhang-build-20261004-231858-641.log`,
  SHA-256 `8f872fc2f4a6368a3094306169b194774a436c35136dc34b2bf8dc698e411559`.

Semantic acceptance: `exists_large_sum_weighted_zero_forcing` has the
original `T,t,x,N` hypotheses and absolute `c,T₀`. One actual maximizing
twist precedes all admissible λ, retaining the same c for displacement
and the sixth-power cutoff. Each λ produces η in the exact source radius,
a convergent sum over actual zero-multiplicity labels and lower bound
`(log x)/4`. The proof transitively consumes actual large-sum comparison,
all-real one-third continuity, the normalized Gaussian lower bound,
the exact residue-bearing identity, actual zero repulsion and conjugation.
No Gaussian, residue, tail, maximizer, convergence or zero-forcing premise
is left to the public caller. Both signs and closed scale endpoints are
retained. A proved uniform quotient bound covers both frequency tails;
an integral pigeonhole proof supplies a sufficient actual frequency point
without assuming a global maximum. These are supporting alternate steps,
not source-contract repairs. Ten regressions cover this four-module chain.

DWWZ-12 is DONE after this pre-acceptance 10/20 test: **11/20**.
Subsequent status updates, two documentation-only numeric typo corrections
(`199/200` and the `17/18/19/20` gate list), and `DiskZeroGeometry`
development are outside the receipt. The Lean constants and frozen
source bytes were not altered by those typo corrections. T1/T2 remain
unproved; no whole-paper completion is claimed.

### Zero-count and conjugation acceptance — 4 October 2026

Checkout `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, main, DIRTY;
toolchain and all dependency/source pins unchanged. Both BATs ran sequentially
with `ELAN_HOME=C:/Users/Naraphim/.elan` and no intervening edits.

- Foundation: `cmd /c run_lake_build.bat --no-pause`, PASS, exit 0;
  8,857 jobs, 301 production and two regression modules, 7,636 explicit
  declarations and 14,290 discovered theorems; sixteen linters, zero
  Lean diagnostics. Log `logs/foundation_freeze_20261004_223243.log`,
  SHA-256 `bbff13e7555b17504d279ad5d286db2f1449a634a37e45b3b1d36f4fa81046cf`;
  JSON `logs/foundation_freeze_20261004_223243.json`, SHA-256
  `cecddc476ced04aff8a6c83b582cb146e2b7ebac01e3e592a8e0858474660ac3`.
- Paper: `cmd /c run_dong_wang_wang_zhang_build.bat --no-pause`,
  DEVELOPMENT PASS, exit 0; 73 classified files, 30 production and two
  verification modules, 3,829 jobs, 112 semantic regressions, 1,022
  discovered theorems, 593 required consumers. Sixteen linters passed on
  663 declarations plus 409 automatic declarations. Complete root coverage,
  nine source pins, 34 local links and integrity scans passed; zero Lean
  diagnostics. Log `logs/dong-wang-wang-zhang-build-20261004-223610-183.log`,
  SHA-256 `a2159a00b1cbecfd4cda451dc6d3fc6bafddf3c9d2957d36fe038bcde67e3807`.

Semantic acceptance: `zeroCountIn` counts all actual xi divisor labels;
`zeroCountIn_eq_sum_multiplicities` identifies each complete fiber with
zeta's analytic order. Bounded-region/disk/window finiteness is proved,
not inferred from totalized cardinality. `zeroCountIn_rectangle_eq`,
`zeroCountIn_eq_rectangle_filter`, `rectangle_filter_count_independent`
and `zeroCountIn_sourceWindow_eq` consume the foundation's actual rectangle
count, with the positive-left-edge range required by the source window.
`xiZeroConjEquiv` preserves each multiplicity label; both-sign disk/window
and convergent weighted-kernel equalities are proved. Disk boundaries stay
open, window boundaries stay closed, and exact disk-to-window count transfer
is proved. No finiteness, multiplicity or conjugation premise is left as a
source assumption. Eight regressions and explicit/exhaustive audits retain
these contracts. DWWZ-04 is DONE after this pre-acceptance 9/20 test: **10/20**.
Subsequent status documentation and `GaussianConcentration` development are
outside this receipt. Both frozen main contracts remain unproved.

After explicit activation, record exact repository revision and dirty/clean status, toolchain/manifest/source hashes, all module classifications, actual imports, explicit and exhaustive transitive audits, semantic/exact-type regressions, full BAT commands, stage results, exit codes, logs and hashes. No copied historical receipt, focused build alone or scaffold PASS can satisfy DWWZ-18/19.

Both public theorem statements and all consuming bridges must pass semantic review in addition to Lean's dependency checks. Independent external review and publication remain distinct. No recovery-record file is required or maintained.
