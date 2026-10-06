# Dubon 2026 — reproduction manifest

**GOAL ACTIVE — 0/20 proof gates complete.** Owner activation: 6 October 2026. The isolated package and active verifier are now in place; the complete paper remains unfinished.

The implemented scope includes actual finite Dirichlet polynomials, support and analytic multiplicities; prime-log independence and continuous-test equidistribution of the actual vertical flow; and multivariate zero-set nullity, log integrability, iterated Jensen and the exact quadratic-energy identity. The Haar log potential satisfies 0 ≤ J_Haar ≤ log(E)/2. The actual symmetric vertical logarithmic mean is now identified with J_Haar. Convexity and continuity of the actual Jessen function are now proved; the Jessen–Tornehave frequency formula and all concentration applications remain open. Exact regressions and exhaustive transitive dependency checks are retained. Current verification receipts are recorded below; historical setup receipts do not verify subsequent Lean code.

The complete Proposition 3.3 conclusion is assembled by `bohr_jessen_proposition_source`, including convexity from finite torus grids, actual analytic twist products and Hadamard three-lines. Its 37-module checkpoint passed the sequential checks below. Subsequent additions require fresh verification.

Verified 61-module checkpoint after the 54-module receipt: `HeightLimitTransfer`, the periodic/binomial normalization chain, and `IsolatedPrimeSupport`. That checkpoint had 61 production modules, 33 exact consumers and 376 explicit registrations. The 60-module intermediate focused audit passed with 548 discovered theorems and zero errors from sixteen linters across 447 declarations plus 184 generated declarations. The expanded 61-module focused build and audit passed: 558 discovered theorem declarations, 376 explicit registrations, and sixteen linters with zero errors across 455 declarations plus 188 generated declarations. Inventory validation passed with 130 retained files, 82 local links and 4,320 preserved existing Lean files. The required sequential checks passed with zero Lean diagnostics:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**; all 301 production modules, two retained regressions, exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_052532.log), SHA-256 `a21ceaa5b488e246b253ec4c9375e4fab4a2dce7759e0032a98d435d540b468c`; [machine receipt](../../logs/foundation_freeze_20261006_052532.json), SHA-256 `f7f6b696ef6f79f24f1712db04e6e596e10547bf232259e25692a3fdb9872fa0`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**; all 61 modules, 33 exact consumers and exhaustive audit. All source pins and verifier fixtures passed. [Log](logs/dubon-build-20261006-052827-252.log), SHA-256 `d1beca47cf9b17ee2ea4377ba95dc9f3edbca1af1d29ebcde8278a836d004cd6`.

Both runs used dirty checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`, unchanged root pins and unchanged owner BAT. This receipt covers modules through `IsolatedPrimeSupport`. Subsequent additions require fresh verification; whole-paper acceptance remains open. All twenty source gates remain OPEN.

## Verified rectangle and height-bound checkpoint — 6 October 2026

Additions after the verified 45-module checkpoint: nine modules through `ZeroCountHeight` prove the actual rectangle-count adapter, zero-free contours and half-planes, uniform local multiplicity bounds and bounded unit height increments. The expanded inventory has 54 production modules, 29 exact consumers and 329 explicit registrations. The focused build/audit passed with 473 discovered theorem declarations and only the three permitted logical axioms; sixteen linters found zero errors across 398 declarations plus 150 generated declarations. Inventory validation passed with 123 retained files and 79 local links. The required sequential verification passed with zero Lean diagnostics:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**; all 301 production modules, two retained regressions, exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_045232.log), SHA-256 `79fbda75623d1e05a4addf7b8fec1e46db571621b81d87a8d73902f03b43264c`; [machine receipt](../../logs/foundation_freeze_20261006_045232.json), SHA-256 `7ff96f655a51209d983dc30a31f898ebe190b318fdecc240fa401b0109d51fee`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**; all 54 modules, 29 exact consumers and exhaustive audit. All 26 source pins, 123 retained files, 79 local links, 4,320 preserved existing Lean files and verifier fixtures passed. [Log](logs/dubon-build-20261006-045748-245.log), SHA-256 `971e10b2bc8d6d5fe17e433bcfd52c6782c4b3ee8a449c1e52c1a82e1ca5baf7`.

Both runs used dirty checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`, unchanged pins and owner BAT. This receipt covers modules through `ZeroCountHeight`; later additions require fresh verification. All twenty source gates remain OPEN.

## Verified derivative-measure checkpoint — 6 October 2026

The package has 45 production modules through `JessenMass`, 26 exact source consumers and 295 explicit theorem registrations. The exhaustive audit checked 432 theorem declarations with only the three permitted logical axioms. Sixteen linters found zero errors across 364 declarations plus 143 generated declarations. The actual derivative measure, one-sided interval/atom formulas, both endpoint asymptotes, total mass and probability normalization are kernel-checked. Zero-frequency identification and the remaining source acceptance conditions remain open; 0/20 gates are accepted.

The required sequential checks passed with no Lean warnings, errors, tactic suggestions or linter failures:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**; all 301 production modules, two retained regressions, exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_042842.log), SHA-256 `1fabfe988d87342217b5cbdf6467af45f3754bc17fbe9919fea6ccd2cffff7f5`; [machine receipt](../../logs/foundation_freeze_20261006_042842.json), SHA-256 `4a068ea8bc075fd3a6a06880f61cb2006ab5af1865d33250e186a8c0bfc1739e`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**; all 45 modules, 26 exact consumers and exhaustive audit. All 26 source pins, 114 retained files, 76 local links, 4,320 preserved existing Lean files and all verifier fixtures passed. [Log](logs/dubon-build-20261006-043148-304.log), SHA-256 `70783af51e0a72e9eb10acd9fb50b1174e1a40528e89cf95ae37d8c0ed3ac353`.

Both runs used dirty checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`, unchanged root pins and unchanged owner BAT. No staging, commit or push was performed. Subsequent source additions need fresh verification.

## Historical Jessen convexity checkpoint — 6 October 2026

The package contains 37 production modules, 23 unfolded source regressions and 254 explicitly registered public/consumer theorems. The exhaustive audit found 376 theorem declarations including private/generated declarations, with only `propext`, `Classical.choice` and `Quot.sound`; sixteen linters found zero errors across 315 declarations plus 130 generated declarations. The complete mathematical conclusion of Proposition 3.3 is kernel-checked. All twenty source gates remain OPEN pending their complete acceptance conditions; this is not whole-paper completion.

The required sequential checks completed with no Lean warnings, errors, linter failures or tactic suggestions:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**; 301 production modules, two retained regressions, exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_040622.log), SHA-256 `b9fc09b1d8205f3c63157c113fe25772acc65e1403f8d56c4462d88e6e3603ed`; [machine receipt](../../logs/foundation_freeze_20261006_040622.json), SHA-256 `e1fa5c020471a4e0ff016fa09c40a0251b69fa7abc526db5458b2ae8712a66e0`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**; all 37 modules, 23 source regressions and exhaustive audit. All 26 source artifacts, 106 retained files, 4,320 unchanged existing Lean files and source/inactive/active metadata fixtures passed. [Log](logs/dubon-build-20261006-041349-242.log), SHA-256 `6f13e4748e5fa75b9dfaf1b897dd54e5ffa7323e7ee310e7a4571da410497f1e`.

Both runs used dirty checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`, unchanged pins and unchanged owner BAT; no synchronization was run. This receipt covers modules through `JessenConvexity` only.

## Historical vertical-mean checkpoint — 6 October 2026

The package contains 28 production modules, 22 unfolded source regressions and 209 explicitly registered public/consumer theorems. The exhaustive audit found 314 theorem declarations including private/generated declarations, with only `propext`, `Classical.choice` and `Quot.sound`; sixteen linters found zero errors across 265 declarations plus 114 generated declarations. The actual fixed-N symmetric vertical mean, its Haar identity and uniform logarithmic truncation estimate are kernel-checked. Convexity and the remaining paper chain are open; 0/20 source gates are accepted.

The required sequential checks completed with no Lean warnings, errors, linter failures or tactic suggestions:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**; 301 production modules, two retained regressions, frozen exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_034428.log), SHA-256 `da1943abf3e671e52a42603997a3db282415c92bbac0b1adf814043158e1c64d`; [machine receipt](../../logs/foundation_freeze_20261006_034428.json), SHA-256 `a4618ec1c8d2463fd08ceee78ecc5774ae3d6c06f143e0f53d18c0c04eeedbad`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**; all 28 modules, 22 source regressions and exhaustive audit. All 26 source artifacts, 97 retained files, 4,320 unchanged existing Lean files and source/inactive/active metadata regression fixtures passed. [Log](logs/dubon-build-20261006-034723-799.log), SHA-256 `54771a4cd8f79d34551fd4f89a4658236a00fc1867cbd5082af8e16390dcfa6b`.

Both runs used dirty checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`, unchanged Lean/Mathlib/PNT+ pins and the retained verifier/source hashes. The owner BAT remains unchanged and was not run. This receipt covers modules through `JessenMean`; subsequent source additions require fresh verification.

## Historical thirteen-module checkpoint — 6 October 2026

The root imports thirteen production modules and the verification package retains seventeen unfolded source regressions. A focused build of `Dubon2026`, `Dubon2026.SemanticRegression` and `Dubon2026.Audit` passed: 217 discovered theorem declarations, 134 explicitly registered public/consumer theorems, and sixteen linters with zero errors across 170 declarations plus 83 generated declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited dependency closure.

The fresh foundation run completed before the paper run: `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, with zero project warnings, tactic suggestions or linter failures; all 301 production modules, two retained regressions, frozen publication contracts and 14,290 discovered theorem dependencies passed. Evidence: [foundation log](../../logs/foundation_freeze_20261006_025437.log) and [machine receipt](../../logs/foundation_freeze_20261006_025437.json).

Foundation log SHA-256: `fb540d6d4d45ede481c4cbfa31af7ba398800081ef6c8166f890a31cd3e434e7`.

Foundation json SHA-256: `e2d55da14e203fe2e36a2e4fd0524bfb90d3fbf615e73d8d14c810282f18288f`.

The subsequent `cmd /c run_dubon_build.bat --no-pause` returned **DEVELOPMENT PASS, exit 0**, with zero Lean diagnostics in the complete package build, explicit source regressions and exhaustive audit. All 26 source pins, 82 retained files, 4,320 preserved existing Lean files, eight source-ledger fixtures, fourteen inactive-state fixtures and four active-metadata fixtures passed. Evidence: [active paper log](logs/dubon-build-20261006-025919-553.log), SHA-256 `e11758f5dabc6d6142ed752b0b3c1164e3f0bc268c917d4d4147f865bada2a04`. This receipt covers the thirteen production modules through `TorusJensen`; later source additions require fresh checks. The earlier active run `dubon-build-20261006-021407-070.log` correctly rejected three missing docstrings; those were repaired and the focused exhaustive audit above passed. The paper remains incomplete, with 0/20 accepted source gates.

<details>
<summary>Historical inactive template verification, before owner activation</summary>

**Historical template-only status: 0/20 gates.** Setup and source/tooling verification only; no Lean build, theorem implementation, axiom audit or proof completion is claimed for Project 83.

Baseline: Git checkout `8dcbf0c4c47b099bd00767899fa11df740bfcd87`; research date 6 October 2026. Root Lean/Mathlib/PNT+ pins are frozen in `Tools/scaffold.json` and unchanged. Existing tracked owned Lean files are hashed in the local-reuse inventory. The owner synchronization BAT must remain byte-identical to Project 63.

## Reproduce offline

```powershell
cmd /c run_dubon_build.bat --no-pause
```

The wrapper enters its own project directory, records a timestamped log, validates all source hashes and the exact two-member archive, runs both tooling regression suites, and checks the complete template/documentation inventory. Exit 0 means **SCAFFOLD PASS — no Lean proof tested**. Any failed stage returns nonzero. Python 3 and Windows PowerShell are required; no additional Python package or network access is needed for verification.

Source HTTP retrievals, final URLs, SHA-256 values and sizes are in `Tools/download_receipts.json`; immutable edition identity is separately pinned by the validator. Source-label and bibliography counts come directly from the frozen TeX. Upstream HEADs were observed without changing selected dependencies. The PDF reader used during research lives only in ignored scratch space and is not required for verification.

Final setup verification receipts are recorded below after the checks run. They do not certify the mathematical gates. Existing foundation/extension proof receipts retain their own scope; no new proof status was assigned during setup.

## Verified setup receipt — 6 October 2026

The checks below ran sequentially: the existing foundation verifier finished before the final Project-83 scaffold run. The checkout was in development mode with the new template/documentation changes uncommitted; this is not a clean-clone release certificate.

| Check | Result / evidence |
|---|---|
| Existing foundation `cmd /c run_lake_build.bat --no-pause` from the Lean root | **PASS, exit 0**; 301 production modules, two explicit regressions, zero unclassified files, 14,290 discovered theorem dependencies accepted, exact publication contracts and 16 linter checks passed; zero project warning/tactic-suggestion/linter diagnostics |
| Foundation log | [foundation_freeze_20261006_013140.log](../../logs/foundation_freeze_20261006_013140.log), SHA-256 `27001087f304a6fe5ec257d29a7e544ba2b9d84e2505b59253f83403bae63a36` |
| Foundation machine receipt | [foundation_freeze_20261006_013140.json](../../logs/foundation_freeze_20261006_013140.json), SHA-256 `157e31a7228f6abe971ecf9b5a97d9579fe8d56be3deab1427aea53ab5afd56d` |
| Project 83 `run_dubon_build.bat --no-pause`, launched from `E:\Lean` | **SCAFFOLD PASS, exit 0 — no Lean proof tested**; arbitrary caller directory supported |
| Scaffold log | [scaffold-20261006-013542-527.log](logs/scaffold-20261006-013542-527.log), SHA-256 `b8d9c9999bf87ab5b58abccbb9e3d01166ddcd549e882e7e8eeab5f4a5bb967d` |
| Source/archive integrity | All 26 artifacts pinned; both source members identical to the frozen tar; 139 labels and 25 bibliography entries matched |
| Tooling fixtures | Eight source-ledger cases and fourteen inactive-state/documentation cases passed; these are tooling tests, not mathematical proofs |
| File/document consistency | 63 retained files exhaustively classified; all 63 local links at the logged BAT checkpoint resolved; the post-receipt validator also passed with all 66 links, including the three receipt links; twenty OPEN gates agree across JSON, Checklist and diagram |
| Existing work | All 4,320 tracked owned Lean files in the baseline inventory unchanged; three root configuration files unchanged; no Lean/Lake file in Project 83 |
| Owner synchronization script | Byte-identical to Project 63, SHA-256 `9dd7c9f61aeb2704832c897475a76d471f855150ff6cde03e08cee141a090114`; not executed |
| Working-tree review | `git diff --check` passed. Raw scan matches for “constant” were existing comments/structure fields, not postulates; the canonical foundation scanner also passed. No staging, commit or push performed. |

Logs and fixture directories are generated, Git-ignored local evidence. This receipt validates setup and preserves the separate foundation verification scope. **Project 83 remains inactive, with 0/20 mathematical gates complete.**

</details>

Historical expansion beyond the recorded 61-module receipt: the nine circle/Bessel modules, including the literal-series identity, small/strict/large bounds and radial Fourier bridges. The root now classifies 70 production modules, 35 exact source consumers and 438 explicit theorem registrations. The focused 70-module build and exhaustive audit passed: 664 discovered theorems, 438 explicit registrations, and sixteen linters with zero errors across 521 declarations plus 232 generated declarations. Inventory validation passed with 139 retained files, 85 local links and 4,320 unchanged existing Lean files. The required sequential verification passed with zero Lean diagnostics, as recorded below. Earlier receipts retain their original scope. All twenty acceptance gates remain OPEN.

Verified 70-module sequential checkpoint:

- Foundation: `cmd /c run_lake_build.bat --no-pause` — **PASS, exit 0**, all 301 production modules, two regressions, exact publication contracts and 14,290 discovered theorem dependencies. [Log](../../logs/foundation_freeze_20261006_060338.log), SHA-256 `db19c4ef9ec47592331b64e60aab15fd6c4b8ce4b825fbec310f6623bafed593`; [machine receipt](../../logs/foundation_freeze_20261006_060338.json), SHA-256 `2a372de897122394f209001711f8e74b08e7ff95067579c2d0aa23a9867d8a4f`.
- Then paper: `cmd /c run_dubon_build.bat --no-pause` — **DEVELOPMENT PASS, exit 0**, all 70 production modules, 35 exact consumers, 438 explicit registrations and 664 exhaustively audited theorem declarations. All sixteen linters, source pins, inventory and verifier fixtures passed. [Log](logs/dubon-build-20261006-060703-010.log), SHA-256 `6861ab98929bbc463231bbcdcf52199a9fad8924b51208fb6362f9f3a2b7df96`.

Checkout remains `8dcbf0c4c47b099bd00767899fa11df740bfcd87` with the existing dirty working tree. Root pins and the owner synchronization BAT are unchanged; no staging, commit or push occurred. `git diff --check` passed. These are development receipts, not whole-paper acceptance.

Intermediate development stage after the verified 70-module checkpoint: six Steinhaus/radial modules brought the root to 76 production modules, 37 exact consumers and 476 explicit registrations. Their focused builds passed; this stage was superseded by the verified 80-module checkpoint below.

The verified intermediate expansion reached 80 production modules, 38 exact consumers and 489 explicit theorem registrations, including the actual dimension-uniform planar characteristic-function L¹ bound. The aggregate audit and required sequential verification passed with zero Lean diagnostics: 749 exhaustively discovered theorems, 489 explicit registrations, and sixteen linters with zero errors across 582 declarations plus 264 generated declarations.

Verified 80-module sequential checkpoint (6 October 2026): foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**. Both had zero Lean diagnostics. Foundation coverage remains 301 production modules, two regressions and 14,290 discovered theorem dependencies. Paper coverage is 80 production modules, 38 exact source consumers, 489 explicit registrations and 749 exhaustive theorem checks; all sixteen linters passed. The inventory validated 149 retained files, 88 local links, all 26 source pins and 4,320 unchanged existing Lean files. All twenty acceptance gates remain OPEN.

- [foundation_freeze_20261006_064204.log](../../logs/foundation_freeze_20261006_064204.log), SHA-256 `c9f29277ed2af11db91fca1476cdae680a4814a3bbf26df9f1cb27f07900f10f`.
- [foundation_freeze_20261006_064204.json](../../logs/foundation_freeze_20261006_064204.json), SHA-256 `e138f59ab0a61f79a60646bb5eab145a36cce9ad4fd56bd02ba9d3994ae65101`.
- [dubon-build-20261006-064503-647.log](logs/dubon-build-20261006-064503-647.log), SHA-256 `0e4b5ae7533277f033807412f60df276c795518a2d052b9a6fec0150a76657d7`.

Current expansion after the verified 80-module checkpoint: ten inverse-integral/Gaussian/density modules, ending with `SteinhausDensity`. The root imports 90 production modules, with 39 exact consumers and 536 explicit theorem registrations. Focused modules, aggregate audit and sequential foundation/paper verification pass with zero diagnostics; the previous receipts retain their exact scope. The actual uniform density and translated small-ball estimates are proved, while the translated logarithmic bound remains OPEN.

Verified 90-module sequential checkpoint: foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**. Both had zero Lean diagnostics. Foundation coverage remains 301 production modules, two regressions, exact publication contracts and 14,290 discovered theorem dependencies. Paper coverage is 90 production modules, 39 source consumers, 536 explicit registrations and 821 exhaustive theorem checks. Sixteen linters reported zero errors across 634 declarations plus 289 generated declarations. The inventory validated 159 retained files, 91 local links, all 26 source pins and 4,320 unchanged existing Lean files. `git diff --check` passed. This remains development evidence at the unchanged dirty checkout, with 0/20 accepted source gates.

- [foundation_freeze_20261006_070630.log](../../logs/foundation_freeze_20261006_070630.log), SHA-256 `c09c5e7192d242f748ffa1b53e04b69195266fd479bed4a5b8c16a71f19a64f8`.
- [foundation_freeze_20261006_070630.json](../../logs/foundation_freeze_20261006_070630.json), SHA-256 `82ad8c1f2af84f70e1b83b32dc46847db69d4aee17c9bfc7270edea5938607dc`.
- [dubon-build-20261006-070926-064.log](logs/dubon-build-20261006-070926-064.log), SHA-256 `aefbe9941a23308daef32a6e5216a6bef0d8835162b17923881c11eb08f86500`.

Current logarithmic expansion after the verified 90-module checkpoint: six modules through `SteinhausLog` complete the source Lemma 4.1 conclusion for arbitrary independent Steinhaus variables. The root imports 96 production modules, with 41 exact consumers and 553 explicit theorem registrations. Focused modules and the aggregate audit pass: 854 exhaustive theorem checks, 553 explicit registrations and sixteen linters with zero errors across 654 declarations plus 304 generated declarations. Sequential verification for this expansion passed with zero diagnostics; earlier receipts retain their exact scopes. All twenty source acceptance gates remain OPEN.

Verified 96-module sequential checkpoint: foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, followed by paper `cmd /c run_dubon_build.bat --no-pause`, **DEVELOPMENT PASS, exit 0**. Both had zero Lean diagnostics. Foundation coverage remains 301 production modules, two regressions, exact publication contracts and 14,290 discovered theorem dependencies. Paper coverage is 96 production modules, 41 source consumers, 553 explicit registrations and 854 exhaustive theorem checks. Sixteen linters reported zero errors across 654 declarations plus 304 generated declarations. The inventory validated 165 retained files, 94 local links, all 26 source pins and 4,320 unchanged existing Lean files. `git diff --check` passed. No root pin or owner BAT changes, staging, commit or push occurred. All twenty source acceptance gates remain OPEN.

- [foundation_freeze_20261006_072002.log](../../logs/foundation_freeze_20261006_072002.log), SHA-256 `a31afb36653b27d6921ba876af2021184866b989691d1e8fe5daaf4f14a3b8a4`.
- [foundation_freeze_20261006_072002.json](../../logs/foundation_freeze_20261006_072002.json), SHA-256 `9b430de22dc803e9e77e5bce6fc73c77cac6f11472f841ca69b07a405b0d5c08`.
- [dubon-build-20261006-072252-413.log](logs/dubon-build-20261006-072252-413.log), SHA-256 `53e4402365f324cf030ef3b4de3b14c5ee8130ca1fa5548bb5de6e368f17b76f`.

Current expansion after the verified 96-module checkpoint: seven modules through `IsolatedPrimeLower` implement the finite and compact-uniform isolated-prime Jessen lower bounds. The root imports 103 production modules, with 43 exact consumers and 578 explicit theorem registrations. Focused modules and aggregate audit passed: 898 exhaustive theorem checks and sixteen linters with zero errors across 687 declarations plus 322 generated declarations. The required sequential verification passed for this expansion with zero diagnostics. All twenty source acceptance gates remain OPEN.

Verified 103-module sequential checkpoint: foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, then paper `cmd /c run_dubon_build.bat --no-pause` returned **DEVELOPMENT PASS, exit 0**. Both had zero Lean diagnostics. Foundation coverage remains 301 production modules, two regressions, exact publication contracts and 14,290 discovered theorem dependencies. Paper coverage is 103 production modules, 43 exact consumers, 578 explicit registrations and 898 exhaustive theorem checks. Sixteen linters reported zero errors across 687 declarations plus 322 generated declarations. The inventory validated 172 retained files, 97 local links, all 26 source pins and 4,320 unchanged existing Lean files. No root pin or owner BAT changes, staging, commit or push occurred. All twenty source acceptance gates remain OPEN.

- [foundation_freeze_20261006_074617.log](../../logs/foundation_freeze_20261006_074617.log), SHA-256 `26224f3d449d52e68c19af42a4fd9945cd73fa8c63b532b3087c82ed87464c74`.
- [foundation_freeze_20261006_074617.json](../../logs/foundation_freeze_20261006_074617.json), SHA-256 `bbc77e05b3b6431f1aef2a352cc089931944e562edcfba3fa83cf9a23c9c359b`.
- [dubon-build-20261006-074923-821.log](logs/dubon-build-20261006-074923-821.log), SHA-256 `1c77b946ea4b35b12e853d9363583cfcb21baf94785dd75ffc13da6fe2c9e810`.

Current potential expansion after the verified 103-module checkpoint: three modules through `PotentialEquicontinuity` prove the local-uniform potential limit on all real abscissae from literal H1/H2. The root imports 106 production modules, with 44 exact consumers and 587 explicit theorem registrations. Focused modules and the aggregate audit passed with zero diagnostics: 915 exhaustive theorem checks, 587 explicit registrations, sixteen linters with zero errors across 700 declarations plus 330 generated declarations. Sequential verification is superseded by the next expanded checkpoint. All twenty source acceptance gates remain OPEN.

Current concentration expansion: six further modules through `WeakLimit` assemble the abstract analytic criterion, including tightness and weak probability convergence of the actual normalized Stieltjes measures after finitely many degenerate indices. The root imports 112 production modules, with 45 exact consumers and 605 explicit theorem registrations. Focused modules and the aggregate audit passed with zero diagnostics: 942 exhaustive theorem checks, 605 explicit registrations, and sixteen linters with zero errors across 719 declarations plus 339 generated declarations. Sequential verification passed with zero diagnostics, as recorded below. General vertical zero-frequency identification and the concrete arithmetic applications remain unproved. All twenty source acceptance gates remain OPEN.

Verified 112-module sequential checkpoint: foundation `cmd /c run_lake_build.bat --no-pause` returned **PASS, exit 0**, then paper `cmd /c run_dubon_build.bat --no-pause` returned **DEVELOPMENT PASS, exit 0**. Both had zero Lean diagnostics. Foundation coverage remains 301 production modules, two regressions, exact publication contracts and 14,290 discovered theorem dependencies. Paper coverage is 112 production modules, 45 exact consumers, 605 explicit registrations and 942 exhaustive theorem checks. Sixteen linters reported zero errors across 719 declarations plus 339 generated declarations. The inventory validated 181 retained files, 100 local links, all 26 source pins and 4,320 unchanged existing Lean files. `git diff --check` passed. No root pin or owner BAT changes, staging, commit or push occurred. All twenty source acceptance gates remain OPEN.

- [foundation_freeze_20261006_081057.log](../../logs/foundation_freeze_20261006_081057.log), SHA-256 `18bd62e20de48fa9458206225c4c7d1d65d925dfa0e6938f16d9092779be7820`.
- [foundation_freeze_20261006_081057.json](../../logs/foundation_freeze_20261006_081057.json), SHA-256 `e94f3b4b6c533c80c647a12d87e1f6844a467ccba64d7a7ccc475e2241050dc7`.
- [dubon-build-20261006-081346-738.log](logs/dubon-build-20261006-081346-738.log), SHA-256 `786a5d93e0a9d8c449ade96fb2fac561bde35f8ed3be0fbe51a2f66d75c4e896`.

Current arithmetic expansion after the verified 112-module checkpoint: five modules through `DyadicPrimeGrowth`, 117 production modules, 46 source consumers and 638 explicit registrations. The exact node-63 `GafniTaoNative` path was added while preserving every root pin; selected source hashes are recorded in `Tools/pnt_reuse.json`. The initial raw PNT+ import replayed two Wiener admission warnings and was replaced before acceptance by the existing audited local chain. All five focused modules now compile with zero diagnostics. Aggregate verification passed: 1,117 exhaustive theorem checks, 638 explicit registrations and sixteen linters with zero errors across 753 declarations plus 486 generated declarations. The four dependency-graph fixtures and all earlier source/inventory fixtures passed. Sequential verification is pending for this expansion. All twenty source gates remain OPEN.
