# Tao--Trudgian--Yang 2025 reproduction manifest

## Manifest status

**Verified implementation baseline, 20 September 2026.** A unified Lean
package, its selected frozen dependency, exact certificate kernel, semantic
regressions, and transitive axiom audit are installed. This is not yet a
paper-level release: no advertised exponent-pair, density, or energy theorem
is claimed complete.

## Frozen identifiers

| Artifact | Pin |
|---|---|
| primary paper | arXiv `2501.16779v1` |
| paper-time ANTEDB | `9953003a48f46fe8075ccf9534321f98f656032e` |
| current ANTEDB Lean survey | `088040634e8300f87e80f431d8bdc38c42cc8e11` |
| current ANTEDB Lean toolchain | `leanprover/lean4:v4.32.0` |
| local root Lean toolchain | `leanprover/lean4:v4.30.0` |
| local root mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| local `PrimeNumberTheoremAnd` | `4ecb950126c4290293c5662dfe0e884123171df5` |
| local Guth--Maynard release | annotated tag `gm-foundation-freeze-v1.0.1`, commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be` |

The Guth--Maynard dependency's own reproduction files remain authoritative for
its internal verification evidence. This target imports its canonical source
through the local root package rather than copying it.

## Source inventory

`Sources/SHA256SUMS.txt` is the machine-readable authority after the binary
artifacts are installed. `Sources/PINS.md` explains the role of every archive.

Required primary artifacts:

- `tao-trudgian-yang-2501.16779v1.pdf`
- `tao-trudgian-yang-2501.16779v1.tar`
- extracted `TaoTrudgianYang-v1-source/`
- `antedb-expdb-paper-time-9953003....zip`
- `antedb-expdb-current-0880406....zip`

Supporting arXiv sources and PDFs should be pinned where redistribution is
appropriate; citation-only sources remain listed in the source survey.

## Installed verification checks

The principal runner currently verifies:

1. every control document exists;
2. primary paper PDF and TeX are present;
3. both ANTEDB archive commits match their filenames;
4. all `Sources/SHA256SUMS.txt` entries match;
5. no `.lean` file in the target contains a prohibited shortcut;
6. the frozen ANTEDB subset hash ledger and inventory;
7. the complete installed production-module inventory;
8. byte-identical regeneration of the installed generated certificate module,
   including four new-pair coordinates, eight derived Bourgain pieces, and
   nine normalized public energy clauses;
9. a warning-clean default build and semantic regression build; and
10. a dynamic transitive axiom audit over imported boundaries and every
   nonprivate theorem in the target namespace.

Passing these checks certifies the currently installed package scope only.

### Paper-time Python smoke-test result

The archived snapshot was also probed with CPython `3.13.5`. The README
command `python tests/test_all.py` is not directly runnable from its documented
directory: the individual tests use package-relative imports, while
`test_all.py` imports them as top-level modules. Importing the tests through
the `python.tests` package gets past that mismatch but then stops at
`ModuleNotFoundError: No module named 'cdd'`. The snapshot contains no pinned
Python requirements file or environment manifest.

This is a reproducibility finding, not a failed mathematical test. EPZAE-06 must
identify and pin the intended `cdd`/`pycddlib` stack, record a package-aware
test invocation, and then preserve the resulting output. The archived source
has not been patched to conceal the upstream packaging issue.

## Future Python reproduction gate

Run the paper-time snapshot in a pinned Python environment and preserve:

- interpreter and dependency versions;
- exact commands for beta/exponent-pair, zero-density, and energy outputs;
- stdout/stderr logs;
- deterministic rational result files; and
- a comparison against the frozen paper tables.

Floating-point or linear-program output is discovery evidence. The release
gate additionally requires exact rational witnesses replayed in Lean.

## Lean runner and build gate

`run_tao_trudgian_yang_build.bat --no-pause` is the principal entry point and
must be updated whenever modules, pins, certificates, regressions, or audit
surfaces change. With the package installed, it currently:

1. resolve the target directory from the script location;
2. use the pinned target toolchain and dependency graph;
3. build the root library and every production module;
4. run semantic regressions and the exhaustive transitive axiom audit;
5. reject every Lean warning and linter diagnostic;
6. scan the entire target for `sorry`, `admit`, `sorryAx`, project axioms,
   `native_decide`, `implemented_by`, and unsafe proof bypasses;
7. verify source and dependency hashes/pins;
8. regenerate the installed paper-time exponent-pair, Bourgain-envelope, and
   public energy-clause data module and fail on a byte-level difference; and
9. write a timestamped complete log and return success only if all installed
   stages pass.

The deterministic extractor covers the four advertised pair coordinates, all
eight Bourgain pieces, and all nine public energy-clause tables, but extending
regeneration to the underlying energy projection witnesses and running the
full paper-time Python stack are still open
EPZAE-06/40 gates. Accordingly, runner success is a Lean
verification claim for installed modules, not a final paper reproduction
claim.

The latest installed-scope verification ran on 20 September 2026 with
`run_tao_trudgian_yang_build.bat --no-pause`, exited `0`, and wrote
`logs/tao-trudgian-yang-build-20260920-130458-fb69391d.log` (SHA-256
`5ed832a981330e597ed37280d309ebf2b394fe219f619fda1e6fa201c0575b4f`).
It scanned 114 Lean files and audited 1576 nonprivate target declarations plus five
imported boundary declarations and reported no warnings.
Its production inventory also checks that every package Lean source is listed
and every production module is imported directly by the root library. The
warning gate recognizes both bare and filename-prefixed Lean diagnostics.

This run covers the completed `zeroe-from-large` source inequality and the
four public theorems in `EnergyPoweringObstruction`, including the concrete
counterexample to source `power-energy`, and all nine public theorems in
`EnergyPowering`. The four new modules `EnergyPoweredPatterns`,
`EnergyPoweringLimits`, `CorrectedEnergyPowering`, and `EnergyPoweringBounds`
are also covered, with all 32 new named public theorems explicitly audited.
The three Heath--Brown modules (`HeathBrownEnergyFinite`, `EnergyLogLimits`,
`HeathBrownEnergy`) now contain 19 explicitly audited public theorems, including the
exact full-domain source relation, corrected powered consumer, and small-height
consequences. `ClassicalLargeValueRegions` and `EnergyClauseOneGeneral` add
22 explicitly audited public theorems: the actual Huxley energy-region
bridge, corrected cardinality powering, the exact clause-(i) general-energy
certificate, uniform higher-height bounds, and conditional final assembly.
`EnergyClauseOneZeta` adds 11 explicitly audited public theorems: its exact
zeta six-branch certificate, corrected Huxley cap, uniform-cardinality-to-region
bridge, and conditional energy/zero-energy consumers. Eight regressions
cover its endpoints, crossover, height transition, and literal remaining
analytic hypotheses. `ZetaMomentKernel`, `ZetaMomentTransfer`, and
`ZetaMomentAsymptotics` add 21 explicitly audited public theorems and ten
regressions for the literal critical-zeta convolution, weighted twelfth-power
Hölder, separated kernel occupancy, logarithmic-loss absorption, exact
source-window normalization, and actual-pattern consumers with both analytic
inputs explicit. `ZetaIntervalCutoff`, `ZetaMellinEntry`,
`ZetaMellinContour`, and `ZetaMellinShift` add 36 named public theorem
audits, an explicit audit of the constructed native cutoff test object,
and ten regressions for exact endpoints, physical support, phase, and
the residue-preserving whole-critical-line identity.
`ZetaCutoffDerivatives`, `ZetaMellinDerivative`, `ZetaMellinUniform`,
`ZetaMellinLocalization`, `ZetaPerronEntry`, and `ZetaTwelfthFromMoment`
now contain 39 public theorem audits, the derivative-test constructor audit, and
14 regressions. They cover uniform Mellin bounds, localization and error
absorption, actual source-window entry, and uniform LV from the genuine
dyadic moment. `ZetaShortPerron`, `ZetaShortPatterns`, and
`EnergyClauseOneFromMoment` add 11 more public theorem audits and eight
regressions. The new short-height LV theorem accounts for the increase
from 38 to 39 in the preceding six-module group. The actual short-zeta
range and full clause-(i) deduction now need only the genuine dyadic
moment as an analytic input. The current 68 package files are inventoried, and both obstruction
and repair reports are required project files. The counterexample source
hash remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`;
the original Lean file was checked byte-for-byte unchanged.

The owner-authorized two-witness repair is now fully proved:
`correctedCardinalityEnergyPowering : CorrectedCardinalityEnergyPowering`
depends only on `propext`, `Classical.choice`, and `Quot.sound`.
Its exact source-facing consumer is
`InLargeValueEnergyRegion.corrected_powering`. The repair report records
the semantic completion audit, in addition to the dependency audit.
EPZAE-34 and EPZAE-35 are complete. The actual-region
`InCardinalityEnergyRegion.heathBrown_powered` consumes the fully proved
analytic relation and powering theorem; it has no independent analytic
hypothesis. Their named audits report only `propext`, `Classical.choice`,
and `Quot.sound`. The repair report includes the source-semantic audit.
`EnergyPoweringBounds` proves the general
factor-two bounded-range reduction and a zero-energy transfer with zeta
endpoint `1`; the source endpoint `2` remains open. Neither those conditional
consumers nor runner success prove any advertised final estimate.

The clause-(i) general intermediate `imphb-lver-ineq` is now proved with
actual-region consumers, both sigma pieces and closed endpoints. Its uniform
bound extends to all `τ ≥ 8σ-4`. The final consumer
`energyClauseOne_of_zeta_range` still explicitly requires the zeta-energy
bounds on `[1,8σ-4)`; these and the source endpoint-two reduction remain
open. New semantic regressions cover the rational crossover, physical
height endpoints, actual input regions, and that conditional signature.
The six-branch certificate is a Lean proof, not external optimization output;
the broader paper-time Python/projection reproduction gate is still open.

The zeta rational certificate in `EnergyClauseOneZeta` is now proved,
including `σ=65/86`, `τ=4σ-1`, and the advertised-envelope comparison.
`energyClauseOne_of_twelfth_and_short_zeta` reduces final assembly to the
explicit short zeta-energy input on `[1,2)` and uniform twelfth-moment
cardinality on `[2,8σ-4)`. The later continuation derives the cardinality
input from the genuine dyadic moment alone. The short-height continuation
now derives the short-zeta input from that same moment. The moment and
independent source endpoint-two transfer remain open.
No Gafni--Tao twelfth-moment
instance or new dependency was imported. The initial focused regression
build reported one unnecessary-sequence-focus linter warning; the source
was repaired, the focused rebuild had no warning, and the full runner above
passed with zero warnings. No linter setting or warning gate was weakened.

The preceding moment-transfer implementation likewise had one initial
unnecessary-sequence-focus warning in its new interval regression; the
source was repaired before the successful focused and full builds above.
Its modular finite consumer retains both the pointwise Perron entry
inequality and the dyadic critical-line twelfth-moment bound. The moment
window and logarithmic losses are proved and actually consumed. The later
continuation supplies the Perron input and proves the uniform LV deduction
conditional only on the still-open dyadic moment.
The source hashes, dependency graph, and counterexample remain unchanged.

The preceding exact-source-entry implementation proves the sharp integer
cutoff, right-line inversion, absolute sum/integral interchange, finite
moving-pole residue formula, and justified critical-line contour shift.
`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin` consumes the
actual pattern and retains `mellin cutoff (1-it)`, with no independent
analytic hypothesis. At that milestone, uniform-in-`N` kernels,
localization, error absorption, the moment, and uniform LV remained open.
The quantitative continuation below now closes all of those deductions
except the moment theorem itself. The focused
`lake build TaoTrudgianYang2025.ZetaMellinShift` and
`lake build TaoTrudgianYang2025.SemanticRegression TaoTrudgianYang2025.Audit`
both exited `0` without Lean warnings before the full target PASS above.
No dependency, source archive, counterexample, or publication contract
was changed for this source-entry step.

The preceding uniform-source-entry continuation consists of
`ZetaCutoffDerivatives`, `ZetaMellinDerivative`, `ZetaMellinUniform`,
`ZetaMellinLocalization`, `ZetaPerronEntry`, and `ZetaTwelfthFromMoment`.
It adds 38 named public theorem audits, the constructed derivative-test
audit, and 14 semantic regressions. The actual-pattern `perron_entry`
derives its localized convolution estimate from exact endpoints, uniform
Mellin kernels, and proved residue/tail bounds.
`exists_zetaPerron_uniform_threshold` links its physical hypotheses to
all source windows `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`.
`zetaTwelfth_largeValueBound_of_dyadic` proves the uniform LV predicate
from the genuine dyadic moment alone. The composed clause-(i) consumer
retained only that moment and short zeta energy at that milestone. The
short-height continuation below now supplies the latter from the former.
Earlier unused-simp and sequence-focus diagnostics during development
were corrected in source, without weakening warning gates. The final
target and foundation runs recorded here include the subsequent comment
corrections identifying the proved entry and the remaining moment input;
both exited `0`, with no failed stage or Lean diagnostic.

The current short-zeta continuation adds `ZetaShortPerron`,
`ZetaShortPatterns`, and `EnergyClauseOneFromMoment`, and strengthens
`ZetaTwelfthFromMoment` with a proved short-height entry consumer. It
adds 12 public theorem audits and eight semantic regressions. Actual
source windows derive threshold-relative Perron entry on `τ ≥ 3/2`;
native first/second derivative bounds prove actual eventual emptiness
for `σ ≥ 3/4`, `1 ≤ τ < 3/2`. The exact cubic-energy comparison then
supplies all `[1,2]` short zeta energy from the genuine moment.
`energyClauseOne_of_dyadic_moment` composes the full clause-(i) deduction
with only that moment as a mathematical theorem parameter. Its signature
does not assume short-zeta energy or any cardinality/density conclusion.
The moment and all unconditional final outputs remain open. The
endpoint-two source theorem is not used or claimed proved by this route.

The focused command
`lake build TaoTrudgianYang2025.SemanticRegression TaoTrudgianYang2025.Audit`
exited `0` with 1136 permitted-dependency declarations and no Lean warnings.
Two initial sequence-focus warnings in the sharp-prefix proof were fixed
in source; no linter option or warning gate was weakened. The final target
and foundation runners also exited `0`, with no failed stage, Lean warning,
error, or linter diagnostic. Counterexample and source hashes are unchanged.

The preceding uniform-Perron run remains available as
`logs/tao-trudgian-yang-build-20260920-084133-a81add93.log` (SHA-256
`d8f8687032c85bd9acbd49c4dc0500a8cda6946761968c9964780f30b230ac3a`),
with 74 scanned Lean files, 63 package files, and 1124 audited declarations.

The preceding exact-Mellin-entry run remains available as
`logs/tao-trudgian-yang-build-20260920-075752-9b95a02f.log` (SHA-256
`e47122aad7c5c20d309665c0ef966718981ac6f86aee50624e743dd73f1c55f1`),
with 68 scanned Lean files, 57 package files, and 1055 audited declarations.

The preceding moment-transfer run remains available as
`logs/tao-trudgian-yang-build-20260920-072513-5a052a5a.log` (SHA-256
`23561d512810dfaf09df9efdfdaa18afdbf93b84e77d2afce5cfcaf77bf9c867`),
with 64 scanned Lean files, 53 package files, and 992 audited declarations.

The preceding zeta-certificate run remains available as
`logs/tao-trudgian-yang-build-20260920-065437-4b9205d0.log` (SHA-256
`b2434ba6dd6d21af89d439e9060cb14183640b558343ba238c1c1ac99c14468f`),
with 61 scanned Lean files, 50 package files, and 959 audited declarations.

The preceding general-energy run remains available as
`logs/tao-trudgian-yang-build-20260920-063749-a2160b60.log` (SHA-256
`ba237a3e6f34c4f8393ce8194fdbd55ee869ab2d6efcbe4e8f80cfd45a2d2c9b`),
with 60 scanned Lean files, 49 package files, and 939 audited declarations.

The preceding Heath--Brown run remains available as
`logs/tao-trudgian-yang-build-20260920-060628-7776c2a5.log` (SHA-256
`30e200b8a8af0e3a415000559ed443eecfe8a8b624d85bf5168a9a3fd9294f30`),
with 58 scanned Lean files, 47 package files, and 889 audited declarations.

The preceding full-powering/bounded-range run remains available as
`logs/tao-trudgian-yang-build-20260920-054235-1b403222.log` (SHA-256
`3e3f91c22a54d26300cf6c505bf933a7d565ffc2d6e1753f963c764914f0ca26`),
with 55 scanned Lean files, 44 package files, and 869 audited declarations.

The earlier two-witness specification/helper run remains available as
`logs/tao-trudgian-yang-build-20260920-045856-72eb21bc.log` (SHA-256
`4eea54fe0a21ced6c40a5060c5fc9a7d82d236a4d1a3771d1353d91d41d67166`).
The earlier pre-repair run remains available as
`logs/tao-trudgian-yang-build-20260920-001114-f84115e4.log` (SHA-256
`06f934a6db4a4f254184160140eb237f174c6eee322fd0ced746c36b7eaa84e7`).

Before the repair, the broader repository verifier was also run with
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`.
Its first run, `logs/foundation_freeze_20260920_000909.log`, failed only
because the text scanner classified two rational structure fields named
`constant` and seven comment lines as postulate declarations. The scanner
now distinguishes those cases, reads UTF-8, and runs eight positive/negative
regressions; no module or dependency-audit coverage was removed.
The rerun exited `0`, with final status `PASS`, no failed stages, and no
Lean warnings:

```text
log (relative to Riemann Zeta): logs/foundation_freeze_20260920_001239.log
log SHA-256: 1625cce51deb9634c6a2ddd7a73c48783c572b7cafa1eb2df8ce8b653150377c
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
```

The earlier repair-interface broader verification used the same command and unchanged
verifier, exited `0`, and reported `PASS`, with no Lean errors, warnings, or
linter failures:

```text
log (relative to Riemann Zeta): logs/foundation_freeze_20260920_045907.log
log SHA-256: b9e5fdb8cff283c87106cbcf394662aac9b7b645fcbd149cc2b232bb0afeba7e
manifest: logs/foundation_freeze_20260920_045907.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
```

The preceding full-proof and bound-transfer checkout was verified with
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`.
It exited `0`, reported `FINAL RESULT: PASS`, and had no failed stage, Lean
warning, error, or linter diagnostic:

```text
log (relative to Riemann Zeta): logs/foundation_freeze_20260920_054236.log
log SHA-256: 6b399e53035d4606df70bd928f83adf7a39032aa459affc8be599ff84f24174a
manifest: logs/foundation_freeze_20260920_054236.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding Heath--Brown checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_060629.log
log SHA-256: 60ce1a32d0e56fd979498d316fed9e4661db62b4a16808bbf1824621b6682d25
manifest: logs/foundation_freeze_20260920_060629.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding classical-region/general-energy checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_063751.log
log SHA-256: 41a00ea2c9f2da7d97ee4b457693b88356c93e3b92591bfc09f6a084fa2bfb3d
manifest: logs/foundation_freeze_20260920_063751.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding zeta-certificate checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_065438.log
log SHA-256: 66538a4ea141afda1dd46bd1aa99fce75ff20fec414e641d9b5aece53a4aeb63
manifest: logs/foundation_freeze_20260920_065438.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding moment-transfer checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_072524.log
log SHA-256: 6616c0f6b86df9b155b93a528b0478e984367f34b14a4a81fa7b112e9b6246b8
manifest: logs/foundation_freeze_20260920_072524.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding exact-Mellin-entry checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_075803.log
log SHA-256: fc5704b792871d9f4f9a1f237fd390a2ee099225fe6cca2adf8b351dfad54443
manifest: logs/foundation_freeze_20260920_075803.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding uniform-Perron-entry and moment-to-LV checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_084117.log
log SHA-256: ca5c47fcbc4c15b9124fc04fdf66b150cc5f05f4996f5b779dd59818747707cd
manifest: logs/foundation_freeze_20260920_084117.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: 094a9ec234d5dfe6494f0e79aa6b3006b85dfc39 (dirty worktree)
```

The preceding short-zeta and moment-only clause-(i) checkout also passed
`cmd /c run_lake_build.bat --no-pause` from `E:\Lean\Riemann Zeta`:

```text
exit code: 0
final result: PASS
failed stages: none
Lean warnings/errors/linter diagnostics: none
log: logs/foundation_freeze_20260920_090322.log
log SHA-256: 76cc4adbf5e11da66abcd52223c82ce7b0bc71dd1ab12d074ae3ca11c1da51fc
manifest: logs/foundation_freeze_20260920_090322.json
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
foundation audited nonprivate theorems: 14290
module closure: 301 foundation modules plus 2 retained regression modules
recorded HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
```

The recorded HEAD changed externally during this iteration; the agent
did not commit, push, revert, or overwrite that synchronization.
That preceding target runner covered 66 target-package files;
the broader runner separately verifies the canonical foundation and the
repository-wide integrity scans. Neither scope is substituted for the other.

Repository-wide manual shortcut scans also found no prohibited proof terms
or postulate declarations; the `constant` matches were the reviewed fields
and prose above. `git diff --check` passed. Git's initial LF-to-CRLF notices
were line-ending notices, not Lean diagnostics. All 61 public theorems in
the eight pre-repair energy modules, all nine public theorems in
`EnergyPowering`, and all 32 named public theorems in the four full-proof
and bound-transfer modules, plus all 19 current named public theorems in the three
Heath--Brown modules and all 22 named public theorems in the two new
classical-region/general-optimization modules and all 11 public theorems in
`EnergyClauseOneZeta`, plus all 21 public theorems in the three zeta-moment
modules and all 36 public theorems in the four exact Mellin source-entry
modules, plus all 39 public theorems in the six uniform-source-entry and
moment-to-LV modules and the original 11 public theorems in the three short-zeta
modules, have explicit named axiom audits in addition to dynamic declaration
discovery. The actual half-open pattern constructor and the constructed
native interval-cutoff and iterated-derivative test objects are also explicitly audited.
No commit or push was performed by the agent.

## Zeta discreteness continuation: 20 September 2026

`ZetaLargeValueDiscreteness` and `ZetaPointwiseNonexistence` add 12 named
public theorems. `zetaShort_pointwise_powerSaving` adds the thirteenth,
consuming the existing unconditional short-range cancellation. Eight new
regressions cover exact infimum/uniform semantics, arbitrary negative
rates, the negative-infinity equivalence, negative/zero/positive branches,
failure of the analogous arbitrary-real implication, and the actual
sharp-interval conclusion at `σ=3/4`, `τ=1`.

Semantic audit: the empty set is derived from actual finite cardinalities
below one. The pointwise direction constructs a singleton with the exact
indicator coefficients, sharp interval, and actual positive height. The
reverse direction absorbs the `[T,2T]` factor two by a quarter-radius
window and a common threshold. The maximum-to-double lemma uses this
discreteness but retains its explicit analytic-bound input; it is not a
proof of the twelfth moment. EPZAE-21/37 and the full goal stay open.

The final focused command
`lake build TaoTrudgianYang2025.ZetaPointwiseNonexistence` exited `0`
(8581 jobs) with no Lean warning. An earlier combined build succeeded
but reported one unnecessary-`simpa` linter diagnostic; the source was
fixed, not suppressed. The final principal runs were:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-092855-4e55a00b.log
target log SHA-256: 6cba804753ee39166d2c79caecde3fee13eb22fde4605d5bec6fbaeb5df5315f
inventory: 79 scanned Lean files; 68 package files; 28 required project files
audit: 1151 declarations (1146 target plus 5 imported boundary declarations)
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_092826.log
foundation log SHA-256: c5ad3548d104ab483be49b5c1d72ecad5df38ddad715dfb8746e3c2a8c5d70bd
foundation manifest: logs/foundation_freeze_20260920_092826.json
foundation audit: 14290 nonprivate project theorems
foundation closure: 301 modules plus 2 retained regression modules
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
failed stages: none
Lean warnings/errors/linter diagnostics in final runs: none
```

Repository-wide proof-term/bypass scans found no prohibited terms. The
postulate search matches only the already-reviewed structure fields and
comment prose; the principal scanner also passes. `git diff --check`
passes with Git line-ending notices only. The counterexample hash remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No source pin, existing public contract, package dependency pin, commit, or push was
changed by this continuation. Temporary PDF text-reader tooling under
`E:\Lean\.lake\pdf-tools` was used only to inspect existing sources and
is not a Lean or certificate-generation dependency.

The preceding target evidence remains
`logs/tao-trudgian-yang-build-20260920-090310-89f41b5b.log`, SHA-256
`3462bf6725a1e436d304ce3d8d342348ef76e2fc1fe0405a81c60a60facbf426`:
77 scanned files, 66 package files, and 1136 audited declarations.

## Exact local mean-square source entry: 20 September 2026

Six new production modules are directly root-imported and explicitly
inventoried: `ZetaSquareContour`, `ZetaSquareContourShift`,
`ZetaSquareDivisorKernel`, `ZetaSquareDivisorSeries`,
`ZetaSquareSourceEntry`, and `ZetaSquareLocalMean`. Their 47 public
theorems all have named `#print axioms` entries; a mechanical comparison
found zero missing entries. Nine new semantic regressions cover zero
height, reflection, actual divisor coefficients at zero/one, the common
Gaussian constant, integrated-norm summability, actual norm-square entry,
local windows, and degenerate intervals.

Semantic result: the source objects are the completed zeta square and
the actual critical-line zeta norm, not placeholders. The proof constructs
the entire numerator, proves the rectangle and horizontal limits, opens
the ordinary-divisor L-series only in its absolute-convergence half-plane,
and proves both sum--integral exchanges. Nonzero Gamma normalization
identifies the literal norm square. `hasSum_zetaSquareLocalMean` has only
the ordered-endpoint hypothesis `a ≤ b`, not a local mean-square or
twelfth-moment estimate. Compact-dependent convergence bounds do not
give Ivić's uniform Atkinson inequality. That inequality, the twelfth
moment, and all unconditional final `Add-est` outputs remain open.

The final focused build
`lake build TaoTrudgianYang2025.ZetaSquareLocalMean` exited `0`
(8888 jobs), and
`lake build TaoTrudgianYang2025.SemanticRegression TaoTrudgianYang2025.Audit`
exited `0` (8929 jobs). Both final focused builds had no Lean warning.
An earlier local-mean build reported an unnecessary tactic-sequence
linter diagnostic; its source was corrected, not suppressed.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-095940-3c99d628.log
target log SHA-256: 10c8cad3f79a06ea8de6eec1dd8fc55f9593f8b677a297155535cad4f90ed5aa
inventory: 85 scanned Lean files; 74 package files; 28 required project files
audit: 1234 declarations (1229 target plus 5 imported boundary declarations)
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_095952.log
foundation log SHA-256: 1f9b8b36251c43bd02e4adbf291f7046f7d3fdd829505b050f691ea4c41b2ac1
foundation manifest: logs/foundation_freeze_20260920_095952.json
foundation audit: 14290 nonprivate project theorems
foundation closure: 301 modules plus 2 retained regression modules
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
failed stages: none
Lean warnings/errors/linter diagnostics in final runs: none
```

Repository-wide proof-term and bypass scans found no prohibited terms.
The postulate search found only reviewed structure fields and comment
prose, and the principal scanner passed. `git diff --check` passed;
Git's LF-to-CRLF notices are not Lean warnings. The counterexample remains
byte-for-byte unchanged, SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No source archive, dependency pin, public output contract, commit, or push
was changed by this continuation. The adaptation provenance and adjacent
source hashes are recorded in `Tao-Trudgian-Yang Sources.md`.

## Uniform Gaussian averaging and quadratic transform: 20 September 2026

Three new production modules are directly root-imported and explicitly
inventoried behind `run_tao_trudgian_yang_build.bat`:
`ZetaSquareAveraging`, `ZetaSquareGaussianTail`, and
`ZetaSquareGaussianTransform`. Their 31 public theorems have named
`#print axioms` entries; a mechanical comparison found none missing.
Nine new regressions cover the central weight, closed window endpoint,
negative real weights, local majorization, the exact physical integral,
uniform logarithmic tails, the closed `G² = 2T` boundary, negative
frequencies, and the quadratic coefficient's imaginary part.

Semantic result: continuous weighted integrals of the actual normalized
divisor contributions sum to the actual weighted zeta second moment.
The local Gaussian majorization has the uniform constant `exp(1)`.
Centering preserves the Jacobian `G`, and whole-line integrability and
the omitted tail are proved for the actual zeta norm. One constant gives
`C G(1+|T|+G)² exp(-L²/2)`. For every real `A`, one threshold works for
all `0<G≤T` on the window `L=log T`, giving error `G T^(-A)`.
`exists_zetaSquareGaussian_source_approximation` actually combines this
tail with the weighted divisor identity, without a moment premise.

The literal quadratic kernel with coefficient `G^(-2)+i/(2T)` has its
exact Gaussian transform and the norm bound
`sqrt(pi) G exp(-(Gv)²/8)` for `T,G>0`, `G²≤2T`. No theorem yet
substitutes this kernel for the Gamma-normalized zeta source with a
uniform integrated error. That source-phase bridge, shortened divisor
sum, Voronoi/stationary-phase reduction, uniform Atkinson inequality,
scale/spacing assembly, and dyadic twelfth moment remain open.
No unconditional final `Add-est` clause is claimed.

The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression TaoTrudgianYang2025.Audit`
exited `0` (8932 jobs), with no Lean warnings. Earlier local elaboration
and tactic-sequence diagnostics were corrected in source; none was
suppressed or excluded from evaluation.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-102808-317166ea.log
target log SHA-256: 87d3742d4b7ad0c902d9b12c9ac239615979a46f0bb8a9fb7f945fda9119a415
inventory: 88 scanned Lean files; 77 package files; 28 required project files
audit: 1292 declarations (1287 target plus 5 imported boundary declarations)
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_102819.log
foundation log SHA-256: d48120533cc9f947580f65853d1bc977c009c6a7e2b753b60d0b3347817a28d1
foundation manifest: logs/foundation_freeze_20260920_102819.json
foundation audit: 14290 nonprivate project theorems
foundation closure: 301 modules plus 2 retained regression modules
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
failed stages: none
Lean warnings/errors/linter diagnostics in final runs: none
```

Repository-wide proof-term and bypass scans found no prohibited terms.
The postulate search found only reviewed structure fields and comment
prose; both principal integrity gates pass. `git diff --check` passes,
with Git line-ending notices only. The counterexample remains byte-for-byte
unchanged, SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No source archive, dependency pin, public output contract, commit, or push
was changed by this continuation. The full EPZAE-00--41 goal remains active.

## Actual digamma/Gamma-phase transform: 20 September 2026

Four production modules are directly root-imported and explicitly
inventoried behind `run_tao_trudgian_yang_build.bat`:
`ZetaDigammaLog`, `ZetaSquareGammaPhase`, `ZetaSquareGammaQuadratic`,
and `ZetaSquareGammaTransform`. All 25 public theorems have named
`#print axioms` entries; mechanical comparison found zero missing
audits. Twelve new regressions cover both closed digamma-height
boundaries, truncation zero, phase at zero, actual zeta reflection,
frequency at height two, both ends of the closed quadratic window,
the centred kernel identity, integrability at negative frequency,
radius-zero Gaussian tails, and the final actual-transform consumer.

Semantic result: the proof starts from the pinned actual digamma series,
not a Stirling assumption. Unit-interval logarithmic integrals and a
telescoping finite majorant yield `‖psi(z)-log(z)‖≤4/|Im z|` on the
right half-plane for both height signs. The literal quotient
`phi(t)=GammaR(1/2-it)/GammaR(1/2+it)` is linked to the actual zeta
functional equation and the existing contour's Gamma normalization.
Its exact real-frequency differential equation gives a closed-window
quadratic error `(18/T+2r²/T²)|x|`, for `T≥4`, `|x|≤r≤T/2`.

The finite integrated consumer identifies the precise coefficient
`G^(-2)+i/(2T)` and frequency `v-log(T/(2pi))`. The whole-line consumer
proves integrability, pays both tails, and gives error
`2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)`, uniformly for real `v`
and positive `G`. Its following norm bound actually uses the prior
quadratic damping theorem on `G²≤2T`.

The source factorization still contains the actual nonconstant
shifted-Gamma ratio squared, pole-removal factors, and contour/divisor
weights. These are not assumed controlled or replaced by one. Their
uniform amplitude estimate, weighted divisor truncation, Voronoi and
stationary phase, sharp Atkinson inequality, and dyadic twelfth moment
remain open. No final public output or unconditional `Add-est` clause
is claimed; the full EPZAE-00--41 goal remains active.

The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression TaoTrudgianYang2025.Audit`
exited `0` (8936 jobs), with no Lean warnings. Earlier local elaboration,
unused-argument, and tactic-sequence diagnostics were repaired in source;
no warning suppression, proof bypass, or module exclusion was added.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-110503-44e17aae.log
target log SHA-256: 681bdab26495407a9c4d1ce0739b69bd85d4ba4d64dcb6506e4dfaa3ecc0aa9d
inventory: 92 scanned Lean files; 81 package files; 28 required project files
audit: 1357 declarations (1352 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/linter diagnostics: none
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_110515.log
foundation log SHA-256: a4b2130cbf76c4f606b3c077e3b8fed8f217aa5f8e72b5765da135fc007333e7
foundation manifest: logs/foundation_freeze_20260920_110515.json
foundation audit: 14290 nonprivate project theorems
foundation closure: 301 modules plus 2 retained regression modules
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/linter diagnostics: none
```

Repository-wide proof-term and bypass scans found no prohibited terms.
The postulate search contains only reviewed structure fields and comment
prose; both principal integrity gates pass. `git diff --check` passes with
Git line-ending notices only. The original counterexample remains
byte-for-byte unchanged, SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No source archive, dependency pin, public contract, adjacent source file,
commit, or push was changed by this continuation. The source provenance
and primary DLMF reference are recorded in the source survey.

## Uniform actual amplitude and complete reflected-source remainder, 20 September 2026

Seven new root-imported modules prove the actual shifted-Gamma/pole
amplitude and its complete ordinary-divisor source consumer:
`ZetaGammaShiftLog`, `ZetaGammaShiftAmplitude`, `ZetaSquarePoleShift`,
`ZetaSquareNearKernel`, `ZetaSquareGammaInverse`,
`ZetaSquareKernelApproximation`, and `ZetaSquareLeadingDivisor`.
They contain 44 public theorems, each with a named axiom audit. Promoting
the exact existing `hasDerivAt_gammaReal` adds one further named audit;
the earlier phase-module public count is consequently 26 rather than 25.
Fourteen new regressions cover zero shift/height/coefficient, both signed
contour endpoints, the closed shift boundary, complete-series convergence
and the common source remainder constant.

For `t≥4`, `Re w≥0`, `‖w‖≤t/2`, the actual normalized squared
Gamma ratio has relative error at most `B exp(B)`,
`B=(17‖w‖+2‖w‖²)/t`. This follows from the proved digamma series,
principal-log path geometry, the exact derivative and Gronwall.
The actual squared pole factor is bounded by 9 and differs from one
by at most `12‖w‖/t`. The central contour consumes both estimates.
The far contour consumes Euler reflection and the actual inverse Gamma
normalization. Together they give one height-uniform integrable majorant
`C exp(-90u²)(1+|u|)^12` for the complete normalized reflected kernel error.

`hasSum_zetaSquareLeadingDivisorContribution` justifies the entire leading
ordinary-divisor series by absolute integrated-norm summability.
`exists_norm_zetaSquareDivisorIntegral_sub_leading_le` consumes that
series, the original reflected source integral and the complete-kernel
error, proving one uniform `O(1)` remainder for every `t≥4`. No Gamma
asymptotic, local mean-square or moment theorem is an input.

This superseded the previous continuation's open amplitude/remainder
status, not its open paper theorem status. At that historical checkpoint,
weight bounds, height variation and Gaussian source assembly were open;
the subsequent continuation below proves them for the complete quadratic
sum. Shortening, Voronoi/stationary phase, sharp Atkinson estimates, physical
scale/spacing assembly and the genuine dyadic twelfth moment. Therefore
`energyClauseOne_of_dyadic_moment` remains conditional and all final
`Add-est` clauses and the full EPZAE-00--41 goal remain incomplete.

The final focused command `lake build TaoTrudgianYang2025.SemanticRegression`
exited `0` (8942 jobs), with no warnings. The actual audit was rebuilt and
executed by the principal runner below. Earlier local elaboration and
unused-simp/tactic-sequence diagnostics were fixed in source; no warning
suppression, proof shortcut, source pin change or module exclusion was used.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-114345-833edc62.log
target log SHA-256: 34eba2ce1fd13e09304986671c04af8a4ee8497963d5a546ee984a717a911995
inventory: 99 scanned Lean files; 88 package files; 28 required project files
audit: 1428 declarations (1423 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/linter diagnostics: none
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_114346.log
foundation log SHA-256: 187789e37318837a4f86cb50d101892372dd0c7cce37e4c6e3f9499e234d24ee
foundation manifest: logs/foundation_freeze_20260920_114346.json
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 retained regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: de7b892efe8d9b97ef0b0cebdace2baeea0189c3 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/linter diagnostics: none
```

Repository-wide proof-term and unsafe-bypass scans found no prohibited
terms. The postulate scan contains only reviewed structure fields and
comment prose; both principal integrity gates pass. `git diff --check`
passes, with Git line-ending notices only. The original singleton
counterexample remains byte-for-byte unchanged, SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The repaired two witnesses and Heath--Brown relation are unchanged.
No paper archive, dependency pin, adjacent source file, commit or push
was changed. Goal, architecture, checklist, research report, crosswalk,
repair note, READMEs, source survey and principal runner inventory are
synchronized with this precise partial scope.

## Actual weight, freezing and quadratic Gaussian source, 20 September 2026

Nine new modules implement the continuation:

- `ZetaDivisorWeightKernel`, `ZetaDivisorWeightReflection`,
  `ZetaDivisorWeightSource`, `ZetaDivisorWeightVariation`,
  `ZetaDivisorWeightMass`, and `ZetaDivisorWeightFreezing`;
- `ZetaFrozenDivisorGaussian`, `ZetaSquareRealSource`, and
  `ZetaSquareFrozenWindow`.

The actual Mellin integral satisfies `W(q)+W(-q)=1`, `W(0)=1/2`,
and the bounded small-index/decaying large-index estimates on fixed
imaginary strips. Its physical argument retains imaginary part `pi/2`.
Height variation is bounded by
`C (abs x/T) min(T/(2pi n),2pi n/T)` on `abs x≤T/2`.
The absolutely summed coefficient mass is `Oε(T^(1/2+ε))`,
derived from the native convergent divisor L-series.

The complete source freeze keeps the actual phase and oscillatory
coefficient at `T+x`, with error `Cε abs(x) T^(-1/2+ε)` on
`T≥8`, `abs x≤T/2`. Conjugation of both original contour branches
proves the factor-two real-zeta source identity, including height zero.
The new Gaussian source consumer proves the precise finite-window
comparison documented in the goal, with the freeze, Gaussian tails
and actual Gamma-phase replacement all consumed in its proof.

Semantic verdict: these are actual source consumers, without a moment
or result-shaped theorem premise. They prove a comparison with a
complete quadratic divisor sum, not source-scale shortening, the
Voronoi/stationary reduction, Ivić Theorem 6.2 or the twelfth moment.
The latter remains the explicit analytic premise of
`energyClauseOne_of_dyadic_moment`. All nine unconditional
`Add-est` clauses and the full EPZAE-00--41 goal remain open.

All 78 new public theorems have named axiom audits and are also
discovered by the exhaustive audit. Twenty regressions test the
reflection, zero coefficient, signed argument, both closed half-height
endpoints, exact phase retention, factor two at height zero, closed
Gaussian-width boundary, absolute integrated-norm summability and
the complete source-consumer quantifiers. Every new module is a direct
root import and required by the batch runner's backing inventory.

The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` exited `0`
(8951 jobs), without warnings. Earlier elaboration/unused-simp diagnostics
were repaired in source; no warning suppression, excluded module or
proof shortcut was used. The principal runner rebuilt and executed
the real dependency audit.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-123627-bee4d657.log
target log SHA-256: 654d7eec7175fa97055e2028b8ebfef312b17e384c742fa9221a8d1643f902d0
inventory: 108 scanned Lean files; 97 package files; 28 required project files
audit: 1548 declarations (1543 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/linter diagnostics: none
```

The root principal verifier also passed:

```text
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_123638.log
foundation log SHA-256: 6953c1269e3d0009ac4494eb28c5557025ada1a74ddeab474aae0d03afb154e7
foundation manifest: logs/foundation_freeze_20260920_123638.json
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 retained regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: 77fe3141d73fe1b85e24a33735dd3d8e6f27535b (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/linter diagnostics: none
```

The checkout advanced externally during this continuation, from
`de7b892efe8d9b97ef0b0cebdace2baeea0189c3` to
`77fe3141d73fe1b85e24a33735dd3d8e6f27535b` (`Progress Update`).
The agent did not commit, push or revert that change. The verifier's
current-checkout evidence uses the latter HEAD and records a dirty worktree.

Repository-wide proof-term and unsafe-bypass scans find no prohibited
terms. The postulate matches are reviewed comment prose and rational
structure fields, not project postulates. `git diff --check` passes
with Git line-ending notices only. The counterexample remains unchanged:

```text
EnergyPoweringObstruction.lean SHA-256:
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487
```

No source archive, dependency pin, adjacent source file or corrected
powering/Heath--Brown theorem was changed. The goal, architecture,
checklist, research report, crosswalk, repair note, READMEs, source
survey and principal runner inventory describe the same partial scope.


## Source-scale finite divisor entry, 20 September 2026

Six new modules implement the next actual source stage:

- `ZetaQuadraticDivisorBand` and `ZetaQuadraticDivisorShortening`;
- `ZetaSourceLogScales` and `ZetaSourceErrorScales`;
- `ZetaShortDivisorSource` and `ZetaShortDivisorGeometry`.

The actual finite band consists exactly of positive integers with
`G abs(log n-log(T/(2pi)))≤L`, including both endpoints.
Its complement is bounded by the actual coefficient mass times
`sqrt(pi) G exp(-L²/8)`. At `L=log T`, the complete-to-finite
divisor-source error is at most `G T^(-A)` for every requested
real `A`, uniformly after one height threshold before all widths.

For each `δ>0`, the physical source scales
`0<G≤T^(1/2-δ)` derive the half-height window, `G²≤2T` and
`G≤T`. Choosing the coefficient-mass loss `δ/4` and controlling
the logarithmic powers makes the actual freezing/phase error
`Oδ(G log T)`. Both the whole-line Gaussian and unsmoothed local
zeta-second-moment source consumers are proved, with the finite
oscillatory sum retained literally. On `G≥T^δ`, every retained
index satisfies
`abs(n-T/(2pi))≤T log T/(pi G)` and lies in
`[T/(4pi),T/pi]`. The finite sum equals the ordinary divisor
weight applied to the exact complex real-variable test function.

Semantic verdict: the public
`exists_zetaSquareLocalMean_le_short_divisor` consumes the actual
zeta moment, actual Gaussian/window tails, exact reflected phase,
frozen source and finite-band shortening. It has no analytic theorem
premise. This closes source-scale finite divisor entry, not the
smooth-source Voronoi/Bessel/stationary reduction, sharp Ivić/Atkinson
inequality or the genuine twelfth moment. The latter is still the
explicit analytic premise in `energyClauseOne_of_dyadic_moment`.
All nine unconditional `Add-est` clauses and all other full-goal
outputs remain required and incomplete.

The six modules are direct root imports and required by the backing
inventory of `run_tao_trudgian_yang_build.bat`. All 29 public
theorems have named transitive audits and are discovered mechanically.
Eighteen new regressions check zero coefficients, the zero-frequency
centre, both closed band endpoints, closed Gaussian scale, arbitrary
power tails, uniform source-width quantifiers, the actual local
moment, physical support and the exact divisor test-function consumer.

The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` exited `0`
(8957 jobs), without warnings. Earlier local syntax/elaboration and
tactic-sequence diagnostics were repaired, without warning suppression
or excluding modules. The principal runner rebuilt and executed the
actual dependency audit.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-130458-fb69391d.log
target log SHA-256: 5ed832a981330e597ed37280d309ebf2b394fe219f619fda1e6fa201c0575b4f
inventory: 114 scanned Lean files; 103 package files; 28 required project files
audit: 1581 declarations (1576 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/linter diagnostics: none
```

The current foundation verifier also passed:

```text
foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_130510.log
foundation log SHA-256: f1975786880809edfa12dfce036be41b76be6702c915b98a9b050473fda7bee0
foundation manifest: logs/foundation_freeze_20260920_130510.json
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 retained regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: 77fe3141d73fe1b85e24a33735dd3d8e6f27535b (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/linter diagnostics: none
```

`git diff --check` passed after synchronization, with Git line-ending
notices only. Both principal runners emitted zero Lean warnings,
errors or linter diagnostics. Their success certifies the installed
scope, not the remaining paper outputs.

The next native Voronoi interface was inspected, not assumed to apply.
Its `DFIVoronoiTestFunction` requires smoothness and compact positive
support of the actual test function. The hard finite band is not such
an instance. The exact native files/hashes and the remaining cutoff
obligation are recorded in the Sources document. No adjacent file,
source archive or dependency pin was changed.

Repository-wide proof-term and unsafe-bypass scans find no prohibited
terms. The postulate matches are reviewed comments and rational
structure fields, not postulates. The Lemma 62 counterexample remains
byte-for-byte unchanged, SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent fifth coordinates and all powering/Heath--Brown
proofs are preserved. No commit, push, source pin change or module
exclusion was performed by the agent.


## Actual smooth Voronoi/Bessel source verification — 20 September 2026

This continuation adds eight required production modules, 43 named
public theorem audits and 18 semantic regressions. All eight are
directly imported by the root and listed in the inventory backing
`run_tao_trudgian_yang_build.bat`. The counterexample and prior dirty
work were preserved.

The green-node/source-entry test for architecture node `ZVT` is:
`exists_zetaSquareLocalMean_le_bessel` consumes the actual zeta
local moment, the proved finite source, constructed globally smooth
positive-support test, paid cutoff error, native modulus-one Voronoi,
and both literal Bessel bridges. Its conclusion has the full
logarithmic main term and both actual `Y0`/`K0` integrals, with
`-2pi`/`4` normalizations and uniform `Cδ G log T` source error.
No moment, smoothness, support, contour-shift or Voronoi theorem is
assumed for this source. Its companion
`exists_zetaSquarePhysicalGaussian_bessel_approximation` controls
the actual whole-line physical Gaussian integral.

This verifies the source-entry edge only. Uniform main/K0 estimates,
the oscillatory Y0 stationary reduction, sharp Ivić/Atkinson inequality,
genuine twelfth moment and all unconditional `Add-est` outputs remain
open. EPZAE-21/37 and the complete EPZAE-00--41 goal remain active.

The initial standalone regression build found a computational
`example` of the noncomputable constructed test. It was explicitly
marked `noncomputable example`; the exact theorem/structure and
analytic content were unchanged. The subsequent full target runner
compiled the repaired regression and passed every stage.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-133118-d2959250.log
target log SHA-256: cad67ff91accc63e905984288f134b46a33a0bcb599b9f1623b0d12137abee7f
default build: 8965 jobs
inventory: 122 scanned Lean files; 111 package files; 28 required project files
audit: 1642 declarations (1637 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_133052.log
foundation log SHA-256: dfeb6aa653a02c48e6cb17f39c065c78a20dc9ffdb8e847d6f890c9564e99bc5
foundation manifest: logs/foundation_freeze_20260920_133052.json
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 retained regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: 77fe3141d73fe1b85e24a33735dd3d8e6f27535b (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/linter diagnostics: none
```

Repository-wide proof-term and unsafe-bypass scans found no prohibited
terms. Postulate-pattern matches were reviewed comment prose and two
rational structure fields, not mathematical postulates.
`git diff --check` passes; Git emits only LF-to-CRLF notices.
The counterexample's SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent fifth coordinates and powering/Heath–Brown
theorems are unchanged. Existing native Bessel files were inspected
and imported, not edited or copied; their hashes are recorded in
Sources. No dependency pin, exclusion, commit or push was changed
by the agent.


## Complete K0 removal and source-aligned saddle verification — 20 September 2026

This continuation adds thirteen required production modules: seven for
literal K0 decay, full smooth support/mass and complete-series removal,
and six for the lattice phase, reapplied Voronoi, phase-adjusted K0
removal, exact carrier factorization and unique nondegenerate saddle.
All thirteen are directly root-imported and explicitly listed in the
inventory backing `run_tao_trudgian_yang_build.bat`.
There are 69 new named public theorem audits and 38 new semantic
regressions (29/16 for K0 and 40/22 for the phase-aligned chain).

The architecture/source-entry checks are:

- `ZK`: `exists_zetaSquareLocalMean_le_main_minus` consumes the
  actual full smooth support, literal K0 integral, divisor series at
  two and arbitrary power saving. It removes the complete branch
  from the actual local zeta source, uniformly on
  `T^δ≤G≤T^(1/2-δ)), with `Cδ G log T` error.
- `ZAP`: `exists_zetaSquareLocalMean_le_atkinson_reduced` uses
  the actually phase-adjusted source and its newly proved K0 bound.
  The phase equals one at every natural index and has unit norm
  and unchanged support for real x; its continuous integral is not
  identified with the old integral. The native smooth test is
  constructed, Voronoi reapplied, and new complete arithmetic
  convergence proved. No source estimate is assumed.
- The physical Gaussian companions prove the corresponding absolute
  source error. Constants and thresholds precede every allowed width.
- `ZAT` remains open. Exact actual-amplitude/carrier factorization
  and `zetaAtkinsonPhase_stationary_iff` link the saddle to
  `T/(2pi)`; `zetaAtkinsonPhase_secondDeriv_saddle_neg` proves
  nondegeneracy for every real carrier parameter. These are not
  a Y0 asymptotic expansion or a uniform stationary-phase estimate.
  The variable complex Mellin/Gamma/Gaussian amplitude is retained.

The pinned Ivić source was reread in place at PDF pages 115--117,
printed pages 110--112: (6.36), (6.38), (6.47). This exposed the
essential lattice-phase insertion before the stationary reduction.
The source's sign is conjugated to match the actual Lean divisor
test. Its SHA-256 and exact use are recorded in Sources. No scan or
native source was copied, changed or imported from the incompatible
adjacent Gafni–Tao package.

Focused development found and repaired explicit natural-cast
regression mismatches, a nested-comment typo, algebraic normalization
errors and tactic-style diagnostics. All repaired modules and
regressions compiled in the final principal run. No warning was
suppressed and no module excluded.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-142518-62ab5433.log
target log SHA-256: 67f56da0c2a7361b280cd8663a737252409c17399ada502185e969be9078865d
default build: 8978 jobs
inventory: 135 scanned Lean files; 124 package files; 28 required project files
audit: 1738 declarations (1733 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_142530.log
foundation log SHA-256: 7ac38652b329992f1ed7cfb133d987a3359c62b137ce12b2ed8f428a5acc41fa
foundation manifest: logs/foundation_freeze_20260920_142530.json
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 retained regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: 77fe3141d73fe1b85e24a33735dd3d8e6f27535b (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

Repository-wide prohibited-proof and unsafe-bypass searches found no
matches. Postulate-pattern matches were inspected: comment prose
and two rational structure fields, not postulates. The runners'
semantic scans also passed. `git diff --check` passes, with Git
LF-to-CRLF notices only; those are not Lean diagnostics.

The original Lemma 62 counterexample is byte-for-byte unchanged:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The repaired independent fifth coordinates, actual cardinality/energy
powering and Heath–Brown proofs are unchanged and remain audited.

The phase-adjusted main estimate, literal Y0 asymptotic and uniform
stationary reduction, sharp Atkinson inequality, physical dyadic/Gram
assembly and genuine twelfth moment remain required. The conditional
moment premise in the existing clause-(i) consumer is not discharged.
Every unconditional `Add-est` output, EPZAE-21/37 and the full
EPZAE-00--41 goal remain open. These PASS logs certify the installed
scope, not completion of the paper.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and this
manifest are synchronized. The exact batch interface and both
principal runners remain mandatory as the proof changes. No commit,
push, source/dependency pin change or exclusion was performed.

## Actual logarithmic main-term removal verification — 20 September 2026

Nine new production modules are directly root-imported and included in
the inventory backing `run_tao_trudgian_yang_build.bat`:

- `IntervalAmplitudeBounds`, `ZetaMainElementaryWeights`,
  `ZetaMainMellinProfile`;
- `ZetaLogGaussianVariation`, `ZetaQuadraticGaussianDerivative`,
  `ZetaQuadraticLogGaussianVariation`;
- `ZetaAtkinsonMainWeight`, `ZetaAtkinsonMainIntegral`,
  `ZetaAtkinsonMinusSource`.

All 38 new public theorems have named axiom audits, and all 20 new
semantic regressions are covered by the principal runner. The new
`ZAM` node closes the actual phase-adjusted main-integral substep,
not `ZAT`, the twelfth moment or a final paper output.

The semantic/source-entry audit is:

- `IntervalC1Bound` records actual derivative-norm integrals and
  pointwise bounds. Its source instances are proved for the cutoff,
  complex rescaled Mellin profile, square root, logarithm, unit Gamma
  factor and exact quadratic Gaussian; they are not final theorem
  hypotheses.
- The quadratic transform derivative retains its Gaussian damping.
  Actual logarithmic-envelope variation proves the uniform complex
  transform variation bound `4 sqrt(pi) G`, without losing an
  additional power of G. Every cutoff transition is included.
- `exists_intervalC1Bound_zetaAtkinsonMainWeight` constructs one
  `C G sqrt(T) log T` norm/variation bound for the complete
  amplitude, before choosing the source parameters.
- The actual main integrand is absolutely integrable, and
  `zetaAtkinsonVoronoiMain_eq_reflection` proves the exact
  positive-support restriction and carrier identity. The native
  `norm_weighted_gmReflectionIntegral_le` then supplies square-root
  cancellation. `exists_norm_zetaAtkinsonVoronoiMain_le` proves
  `norm(V0_A)≤C G log T` for `T≥16`, `log T≥1`,
  `G>0`, `G²≤2T`, `L>0`, `8L≤G`.
- `exists_zetaAtkinsonVoronoiMain_log_bound` derives every scale
  condition uniformly at `L=log T` before the choice of
  `T^δ≤G≤T^(1/2-δ)`.
- `exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation`
  and `exists_zetaSquareLocalMean_le_atkinson_minus` consume
  that actual bound. The complete phase-adjusted Y0 divisor sum
  remains with its literal `-2pi` normalization, factors `2`
  and `2 exp(1)`, and uniform error `Cδ G log T`. Neither
  an analytic estimate nor a moment is assumed.

Focused development compiled every new module incrementally. The
final focused `lake build TaoTrudgianYang2025.SemanticRegression`
passed with 8987 jobs and no Lean warning. The first principal
attempts rejected a documentation line beginning with
`constant over a length ...` in
`ZetaQuadraticGaussianDerivative.lean` as a possible postulate.
The line was rephrased; the proof and both scanners were unchanged.
These earlier logs are **failed historical attempts**, not verification
evidence for the final source:

- `logs/tao-trudgian-yang-build-20260920-145618-20e76021.log`,
  exit 1, shortcut-scan failure;
- foundation `logs/foundation_freeze_20260920_145620.log`,
  exit 1, proof-integrity-scan failure.

Both runners were subsequently rerun on the corrected source, with
no excluded module, suppressed warning, changed scan or altered pin.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-145714-b1ec7fad.log
target log SHA-256: 245cb9c17670f5ef6c4ced82299d1997711abcf1afeb84ba28c8f698e1af20d8
default build: 8987 jobs
inventory: 144 scanned Lean files; 133 package files; 28 required project files
audit: 1796 declarations (1791 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_150305.log
foundation log SHA-256: e58699b50e03c409f3ff4cdfaec7a05997aa4ed59756e97d27fed6e6ef66ec8c
foundation manifest: logs/foundation_freeze_20260920_150305.json
foundation manifest SHA-256: bffd6407ed92e9ec5129e2cd1db3417fc4953c29353d3c16a0bfcaf0b3a42243
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD: 77fe3141d73fe1b85e24a33735dd3d8e6f27535b (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

Repository-wide placeholder and unsafe-bypass searches found no
matches. Postulate-pattern matches are comment prose and two
rational structure fields, not mathematical postulates; both
principal semantic scans pass. `git diff --check` passes,
with only Git LF-to-CRLF notices, not Lean diagnostics.

The original Lemma 62 counterexample remains byte-for-byte unchanged:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent fifth coordinates, actual powering and
Heath–Brown proofs remain preserved and audited. The native
reflection file was imported, not copied or edited; its hash is in
Sources. Online DLMF/Mathlib research for the next Y0 step is recorded
there as research, not a formal proof or an imported assumption.

The phase-adjusted logarithmic main term, previously open, is now
bounded and removed. Literal Y0 asymptotics, uniform oscillatory
stationary reduction, the sharp Atkinson inequality, physical
dyadic/Gram assembly and the genuine twelfth moment remain open.
The conditional moment premise in the clause-(i) consumer is not
discharged. EPZAE-21/37, every unconditional `Add-est` output
and the complete EPZAE-00--41 goal remain open.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and this
manifest agree on that distinction. The exact batch interface
remains required and its inventory must evolve with the proof.
No commit, push, source/dependency pin change or exclusion was made.


## Literal Neumann expansion and complete source replacement — 20 September 2026

Current milestone: thirteen production modules, 71 new named public
theorem audits and 25 semantic regression examples. All are imported
by the default root and included in the backing inventory of the
unchanged human-facing `run_tao_trudgian_yang_build.bat` interface.

Modules: `NeumannContourKernel`, `NeumannContourShift`,
`NeumannSchlafliEntry`, `NeumannLaplaceRepresentation`,
`NeumannLaplaceAmplitude`, `NeumannRayFactorization`,
`NeumannLaplaceMoments`, `NeumannLaplaceRemainder`,
`NeumannTwoTermExpansion`, `NeumannSourceBounds`,
`ZetaNeumannRemainder`, `ZetaNeumannSeries`,
`ZetaAtkinsonTwoTermSource`.

Semantic/source-entry evidence:

- `neumannContourKernel_finite_rectangle` applies Cauchy to the
  actual analytic kernel with its two separate principal half-powers.
  The top side tends to zero, both vertical rays are absolutely
  integrable, and the limiting ray through one is continuous.
- `neumann_schlafli_complex_identity` proves the exact angular/ray
  identity. The ray through zero equals the existing Schläfli tail.
  `dfiBesselY0_eq_neumannLaplaceIntegral` therefore consumes the
  literal native definition, not a renamed substitute.
- `norm_neumannLaplaceAmplitude_sub_linear_le` proves
  `|(1+iu)^(-1/2)-1+iu/2|≤3u²/8` for all real u.
  The three actual Gamma moments and ray coefficient `(1+i)/2`
  are evaluated before the error integral is bounded.
- `abs_dfiBesselY0_sub_neumannTwoTerm_le` proves, for every x>0,
  `|Y0(x)-P(x)|≤K x^(-5/2)`, where
  `P(x)=sqrt(pi)/pi*((sin x-cos x)x^(-1/2)-(sin x+cos x)x^(-3/2)/8)`
  and `K=(2/pi)(9/128)sqrt(pi)>0`. No asymptotic or DLMF
  statement is a theorem parameter.
- `abs_neumann_source_remainder_le` links the actual argument
  `4pi sqrt(nx)` to `x≥T/16`, `T≥16`, `n≥1`,
  giving `K T^(-5/4)n^(-5/4)`. Actual measurability,
  positive support and absolute integrability are proved before
  subtraction or integration.
- `zetaAtkinsonY0Term_eq_native` identifies the complete original
  summand before using native Voronoi summability. The ordinary
  divisor Dirichlet series at 5/4 sums the actual error. The zero
  divisor coefficient, all complex amplitudes and `-2pi`
  normalization are preserved. The new oscillatory series is
  proved summable, not split into unjustified absolute sums.
- `exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le` gives
  `norm(VY_A-W)≤C G` for `T≥16`, `G>0`, `G²≤2T`,
  `L>0`, `8L≤G`, with one C>0 independent of all source
  parameters and of the complete divisor index.
- `exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation`
  and `exists_zetaSquareLocalMean_le_atkinson_twoTerm` consume
  the complete replacement at `L=log T`. For each δ>0, one
  Cδ>0 and T₀≥16 work for every `T≥T₀`,
  `T^δ≤G≤T^(1/2-δ)`. They retain source factors `2`
  and `2 exp(1)` and error `Cδ G log T`, without an
  amplitude, Bessel, convergence, stationary or moment premise.

The 25 regressions exercise the branch coefficient and negative
amplitude arguments, continuity/integrability at the endpoint ray,
literal Y0 at a small positive argument, all three moments, physical
height/index linkage, zero divisor coefficients, the closed
`G²=2T` endpoint, complete series identities and both actual
zeta consumer signatures. The preserved counterexample remains in
the root, explicit audit, dynamic audit and runner scope.

Focused compilation was incremental. Development failures were
ordinary elaboration issues (function pointwise products/subtractions,
an unnecessarily inferred source height, cast normalization and
extra tactics after a solved goal); one unused simp argument was
removed. No failing source was excluded and no warning was suppressed.
Final focused command `lake build TaoTrudgianYang2025.SemanticRegression`
exited 0 with 9000 jobs and no Lean warnings. Both principal runners
then passed on the final Lean/audit/inventory source:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-155612-208ed31e.log
target log SHA-256: 2cb2158044aa66f3a88757f9b7998f9475e376067a775a573d56460b087d85b5
default build: 9000 jobs
inventory: 157 scanned Lean files; 146 package files; 28 required project files
audit: 1893 declarations (1888 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_155623.log
foundation log SHA-256: 03e3b03aea89d8b296e73e984974effb9b6f843396e7d0c8bdda1ebb5ca34566
foundation manifest: logs/foundation_freeze_20260920_155623.json
foundation manifest SHA-256: a41a8d11c3d0619576cd72646aa690b59c1ae32e8bc6ebe73f7025f27cc88dd9
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

Both audits permit only the ordinary Lean/Mathlib logical axioms
`propext`, `Classical.choice`, `Quot.sound`. The exact
`energyPowering_source_counterexample` is explicitly and dynamically
audited. Its source SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The actual independent-coordinate powering and Heath–Brown chain
are unchanged.

Repository-wide placeholder and unsafe-bypass searches found no
matches. Postulate-pattern matches are existing comment prose and
two rational structure fields, not mathematical postulates; both
principal semantic scans pass. `git diff --check` passes, with
Git LF-to-CRLF notices only, not Lean diagnostics. The native
`DFIEquation24.lean` was imported in place, not copied or edited;
its hash and the primary-source normalization checks are recorded
in Sources. No dependency/source pin, scanner or warning gate changed.

Mathematical verdict: the literal Y0 expansion and complete
two-term source replacement are now kernel-checked. Uniform
stationary evaluation of the actual series, the sharp Atkinson
inequality, physical dyadic/Gram assembly and the genuine twelfth
moment remain open. The clause-(i) consumer still has its genuine
moment premise. EPZAE-21/37, all unconditional Add-est outputs and
the full EPZAE-00--41 goal remain open.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and this
manifest record that same boundary. Node ZAY is green only for
the exact ray/expansion/complete-source consumers; ZAT and ZTM
remain open. Both principal runner requirements and counterexample
preservation remain in the goal. No commit or push was performed
by the agent.


## Actual signed-carrier cancellation and source consumers, 20 September 2026

Ten production modules close the frequency-uniform cancellation edge
for the actual power-weighted source. They do not close the stationary
main-value asymptotic or the genuine twelfth-moment theorem.

| Module | Named public theorem audits | Proved scope |
|---|---:|---|
| `AtkinsonRootPhase` | 8 | Exact square-substituted phase, derivatives and actual saddle slope factorization |
| `AtkinsonFirstDerivative` | 4 | Native reciprocal-slope consumer, proved orientation reflection, both actual tails |
| `AtkinsonRootIntegral` | 5 | Actual unit kernel, integrability, central interval and uniform bound four |
| `AtkinsonAmplitudeIntegral` | 2 | Actual derivative-mass preservation under the square map and weighted integral bound |
| `AtkinsonPowerWeight` | 4 | Actual power/Mellin profile, exact amplitude identity and constructed uniform variation |
| `AtkinsonPowerIntegral` | 3 | Actual source Jacobian, support restriction and uniform power-integral estimate |
| `AtkinsonCarrierAlgebra` | 4 | All four signed Neumann carriers with exact argument powers and coefficients |
| `AtkinsonCarrierIntegrals` | 6 | Actual integrability, term identities and complete arithmetic summability |
| `AtkinsonCarrierBounds` | 4 | Both signed power pairs and actual leading/correction summand bounds |
| `AtkinsonCarrierSource` | 3 | Exact complete-series identity and both physical zeta consumers |

The 43 named public theorem audits and 24 semantic regressions
are added to the existing audit/regression modules. All ten modules
are in the root and the backing inventory of the exact
`run_tao_trudgian_yang_build.bat` interface. No production module,
audit scope or warning gate is excluded or narrowed.

The exact normalized phase after `x=y²` is
`q(T,b,y)=(T/pi)log y-y²+2by`. Its slope is
`2(r-y)(1+(r-b)/y)`, where r is the actual positive saddle
and `r-b>0`. Beyond r±1 its magnitude is at least two.
The pinned native reciprocal-slope theorem supplies both tail
bounds after constructing its actual regularity and monotonicity
hypotheses. The positive orientation is proved by reflection,
not assumed. The central interval has length at most two.
Thus the actual kernel integral has norm at most four on every
`0<a≤c`, for every `T>0` and real b.

Integration by parts and the exact derivative-mass substitution
give the weighted bound `8M`. The actual cutoff, power/Mellin
profile, unit Gamma factor and damped Gaussian construct M.
The public consumer `exists_norm_atkinsonPowerIntegral_le`
therefore proves, for each real α, one Cα>0 with

```text
Iα(T,G,L,b) = integral_(x>0) gA(x) x^(-α) exp(4pi i b sqrt(x)) dx,
|Iα(T,G,L,b)| ≤ Cα G T^(-α)
for T>0, G>0, G²≤2T, L>0, 8L≤G, every real b.
```

The exact four-carrier algebra retains both signs, both quarter
powers, all complex coefficients and `d(n)(-2pi)`.
Actual integrability is proved before integral linearity.
The complete carrier series is summable by equality with the
genuinely convergent two-term source, including n=0.
`exists_norm_zetaAtkinsonTwoTerm_le` consumes the actual
integral bounds to prove

```text
|twoTermSummand(n)| ≤ |d(n)| G
  (C T^(-1/4)n^(-1/4) + D T^(-3/4)n^(-3/4)).
```

These per-summand majorants are not summable and are never used
as an absolute bound on the whole series. The complete exact
series is retained by
`exists_zetaSquarePhysicalGaussian_carrier_approximation` and
`exists_zetaSquareLocalMean_le_carriers`, with source factors
2 and 2 exp(1) and uniform `Cδ G log T` error on
`T^δ≤G≤T^(1/2-δ)` beyond one threshold. These source
identities and the separate summand estimates are distinct
proved edges; the former do not claim a summation of the latter.

Semantic verdict: the new green node ZAC is limited to actual
uniform carrier cancellation, summand estimates and complete
physical source consumers. The sharper arithmetic tails,
uniform stationary main values, sharp Atkinson inequality,
physical dyadic/Gram assembly and genuine twelfth moment remain
open at ZAT/ZTM. The conditional Add-est (i) theorem still
requires its genuine moment premise. EPZAE-21/37, all nine
unconditional Add-est outputs and the full EPZAE-00--41 goal
remain open.

The counterexample, corrected two independent fifth coordinates
and actual powering/Heath–Brown chain are unchanged. The native
`GuthMaynardExternal/PNT/ZetaAppendix.lean` was imported in
place; its hash and exact analytic interface are recorded in Sources.
No dependency/source pin or native source changed.

### Historical verification for the signed-carrier continuation

Focused development resolved elaboration issues in derivative composition,
real-to-complex powers, integral linearity and cast normalization.
An unused simp argument was removed. No source was excluded and
no warning was suppressed. Final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` exited 0
with 9010 jobs and no Lean warnings. Both principal runners then
passed on the final Lean/audit/inventory source:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-164044-86db646e.log
target log SHA-256: 7972b846fd6fababb873c417e2ae1864fb76be05338714999747782d33647ee4
default build: 9010 jobs
inventory: 167 scanned Lean files; 156 package files; 28 required project files
audit: 1957 declarations (1952 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_164056.log
foundation log SHA-256: d08983df77c8fc9b72becebe0f8ed5b2975610699122910fbb8afa1473378aa0
foundation manifest: logs/foundation_freeze_20260920_164056.json
foundation manifest SHA-256: 016526be3691a5b4a3d9ca04acea0b2d3a20ba8aca6bdfcffb1c2131bd251295
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

Both audits permit only the ordinary Lean/Mathlib logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
The preserved `energyPowering_source_counterexample` passes
both named and dynamic target audits. Its source SHA-256 is still
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

Repository-wide scans were rerun from `E:\Lean\Riemann Zeta`:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
git diff --check
```

The first and third searches returned no matches (exit 1).
The second returned only existing comment prose and two rational
structure fields, not postulates; both principal semantic scans
pass. `git diff --check` passes (exit 0), with Git's
LF-to-CRLF notices only, not Lean diagnostics.
The native source hash agrees with the recorded Sources entry.
No proof-integrity or warning gate changed.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and
this manifest record the same mathematical boundary. The goal
still requires both exact runners, counterexample preservation
and every EPZAE-00--41 obligation. The full goal remains active.
No commit or push was performed by the agent.

## Complete correction removal and leading-source consumers, 20 September 2026

The previous goal turn was verified progress: it proved uniform
actual signed-carrier bounds and complete source identities.
This continuation adds the reciprocal-frequency gain needed to
sum and remove the entire Neumann correction.

Four new production modules are installed:

| Module | New named public theorem audits | Actual conclusion |
|---|---:|---|
| `AtkinsonFrequencyTail` | 4 | Both physical-support slope bounds and uniform `1/b` integral gain |
| `AtkinsonCorrectionBounds` | 4 | Near/far combination and the actual divisor-majorized correction |
| `AtkinsonLeadingSeries` | 7 | Complete correction summability, `C G` bound and leading-series identities |
| `AtkinsonLeadingSource` | 3 | Uniform logarithmic error and both actual physical zeta consumers |

A nineteenth named audit covers
`IntervalC1Bound.atkinsonRoot_of_primitive_bound`.
The existing uniform weighted bound now consumes this generalized
integration-by-parts theorem. It derives the weighted estimate
`2 B M` from a bound B on the actual unweighted primitives
and the actual C1 amplitude bound M. The new source consumer
constructs both inputs; neither is a new analytic premise.

For `b≥8sqrt(T)`, the exact root-phase slope is at least b
for the positive carrier and at most -b for the negative carrier
on the whole support `[sqrt(T/16),sqrt(T)]`. Both slopes
are decreasing. The pinned native first-derivative estimate
therefore gives primitive bound `1/(b*pi)`.
The constructed amplitude variation and exact source Jacobian
give, for every fixed real α,

```text
|Iα(T,G,L,±b)| ≤ Cα G T^(-α)/b,
T>0, G>0, G²≤2T, L>0, 8L≤G, b≥8sqrt(T).
```

For the actual α=3/4 correction pair, the near range uses the
earlier uniform cancellation and `T^(-3/4)sqrt(T)≤1`.
The far range uses the new reciprocal-frequency estimate.
Together they give `C G/sqrt(n)` for n>0, uniformly for
T≥1. The exact `n^(-3/4)` coefficient supplies the full
summable divisor-Dirichlet majorant at exponent 5/4.
Zero-index coefficients are handled exactly.

`summable_atkinsonCorrectionTerm` and
`exists_norm_atkinsonCorrectionSum_le` sum that actual
majorant, giving the complete error `C G`. The exact
leading-minus-correction decomposition retains both complex
coefficients, both phases and `d(n)(-2pi)`.
`summable_atkinsonLeadingTerm` obtains the genuinely convergent
leading series from the actual convergent two-term source.
`exists_norm_zetaAtkinsonTwoTermSum_sub_leading_le` then
consumes the full correction bound.

Both public consumers in `AtkinsonLeadingSource` retain only
the complete leading signed-carrier series, source factors
2 and 2 exp(1), and uniform `Cδ G log T` error on
`T^δ≤G≤T^(1/2-δ)`, beyond one threshold.
They have no analytic theorem premise. The leading series'
stationary main values and sharper leading arithmetic tails are
not proved by its summability. The sharp Atkinson inequality,
physical dyadic/Gram assembly and genuine twelfth moment remain
open, as do EPZAE-21/37 and every unconditional Add-est output.

The 19 new public audits and 16 new semantic regressions cover
the exact carrier threshold and both signs, zero coefficients,
height/width boundaries, complete summability and both actual
source consumers. All four modules are root-imported and in
the backing inventory of `run_tao_trudgian_yang_build.bat`.
The existing weighted-bound audit is retained; its proved
statement is unchanged. No verification scope was narrowed.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and
this manifest record the same status. ZCR is green only for
the reciprocal-frequency estimate, complete correction and
leading-only physical-source consumers. ZAT/ZTM stay open.
The full EPZAE-00--41 objective and both runner requirements
remain active. The original counterexample and the proved
independent-coordinate powering/Heath–Brown chain are unchanged.

### Historical verification for complete correction removal

The focused builds resolved a variable-bound multiplication step,
a native pi-lemma name and the order of norm rewrites.
One unnecessary tactic-sequencing warning was fixed in source.
No failing module was excluded and no diagnostic was suppressed.
Final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` exited 0,
with 9014 jobs and no Lean warnings.

Both principal runners passed on the final Lean/audit/inventory
source:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-165815-b75510ef.log
target log SHA-256: 9e576b3f3af51daac5ce15d9cb398f0c0412e5db796828fcf4e8d2ebba92cad1
default build: 9014 jobs
inventory: 171 scanned Lean files; 160 package files; 28 required project files
audit: 1984 declarations (1979 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_165827.log
foundation log SHA-256: 95c5b3d50e8ad6c1564f4ba5afa593d0ec2d4693266ebd806ba0c26d333d6222
foundation manifest: logs/foundation_freeze_20260920_165827.json
foundation manifest SHA-256: cc31b9b0f537bd20210797a58bdb77c8ee255bacc061ca0bd6535e071a789572
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

Both audits permit only ordinary Lean/Mathlib logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
The preserved counterexample is explicitly and dynamically audited.
Its source SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The native `ZetaAppendix.lean` hash is unchanged, and the
inspected native arithmetic source hash is recorded in Sources.

Repository-wide searches were run from the Git root `E:\Lean`:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
git diff --check
```

The first and third searches had no matches (exit 1).
The second found existing comment prose and two rational
structure fields only, not postulates. Both principal semantic
scans pass. `git diff --check` passes (exit 0); Git's
LF-to-CRLF notices are not Lean warnings.
No dependency pin, source archive, native file, scanner or
warning gate changed. No commit or push was performed.

This is verified complete correction removal and an actual
leading-only source bridge, not whole-goal completion. The
stationary leading main values, sharper leading arithmetic
tails, sharp Atkinson inequality and genuine twelfth moment
remain open; the clause-(i) consumer still has its moment
premise. All unconditional Add-est outputs and the full
EPZAE-00--41 goal remain open and active.

## Future axiom gate

Every public theorem and agenda-critical helper must be listed explicitly and
also discovered mechanically. Acceptable inherited logical axioms are limited
to the repository-wide policy (`propext`, `Classical.choice`, `Quot.sound` as
they arise through ordinary Mathlib use). No theorem may depend on `sorryAx`
or a project declaration that postulates mathematics.

## Clean-room reproduction record

Not yet applicable. When EPZAE-40 is attempted, append:

```text
commit/tag:
toolchain:
dependency pins:
runner command:
exit code:
log path:
log SHA-256:
warnings:
axiom audit summary:
semantic regression summary:
Python reproduction summary:
certificate regeneration diff:
```

Do not convert this blank template into a success claim until every field has
current-checkout evidence.

## Actual C2 Fourier decay and finite leading source, 20 September 2026

This continuation constructs actual second-order analytic bounds and consumes
them in quantitative leading-series truncation and both physical zeta theorems.
It does not close the sharp Atkinson or twelfth-moment obligations.
The full goal, dependency pins and frozen sources are unchanged.

### Production and audit inventory

| Module | Named public theorems |
|---|---:|
| `ZetaQuadraticGaussianSecondDerivative` | 3 |
| `IntervalSecondDerivativeBounds` | 5 |
| `ZetaBandSecondDerivatives` | 5 |
| `ZetaBandPhysicalDerivatives` | 6 |
| `SecondDerivativeComposition` | 4 |
| `ZetaGaussianProfileSecondDerivatives` | 5 |
| `AtkinsonPhaseSecondDerivatives` | 5 |
| `AtkinsonRootAmplitudeDerivatives` | 3 |
| `AtkinsonRootFourierSupport` | 7 |
| `AtkinsonRootFourierDecay` | 2 |
| `AtkinsonFourierSource` | 4 |
| `AtkinsonSecondOrderTail` | 2 |
| `AtkinsonLeadingMajorant` | 2 |
| `AtkinsonLeadingTruncation` | 3 |
| `AtkinsonFiniteSource` | 3 |
| Total | 59 |

All fifteen modules are directly imported by the package root and are in
`Tools/run_tao_trudgian_yang_build.ps1`'s exhaustive inventory.
The exact human-facing interface remains `run_tao_trudgian_yang_build.bat`.
Twenty new semantic regressions cover the actual amplitude, positive-root
support, both carrier signs, closed scale bounds, n=0, the N=1 tail boundary
and full physical finite-source quantifiers. Every new public theorem has
an explicit named audit as well as dynamic transitive dependency inspection.

### Semantic edge checks

1. `exists_intervalC2Bound_atkinsonRootFourierCore` constructs all component
   bounds. The cutoff is the actual exponential-edge band; both transition
   widths have proved inverse bounds. The real quadratic Gaussian has its
   actual second derivative, not an arbitrary smooth proxy. Constants for
   fixed profiles are chosen before the physical parameters.
2. `contDiff_atkinsonRootFourierAmplitude` and
   `support_atkinsonRootFourierAmplitude` construct the positive-root
   extension. Its support lies in [1/4,1]; the true band vanishes near zero.
   No auxiliary cutoff or assumed derivative estimate replaces the source.
3. `exists_norm_fourier_atkinsonRootFourierAmplitude_le` consumes those
   results and all constructed C2 bounds in native order-two Fourier
   integration by parts. On T≥1, G>0, G²≤2T, L≥1, 8L≤G, the bound is
   Cα G T^(-α) T² after multiplication by (1+|ξ|)².
4. `atkinsonPowerIntegral_eq_fourier` proves the exact source equality
   with Jacobian 2sqrt(T), unit phase exp(i T log T), and frequency
   -2b sqrt(T). `exists_sq_mul_norm_atkinsonPowerIntegral_le` actually
   consumes that identity and the Fourier bound. Both signs are retained.
5. `exists_norm_atkinsonLeadingTerm_le` retains d(n)(-2pi), the exact
   quarter-power Bessel coefficient and both complex leading coefficients.
   It yields C G T^(5/4) |divisorDirichletTerm(5/4,n)|, including n=0.
6. `exists_norm_atkinsonLeadingSum_sub_finite_le` proves the quantitative
   complete-series tail C G T^(5/4) N^(-1/8), N>0. Its proof constructs
   summability and uses the true divisor Dirichlet series at 9/8. For
   N≥T^10, `exists_norm_atkinsonLeadingSum_sub_polynomial_le` gives C G.
7. `exists_zetaSquarePhysicalGaussian_atkinson_finite_approximation`
   and `exists_zetaSquareLocalMean_le_atkinson_finite` consume the tail
   and the established physical source, preserving factors 2 and 2exp(1).
   For each δ>0, one threshold and constant work on
   T^δ≤G≤T^(1/2-δ) for every natural N≥T^10, with Cδ G log T error.
   Neither signature has an analytic theorem premise.

**Green-node verdict:** ZFT is complete for coarse polynomial truncation
and actual finite physical-source consumers only. The finite summands remain
actual oscillatory integrals. Stationary main values, sharp source-scale
localization, the sharp Atkinson inequality and physical dyadic/Gram assembly
remain required. ZAT, ZTM, EPZAE-21/37 and every unconditional Add-est output
remain open. The full EPZAE-00--41 completion contract is not reduced.

### Native reuse and preserved discovery

`../71 Guth-Maynard, 2026/GuthMaynard/DFIParametricMellin.lean` was
inspected and imported in place; its order-two Fourier theorem is consumed.
SHA-256:
`d07da5016fb76403dabaa23c377ca137ddf78c78767a03b9ac5303a92d9e4b42`.
The previously recorded `HughesYoungAFE.lean` supplies genuine
ordinary-divisor summability at both 5/4 and 9/8. Neither native file changed.

The original `EnergyPoweringObstruction.lean` remains byte-for-byte intact:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent fifth-coordinate witnesses and proved full
Heath–Brown relation remain unchanged.

The following verification record supersedes the prior correction-removal
record for the current checkout; older dated evidence is retained as history.

### Historical verification for the finite leading source

Incremental builds resolved only proof elaboration issues (local smoothness
order, real/complex casts, rewrite orientation and exact source normalization).
No diagnostic was suppressed and no failing module was excluded.
The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` exited 0
with 9029 jobs and no Lean warnings or tactic suggestions.

Both principal runners passed on the final Lean/audit/inventory source:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-175710-0f734f13.log
target log SHA-256: 6485f017acf8ed4966107af065876d15078434ac38ad4eaa5523d0088957bcc4
default build: 9029 jobs
inventory: 186 scanned Lean files; 175 package files; 28 required project files
audit: 2071 declarations (2066 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_175711.log
foundation log SHA-256: 517fe675e76105af27e1f6df1e971bf0cdc2a1ff369a8b752d6bd1e2d537f754
foundation manifest: logs/foundation_freeze_20260920_175711.json
foundation manifest SHA-256: 81b6475fb4493d41a79e6bf3303df11913e69cf4ccaf89003ba21aacd77c0ae8
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

The target log has no Lean warning/error/tactic-suggestion diagnostic.
Both audits admit only ordinary logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
All 59 new named public audits are present; 20 new semantic regressions
compile. The independent-coordinate repair and its preserved counterexample
remain in the same production and dependency-audit scope.

Repository-wide searches were run from the Git root `E:\Lean`:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
git diff --check
```

The first and third searches have no matches (exit 1); the second finds
existing comment prose and two rational structure fields only, not postulates.
Both principal semantic integrity scans pass. `git diff --check`
passes (exit 0); Git's LF-to-CRLF notices are not Lean diagnostics.
The counterexample SHA-256 was rechecked after compilation and is unchanged.
No native source, dependency pin, archived source, scanner or warning gate
was changed. No commit or push was performed.

README, Extension README, Tools README, Goal Prompt, Checklist,
Research Agenda, Crosswalk, Architecture, Repair, Sources and this manifest
are synchronized. ZFT is green only for actual C2/Fourier control, coarse
polynomial truncation and finite physical-source consumers. The sharp
stationary main values/localization, sharp Atkinson inequality, physical
dyadic/Gram assembly and genuine twelfth moment remain open. The conditional
clause-(i) consumer still has its genuine moment premise; all unconditional
Add-est outputs remain open. The full EPZAE-00--41 goal remains active.

## Actual finite stationary reduction, 20 September 2026

This checkpoint adds the following twelve production modules:

```text
AtkinsonSaddleNormalization
AtkinsonSaddlePhase
AtkinsonSaddleGaussian
AtkinsonSaddleTaylor
ZetaGaussianNaturalDerivatives
AtkinsonNaturalAmplitude
AtkinsonLocalStationary
AtkinsonStationaryTails
AtkinsonStationaryReduction
AtkinsonFiniteStationaryMain
AtkinsonSignedStationaryMain
AtkinsonStationaryPhysical
```

All 71 new public theorems have explicit named dependency audits;
22 additional semantic regressions check source signs, alternating
factor, zero-frequency/window cases, closed Gaussian and frequency
boundaries, both logarithmic-remainder endpoints, natural derivative
scale and actual full-integral consumers. Root imports and the exact
PowerShell inventory behind `run_tao_trudgian_yang_build.bat` are updated.
No module, source hash check or diagnostic gate is excluded.

Semantic green-node audit for ZSR:
`exists_atkinsonPowerIntegral_small_n_pair_approximation` begins with
the actual positive-support carrier `atkinsonPowerIntegral`. It derives
the actual root windows and proves both b=±sqrt(n) estimates with a
single constant Cα preceding every physical parameter. Its conclusion is

```text
|Iα(T,G,L,b) - Mα(T,G,L,b,H)| ≤ Cα G T^(-α)
  [4/(pi H) + 4(G/sqrt(T))H² + 432H⁴/sqrt(T)],
T>0, G≥1, G²≤2T, L≥1, 8L≤G, 0<H≤sqrt(T)/12, 10000n≤T.
Mα = 2 Wα(r²) exp(2pi i q(T,b,r)) integral_(-H)^H exp(-2pi i c z²) dz,
r = r(T/(2pi),b), c = 1+(T/(2pi))/r².
```

Its immediate chain is the physical saddle bound, actual full finite
stationary approximation, exact root Jacobian/support bridge, constructed
C1 variation and natural-scale C2 amplitude bounds, true logarithmic
cubic remainder, and actual weighted reciprocal-slope tails. None is a
stationary-estimate premise. The general full-integral consumer retains
16T H⁴/r³ and explicit geometric window conditions; the physical consumer
discharges those conditions, rather than packing unrelated bounds.
`AtkinsonSignedStationaryMain` consumes the literal phase and common
Gaussian bridges in both signed main-term identities. The separate
actual cutoff/Mellin profiles remain; no unsupported conjugacy is used.

The main term still contains a **finite quadratic integral**.
No Fresnel limit, sharp Atkinson truncation or uniform summation of its
stationary errors is claimed. ZAT, the genuine twelfth moment,
EPZAE-21/37 and all unconditional Add-est outputs remain open.
The complete EPZAE-00--41 goal and frozen public statements are unchanged.

Source evidence: the pinned Ivić Orsay scan was reread at printed
107–115; the online PDF exceeded the web-reader size limit. The
adjacent literal Atkinson phase was inspected in place, not imported
as a conditional moment theorem. The Sources document records the
exact local SHA-256 values. No native source, source archive,
dependency pin or counterexample was modified. Counterexample SHA-256:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The historical PASS immediately above predates these twelve modules.
Terminal evaluation evidence for both required runners at that historical checkpoint follows.

### Historical verification for the finite stationary reduction

The final focused semantic-regression build passed (9041 jobs, exit 0):

```powershell
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build TaoTrudgianYang2025.SemanticRegression
```

Both required principal runners then passed on the same Lean/audit/inventory
source, with the twelve new modules included:

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-184825-f2641a88.log
target log SHA-256: 713767645e52ff3ee17c413a0218938508b6bd7a1258270e63a49831b6807f99
default build: 9041 jobs
inventory: 198 scanned Lean files; 187 package files; 28 required project files
audit: 2194 declarations (2189 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_184826.log
foundation log SHA-256: e26f54b8108a714fb38fa7914d000aad6cb020607ae91f7e7997ea1c8580fba5
foundation manifest: logs/foundation_freeze_20260920_184826.json
foundation manifest SHA-256: aa8190cd37bfbe7f249950bb61dd339fb6b7d7be0d5ba0cbff52495ec4093038
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

All six foundation stages report exit 0, passed=true, warnings=0,
tacticInfo=0, informationalBuilds=0 and linterFailures=0.
Both dependency audits allow only ordinary logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
A mechanical check confirms all twelve root imports, twelve backing
inventory entries and 71 named public audits; all 22 new regressions compile.
The counterexample hash was rechecked after both target compilation and audit.

Repository-wide checks from E:\Lean:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
git diff --check
```

The first and third scans have no matches (exit 1). The second finds
comment prose, including the new explanation that a finite quadratic
integral is not an assumed Fresnel constant, and the two pre-existing
rational structure fields; no postulate occurs. Both semantic integrity
scanners pass. `git diff --check` passes (exit 0); Git's LF-to-CRLF
notices are not Lean diagnostics. No source pin, native source,
archived paper, warning gate or preserved counterexample changed.
No commit or push was performed.

All eleven target documents are synchronized, including the Goal Prompt
and its requirement to maintain the exact batch runner. ZSR is green
only for the proved actual finite-window reduction and physical
small-frequency consumers. Fresnel evaluation, sharp source-scale
localization/error summation, sharp Atkinson, dyadic/Gram assembly,
the genuine twelfth moment and unconditional Add-est remain open.
The complete EPZAE-00--41 goal remains active.

## Evaluated Fresnel main and source power saving, 20 September 2026

This checkpoint supersedes the preceding finite-window-only status.
Nine new modules are in the root and exact PowerShell inventory:

```text
ContinuousKernelPrimitive
FresnelDampedTails
FresnelGaussianComparison
FresnelAbelLimit
FresnelEvaluation
AtkinsonStationaryMain
AtkinsonStationaryEvaluation
AtkinsonEvaluatedPhases
AtkinsonStationaryPowerSaving
```

All 35 public theorems have explicit named dependency audits.
Sixteen regressions cover zero damping, the finite-interval limit,
principal square-root branch, both quarter-turn cancellations,
actual signed main identities, the closed power-balance boundary,
the η=1/10 endpoint and the full paired source-width consumer.

Semantic green-node audit for ZFE:
`exists_atkinsonPowerIntegral_source_power_saving` starts at the real
`atkinsonPowerIntegral` and concludes a bound for its difference from
`atkinsonStationaryMain`, not an assumed stationary estimate.
The latter unfolds to 2 Wα(r²) K(T,b,r) times the proved
exp(-i pi/4)/sqrt(2c), where r and c are linked to T,b.
Its immediate chain is the actual finite-window approximation,
constructed saddle-amplitude bound and quantitative Fresnel tail
2/(c H pi). The positive-damping Gaussian proof uses actual integrability;
only finite windows pass to zero damping. Branch identification is proved.

H=T^η/12 derives the geometric constraints and bounds the error bracket
by 20 T^(-η), using G(T^η)^3≤sqrt(T) and (T^η)^5≤sqrt(T).
For fixed α the constant Cα precedes η,T,G,L,b.
The source consumer sets η=min(δ/3,1/10), L=log T, derives all window
scales eventually from T^δ≤G≤T^(1/2-δ), and proves both ±sqrt(n)
bounds for 10000n≤T. The signed-main identities consume the source
phase and common Gaussian; actual amplitude profiles stay separate.

This is per-carrier progress, not a full source sum: the small-frequency
range 10000n≤T does not match the earlier N≥T^10 finite truncation.
Sharp localization, a sufficiently strong summed stationary error,
sharp Atkinson, physical dyadic/Gram assembly and the genuine twelfth
moment remain open. EPZAE-21/37 and unconditional Add-est remain open;
the full EPZAE-00--41 goal stays active.

No source pin, native file, archived paper, warning gate or counterexample
changed. The original Lemma 62 obstruction remains byte-preserved:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected separate cardinality/energy witnesses and proved
Heath–Brown relation are unchanged. Both principal runners remain
mandatory, including updates to `run_tao_trudgian_yang_build.bat`
and its inventory as needed.

### Historical verification for evaluated stationary main terms

Focused builds and the final semantic-regression build passed without
Lean warnings, errors, tactic suggestions or linter diagnostics:

```powershell
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build TaoTrudgianYang2025.AtkinsonStationaryPowerSaving
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build TaoTrudgianYang2025.SemanticRegression
```

These terminal builds returned exit 0, respectively 9012 and 9050 jobs.
The two required principal runners then passed on the same Lean/audit/
inventory source. Documentation was synchronized around those runs;
no Lean or inventory file changed after them.

```text
target command: cmd /c run_tao_trudgian_yang_build.bat --no-pause
target cwd: the Tao–Trudgian–Yang 2025 folder
target exit: 0
target final result: LEAN VERIFICATION PASS
target log: logs/tao-trudgian-yang-build-20260920-192612-e2329e1d.log
target log SHA-256: 5898076fc90d92118884c75591c4879b35eee58d243f3afb31646567eaf28b84
default build: 9050 jobs
inventory: 207 scanned Lean files; 196 package files; 28 required project files
audit: 2242 declarations (2237 target plus 5 imported boundary declarations)
target failed stages: none
target Lean warnings/errors/tactic suggestions/linter diagnostics: none

foundation command: cmd /c run_lake_build.bat --no-pause
foundation cwd: E:\Lean\Riemann Zeta
foundation exit: 0
foundation final result: PASS
foundation log: logs/foundation_freeze_20260920_192623.log
foundation log SHA-256: e54eb06c20a80718031a860ee031137e2ec21862b67866c35b53cc764c60a039
foundation manifest: logs/foundation_freeze_20260920_192623.json
foundation manifest SHA-256: a2ab388be7bd9ad6a05d72d49ed39879ceb06026b4d4e333ca79d5418d93afef
foundation audit: 14290 nonprivate project theorems; 7636 explicit public declarations
foundation closure: 301 modules plus 2 explicit regression modules; no exclusions/unclassified files
verifier SHA-256: 0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7
HEAD during both verifications: f16f0788afefff9b82811438a7672ef485cf8bc7 (dirty worktree)
foundation failed stages: none
foundation Lean warnings/errors/tactic suggestions/linter diagnostics: none
```

All six foundation stages report exit 0, passed=true, warnings=0,
tacticInfo=0, informationalBuilds=0 and linterFailures=0.
Both dependency audits allow only ordinary logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
The nine root imports, nine backing inventory entries and 35 named
public audits are mechanically checked; all 16 new regressions compile.

Repository-wide checks from E:\Lean:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
git diff --check
```

The first and third scans have no matches (exit 1). The second finds
only comment prose and the two pre-existing rational structure fields,
not project postulates. Both semantic integrity scanners pass.
`git diff --check` passes (exit 0); Git's LF-to-CRLF notices are not Lean
diagnostics. Counterexample SHA-256 was rechecked after both runners.
No commit or push was performed.

All eleven target documents, including the Goal Prompt and architecture,
now distinguish the proved Fresnel/per-carrier continuation from the
still-open sharp source sum and final outputs. The exact batch-runner
maintenance requirement and preserved-counterexample contract remain.

## Source-scale truncation and linked cutoff, 20 September 2026

This checkpoint supersedes the earlier coarse-cutoff/per-carrier-only
status. Eleven new production modules are root-imported and explicitly
inventoried by the PowerShell implementation of
`run_tao_trudgian_yang_build.bat`:

```text
AtkinsonSaddleSupport
AtkinsonRootBand
AtkinsonBandCancellation
ReciprocalSecondDerivativeBounds
AtkinsonSecondOrderIntegration
AtkinsonSlopeDerivativeBounds
AtkinsonBandAmplitude
AtkinsonBandSecondOrder
AtkinsonSharpTruncation
AtkinsonSourceBand
AtkinsonSourceCutoff
```

All 53 public theorems have named dependency audits; 22 regressions
cover both signs, vanishing cutoff endpoints, closed G²=2T and
frequency thresholds, literal ceiling values and the uniform physical
source and retained-index stationary consumers.

Semantic green-node audit for ZBT:
`exists_zetaSquarePhysicalGaussian_atkinson_band_approximation`
and `exists_zetaSquareLocalMean_le_atkinson_band` consume the actual
complete leading series and a proved tail, not an assumed finite-sum
majorant. The original cutoff supplies exact root-band support and
vanishing endpoints. Its length is at most 4sqrt(T)L/G.
The actual phase satisfies |q'(T,0,y)|≤6sqrt(T)L/G there.
Both signed frequencies outside that band have nonzero slopes.
Constructed reciprocal-slope C2 bounds and two integrations by parts
give Cα G² T^(-α)L/(sqrt(T)n), for n≥36T(L/G)².

The actual Bessel coefficient produces the ordinary-divisor
Dirichlet majorant at 5/4. It sums the full tail to C G²L T^(-3/4);
the physical width and logarithmic scales reduce this to O(G).
The two real zeta consumers retain their source factors 2 and 2exp(1),
the actual finite leading sum and Cδ G log T error, now for every
N≥36T(log T/G)², beyond one threshold for each δ>0 on
T^δ≤G≤T^(1/2-δ). This replaces the coarse N≥T^10 requirement.

The original saddle cutoff independently makes both evaluated main
terms zero for n>9T(L/G)². This does not assert that the carrier itself
vanishes there. `atkinsonSourceCutoff` is the literal natural ceiling
of 36T(L/G)². It satisfies the full tail condition and, eventually on
the lower power-width range, 10000N≤T.
`exists_atkinsonSourceCutoff_carrier_approximation` derives that range
condition and applies both evaluated stationary estimates to every
retained n<N. The previously disconnected cutoff and stationary ranges
are now linked to the same physical parameters.

A sufficiently strong summed stationary error and remaining main
assembly still separate this chain from the sharp Atkinson inequality.
The genuine twelfth moment, EPZAE-21/37 and unconditional Add-est remain
open; the full EPZAE-00--41 goal stays active.
The original counterexample remains byte-preserved:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent-coordinate powering/Heath–Brown chain is unchanged.
No source pin, native source, archive, exclusion or diagnostic gate changed.
Both principal runners remain mandatory; terminal evidence follows.

### Historical verification for source-scale truncation

Terminal checks used the existing dirty checkout at
`f16f0788afefff9b82811438a7672ef485cf8bc7`, Lean 4.30.0. No commit or
push was made. These results supersede the historical verification
headings above for the installed package scope.

Focused `lake build TaoTrudgianYang2025.<module>` checks for all eleven
modules listed above completed with exit code 0 and no Lean diagnostics.
The final focused command
`lake build TaoTrudgianYang2025.SemanticRegression` completed successfully
with 9061 jobs and exit code 0. Mechanical coverage checks found all
eleven exact root imports and PowerShell inventory entries, all 53
named public audits, and exactly 22 examples in
`AtkinsonSourceBandRegression`.

From this target folder:

```text
cmd /c run_tao_trudgian_yang_build.bat --no-pause
Exit code: 0
FINAL RESULT: LEAN VERIFICATION PASS
Log: logs/tao-trudgian-yang-build-20260920-201719-4a6356aa.log
SHA256: d7a0c33934dfc9b323d9425a5c0315ac32e2a12eb7b0929c77d4e9e8dd859897
```

All stages passed: 28 required files, 20 pinned source files, 12 frozen
ANTEDB files, 218 scanned Lean files, complete coverage of 207 Lean
package files, deterministic regeneration, default build (9061 jobs),
semantic regression, and transitive dependency audit. The dynamic audit
checked 2316 declarations: 2311 nonprivate target theorems plus five
imported inputs, with only permitted logical axioms. No Lean warning,
error, tactic suggestion or linter failure appeared in the target log.

From `E:\Lean\Riemann Zeta`:

```text
cmd /c run_lake_build.bat --no-pause
Exit code: 0
FINAL RESULT: PASS
Log: logs/foundation_freeze_20260920_201730.log
Log SHA256: 58945869dee416dfa6c787ec820709625fdf9072f810cb1f8432c5a11cec8274
Manifest: logs/foundation_freeze_20260920_201730.json
Manifest SHA256: 49d8d0a24c71630314e4ec5e4b2f552b3616368b6a093e55f77e6893154af8c5
```

The foundation manifest reports all six stages with `exitCode=0`,
`warnings=0`, `tacticInfo=0`, `informationalBuilds=0`,
`linterFailures=0` and `passed=true`; its failure list is empty.
The default build completed with 8857 jobs. Coverage is 301 root-graph
modules and two explicit regression modules, with no excluded or
unclassified files. The audit covered 14290 discovered nonprivate
theorems and 7636 explicit public declarations.
The unchanged verifier SHA256 is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

The three mandatory repository-wide `rg` scans were rerun from
`E:\Lean`. Placeholder and unsafe-proof scans returned 1 with no matches.
The postulate-pattern scan returned 0: all matches are existing comment
prose or the two rational data fields named `constant`; none is a
postulated declaration. The canonical postulate scanner and its regressions
also passed. `git diff --check` returned 0; Git's LF-to-CRLF notices
are present and are not Lean diagnostics. The preserved counterexample's
SHA256 was rechecked after both runners and remains the value above.

All eleven target documents are synchronized. Older cutoff-status
paragraphs now point to the proved continuation, and earlier terminal
records are labelled historical. The goal explicitly retains the exact
batch interface, its backing inventory, future maintenance and both
required evaluations. No Lean source changed after these passing checks.

Kernel integrity and the source-scale consumers are verified. The summed
stationary error and final main assembly, genuine twelfth moment, all
unconditional Add-est clauses and the full EPZAE-00--41 goal remain OPEN.

## Symmetric stationary summation, 20 September 2026

Ten new production modules are root-imported and explicitly inventoried
behind `run_tao_trudgian_yang_build.bat`:

```text
StationaryOddRemainder
AtkinsonSymmetricStationary
AtkinsonSymmetricReduction
AtkinsonSymmetricBalance
AtkinsonFourthRootRadius
DivisorQuarterPrefix
AtkinsonStationarySeries
AtkinsonStationarySumScale
AtkinsonStationarySumError
AtkinsonStationaryZetaSource
```

All 43 public theorems have named dependency audits. The 24 regressions
in `SymmetricStationarySumRegression` cover both amplitude endpoints,
both logarithmic Taylor endpoints, exponential-error branches, reversed
odd-integral orientation, closed radius balances, the empty divisor
prefix, cutoff 18, actual finite-support summation, both endpoint prefix
exponents and all four exact physical consumer signatures.

Semantic green-node audit for ZSE:
`IntervalC2Bound.atkinsonLocalSymmetric` consumes actual first/second
derivative bounds, subtracts the linear-amplitude and cubic-phase terms,
and proves both odd integrals vanish. It does not bound the uncancelled
cubic phase by an assumed stationary estimate.
`exists_atkinsonPowerIntegral_symmetric_approximation` combines that
local theorem with the actual outer tails and proved Fresnel evaluation.

`atkinsonSymmetricRadiusScale_balance` derives the radius constraints
from T^(1/4)≤G≤sqrt(T), and
`exists_atkinsonPowerIntegral_fourthRoot_pair` derives both signed
geometric conditions for 10000n≤T. Its error is
Cα G sqrt(G) T^(-α-1/4), with no analytic theorem parameter.

`hasSum_atkinsonStationaryLeadingTerm` consumes the actual saddle
cutoff to prove finite support of the original evaluated Bessel/divisor
series; the complete sum equals the same ceiling-truncated sum.
`exists_norm_atkinsonLeadingFiniteSum_sub_stationary_le` consumes
both carrier bounds and the ordinary-divisor prefix, retaining every
coefficient and both separate saddle profiles. The linked ceiling bound
N≤37T L²/G² cancels the physical coefficient scale. Logarithmic
absorption gives Oε(T^(1/4+ε)) for the complete retained error,
and the already proved source tail adds O(G).

The public Gaussian and local-mean consumers use this actual full-series
difference. Their error is Cδ,ε (G log T+T^(1/4+ε)) on the original
power-width range with G≥T^(1/4). Their above-fourth-root consumers give
Cδ,κ G log T for G≥T^(1/4+κ), κ>0.
The source factors 2 and 2exp(1), both signed phases, original Bessel
coefficients and separate cutoff/Mellin profiles are preserved.
All thresholds and constants precede T and G.

The smaller-width source error and remaining main-amplitude/Atkinson
assembly remain OPEN. A twelfth-moment route that omits smaller widths
must prove a legitimate lower-value-range reduction first. No such
reduction or genuine twelfth-moment theorem is claimed here.
EPZAE-21/37, unconditional Add-est and the full EPZAE-00--41 goal stay OPEN.

The renewed source check used the existing adjacent Ivić scan, including
visual inspection of printed page 130. Its unchanged SHA256 is
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`.
No source pin, native source, archive, exclusion or diagnostic gate changed.
The PDF reader under ignored workspace `.tmp` is inspection tooling only.
The original counterexample remains byte-preserved:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent powering witnesses and proved Heath–Brown chain are unchanged.
Terminal verification for both principal runners follows.

### Historical terminal verification: symmetric stationary summation

Both principal evaluations were resumed on their original terminal handles
until completion; both returned exit code 0. These are current-checkout
results, not the preceding historical PASS records.

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`,
  launched from this folder, ended **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-210030-07905f95.log`.
  SHA256:
  `f3c0bedcf1a4f282458cba655e542d3ca9e31dddfb761facd57c5b8f627b68a5`.
  All 28 required files, 20 pinned sources, 12 frozen ANTEDB sources,
  228 scanned Lean files and 217 covered package files passed.
  The default build completed 9071 jobs; deterministic regeneration and
  semantic regression passed. The exhaustive dependency audit passed all
  2387 declarations: 2382 discovered target theorems and five imported
  declarations. Only permitted standard logical axioms occurred.
- Foundation: `cmd /c run_lake_build.bat --no-pause`, launched from
  `E:\Lean\Riemann Zeta`, ended **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_210042.log`.
  SHA256:
  `57a59fba86594284aa19834d9a23b1cc45e51f55ba5c9fde6c23638fa83e90c4`.
  Companion JSON: `logs/foundation_freeze_20260920_210042.json`
  relative to the foundation root; SHA256:
  `45350fd8f638e57ff68202fe2639f5cc7b028e1976d56b1d536f128f8469a166`.
  All six stages have exit code 0, zero warnings, zero tactic-info output,
  zero informational builds, zero linter failures and `passed: true`.
  The root build completed 8857 jobs. The audit passed 14290 discovered
  nonprivate theorems and the 7636-entry explicit public source list.
  Module classification remains 301 root-graph modules and two retained
  regressions, with no excluded or unclassified production modules.

The foundation verifier remains
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The evaluated HEAD was `f16f0788afefff9b82811438a7672ef485cf8bc7`,
with the existing dirty working tree preserved. No commit or push was made.

A fresh mechanical coverage check found all ten new root imports,
all ten backing PowerShell inventory entries, all 43 named theorem audits
and exactly 24 examples in `SymmetricStationarySumRegression`.
The three mandatory repository-wide scans were rerun from `E:\Lean`:
placeholder and unsafe-proof scans returned 1 with no matches; the
postulate-pattern scan returned 0 only for existing comment prose and
the two rational data fields named `constant`, not mathematical postulates.
The canonical scanner and scanner regressions also passed.
Both full logs contain no Lean warning, error or tactic suggestion.
`git diff --check` returned 0; Git's line-ending notices are not Lean
diagnostics. The counterexample SHA256 was rechecked after both runners
and is unchanged.

All eleven target documents, the architecture, exact consumer claims and
the goal's continuing batch-runner maintenance requirement are synchronized.
No Lean source changed after these passing evaluations. The remaining
smaller-width source estimate, main-amplitude/Atkinson assembly, genuine
twelfth moment and unconditional Add-est obligations remain OPEN; the
whole EPZAE-00--41 goal stays active.

## Normalized main terms and actual Abel consumer

Five production modules now continue the stationary series:
`AtkinsonMainNormalization`, `AtkinsonSignedPhaseSeries`,
`AtkinsonMainWeightBounds`, `AtkinsonMainPartialSummation` and
`AtkinsonMainZetaConsumer`. Their 30 public theorems have named audits;
24 `NormalizedMainAbelRegression` examples cover zero/one-index cases,
both signs, exact coefficients and all four physical consumer signatures.

The real saddle power and curvature cancel together. At alpha=1/4,
`atkinsonSaddleProfile_div_curvature` extracts the common factor
1/(sqrt(2) sqrt(sqrt(b²+2T/pi))) from the actual saddle profile.
The remaining factor is the actual Mellin profile times the original
cutoff, evaluated separately at b and -b; the Gamma phase is retained.

For n>0 the exact fourth-root coefficient is

```text
a(T,n) = (1/sqrt(2)) n^(-1/4) (n+2T/pi)^(-1/4).
```

The zero-index term is also handled with the original zero divisor weight.
`atkinsonStationaryLeadingSum_eq_signed` derives, from the original
Bessel coefficients and the proved finite-support theorem,

```text
stationary sum = (1+i) GammaPhase(T) exp(i centralPhase(T)) (Splus-Sminus).
```

Each S retains its own weight a(T,n) times the common actual quadratic
Gaussian times its separate cutoff/Mellin profile, multiplied by
(-1)^n d(n) exp(±i f(T,n)). Both sums use the same explicit source ceiling.
Only the raw negative-phase sums are proved conjugate to the positive
ones; no conjugacy or equality of the two weights is assumed.

`exists_norm_atkinsonMainWeights_le` constructs a uniform constant,
before T,G,L,n, bounding both actual weights by
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) for n≤T,
T,G,L>0, G²≤2T and 8L≤G. It consumes the actual cutoff support,
the compact Mellin bound and the actual saddle Gaussian.

`atkinsonMainAbelBound` is the explicit endpoint term plus a finite sum
of literal differences of the two weights times raw phase partial sums.
Mathlib's finite summation-by-parts identity proves the bound at every
natural cutoff, including 0 and 1. It is not an assumed variation estimate.
The actual Gaussian consumer now has the normalized signed main term;
the actual local-mean consumer is bounded by 4exp(1) times this Abel quantity
plus Cδ,ε(G log T+T^(1/4+ε)), eventually on
T^δ≤G≤T^(1/2-δ), G≥T^(1/4). The corresponding above-fourth-root
consumers have Cδ,κ G log T error when G≥T^(1/4+κ), κ>0.

The continuation below proves uniform variation of these actual weights
and the actual source-block bound. The newest continuation also proves
global dyadic assembly. The phase-sum/Gram estimate, source-form bridge,
and smaller-width error or a proved lower-value-range reduction remain required.
This is not the full sharp Atkinson theorem or the genuine twelfth moment.
EPZAE-21/37, every unconditional Add-est clause and the full goal remain OPEN.

Maintain these five root imports, all 30 named audits, all 24 regressions
and the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and execute
it and `run_lake_build.bat` after relevant changes. Preserve the original
counterexample byte-for-byte and the proved independent-coordinate
powering/Heath–Brown chain; never restore the false fifth-coordinate scaling.

### Normalized-main semantic and reproduction record

ZMN closes only the exact normalized-main, pointwise-weight and literal-Abel
consumer scope above. `atkinsonSaddleProfile_div_curvature` consumes the
proved saddle equation and curvature product; the paired mains consume
the actual evaluated Fresnel phases. The original Bessel coefficient
calculation then factors the complete finite-support divisor series.
No normalization, weight identity or variation bound is assumed.

The actual cutoff gives compact positive physical support for the Mellin
bound. Together with the previously proved saddle Gaussian, this produces
the pointwise weight bound, including n=0. The Abel theorem applies a
kernel-checked Mathlib finite identity and conjugates only raw phases.
The four final physical consumers retain constants and thresholds before
T and G and derive positivity, logarithmic width and the exact cutoff
from the original power-width assumptions. No analytic theorem parameter
is added. The continuation below now proves uniform damped variation;
the source's full-width estimate remains open.

The only proof-development diagnostics were ordinary elaboration errors
and unused-simp arguments; their causes were repaired, not suppressed.
The 24 new regressions include exact real exponents at zero, both signed
normalizations, zero/one cutoff summation, raw conjugacy, an actual weight
bound at T=64,G=8,L=1 and all four physical consumer types.

The counterexample's SHA256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No native source, archive, pin, production exclusion or diagnostic gate
changed. No commit or push was made. Current terminal results follow.

### Historical terminal verification: normalized main and Abel consumer

The focused command
`lake build TaoTrudgianYang2025.SemanticRegression` ran with the pinned
Lean 4.30 toolchain from `Extension`, completed 9076 jobs and returned
0 with no Lean diagnostic after the source fixes.
Mechanical checks found all five new root imports, five exact backing
PowerShell inventory entries, 30 named theorem audits and 24 regressions.

Both principal runner handles were polled to terminal completion.
Both returned exit code 0; no stage remains running or failed.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, launched from
  this folder: **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-212318-f84ce2fb.log`.
  SHA256:
  `99478ed1d98b8319f3140213014b79e388032488171e5db4f1e1e4b533feea2c`.
  The runner checked 28 required files, 20 pinned sources,
  12 frozen ANTEDB sources, 233 Lean files in its integrity scan and
  all 222 package files in its production coverage.
  The default build completed 9076 jobs; deterministic regeneration and
  semantic regression passed. The transitive audit passed all 2439
  declarations: 2434 discovered target theorems and five imported
  declarations. Dependencies contain only permitted standard logical axioms.
- `cmd /c run_lake_build.bat --no-pause`, launched from
  `E:\Lean\Riemann Zeta`: **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_212329.log`.
  SHA256:
  `a61c1fef33a12f51125f37a467cd596b5a4197a2d9b5b25d129a2b1bfb118050`.
  JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_212329.json`.
  SHA256:
  `5d29526f98219cbc3b9fc347aeebca910d12e8fb187c3953dad483f6c16fed2e`.
  All six stages have exit code 0, zero warnings, zero tactic-info output,
  zero informational builds, zero linter failures and `passed: true`.
  The root build completed 8857 jobs. The audit passed 14290 discovered
  nonprivate theorems and the explicit 7636-entry public source list.
  Coverage remains 301 root-graph modules and two explicit regressions;
  no production file is excluded or unclassified.

The unchanged foundation verifier is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs evaluate HEAD `f16f0788afefff9b82811438a7672ef485cf8bc7`
with the existing dirty tree, not a newly committed revision.

All three mandatory repository-wide scans were rerun from `E:\Lean`.
The placeholder and unsafe-proof scans returned 1 without matches.
The postulate-pattern scan returned 0 for existing comment prose and
the two rational data fields named `constant`; none is a mathematical
postulate. Both canonical integrity scanners and their regressions passed.
The full logs contain no Lean warnings, errors or tactic suggestions.
`git diff --check` returned 0; Git's LF-to-CRLF notices are not Lean
diagnostics. The preserved counterexample hash was rechecked after both
runners and is unchanged.

All eleven target documents were mechanically compared with their
synchronized updates. The architecture's ZMN node records only the
proved exact normalization, pointwise weights and literal Abel consumer.
The goal retains maintenance of the exact batch interface and its
PowerShell inventory. No Lean source changed after these evaluations.
At that checkpoint, uniform dyadic variation, smaller-width source estimates
or a genuine lower-value reduction, the dyadic/Gram argument, the twelfth moment and
unconditional Add-est remain open. The full EPZAE-00--41 goal stays active.

## Damped main-weight variation and actual source blocks

Six additional production modules now close the uniform variation step:
`FiniteWeightVariation`, `AtkinsonGaussianVariation`,
`AtkinsonSaddleSamples`, `AtkinsonResidualVariation`,
`AtkinsonMainVariation` and `AtkinsonPhaseBlockBound`.
All 36 public theorems have named dependency audits; 24
`DampedWeightVariationRegression` examples check the actual objects,
both signs, empty blocks and closed physical boundaries.

`FiniteVariationBound f N M` records three proved inequalities:
M is nonnegative, every norm at indices 0 through N is at most M,
and the sum of adjacent norm differences over indices below N is at
most M. It is not an assumed zeta or exponential-sum estimate.
The generic product and ordered-sampling rules are applied to all four
factors of each actual normalized main weight.

For E(G,v)=exp(-(Gv)²/8), the actual complex Gaussian increment from
0≤a≤b is bounded by 2sqrt(pi) G (E(G,a)-E(G,b)).
The proof integrates the already proved actual derivative bound using
the exact real envelope primitive. The increasing saddle frequency
2arsinh(sqrt(pi n/(2T))) then gives a telescoping, damped variation bound.

The positive and negative normalized saddle roots are respectively
increasing and decreasing. On 10000(m+N)≤T their samples lie in [1/4,1],
where the actual Mellin profile has a constructed uniform Lipschitz bound.
Each original cutoff transition has variation at most one; their
product has variation at most two, independently of transition width.
The actual fourth-root coefficient is decreasing for positive indices.
These facts prove, for both separate weights Wplus and Wminus,

```text
sup_(0<=i<=N) |W(T,G,L,m+i)| <= B,
sum_(0<=i<N) |W(T,G,L,m+i+1)-W(T,G,L,m+i)| <= B,
B = C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)).
```

`exists_finiteVariationBound_atkinsonMainWeights` constructs one C>0
before T,G,L,m,N. Its range is T,G,L>0, G²≤2T, m>0 and
10000(m+N)≤T. No 8L≤G premise or equality of the two residual weights
is needed. The supremum and variation are each bounded by B; their
sum is not asserted to be at most B.

`atkinsonStationaryBlock` is the sum of the original stationary
Bessel/divisor terms at m through m+N-1. Let A(T,m,N) be the maximum,
over 0≤j≤N, of the norm of the actual raw positive-phase sum at
m through m+j-1. Finite partial summation, both separate weight bounds
and the exact common source phase prove

```text
|atkinsonStationaryBlock(T,G,L,m,N)|
  <= C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)) A(T,m,N).
```

`exists_atkinsonSourceCutoff_block_bound` is the actual-source consumer.
For each δ>0 it derives all preceding scale hypotheses beyond one
threshold T₀≥40000, from T^δ≤G≤T^(1/2-δ), L=log T,
m>0 and m+N≤atkinsonSourceCutoff(T,G,log T).
In particular, it consumes the proved eventual smallness of that exact
ceiling cutoff; small-frequency geometry is no longer a premise here.
This block theorem applies throughout the original power-width range.
It does not alter the earlier stationary-error estimate, which still
requires G≥T^(1/4).

The next continuation now assembles the complete source with a faithful
finite dyadic partition and a truncated last block below the same cutoff.
The required maximal phase-sum/Gram estimate remains open.
A maximum of partial sums is not silently identified with Ivić's
endpoint-plus-integral expression. Smaller-width stationary errors or a
genuine lower-value-range reduction also remain required.
The sharp full-width Atkinson theorem, critical twelfth moment,
EPZAE-21/37, every unconditional Add-est clause and the full
EPZAE-00--41 goal remain OPEN. ZVB is green only for the proved variation
and actual source-block consumer.

Maintain all six root imports, 36 named audits, 24 regressions and the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed; execute
it and `run_lake_build.bat` after relevant changes.
Preserve the original Lemma 62 counterexample byte-for-byte and the
proved independent ρ/k and ρ*/k witnesses with their actual Heath–Brown
application. Never restore false fifth-coordinate scaling or a third
s-preserving witness.

### Damped-variation semantic audit

ZVB closes a source-block consumer, not just a generic variation lemma.
Its public theorem is `exists_atkinsonSourceCutoff_block_bound`.
Unfolding `atkinsonStationaryBlock` gives the original stationary
Bessel/divisor terms, and unfolding `atkinsonPhaseBlockMax` gives the
finite maximum of the actual raw phase partial sums, including zero
and the final prefix. No supplied weight, phase bound, stationary estimate
or independently chosen logarithmic scale is a theorem parameter.

The exact signed stationary identity applies the constructed uniform
variation theorem to each actual normalized weight. It uses the original
cutoff transitions, the actual saddle-root Mellin profile and the
actual quadratic Gaussian, whose complex derivative is integrated
against the real damping envelope. The scalar fourth-root factor is
proved antitone on positive indices. Only raw negative phases are
conjugated. Uniform constants precede all physical and block parameters.

The source-cutoff consumer invokes `eventually_atkinsonSourceCutoff_small`
at the same T,G,log T. Thus it derives 10000(m+N)≤T from the actual
ceiling cutoff; it also derives G>0, log T>0 and G²≤2T from the original
power-width assumptions. No 8L≤G or G≥T^(1/4) hypothesis is introduced
into this block theorem. The earlier full-zeta consumers are unchanged
and retain their fourth-root-width stationary-error restriction.

The 24 regressions cover constant and product variation, increasing and
decreasing samples, zero frequency, equal Gaussian-increment endpoints,
both saddle signs, both closed small-frequency endpoints, an actual
cutoff with L=100 and G=1, empty stationary/phase blocks, the final
prefix in the maximum, and the exact general and source-cutoff consumer
types. The actual-weight boundary T=20000,G=200,m=N=1 checks both
G²=2T and 10000(m+N)=T, including the endpoint sample.
No regression substitutes a numerical special case for a universal proof.

All six modules are root-imported and explicitly listed in the unchanged
batch interface's backing PowerShell inventory. All 36 public theorems
have explicit `#print axioms` entries in addition to exhaustive discovery.
The proof-development elaboration failures were repaired at their cause;
the final focused semantic build returned 0 with no Lean diagnostic
(9082 jobs). No diagnostic suppression, proof oracle, new pin, source
archive change or production exclusion was introduced. The original
counterexample and repaired powering/Heath–Brown chain are unchanged.
Terminal verification of this checkpoint follows.

### Historical terminal verification: damped variation and source blocks

Both principal runner handles were polled to terminal completion.
Both returned exit code 0. No stage remains running or failed; the full
logs contain no Lean warnings, errors or tactic suggestions.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, from this
  folder: **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-215401-e9abe474.log`.
  SHA256:
  `76d8d7727d8ed997598c616648ff272d152bba9e1642bf881361dfa5a22182b4`.
  The runner checked 28 required files, 20 pinned sources, 12 frozen
  ANTEDB sources, 239 Lean files in its integrity scan and all 228
  package files in production coverage. Deterministic regeneration,
  the 9082-job default build and semantic regression passed.
  The transitive audit passed all 2494 declarations: 2489 discovered
  target theorems and five imported boundary declarations.
  Only permitted standard logical axioms occur.
- `cmd /c run_lake_build.bat --no-pause`, from
  `E:\Lean\Riemann Zeta`: **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_215402.log`.
  SHA256:
  `b6b8dde1a70ed12075f29e0551607f1d17fba151406f8743424f60afbdd344e3`.
  JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_215402.json`.
  SHA256:
  `10d824dec4255904347bc671c9b4d6a6456fd35bd0b6f6b1f961f27c6b739892`.
  All six stages have exit code 0, zero warnings, zero tactic-info
  output, zero informational builds, zero linter failures and
  `passed: true`. The root build completed 8857 jobs; the dependency
  audit passed 14290 discovered nonprivate project theorems and the
  explicit 7636-entry public source list. Coverage remains 301
  root-graph modules plus two explicit regressions, with no excluded
  or unclassified production file.

The foundation verifier remains SHA256
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs evaluate HEAD `f16f0788afefff9b82811438a7672ef485cf8bc7`
with the existing dirty worktree; no commit or push was made.

Mechanical checks confirmed six new root imports, six exact backing
inventory entries, all 36 named public theorem audits and 24 regression
examples. All eleven target documents were compared against their
synchronized contents, including the goal's exact batch-maintenance
requirement and ZVB's actual-source semantic scope.

The three mandatory repository-wide scans ran from `E:\Lean`.
The placeholder and unsafe-proof patterns returned 1 with no matches.
The postulate pattern returned 0 for existing comment prose and two
rational data fields named `constant`; none is a mathematical postulate.
Both canonical integrity gates passed. `git diff --check` returned 0;
Git's LF-to-CRLF notices are not Lean diagnostics.

After both runners, the preserved counterexample still has SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No Lean source changed after these evaluations. The independent-coordinate
powering/Heath–Brown chain and frozen public contracts are unchanged.

That checkpoint closed uniform damped variation and the actual source-block
consumer only. Global dyadic assembly, the phase-sum/Gram argument,
smaller-width stationary estimates or a proved lower-value reduction,
the genuine twelfth moment and unconditional Add-est remain open.
EPZAE-21/37 and the full EPZAE-00--41 goal remain active, not completed
or blocked. Proposed owner-run commit message:
`Prove damped main-weight variation and source block bounds`.

## Complete dyadic source assembly and physical zeta consumers

Three production modules, `TruncatedDyadicPartition`,
`AtkinsonDyadicMain` and `AtkinsonDyadicZetaConsumer`, now have
20 named public theorem audits and 24 semantic regressions.
They consume the previously proved actual block estimates rather than
assuming a bound for an abstract main sum.

For a natural cutoff N, block j starts at M=2^j and has length
min(M,N-M). The index range is j<clog(2,N), the natural ceiling
logarithm. Every retained block has positive length, starts strictly
below N and ends at or before N. At an exact power of two the last
block is full and no extra empty block is retained. The zero and one
cutoffs have no blocks.

`sum_range_eq_truncatedDyadic` proves the exact partition for every
additive sequence whose zero coefficient vanishes. The induction first
partitions a prefix ending at min(N,2^J); it never extends the source
to a larger power-of-two cutoff.
`atkinsonStationaryLeadingFiniteSum_eq_dyadic` applies that theorem
to the original stationary Bessel/divisor terms and their proved zero
coefficient. Both signs and their separate weights remain in each block.

Define A(T,M,K) as the maximum of the actual raw phase-prefix norms
on indices M through M+K-1. The complete stationary series is bounded
by C G T^(-1/4) times

```text
D(T,G,N) = sum_(j<clog(2,N))
  M^(-1/4) exp(-G²M/(12T)) A(T,M,min(M,N-M)),  M=2^j.
```

`exists_norm_atkinsonStationarySum_le_dyadic` sets
N=atkinsonSourceCutoff(T,G,log T), consumes the actual finite-support
identity and source-cutoff block theorem, and derives all support and
width hypotheses from T^δ≤G≤T^(1/2-δ), eventually for each δ>0.
Its constant and threshold precede T and G. This stationary-main bound
does not require G≥T^(1/4).

For later height estimates, `atkinsonPhaseBlockMax_mono` proves that
each shortened last-block phase maximum may be enlarged to A(T,M,M).
Only the raw phase maximum is enlarged: no stationary term, cutoff
support or small-frequency estimate is applied beyond N.
The resulting full-block sum is `atkinsonFullDyadicPhaseBound`,
denoted Dfull below. The public complete-series consumer
`exists_norm_atkinsonStationarySum_le_fullDyadic` proves the same
bound with Dfull in place of D.

Four physical consumers now apply this complete-series estimate to the
actual Gaussian and local zeta means. For both
I=integral_R exp(-((t-T)/G)²)|zeta(1/2+it)|² dt and
I=integral_(T-G)^(T+G)|zeta(1/2+it)|² dt, they prove

```text
I <= C_(delta,epsilon) [
  G T^(-1/4) Dfull(T,G,atkinsonSourceCutoff(T,G,log T))
  + G log T + T^(1/4+epsilon)],
```

eventually on the original power-width range with G≥T^(1/4).
Their `above_fourthRoot` versions replace the last two terms by
G log T when G≥T^(1/4+κ), κ>0. The original source factors are
absorbed into a uniform positive C, not dropped. The Gaussian theorem
is an upper bound, not an approximation identity after discarding
the main term's sign.

ZDA is green for exact dyadic assembly and these actual physical
consumers only. Next prove the maximal phase-sum/Gram estimate with
the required height scales and spacing. The inspected adjacent prefix
Gram theorem has one common prefix at every height and interval (K,2K];
it cannot be applied directly to these height-dependent maxima on [M,2M).
Prove the variable-prefix and endpoint bridges before reusing that result.
A maximum of raw phase prefixes
is still not identified with Ivić's endpoint-plus-integral expression.
Smaller-width stationary errors or a proved lower-value-range reduction
remain required as well. The genuine critical twelfth moment,
EPZAE-21/37, all unconditional Add-est clauses and the full
EPZAE-00--41 goal remain OPEN.

Maintain all three root imports, 20 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and run
it and `run_lake_build.bat` after relevant changes.
Preserve the Lemma 62 counterexample byte-for-byte and the proved
independent ρ/k and ρ*/k witnesses and actual Heath–Brown application.
No false fifth-coordinate scaling or third s-preserving witness returns.

### Dyadic-source semantic audit

ZDA's actual upstream objects are
`atkinsonStationaryLeadingTerm` and
`atkinsonStationaryLeadingSum`, not abstract coefficient data.
`sum_range_eq_truncatedDyadic` requires the actual zero-index
coefficient to vanish; the source consumer discharges that with
`atkinsonStationaryLeadingTerm_zero`.
The finite-support identity uses the original saddle cutoff.
Every block's endpoint inequality is proved from j<clog(2,N);
no support, variation or stationary estimate is a public theorem premise.

`exists_norm_atkinsonStationarySum_le_dyadic` consumes the real
source-cutoff block theorem and derives the positive/logarithmic width
conditions needed for the complete-series identity. Constants and the
large-height threshold precede T and G. The physical parameters in
the cutoff, stationary terms, damping and raw phase sums are identical.
The maximum includes all prefixes through the last index. Its proved
monotonicity enlarges only the raw phase sum, not the source geometry.

All four physical consumers use the earlier actual Gaussian/local-mean
theorems and the newly proved complete stationary norm bound. They
retain G≥T^(1/4), or G≥T^(1/4+κ), and absorb only nonnegative terms
into a uniform constant. They do not claim a signed main approximation,
the missing smaller-width error, a Gram estimate or the twelfth moment.
The full-block maximum remains distinct from the source's
endpoint-plus-integral phase expression.

The 24 regressions include ceiling logarithms at 0,1,8,9; truncated
lengths before, at and after a power of two; the closed endpoint at
cutoff 3; generic exact partition; actual zero/one stationary sums;
the actual two-block decomposition at cutoff 3; empty phase majorants;
monotone phase maxima; both complete-series signatures; and all four
physical zeta consumer types.

All three production modules, 20 named public audits and 24 regressions
are in the root graph and exact backing batch-runner inventory.
The focused semantic build completed 9085 jobs with exit code 0 and
no Lean diagnostic. Ordinary elaboration issues with natural-number
inequalities, occurrence syntax, numeral types and multiplication
association were repaired without suppression.
No source pin, native file, archive, diagnostic gate or exclusion changed.
The counterexample remains byte-preserved and the corrected powering/
Heath–Brown chain is untouched. Terminal verification follows.

### Current terminal verification: complete dyadic source assembly

Both principal runner handles were polled to terminal completion.
Both returned exit code 0; no stage remains running or failed.
The complete logs contain no Lean warning, error or tactic suggestion.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, launched
  from this folder: **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-221154-c3aacb9f.log`.
  SHA256:
  `a0fc4a2150e620932d821fa4d1b5c5691d5c6b082f0fe0b0f4b81810da35da3c`.
  The runner checked 28 required files, 20 pinned sources, 12 frozen
  ANTEDB sources, 242 Lean files in the integrity scan and all 231
  package files in production coverage. Deterministic regeneration,
  the 9085-job default build and semantic regression passed.
  The transitive audit passed all 2524 declarations: 2519 discovered
  target theorems and five imported boundary declarations.
  Only permitted standard logical axioms occur.
- `cmd /c run_lake_build.bat --no-pause`, launched from
  `E:\Lean\Riemann Zeta`: **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_221155.log`.
  SHA256:
  `a9f3cdfcfce239ca47b4f733264dd906f9b99f6aabfe3f01abee6ff60cf1f378`.
  JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_221155.json`.
  SHA256:
  `2aed309b7183677b6a5847ff2a37952e95daf33fb297967dac7ca576fd8eb505`.
  All six stages have exit code 0, zero warnings, zero tactic-info
  output, zero informational builds, zero linter failures and
  `passed: true`. The root build completed 8857 jobs. The audit
  passed 14290 discovered nonprivate project theorems and the explicit
  7636-entry public source list. Coverage remains 301 root-graph
  modules plus two explicit regressions, with no production exclusion
  or unclassified file.

The unchanged foundation verifier is SHA256
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs evaluate HEAD `f16f0788afefff9b82811438a7672ef485cf8bc7`
with the existing dirty worktree. No commit or push was made.

Mechanical checks found all three new root imports, three exact
backing PowerShell inventory entries, 20 named public audits and 24
`TruncatedDyadicSourceRegression` examples. All eleven target documents
were compared with their synchronized contents. The goal retains
maintenance of the exact batch interface and both principal evaluations.
The architecture marks ZDA green only for the exact source assembly
and actual fourth-root-width physical consumers.

All three mandatory repository-wide scans ran from `E:\Lean`.
The placeholder and unsafe-proof scans returned 1 with no matches.
The postulate-pattern scan returned 0 for existing comment prose and
two rational data fields named `constant`; no mathematical postulate
was found. Both canonical integrity gates passed.
`git diff --check` returned 0; Git's LF-to-CRLF notices are not
Lean diagnostics.

The counterexample was rehashed after both runs and remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No Lean source changed after the evaluations. The corrected independent
powering witnesses, actual Heath–Brown application and frozen public
contracts are unchanged.

Global dyadic assembly is now proved. The next analytic obligation is a
faithful maximal phase-sum/Gram estimate, including height-dependent
prefixes and endpoint conventions. Smaller-width source estimates or
a proved lower-value reduction, the critical twelfth moment and
unconditional Add-est remain open. EPZAE-21/37 and the full
EPZAE-00--41 goal stay active, not completed or blocked.
Proposed owner-run commit:
`Assemble truncated dyadic Atkinson source bounds`.
