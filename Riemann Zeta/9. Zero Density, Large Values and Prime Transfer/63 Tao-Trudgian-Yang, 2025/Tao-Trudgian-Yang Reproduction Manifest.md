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
