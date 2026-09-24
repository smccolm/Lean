# Tao--Trudgian--Yang 2025 reproduction manifest

Current analytic progress: [Actual common-shift reflected family](#actual-common-shift-reflected-family--current-checkpoint).
One common shift and a literal nonempty separated family are now extracted from the actual reflection convolution, preserving the required amplitude-cardinality loss. Finite target normalization and the exact reflection supremum remain open under EPZAE-21. Completion remains 28/42; both counterexamples and all nine repaired Add-est clauses are preserved.

Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


## Historical implementation baseline

**Verified implementation baseline, 20 September 2026.** A unified Lean
package, its selected frozen dependency, exact certificate kernel, semantic
regressions, and transitive axiom audit are installed. This is not yet a
paper-level release: at that baseline no advertised exponent-pair, density,
or energy theorem was claimed complete. The current checkpoint above and
the latest evidence below supersede this historical status.

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

### Historical terminal verification: complete dyadic source assembly

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

## Actual height-dependent maximal Gram consumers

The eight production modules are `FinitePrefixGram`,
`AtkinsonPrefixVectors`, `AtkinsonMaximalGram`,
`AtkinsonCoefficientEnergy`, `AtkinsonDyadicGramBudget`,
`AtkinsonPacketGram`, `AtkinsonLocalMeanGram` and
`AtkinsonGramPhysicalCutoff`. All 41 public theorems have named
axiom audits; 24 regressions cover the real objects and final signatures.

Let f(t,n) be the already proved actual source phase in radians,
A(t,M,N) the actual raw phase-prefix maximum, and

```text
E(M,N) = sum_(i<N) |d(M+i)|²,
Q(M,j;t,u) = sum_(i<j) exp(i [f(u,M+i)-f(t,M+i)]),
B(M,N;t,u) = max_(0<=j<=N) |Q(M,j;t,u)|.
```

The coefficient is the actual d(n)(-1)^n. Its sign cancels in its
squared norm. Each height t separately attains its maximum at j(t)≤N.
The exact vector inner product is Q(M,min(j(t),j(u));t,u), not
Q(M,N;t,u). Zero prefixes, unequal prefixes and both height orders
are covered. The direct masking proof uses [M,M+j), with no appeal
to the adjacent common-prefix theorem on (K,2K].

`sum_atkinsonPhaseBlockMax_sq_le_selectedGram` first proves the
inequality with these actual selected pairwise prefixes.
`sum_atkinsonPhaseBlockMax_sq_le_gramMax` then proves, for every
finite W,

```text
(sum_(t in W) A(t,M,N))² <= E(M,N) sum_(t,u in W) B(M,N;t,u).
```

No spacing or analytic Gram estimate is a premise.
B(M,N;t,t)=N is proved exactly; B is symmetric and nonnegative.
The separate `exists_atkinsonBlockCoefficientEnergy_le` theorem
uses the native ordinary-divisor bound at ε/2 to prove, uniformly
for 0<M and N≤M, E(M,N)≤Cε M^(1+ε).
Its block-level consumer is also proved. This is an epsilon-power
estimate, not a claimed M log³M bound.

For J=clog(2,N), define the literal nonnegative budget

```text
Gamma(N,W) = J sum_(j<J)
  (M^(-1/4))² E(M,M) sum_(t,u in W) B(M,M;t,u),  M=2^j.
```

The damped full-dyadic source majorant is bounded by the undamped
sum U(t,N)=sum_(j<J) M^(-1/4) A(t,M,M).
Finite Cauchy–Schwarz in j consumes the actual maximal Gram theorem:
(sum_(t in W) U(t,N))²≤Gamma(N,W). The Gaussian is removed by an
upper bound, not an identity. Gamma still uses literal E; the separate
epsilon-energy theorem is substituted in the later numerical budget below.

The source-cutoff maximum over W is derived, not supplied as a premise.
For H≥1, G>0 and W contained in [H,2H], monotonicity of the actual
ceiling cutoff proves

```text
max_(t in W) atkinsonSourceCutoff(t,G,log t)
 <= atkinsonSourceCutoff(2H,G,log(2H))
  = ceil(72H(log(2H)/G)²).
```

Only nonnegative phase/Gram majorants are enlarged; no stationary
term is extended beyond its own source cutoff.

`exists_atkinsonStationaryPacket_sq_le_physicalGram` consumes the
complete actual stationary Bessel/divisor sum S(t,G,log t) and proves

```text
(sum_(t in W) |S(t,G,log t)|)²
 <= Cδ G² H^(-1/2) Gamma(ceil(72H(log(2H)/G)²),W).
```

For every δ>0 its Cδ>0 and H0≥40000 precede H,G,W. The hypotheses
are H0≤H, G>0, H≤t≤2H and t^δ≤G≤t^(1/2-δ) for each t in W.
There is no fourth-root-width restriction for this stationary-only bound.

The final two `exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram`
theorems consume the actual local zeta integral
I(t,G)=integral_(t-G)^(t+G)|zeta(1/2+iv)|² dv.
They bound the square of the sum of max(0,I(t,G)-error) by the same
physical Gamma expression with a uniform positive factor D.
For δ,ε>0 the error is Cδ,ε(G log t+t^(1/4+ε)) and G≥t^(1/4)
remains required. The `above_fourthRoot` version has error
Cδ,κ G log t for κ>0 and G≥t^(1/4+κ). All constants and thresholds
precede the physical parameters. The original local-source factor
2 exp(1) is retained in the deduction and absorbed into D.

ZMG is green for this finite maximal-prefix argument and its actual
stationary/local-excess consumers. The continuation below proves
uniform cancellation for every truncated Q(M,j;t,u), derives the full
mean-value endpoint geometry at the physical cutoff and substitutes
the arithmetic coefficient-energy bound. ZPC records those actual
numerical consumers. ZGB retains separated-height summation and scale
optimization as open. No full-block estimate is substituted for an
unknown prefix.

The raw maximum is still not identified with Ivić's endpoint-plus-integral
expression. The source-form bridge, smaller-width stationary errors or
a proved lower-value-range reduction, and the genuine critical twelfth
moment remain open. EPZAE-21/37, every unconditional Add-est clause and
the full EPZAE-00--41 goal remain OPEN; this checkpoint does not narrow
their acceptance tests.

Maintain all eight root imports, 41 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that batch interface and its implementation as needed, and
execute it and `run_lake_build.bat` after relevant changes.
Preserve the Lemma 62 counterexample byte-for-byte and the proved
independent ρ/k and ρ*/k witnesses and actual Heath–Brown application.
Never restore false fifth-coordinate scaling or a third s-preserving
witness. Keep the full goal active until all original completion tests pass.

### Semantic audit: actual maximal-prefix Gram assembly

The new finite duality consumes the native `phaseAlign`,
`norm_sum_mul_sq_le` and `sum_norm_sq_sum_le_gram` results;
no analytic theorem is assumed. Actual alternating coefficients and the
radian source phase are identified with the raw phase sum in
`atkinsonPhaseBlockSum_eq_masked`.
`atkinsonMaskedPhaseVector_gram` proves the paired minimum-prefix
identity on the target's actual zero-based interval, including empty
prefixes. `atkinsonMaximizingPrefix_spec` supplies the attained
prefix independently at each height. No measurable-selection claim
is made or needed for the finite height family.

The selected-prefix and maximal-prefix Gram consumers retain literal
ordinary-divisor energy. The separate arithmetic-energy theorem uses
the native pointwise divisor bound, not an assumed coefficient estimate.
The physical packet budget currently retains the literal energy, so
its proof is not described as consuming the separate epsilon-power
energy theorem. Finite dyadic Cauchy–Schwarz, the proved undamped
enlargement and source-cutoff monotonicity perform the actual assembly.

The three final physical consumers above have no stationary-source,
local-zeta-entry, summability or Gram inequality as a theorem parameter.
Their scale H, actual heights t, common G, log t and source ceilings
are linked in the same chain. The local-excess positive part is the
actual integral minus the previously proved error, not a proxy for a
zeta moment. Its comparison uses the source factor 2 exp(1), the real
part bound and the actual stationary packet estimate. Width restrictions
are explicit and unchanged.

The 24 regressions cover generic zero-prefix masking; unequal prefixes
1 and 3 with minimum 1; zero against nonzero prefix; conjugate reversal;
zero and nonzero diagonal entries; maximal diagonal and zero-block
values; actual maximizers including N=0; literal coefficient energies
E(1,0)=0 and E(1,2)=5; the empty-height lower-value consumer; the
epsilon-energy signature; undamped enlargement even at G=0; empty
dyadic sums/budgets/packet cutoffs; the physical cutoff comparison;
the literal local-excess definition; selected-prefix Gram type; and
all three final physical consumer signatures.

The focused semantic build completed 9093 jobs with exit code 0 and
no Lean diagnostic. Initial proof-elaboration and two numerical-regression
errors were repaired at source; no warning or linter suppression was
introduced. All eight modules and 41 named public audits are in the
root and exact backing PowerShell inventory. No dependency pin, native
file, source archive, exclusion or diagnostic gate changed in this
checkpoint. The preserved counterexample and corrected independent
powering/Heath–Brown chain are untouched. Terminal verification follows.

### Historical terminal verification: height-dependent maximal Gram consumers

Both principal runner handles were polled to terminal completion.
Both returned exit code 0; no stage remains running or failed.
The full logs contain no Lean warning, error or tactic suggestion.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, launched
  from this folder: **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-224613-2e9aebf3.log`.
  SHA256:
  `d88ef341c53936e33ea3e4f0dfe1c3c7093a374313da398accfaffc82f8746b4`.
  The runner checked 28 required files, 20 pinned sources, 12 frozen
  ANTEDB sources, 250 Lean files in the integrity scan and all 239
  package files in production coverage. Deterministic regeneration,
  the 9093-job default build and semantic regression passed.
  The transitive audit passed all 2575 declarations: 2570 discovered
  target theorems and five imported boundary declarations.
  Only permitted standard logical axioms occur.
- `cmd /c run_lake_build.bat --no-pause`, launched from
  `E:\Lean\Riemann Zeta`: **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_224614.log`.
  SHA256:
  `487b28e3bbfb912b121c29c047921b4e05a0383467f1aedd905f0a1eb576bd86`.
  JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_224614.json`.
  SHA256:
  `c3dab61686ce336d83fd7ad5dfa2052cac057ee2110e98918ba54ec8051a0f64`.
  All six stages have exit code 0, zero warnings, zero tactic-info
  output, zero informational builds, zero linter failures and
  `passed: true`; the manifest status is `PASS` with no failures.
  The root build completed 8857 jobs. The audit passed 14290 discovered
  nonprivate project theorems and the explicit 7636-entry public source
  list. Coverage remains 301 root-graph modules plus two explicit
  regressions, with no production exclusion or unclassified file.

The unchanged foundation verifier is SHA256
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The current runs evaluate HEAD
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`
with a dirty worktree. That is the actual run revision, not the
preceding checkpoint's revision. No commit or push was made by this
proof continuation; existing user changes were preserved.

Mechanical checks found all eight root imports, eight exact backing
PowerShell inventory entries, 41 named public audits and 24
`HeightDependentPrefixGramRegression` examples. The path check was
corrected to normalize Windows separators; no production-inventory
entry was missing. All eight production source files were compared
with their compiled contents, and all eleven target documents with
their synchronized contents.

The goal retains maintenance of the exact
`run_tao_trudgian_yang_build.bat` interface and both principal
evaluations. The architecture marks ZMG green only for finite
height-dependent-prefix Gram assembly and the actual physical
stationary/local-excess consumers. ZGB is explicitly open for numerical
truncated phase-difference estimates and separated-height summation.
The final physical budget retains literal divisor energy and is an
undamped upper bound; the separate epsilon-energy result is not
misreported as a consumed numerical budget estimate.

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

The next analytic obligation is a uniform bound for the actual
truncated phase-difference sums, with physical gap and full endpoint
geometry proved at the enlarged cutoff, followed by separated-height
summation. The source-form bridge, smaller-width source estimate or
a proved lower-value reduction, critical twelfth moment and
unconditional Add-est remain open. EPZAE-21/37 and the full
EPZAE-00--41 goal stay active, not completed or blocked.
Proposed owner-run commit:
`Prove height-dependent maximal Gram source consumers`.

## Uniform truncated phase cancellation and arithmetic gap packets

Thirteen modules add 79 named public theorem audits and 30 regressions:
`AtkinsonIndexPhase`, `AtkinsonIndexCurvature`,
`AtkinsonIndexHeight`, `AtkinsonIndexScales`,
`AtkinsonIndexBProcess`, `AtkinsonIndexFirstDerivative`,
`AtkinsonPrefixCancellation`, `AtkinsonPrefixGapBound`,
`AtkinsonGramCutoffGeometry`, `AtkinsonGapBudget`,
`AtkinsonGapPacketConsumers`, `AtkinsonGapArithmetic` and
`AtkinsonArithmeticGapPackets`.

The first six adapt the inspected adjacent real-index proofs locally.
The real phase restricts exactly to the already connected
`atkinsonSourcePhase`; there is no new source-entry assumption or
adjacent conditional moment import. For T,x>0 its first derivative is
sqrt(2πT/x+π²), and its second derivative is
-πT/[x² sqrt(2πT/x+π²)]. The height derivative of the positive
curvature magnitude and two mean-value arguments derive the literal
uniform increment and second-difference bounds.

For ordered heights 0<u<t≤2u, M>0 and M+N+2≤u, put
Δ=t-u, B=M+N+2, D=M+N+1 and

```text
sMinus(u,x) = sqrt(2*pi*u/x),
sPlus(u,x)  = sqrt((2*pi+pi²)*2*u/x),
lambda     = pi*Delta/(2*B²*sPlus(u,M)),
Lambda     = pi*Delta/(M²*sMinus(u,B)),
L          = pi*Delta/(D*sPlus(u,M)),
U          = pi*Delta/(M*sMinus(u,D)).
```

Both curvature parameters are positive and are proved bounds for the
actual phase differences. For every j≤N,

```text
|Q(M,j;t,u)| <= (N*Lambda/(2*pi)+2) *
  (2*pi/sqrt(lambda)+2*(sqrt(lambda)/lambda+1)).
```

`norm_atkinsonPrefixGram_le_bProcess` applies the native B-process
to the restricted actual second-difference bounds. Its full ambient
M,N parameters are independent of j. The empty prefix is included.
The same argument bounds the maximum over all j≤N.

When U≤π, `norm_atkinsonPrefixGram_le_firstDerivative` proves
|Q(M,j;t,u)|≤2π/L=2D sPlus(u,M)/Δ. The positive-slope orientation is
the conjugate Gram entry; its exact conjugacy and decreasing unit
increments are proved. The period-endpoint conditions are derived
from the actual lower/upper slope scales, not assumed as a cancellation
theorem.

Let F(M,N;t,u)=`atkinsonPrefixGapMajorant M N t u`. On the diagonal
F=N exactly. Off the diagonal, the larger height is placed first.
F is the minimum of N and the B-process bound; when U≤π it also
takes the minimum with the first-derivative bound. The triangle bound,
both cancellation alternatives, symmetry and the bound for every
actual truncated Gram entry are proved. F is a literal numerical
expression, not a new name for the unevaluated phase maximum.

The required endpoint geometry is now derived at the physical cutoff.
For δ>0, eventually and uniformly for H^δ≤G,

```text
2*atkinsonSourceCutoff(2H,G,log(2H))+2 <= H.
```

The proof uses (2H)^(δ/2)≤H^δ for H≥2 and the earlier source-ceiling
smallness theorem at exponent δ/2. Therefore every M=2^j with
j<clog(2,atkinsonSourceCutoff(2H,G,log(2H))) has
M+M+2≤H. If t,u belong to [H,2H], the positivity and dyadic height
conditions also follow. No free endpoint or curvature hypothesis
remains in the final physical consumer.

`exists_atkinsonPhysicalGramBudget_le_gapBudget` replaces every
actual Gram maximum by F. It derives H^δ≤G from any member of a
nonempty actual packet satisfying t^δ≤G; the empty packet is proved
separately. No artificial nonemptiness or extra width assumption is
introduced into the source theorem.

The next arithmetic step consumes the already proved ordinary-divisor
energy bound, rather than merely citing it nearby. For η>0,
`exists_atkinsonPhysicalGapBudget_le_arithmetic` replaces the
coefficient-energy sum in every block. The identity
(M^(-1/4))² M^(1+η)=M^(1/2+η) supplies the exact final weight.
Define the fully numerical budget, J=clog(2,N),

```text
Psi(eta,N,W) = J sum_(j<J)
  M^(1/2+eta) sum_(t,u in W) F(M,M;t,u),  M=2^j.
```

`exists_atkinsonStationaryPacket_sq_le_arithmeticGap` proves

```text
(sum_(t in W) |S(t,G,log t)|)²
 <= C_(delta,eta) G² H^(-1/2) Psi(eta,ceil(72H(log(2H)/G)²),W).
```

Its C>0 and H0≥40000 precede H,G,W. It consumes the actual complete
stationary Bessel/divisor series, with H0≤H, G>0, H≤t≤2H and
t^δ≤G≤t^(1/2-δ) for every t in W. It has no fourth-root-width
restriction and no assumed analytic estimate.

The two `exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap`
consumers prove the analogous bound for the square of the sum of
max(0,I(t,G)-error), with I the actual local zeta-square integral.
The error remains Cδ,ε(G log t+t^(1/4+ε)) for G≥t^(1/4), or
Cδ,κ G log t for G≥t^(1/4+κ). Their constants and threshold precede
the physical parameters, and the source factor 2 exp(1) remains
accounted for through the earlier actual-source deduction.
The preceding three `physicalGap` consumers, retaining literal E,
are also proved and audited.

ZPC is green for these uniform truncated estimates, derived physical
geometry and actual numerical source consumers. ZGB remains OPEN:
sum the explicit gap expressions using physical height separation,
simplify their radical scales uniformly and optimize the resulting
height/index ranges. Psi's finite double sum does not itself estimate
separated-height occupancy. No such summation theorem is a premise
of the current result or is silently claimed as proved.

The source-form bridge, smaller-width stationary error or a proved
lower-value reduction, genuine critical twelfth moment and every
unconditional Add-est clause remain open. EPZAE-21/37 and the full
EPZAE-00--41 completion contract are unchanged.

Maintain all thirteen root imports, 79 named audits, 30 regressions
and the exact PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`. Update the batch interface and
its implementation as needed, and run it and `run_lake_build.bat`
after relevant changes. Preserve the original Lemma 62 counterexample
byte-for-byte and the proved independent ρ/k and ρ*/k witnesses and
actual Heath–Brown application. Never restore false fifth-coordinate
scaling or a third s-preserving witness. Keep the full goal active.

### Semantic audit: actual truncated cancellation and numerical packets

The real-index phase is definitionally the already connected natural
source phase at integral indices; its exact derivative proof is local.
The six adapted modules use only current native/Mathlib foundations,
not the adjacent conditional twelfth-moment package.

`norm_atkinsonPrefixGram_le_bProcess` uses one ambient pair of
curvature bounds for M,N, restricts their actual unit second differences
to j-1, and proves the inequality for all j≤N including zero.
`norm_atkinsonPrefixGram_le_firstDerivative` does the analogous
restriction for actual decreasing unit increments. The orientation
change is a proved conjugation, not a discarded sign convention.
No desired cancellation bound is a public theorem premise.

`atkinsonPrefixGramMax_le_gap` combines those actual results with
the exact diagonal and triangle bound. `atkinsonPrefixGapMajorant`
unfolds to radicals, the physical gap, an explicit period condition,
minima and the diagonal length; it contains no phase sum.

`exists_atkinsonPhysicalCutoff_prefix_geometry` derives the full
two-extra-endpoint range at the real ceiling cutoff. The subsequent
physical consumer derives H^δ≤G from an actual packet member, or
proves the empty case. Thus no scale, geometry, nonemptiness or
coefficient estimate is left as an unproved physical-entry parameter.

The three `physicalGap` packet consumers compose the actual previous
source with these estimates. The three `arithmeticGap` consumers
further consume `exists_atkinsonBlockCoefficientEnergy_le` through
the proved budget inequality. Their explicit eta-weighted budget
contains neither unevaluated phase sums nor coefficient-energy sums.
Source errors, power-width hypotheses and the fourth-root-width
restrictions on the local-mean error are unchanged. No separated-height
sum or critical moment is assumed or claimed.

Thirty regressions cover the actual real/natural phase equality;
the real-index derivative and curvature signs; positive curvature
parameters at heights 100,101; empty, proper and maximal prefixes;
the explicit first-derivative branch; both height orders and diagonal;
the doubled-height exponent conversion; the quarter-power arithmetic
identity; empty and zero-cutoff budgets; the full endpoint geometry;
physical Gram and arithmetic budget signatures; and all six actual
physical packet consumer signatures.

An initial numerical normalization error in one regression was fixed.
The resulting unnecessary sequential-focus linter diagnostic was then
fixed at its cause, without suppression. Focused clean verification and
both principal terminal evaluations must be recorded below; the earlier
warning-producing attempt is not counted as a clean pass.

All thirteen modules, 79 named public audits and 30 regressions are
in the default root and the exact backing PowerShell inventory.
No source pin, native source, archived paper, production exclusion or
diagnostic gate was changed. The preserved counterexample and proved
independent powering/Heath–Brown chain are untouched.

### Historical terminal verification: truncated cancellation and numerical packets

Both principal runner handles were polled to terminal completion.
Both returned exit code 0; no stage remains running or failed.
The full logs contain no Lean warning, error or tactic suggestion.
The final focused semantic build also returned exit code 0 for 9106
jobs with no Lean diagnostic, after the regression normalization and
sequential-focus issue were fixed at source.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, launched
  from this folder: **LEAN VERIFICATION PASS**.
  Log: `logs/tao-trudgian-yang-build-20260920-231544-e70cb56f.log`.
  SHA256:
  `de4c5ad4e80289d300a3886923148e0a167540695b34cbf0c3b6b2f75e6898a9`.
  The runner checked 28 required files, 20 pinned sources, 12 frozen
  ANTEDB sources, 263 Lean files in the integrity scan and all 252
  package files in production coverage. Deterministic regeneration,
  the 9106-job default build and semantic regression passed.
  The transitive audit passed all 2704 declarations: 2699 discovered
  target theorems and five imported boundary declarations.
  Only permitted standard logical axioms occur.
- `cmd /c run_lake_build.bat --no-pause`, launched from
  `E:\Lean\Riemann Zeta`: **PASS**.
  Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_231545.log`.
  SHA256:
  `e5ff81e138f4481fc8da165b77435b85f3202c47ebad3d59e37496099307d9a1`.
  JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260920_231545.json`.
  SHA256:
  `a293340f1b138c9ec57eca4964265d29e3ec05535600e282312bc8c65cc6d766`.
  All six stages have exit code 0, zero warnings, zero tactic-info
  output, zero informational builds, zero linter failures and
  `passed: true`. The manifest status is `PASS` with no failures.
  The root build completed 8857 jobs. The audit passed 14290 discovered
  nonprivate project theorems and the explicit 7636-entry public source
  list. Coverage remains 301 root-graph modules plus two explicit
  regressions, with no production exclusion or unclassified file.

The unchanged foundation verifier is SHA256
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both current runs evaluate HEAD
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`
with a dirty worktree. No commit or push was made by this continuation;
existing user changes were preserved.

Mechanical checks found all thirteen root imports, thirteen exact
backing PowerShell inventory entries, 79 named public audits and 30
`TruncatedPhaseCancellationRegression` examples. All thirteen
production source files were compared with their compiled contents.
All eleven target documents were compared with their synchronized
contents. The exact batch interface and both principal evaluations
remain requirements in the goal.

The architecture marks ZPC green only for uniform truncated cancellation,
the derived physical endpoint geometry, consumed divisor-energy estimate
and actual numerical packet consumers. The eta-weighted budget still
contains a finite double sum over actual height gaps. ZGB remains open
for its separated-height summation and scale optimization; the finite
sum is not misreported as a completed spacing theorem.

All three mandatory repository-wide scans ran from `E:\Lean`.
The placeholder and unsafe-proof scans returned 1 with no matches.
The postulate-pattern scan returned 0 for existing comment prose and
two rational data fields named `constant`; no mathematical postulate
was found. Both canonical integrity gates passed.
`git diff --check` returned 0; Git's LF-to-CRLF notices are not
Lean diagnostics.

The counterexample was rehashed after both runs and remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No Lean source changed after these evaluations. The corrected independent
powering witnesses, actual Heath–Brown application and frozen public
contracts are unchanged.

The next analytic obligation is separated-height summation of the
explicit B-process / reciprocal-gap expressions and uniform scale
simplification. Native unit-annulus occupancy and reciprocal-distance
harmonic estimates were inspected as available inputs, not treated as
an already proved bound for the present kernel. The source-form bridge,
smaller-width stationary estimate or a proved lower-value reduction,
genuine twelfth moment and unconditional Add-est remain open.
EPZAE-21/37 and the complete EPZAE-00--41 goal stay active, not completed
or blocked. Proposed owner-run commit:
`Prove truncated Atkinson cancellation and numerical packet bounds`.

## Historical checkpoint: separated near-height cancellation

EPZAE-21 now consumes the actual physical separation `IsSeparated G W`.
For every positive dyadic block `M` and heights in `[H,2H]`, the
half-period condition is derived whenever `0 < |t-u| ≤ sqrt(H*M)`.
The literal numerical majorant already used by the source satisfies
`F(M;t,u) ≤ 60*sqrt(H*M)/|t-u|`; both height orders and the exact
diagonal `F(M;t,t)=M` are retained.

Rescaling the actual height set by `t/G` proves unit separation.
The native reciprocal-distance shell estimate is then applied, giving
the near-row bound
`M + 120*sqrt(H*M)/G * harmonic(ceil(sqrt(H*M)/G))`.
The remaining row is exactly the sum over `sqrt(H*M) < |u-t|`;
no near pair, diagonal, common-prefix assumption, or unproved packing
hypothesis is concealed in that remainder.

Four new production modules are root-reachable and included in the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`AtkinsonNearGap`, `AtkinsonSeparatedReciprocal`,
`AtkinsonNearGapBudget`, and `AtkinsonSeparatedNearPackets`.
They add 17 named theorem audits and 14 semantic regressions, preserving
all previous imports, audits and regressions.

The three public `exists_atkinson*Packet_sq_le_separatedNear` consumers
use the actual stationary sum or actual local mean, with the same
source ceiling `N=ceil(72*H*(log(2H)/G)^2)`, dyadic weights
`M^(1/2+η)`, actual divisor-energy estimate, and physical width `G`.
Constants and thresholds remain before the heights and finite sets.
Local-mean errors and fourth-root/above-fourth-root width restrictions
are unchanged. This is an actual-source consumer of the near estimate,
not a proof of the full source-form or twelfth-moment theorem.

ZNH is the completed near-height substep. ZGB remains OPEN for the
far-height B-process summation, height localization and scale
optimization. ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and the full
EPZAE-00–41 goal remain OPEN. Continue those obligations; do not replace
the full goal with this checkpoint.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte, the corrected
independent ρ/k and ρ*/k witnesses, their independent fifth coordinates,
and the actual Heath–Brown application. Never restore the false
s-scaling or third s-preserving witness. Maintain and update
`run_tao_trudgian_yang_build.bat` and its backing implementation as
needed, and evaluate it and `run_lake_build.bat` after relevant changes.
The Reproduction Manifest separates terminal integrity evidence from
the mathematical scope just described.

The new physical budget is `atkinsonSeparatedGapBudget η H G N W`.
Writing `J=clog 2 N`, `M=2^j`, and `R_M=sqrt(H*M)`, it is

```text
J * sum_{j<J} M^(1/2+η) *
  (card(W) * (M + 120*R_M/G * harmonic(ceil(R_M/G)))
   + sum_{t in W} sum_{u in W, R_M < |u-t|} F(M;t,u)).
```

Semantic dependency check: `atkinson_near_half_period` derives the
increment restriction from the physical gap and the actual radical
slopes. `atkinsonPrefixGapMajorant_le_near` uses that result and the
proved first-derivative alternative of the existing majorant.
`atkinson_sum_inv_gap_le_harmonic_ceil` uses the actual scaled finite
set and native `sum_inv_distance_near_le_harmonic`.
`atkinsonArithmeticGapBudget_le_separated` substitutes the resulting
row estimate into every dyadic block. The three final packet theorems
explicitly consume the previous arithmetic source theorems and that
budget inequality. No phase/cancellation or energy hypothesis is added;
the only new physical premise is `IsSeparated G W`.

The exact public consumers are
`exists_atkinsonStationaryPacket_sq_le_separatedNear`,
`exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear`, and
`exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear_above_fourthRoot`.
Their right sides keep `G^2*H^(-1/2)` times the displayed budget.
The local-mean versions retain respectively the error
`C*(G*log(t)+t^(1/4+ε))` with `t^(1/4)≤G`, and `C*G*log(t)`
with `t^(1/4+κ)≤G`. Both still require the original power-width range.

Next acceptance obligation: estimate the filtered far-height sums from
the actual truncated B-process scales, localize the height sets with
proved covering/cardinality control, and carry the optimized scales
through the actual source consumer. The divisor estimate here is the
proved epsilon-power bound, not a newly claimed sharp logarithmic
divisor-square asymptotic. Smaller-width source entry and genuine
twelfth-moment assembly remain separate obligations.

### Historical terminal verification: separated near-height cancellation

Verified on the dirty working tree at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`, Lean 4.30.0.
No commit or push was made. The preceding checkpoint's logs remain
historical evidence, not the verification record for these four modules.

Target command, from this project folder:
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: LEAN VERIFICATION PASS`.
- Log: `logs/tao-trudgian-yang-build-20260920-233931-ef9e4ddf.log`.
- Final SHA256:
  `bf552b9310c9744e642b2876477a955cdc51061577ea970a1315966bc6e4ed76`.
- 9,110 default-build jobs; semantic regression PASS.
- 267 Lean integrity-scan files; exact package coverage 256 Lean files.
- 28 required project files, 20 pinned source files and 12 frozen
  ANTEDB files verified; deterministic certificate regeneration PASS.
- Exhaustive audit: 2,734 discovered nonprivate target theorems and
  five imported contracts, 2,739 total declarations.
- All 17 newly named public theorem audits printed only the permitted
  standard logical dependencies. No project axiom or admitted proof
  dependency was found. No Lean warning or tactic/linter diagnostic.
- `SeparatedNearGapRegression` contains 14 new tests, including the
  half-period boundary, both height orders, the exact diagonal,
  empty/singleton cases, real physical rescaling, reciprocal sums,
  the budget inequality and all three exact source-consumer types.

Foundation command, from `E:/Lean/Riemann Zeta`:
`cmd /c run_lake_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: PASS`.
- Log: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260920_233932.log`.
- Final log SHA256:
  `79e8523550a6b6194690b64bd66e075587715b7af9143866812cdd93302c93f4`.
- JSON: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260920_233932.json`.
- JSON SHA256:
  `58aa6994922117fe94b8a0e3710be9706e6d565ea7ebe2c837bdc742377b3f85`.
- JSON status PASS and empty failures; all six stages have exit code 0,
  warnings 0, tactic-info 0, informational-builds 0, linter-failures 0
  and `passed=true`.
- 8,857 build jobs; 14,290 discovered nonprivate project theorems and
  the 7,636-entry explicit public source list audited.
- Import classification: 301 root-graph modules, two explicit
  regressions, zero excluded and zero unclassified.
- Canonical verifier SHA256 unchanged:
  `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Both process handles reached completion; neither remained running at
handoff. No Lean source, import, audit or runner change was made after
these terminal evaluations. Documentation-only evidence was appended
afterward.

Repository-wide three-pattern checks: placeholder and unsafe-bypass
searches returned no matches; the postulate-pattern matches were
reviewed as explanatory comments and the two pre-existing rational
`constant : ℚ` data fields, not mathematical postulates.
`git diff --check` passed; Git's LF/CRLF conversion notices are not Lean
diagnostics. All eleven target documentation files were synchronized.

`EnergyPoweringObstruction.lean` SHA256 after both runners:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The counterexample and corrected independent powering/Heath–Brown
application were not changed.

Semantic verdict: the actual truncated majorant's near-height sum is
proved at the physical separation scale, and the actual source
consumers use it. The remaining `atkinsonFarGapRow` is an explicit
filtered far-height sum, not a proved cancellation estimate.
Far-height B-process simplification/summation, localization, optimized
scale absorption, smaller-width source entry, the genuine twelfth
moment and unconditional Add-est remain OPEN. The full goal remains
active, neither complete nor blocked.

Proposed owner-run commit:
`Prove separated near-height cancellation for Atkinson packets`.

## Closed near/far packet bounds — current checkpoint

EPZAE-21 now has a proved estimate for every height pair in the actual
truncated Gram budget. The preceding near-height result and physical
`G`-separation remain intact. For `R_M=sqrt(H*M)`, the far-height
bound is

```text
|t-u| >= R_M  ==>  F(M;t,u) <= 2000*sqrt(M*|t-u|/R_M).
```

The curvature proof includes the actual two extra discrete endpoints:
`B=2*M+2 <= 4*M`. With `Q=M*sqrt(H*M)` and `d=|t-u|`,
the lower curvature is at least `d/(320*Q)` and the upper curvature
at most `4*d/Q`. For `d<=Q` the B-process gives the square-root
bound; for `d>Q` the proved triangle bound supplies it. Both height
orders are covered. No upper-gap restriction is smuggled into the result.

For a height set in `[A,A+L]`, the far-row sum is now bounded by
`2000*card(W)*sqrt(M*L/sqrt(H*M))`. This is the actual filtered far
row, not a separately supplied estimate. Combining it with the
near-height harmonic bound and bounding each dyadic power at the
terminal index removes all phase, coefficient-energy, height-pair and
dyadic sums.

Write `R=card(W)`, `N=ceil(72*H*(log(2H)/G)^2)`,
`J=clog 2 N`, and `K=harmonic(ceil(sqrt(H*N)/G))`.
The closed budget `atkinsonPowerGapBudget η H G L N R` is

```text
J^2 * ( R*N^(3/2+η)
      + 120*R*sqrt(H)/G * N^(1+η)*K
      + 2000*R^2*H^(-1/4)*sqrt(L)*N^(3/4+η) ).
```

The six public consumers in `AtkinsonPowerGapPackets` apply this
budget to the actual stationary sum and actual local-mean excesses,
with the original factor `C*G^2*H^(-1/2)`. Three quantify the
localization interval after their uniform constants; three derive
`A=L=H` directly from the original height range `[H,2H]`.
The source ceiling, divisor-energy epsilon, separation, original
power-width range and local-mean error restrictions are unchanged.

Seven new root-reachable production modules are installed:
`AtkinsonFarCurvature`, `AtkinsonFarRadical`, `AtkinsonFarGap`,
`AtkinsonLocalizedGapBudget`, `AtkinsonLocalizedPowers`,
`AtkinsonPowerGapBudget` and `AtkinsonPowerGapPackets`.
They add 30 named public theorem audits and 27 semantic regressions.
All earlier near-height modules, 17 named audits and 14 regressions,
and all previous proof work remain installed.

ZFH is the completed far-height/closed-budget substep. ZGB remains
OPEN for physical-cutoff optimization, a covering of the height set
by suitably chosen intervals, and proved absorption/cardinality
estimates. A supplied localization interval is not yet a constructed
optimized covering. ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and
the full EPZAE-00–41 completion contract remain OPEN.

Keep the full goal active. Continue toward the real requested
endpoints, not a replacement goal consisting of this checkpoint.
Preserve `EnergyPoweringObstruction.lean` byte-for-byte and the
corrected independent ρ/k and ρ*/k witnesses, independent fifth
coordinates and actual Heath–Brown application. Never restore false
s-scaling or a third s-preserving witness. Maintain and update
`run_tao_trudgian_yang_build.bat` and its backing implementation as
needed; its exact inventory includes every new module. Run that
interface and `run_lake_build.bat` after relevant changes.

Semantic acceptance evidence:

- `atkinson_far_lambda_bounds` derives the numerical curvature
  inequalities from the actual source phase's slope bounds, including
  the true `2*M+2` endpoint geometry.
- `atkinsonPrefixGapMajorant_le_far` consumes those inequalities,
  the literal B-process alternative and the proved triangle alternative.
  It is about the same `F` already bounding every truncated prefix.
- `atkinsonSeparatedGapBudget_le_localized` estimates the actual
  filtered far rows using the physical diameter. It does not add an
  assumed cancellation, coefficient or kernel estimate.
- `atkinsonLocalizedGapBudget_le_power` uses exact exponent identities,
  monotonicity of powers and harmonic numbers, and `2^j<N` from the
  actual dyadic cutoff. The displayed `J^2` is retained explicitly.
- `exists_atkinsonStationaryPacket_sq_le_localizedPowers` and both
  `exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers`
  variants explicitly compose those inequalities with the real source
  consumers. Their corresponding `physicalPowers` theorems derive
  the global interval from `H<=t<=2*H`, rather than adding it as an
  unproved premise.

The local-mean error remains `C*(G*log(t)+t^(1/4+ε))` with
`t^(1/4)<=G`; the above-fourth-root variant retains `C*G*log(t)`
with `t^(1/4+κ)<=G`. All versions retain
`t^δ<=G<=t^(1/2-δ)`. These results do not yet establish the full
smaller-width source form, a lower-value reduction, or the critical
twelfth moment. The coefficient-energy estimate remains the proved
epsilon-power divisor bound, not a newly claimed logarithmic asymptotic.

Next acceptance obligation: substitute the actual ceiling and bound the
remaining explicit logarithmic factors with uniform parameter control,
construct the localization covering at the chosen physical length,
absorb the quadratic-cardinality term and derive the needed
large-value/cardinality bound from an actual upstream value witness.
Then complete the source-entry/lower-value obligations and genuine
twelfth-moment consumer before advertising any unconditional Add-est
conclusion. Terminal audit counts alone cannot close those obligations.

### Historical terminal verification: far-height cancellation and closed powers

Verified on 2026-09-21, dirty working tree at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`, Lean 4.30.0.
No commit or push was made. The preceding near-height verification
record is historical and remains available above.

Target command, from this project folder:
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: LEAN VERIFICATION PASS`.
- Log: `logs/tao-trudgian-yang-build-20260921-000627-920a86e7.log`.
- Final SHA256:
  `18af09f103ebd98a0b033a7b93d849c185bca8cb284ac631cdd6a1799c50c629`.
- 9,117 default-build jobs; semantic regression PASS.
- 274 Lean integrity-scan files; exact package coverage 263 Lean files.
- 28 required project files, 20 pinned source files and 12 frozen
  ANTEDB files verified; deterministic certificate regeneration PASS.
- Exhaustive audit: 2,781 discovered nonprivate target theorems and
  five imported contracts, 2,786 total declarations.
- All 30 new named public theorem audits printed only the permitted
  standard logical dependencies. No project axiom or admitted proof
  dependency was found. No Lean warning, tactic or linter diagnostic.
- `FarGapPowerRegression` adds 27 tests. They cover physical curvature
  scales, both branches of the B-process/triangle split, both height
  orders and the far-gap boundary, empty/singleton cases, exact
  weighted powers, harmonic/index monotonicity, the closed budget and
  all six complete localized/physical source-consumer types.
- Incremental proof failures were repaired in the source: normalization
  of rational factors, one redundant tactic, and explicit inference
  of the physical width in the consumers. No theorem was weakened to
  address an elaboration failure.

Foundation command, from `E:/Lean/Riemann Zeta`:
`cmd /c run_lake_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: PASS`.
- Log: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_000628.log`.
- Final log SHA256:
  `44de081a2eb22da067a7afde178f220efdf93b157ba8e6444296c6b2176acc58`.
- JSON: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_000628.json`.
- JSON SHA256:
  `14cf90476afc1ad67c208b42613c37eab6c312aa4edcd4a2c22f25de7569bb15`.
- JSON status PASS and empty failures; all six stages have exit code 0,
  warnings 0, tactic-info 0, informational-builds 0, linter-failures 0
  and `passed=true`.
- 8,857 build jobs; 14,290 discovered nonprivate project theorems and
  the 7,636-entry explicit public source list audited.
- Import classification: 301 root-graph modules, two explicit
  regressions, zero excluded and zero unclassified.
- Canonical verifier SHA256 unchanged:
  `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Both process handles reached completion. No Lean source, import, audit
or runner change was made after these terminal evaluations.
Documentation-only evidence was appended afterward.

Repository-wide three-pattern checks: placeholder and unsafe-bypass
searches returned no matches. Postulate-pattern matches were reviewed
as explanatory comments and the two pre-existing rational
`constant : ℚ` data fields, not mathematical postulates.
`git diff --check` passed; Git's LF/CRLF notices are not Lean
diagnostics. All eleven target documentation files were synchronized;
the main current sections consolidate the previous near-height status
with the new far-height result.

`EnergyPoweringObstruction.lean` SHA256 after both runners:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The original counterexample and the corrected independent powering
witnesses and actual Heath–Brown application remain unchanged.

Semantic verdict: actual far-height cancellation is proved and consumed
by six source-packet theorems with the closed three-term budget above.
No unevaluated phase, coefficient-energy, height-pair or dyadic sum
remains on their right sides. The explicit source ceiling, clog factor
and harmonic factor still need physical-scale optimization. Constructed
local covering, absorption/cardinality, the remaining source-entry or
lower-value reduction, the genuine twelfth moment and unconditional
Add-est remain OPEN. ZFH is complete only for its named substep.
ZGB/ZAT/ZTM, EPZAE-21/37 and the full goal remain active, not complete
or blocked.

Proposed owner-run commit:
`Prove far-height cancellation and closed Atkinson packet bounds`.

## Optimized physical packet bounds — current checkpoint

EPZAE-21 now has a kernel-checked two-term physical estimate for the
actual stationary source and actual local-mean excesses. Write
`R=card(W)`. For every `δ>0` and `ν>0`, the stationary result is

```text
(sum_(t in W) |S(t,G,log t)|)^2
 <= D_(δ,ν) H^ν * (R*H/G + R^2*sqrt(G*L)).
```

Here W is G-separated, each t is in [H,2H] with
`t^δ <= G <= t^(1/2-δ)`, and W lies in [A,A+L].
The positive constant and threshold H0≥40000 precede H,G,A,L,W.
The actual complete stationary series is unchanged; no analytic
estimate, cutoff bound, logarithmic bound or width conversion is
assumed in this public consumer. Its stationary-only version has no
fourth-root-width restriction.

The two local-mean consumers bound the square of the sum of the
actual `atkinsonLocalMeanExcess`, with the same two physical terms.
Their source errors remain `C*(G*log(t)+t^(1/4+ε))` for
`G>=t^(1/4)`, or `C*G*log(t)` for
`G>=t^(1/4+κ)`, with ε>0 or κ>0. These parameters remain
independent of ν, and all constants precede the physical parameters.
Three global versions derive A=L=H directly from the height range.

The preceding near/far cancellation and closed three-term budget
remain proved and installed. The new scale calculation uses the
literal cutoff `N=ceil(72*H*(log(2H)/G)^2)`, paying rounding via
`N <= 74*H*log(2H)^2/G^2`. Existing physical cutoff geometry
derives N≤H from the original lower width. For nonempty W, a member
of W supplies both H^δ≤G and G≤sqrt(2H); the empty set is handled
explicitly. Thus no additional physical-scale premise is introduced.

The exact dyadic count and harmonic factor satisfy

```text
clog(2,N) <= (1/log(2)+1)*log(2H)
harmonic(ceil(sqrt(H*N)/G)) <= 2*log(2H).
```

The three cutoff powers yield diagonal/near scale R H/G and far
scale R² sqrt(G L). The intermediate upper bound is
`148000*(1/log(2)+1)^2*H^η*log(2H)^5` times those two terms.
Choosing η=ν/2 and proving eventual `log(2H)^5<=H^(ν/2)`
absorbs every remaining logarithmic factor. This uses the existing
epsilon-power divisor-energy bound, not a new sharp logarithmic
divisor asymptotic.

Five root-reachable modules are installed:
`AtkinsonPhysicalLogs`, `AtkinsonCutoffPowers`,
`AtkinsonPhysicalTerm`, `AtkinsonPhysicalBudget` and
`AtkinsonPhysicalPackets`. All 19 new public theorems have named
dependency audits; 22 new regressions cover their exact types and
the zero-cutoff, unit-index and zero-localization boundary cases.
Every prior module, audit and regression remains installed.

ZPH is the completed physical-cutoff/logarithmic-optimization substep.
ZGB remains OPEN for a constructed localization covering and
absorption/cardinality bound from an actual upstream value witness.
An arbitrary supplied [A,A+L] is not an optimized covering, and the
two-term bound alone is not a large-value count. ZAT, ZTM, all
unconditional Add-est clauses, EPZAE-21/37 and the full EPZAE-00–41
completion contract remain OPEN.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte and the
corrected independent ρ/k and ρ*/k witnesses, their independent
fifth coordinates and the actual Heath–Brown application. Never
restore the false s-scaling or a third s-preserving witness.
Maintain and update `run_tao_trudgian_yang_build.bat` and its
backing implementation as needed; its exact inventory includes
all five modules. Run it and `run_lake_build.bat` after relevant
changes. Keep the full goal active, not replaced by this checkpoint.

Semantic acceptance evidence:

- `atkinsonPhysicalCutoff_le_natural` consumes the actual source
  ceiling theorem, with rounding paid by the coefficient 74.
- `atkinsonPhysical_gap_budget_log_le` estimates the literal
  `atkinsonPowerGapBudget`; the epsilon factor is split exactly
  and the dyadic and harmonic losses are proved, not supplied.
- `exists_atkinsonPhysicalGapBudget_le_twoTerm` consumes the
  actual eventual cutoff geometry and logarithmic power bound.
  Its threshold precedes H,G,L,R.
- `atkinson_packet_width_scales` derives the needed width bounds
  from a member of the actual height set, including the original
  sub-square-root power-width restriction.
- The three `localizedPhysical` consumers in
  `AtkinsonPhysicalPackets` compose the numeric theorem with
  the preceding actual stationary/local-mean `localizedPowers`
  consumers. Their proof terms retain the real source objects.
  The three `globalPhysical` consumers derive their interval
  directly rather than introducing a new source assumption.

Next acceptance obligation: construct the physical localization
covering, derive an excess lower bound from the relevant upstream
value witness, absorb the quadratic-cardinality term at the chosen
length, and obtain the required cardinality estimate. Complete the
remaining source-entry/smaller-width or genuine lower-value reduction
and critical twelfth-moment consumer before claiming any unconditional
Add-est endpoint. Kernel integrity and source completeness remain
separate verdicts.

### Historical terminal verification: optimized physical packet bounds

Verified on 2026-09-21, dirty working tree at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`, Lean 4.30.0.
No commit or push was made. The preceding far-height evaluation is
historical and remains recorded above.

Target command, from this project folder:
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: LEAN VERIFICATION PASS`.
- Log: `logs/tao-trudgian-yang-build-20260921-003056-a1b5e292.log`.
- Final SHA256:
  `b4f18a44470ed8383864f3a390f840e48b5d67983c0bc8139fe904f7c293f41a`.
- 9,122 default-build jobs; semantic regression PASS.
- 279 Lean integrity-scan files; exact package coverage 268 Lean files.
- 28 required project files, 20 pinned source files and 12 frozen
  ANTEDB files verified; deterministic certificate regeneration PASS.
- Exhaustive audit: 2,800 discovered nonprivate target theorems and
  five imported contracts, 2,805 total declarations.
- All 19 new named theorem audits reported only permitted standard
  logical dependencies. No project axiom or admitted dependency.
- `PhysicalCutoffRegression` adds 22 passing tests: all 19 public
  theorem types, including every uniform-constant source consumer,
  plus unit-index, zero-localization and zero-cutoff boundary cases.
- No Lean error, warning, tactic suggestion or linter diagnostic.
  Incremental failures were repaired by correct cast/rational
  normalization, removing one ineffective tactic and qualifying
  `Filter.atTop` in a regression; no statement was weakened.

Foundation command, from `E:/Lean/Riemann Zeta`:
`cmd /c run_lake_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: PASS`.
- Log: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_003057.log`.
- Final log SHA256:
  `9b0234ca48d3ea8ff46acd04321e9b4ebd702775fc88192153880a4880f720b2`.
- JSON: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_003057.json`.
- JSON SHA256:
  `ea3d02518ca8135f33c7c8f7cd7d255fff55b5ba98ec2b5ffcc3cf6029163eed`.
- JSON status PASS and no failures. All six stages have exit code 0,
  warnings 0, tactic-info 0, informational-builds 0, linter-failures 0
  and `passed=true`.
- 8,857 build jobs; 14,290 discovered nonprivate foundation theorems
  and the 7,636-entry explicit public list audited.
- Classification: 301 root-graph modules, two explicit regressions,
  zero excluded and zero unclassified.
- Canonical verifier SHA256 remains
  `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Both process handles reached terminal completion. No Lean source,
root import, audit, regression or runner changed afterward; only
documentation evidence was appended.

Repository-wide searches found no placeholder or unsafe proof bypass
(exit 1, no matches). The postulate-pattern search (exit 0) was
reviewed: matches are explanatory comments and the two pre-existing
rational `constant : ℚ` fields, not mathematical postulates.
`git diff --check` passed. Git's LF/CRLF notices are not Lean
diagnostics. All eleven target documents were synchronized.

Counterexample SHA256 after both runners:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent powering witnesses, fifth coordinates and
actual Heath–Brown application remain unchanged.

Semantic verdict: ZPH is complete for the actual two-term source
estimate with physical cutoff and logarithmic losses absorbed.
The cutoff bound and both physical width bounds are derived in its
consumer chain; no assumed analytic packet estimate is introduced.
Constructed covering, value-witness absorption/cardinality, remaining
source entry or genuine lower-value reduction, critical twelfth moment
and unconditional Add-est remain OPEN. The full EPZAE-00–41 goal
remains active, not complete or blocked.

Proposed owner-run commit:
`Optimize physical Atkinson packet bounds and preserve powering repair`.

## Constructed covering and local-mean counts — preceding checkpoint

EPZAE-21 now proves a sixth-power superlevel counting estimate for
the actual critical-line local zeta integral. For every δ>0, ε>0
and ν>0 there are C,D>0 and H0≥40000, before H,G,Y,W, such that

```text
card {t in W : C*(G*log(t)+t^(1/4+ε)) + Y
                 <= integral_(t-G)^(t+G) |zeta(1/2+i*u)|^2 du}
 <= D*H^ν * (H/(G*Y^2) + H^2/Y^6).
```

The hypotheses are H≥H0, G>0, Y>0, G-separation of W, and for
each t in W, `H<=t<=2H`,
`t^δ<=G<=t^(1/2-δ)`, and `t^(1/4)<=G`.
The above-fourth-root version instead has error `C*G*log(t)`
and requires `t^(1/4+κ)<=G`, κ>0. All source restrictions
remain explicit. Both theorems count the literal integral's
superlevel set; no analytic packet estimate, prescribed covering,
absorption inequality or cardinality bound is a premise.

The preceding physical packet theorem remains installed:
the square of the sum of actual excesses is at most
`D0*H^a*(R*H/G+R^2*sqrt(G*L))`, with uniform constants
before the localization interval. Its cutoff/logarithmic optimization,
including the literal source ceiling and derived width bounds,
is unchanged.

The new deduction constructs the length and bins. Put
`A=D0*H^a` and `L=(Y^2/(4*A))^2/G`. Then L>0 and

```text
sqrt(G*L) = Y^2/(4*A)
2*A*sqrt(G*L) <= Y^2.
```

The bin of t is `floor((t-H)/L)`. Its actual fiber is contained
in `[H+k*L,H+(k+1)*L]`; the bins partition W for
`0<=k<floor(H/L)+1`. This includes the terminal height 2H,
even when H/L is integral. Separation and every original source
range are inherited by each fiber.

On a fiber whose actual excess is at least Y, the packet inequality
and the proved absorption give `R<=2*A*H/(G*Y^2)`.
Summing the exact fiber cardinalities and paying the final bin gives

```text
card(W) <= 2*A*H/(G*Y^2) + 32*A^3*H^2/Y^6.
```

Choosing the packet exponent a=ν/3 and absorbing constants yields
the displayed global estimate. The exact positive-threshold
equivalence between excess≥Y and integral≥error+Y is proved,
then used on the actual filtered superlevel set.

Four root-reachable modules are installed:
`AtkinsonCardinalityAbsorption`, `AtkinsonHeightCover`,
`AtkinsonGlobalCardinality` and `AtkinsonLocalMeanCounting`.
All 17 new public theorems have named audits. The 27 new regressions
cover every public theorem type, exact chosen-length arithmetic,
empty fibers, unit/terminal bins, zero threshold geometry and the
complete source-consumer signatures. Earlier work remains installed.

ZLC is complete for constructed covering, absorption and actual
local-mean superlevel counting. This is not yet a pointwise zeta
large-value count: the entry from point values to these local
integrals, a compatible physical width choice, an occupancy-preserving passage
from unit-separated points to G-separated local windows, and the
remaining value-range reduction are still required. ZGB, ZAT, the genuine
critical twelfth moment ZTM, all unconditional Add-est conclusions,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Preserve the original Lemma 62 counterexample byte-for-byte.
The corrected independent ρ/k and ρ*/k witnesses, independent
fifth coordinates and actual Heath–Brown application are unchanged.
Never restore false s-scaling or a third s-preserving witness.
Maintain and update `run_tao_trudgian_yang_build.bat` and its
backing implementation as needed; its exact inventory includes
all four new modules. Run it and `run_lake_build.bat` after
relevant changes. Keep the full goal active.

Semantic acceptance evidence:

- `atkinsonAbsorptionLength_radical` proves the exact physical
  square-root identity; `atkinsonAbsorptionLength_absorbs`
  discharges the needed numerical absorption. L is not a freely
  supplied scale left for a later argument.
- `atkinsonHeightFiber_interval` proves the translated location
  of each floor fiber, and `atkinsonHeightFiber_card_partition`
  supplies the exact finite partition including the last endpoint.
- `atkinson_card_le_of_local_packets` is an explicitly conditional
  reusable finite deduction. Its localized packet premise is narrower
  than the global count, and is not an unconditional source theorem.
- Both `exists_atkinsonLocalMeanExcess_card_le` versions discharge
  that premise with the actual `localizedPhysical` source theorem
  on every subset/fiber. They derive inherited separation, locations,
  widths and absorption rather than assuming these conclusions.
- Both `exists_atkinsonLocalMean_superlevel_card_le` versions
  use `atkinsonLocalMeanExcess_threshold_iff` to count the literal
  integral's filtered superlevel set. No pointwise-value or
  moment bound is hidden in the set's definition.

Next acceptance obligation: prove the pointwise critical-zeta
value-to-local-integral entry, choose a physical G compatible with
both the threshold and the retained fourth-root source range,
and handle the remaining lower-value range through a genuine source
or moment reduction. Then assemble the pointwise large-value count
and critical twelfth moment. The present integral superlevel bound
must not be relabeled as any of these still-open endpoints or as
an unconditional Add-est theorem.

### Historical terminal verification: constructed covering and local-mean counts

Verified on 2026-09-21, dirty working tree at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`, Lean 4.30.0.
No commit or push was made. Earlier checkpoint evaluations are
historical and remain recorded above.

Target command, from this project folder:
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: LEAN VERIFICATION PASS`.
- Log: `logs/tao-trudgian-yang-build-20260921-004731-117ec279.log`.
- Final SHA256:
  `a2e515d249bf693096e49a780d50ea66c3f118a18f502ac9acd7bd269779aa8e`.
- 9,126 default-build jobs; semantic regression PASS.
- 283 Lean integrity-scan files; exact package coverage 272 Lean files.
- 28 required project files, 20 pinned source files and 12 frozen
  ANTEDB files verified; deterministic certificate regeneration PASS.
- Exhaustive audit: 2,842 discovered nonprivate target theorems and
  five imported contracts, 2,847 total declarations. The discovery
  count includes generated theorem declarations and is not a count
  of source-level public statements.
- All 17 new named public theorem audits reported only permitted
  standard logical dependencies; no project axiom or admitted proof.
- `AtkinsonCountingRegression` adds 27 passing tests: all 17 public
  theorem types plus ten arithmetic, threshold, empty-fiber and
  endpoint-bin regressions. The terminal height 2H is explicitly
  tested in its last bin.
- No Lean error, warning, tactic suggestion or linter diagnostic.
  Incremental diagnostics were repaired by removing a genuinely
  unnecessary sign parameter, replacing redundant tactic sequencing,
  using the correctly oriented sum inequality and normalizing the
  numerical radical regression. The intended count was not weakened.

Foundation command, from `E:/Lean/Riemann Zeta`:
`cmd /c run_lake_build.bat --no-pause`.

- Terminal exit 0, `FINAL RESULT: PASS`.
- Log: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_004732.log`.
- Final log SHA256:
  `20a0ab923ed1d9a758770a55238ec5c5fb1391ec7228c0f7b8a1ba67f17864d0`.
- JSON: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_004732.json`.
- JSON SHA256:
  `811d3e4e57e49ebfe8c6ec729c226df468dbb787cd835144fc04fb7e0206825d`.
- JSON status PASS, no failures. All six stages have exit code 0,
  warnings 0, tactic-info 0, informational-builds 0, linter-failures 0
  and `passed=true`.
- 8,857 build jobs; 14,290 discovered nonprivate foundation theorems
  and the 7,636-entry explicit public list audited.
- Classification: 301 root-graph modules, two explicit regressions,
  zero excluded and zero unclassified.
- Canonical verifier SHA256 remains
  `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Both process handles reached terminal completion. No Lean source,
root import, audit, regression or runner was changed afterward.
Only documentation, research notes and verification evidence were
updated after the runs.

The three repository-wide proof-integrity searches were run explicitly.
Placeholder and unsafe-bypass scans returned exit 1 with no matches.
Postulate-pattern matches (exit 0) were reviewed as comments and
the two pre-existing rational `constant : ℚ` data fields, not
mathematical postulates. `git diff --check` passed; Git's LF/CRLF
notices are not Lean diagnostics. All eleven target docs agree.

Counterexample SHA256 after both runners:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent corrected powering witnesses, fifth coordinates and
actual Heath–Brown application remain unchanged.

Semantic verdict: ZLC is complete for the constructed covering,
derived absorption and actual local-integral superlevel count.
The generic finite packet deduction is conditional, but its packet
premise is discharged by the real source theorem in each final
consumer. No pointwise zeta-value or twelfth-moment theorem is claimed.
Point-value entry, occupancy-preserving separation/width choices,
remaining value ranges, the genuine twelfth moment and unconditional
Add-est remain OPEN. The complete EPZAE-00–41 goal remains active.

Proposed owner-run commit:
`Prove constructed Atkinson covering and local-mean superlevel counts`.

## Point-entry kernels and literal zeta overlap — preceding checkpoint

The preserved Lemma 62 counterexample and the proved corrected two-witness
powering/Heath–Brown chain are unchanged. EPZAE-21 now additionally proves
the Gamma-kernel and bounded-overlap components needed for point-value entry.

For every 0<δ≤1/4 and a,b independently chosen from {δ,-δ}, the
literal product

```text
P(a,b,u,w) = |Gamma(a+i*w)| |Gamma(b+i*(u-w))|
```

is integrable in w, and a single absolute C>0 gives
`integral P <= (C/δ)*exp(-|u|)`. The public consumer
`exists_pointMeanGammaProduct_integral_le` derives integrability and
uses both proved shifted-Gamma bounds and the numerical convolution.
Its height-linked companion
`exists_pointMeanGammaProduct_log_integral_le` substitutes
δ=1/log(t), derives 0<δ≤1/4 from t≥exp(4), and proves
`integral P <= C*log(t)*exp(-|u|)`. Both displacement signs and
zero ordinate are retained; no Gamma or convolution estimate is assumed.

For a unit-separated finite W, the actual exponential kernels satisfy
`sum_(t in W) exp(-|t-u|) <= 4`. The moving-window consumer
`sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment` proves

```text
sum_(t in W) integral_(t-L)^(t+L)
  exp(-|t-u|) |zeta(1/2+i*u)|^2 du
 <= 4 * integral_(center-G)^(center+G) |zeta(1/2+i*u)|^2 du.
```

It assumes G,L≥0, W⊂[center-G/2,center+G/2],
G/2+L≤G and unit separation. It derives every interval enlargement
and finite integral interchange. The cost is the absolute factor four,
not the cluster occupancy or the physical width G.

The previously proved local-integral superlevel count remains:
`card <= D*H^ν*(H/(G*Y^2)+H^2/Y^6)`, with all original physical
width restrictions, actual source errors, positive thresholds and
uniform constant dependencies retained. This new overlap theorem does
not yet connect pointwise zeta largeness to that count.

Eight root-reachable modules are installed: `PointMeanDigamma`,
`PointMeanGammaShift`, `PointMeanGammaDecay`, `PointMeanGammaKernel`,
`PointMeanGammaConvolution`, `PointMeanExponentialOverlap`,
`PointMeanIntegralOverlap` and `PointMeanGammaProduct`.
All 38 public theorems have named audits; 46 new regressions cover
their exact types and shell endpoints, empty sets, zero ordinates,
and the negative displacement. Seven modules adapt inspected node-74
proofs to the existing target/native imports and actual
`zetaMomentCriticalNorm`; the eighth supplies new literal Gamma consumers.
No adjacent package, dependency pin, source archive, or frozen foundation
has been changed.

ZGK is complete only for the literal Gamma convolution and its
height-linked logarithmic bound. ZEO is complete only for the actual
exponential local-integral overlap. The complete contour proof of
Heath–Brown Lemma 3 is NOT yet installed in this target. Its residue,
displaced zeta bounds, horizontal edges, truncated tail and compact range
remain to be assembled. Pointwise large-value counting also still needs
occupancy-aware clustering, compatible G selection and the lower-value
reduction. ZGB, ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and the full
EPZAE-00–41 completion contract remain OPEN.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte. Never restore
false s-scaling or a third s-preserving witness. The independent ρ/k and
ρ*/k witnesses and actual Heath–Brown application remain intact.
Maintain and update `run_tao_trudgian_yang_build.bat` and its backing
implementation as needed, including all eight modules in the exact
inventory. Run it and `run_lake_build.bat` after relevant changes.
Keep the full goal active.

Semantic acceptance and next analytic input:

- The coefficient-one real-part digamma estimate comes from the actual
  convergent series. Gronwall and Gamma reflection give exponential decay;
  recurrence gives both displaced lines without dropping δ+|v|.
- The stronger rate 4/3 leaves an exponential reserve. Its square is
  bounded by 1/(δ²+x²), whose integral is π/δ. The subsequent
  `pointMeanGammaProduct` consumer applies this to the actual Gamma
  functions, rather than claiming a numerical majorant alone is a source theorem.
- The overlap proof constructs integer distance shells, proves at most
  two points per shell using unit separation, and sums a geometric series.
  The final specialization consumes the literal continuous zeta-square integrand.
- The next source target is the actual weighted Lemma 3 inequality
  `|zeta(1/2+i*t)|² <= C*log(t)*(1+integral_(-log²t)^(log²t)
  exp(-|u|)*|zeta(1/2+i*(t+u))|² du)`, for every t≥10.
  The adjacent `HeathBrownLemmaThreeTail` and
  `HeathBrownEquation44Native` contain proved consumers, but they are
  NOT imports of this package and their conclusions are not yet target theorems.
  Narrow their Mellin/contour prerequisites onto the current native foundation,
  then assemble the residue and all analytic errors without a Lemma-3 hypothesis.
- After that entry is proved, use the installed overlap to keep cluster
  multiplicities when moving to G-separated windows. Merely thinning the
  unit-separated points loses a factor G and does not meet acceptance.

### Primary source and local reuse checked, 21 September 2026

D. R. Heath–Brown, *The twelfth power moment of the Riemann zeta-function*,
Quart. J. Math. 29 (1978), 443–462,
[DOI 10.1093/qmath/29.4.443](https://doi.org/10.1093/qmath/29.4.443).
The [primary-paper PDF hosted by NTNU](https://wiki.math.ntnu.no/_media/ma3001/2025h/analyticnumbertheory/heathbrowntwelfthmoment.pdf)
was opened: printed pp. 455–456, Lemma 3, equations (40)–(44).
Equation (41) retains the denominator δ+|v|; the subsequent double
convolution must lose only δ⁻¹. The new rate-4/3 majorant is a proved
strengthening used to preserve that loss. The local overlap adaptation
keeps the printed exponentially weighted zeta-square integrals.

The seven reused local files and their SHA256 hashes are recorded in the
Reproduction Manifest. Only imports, namespace/provenance and the bridge
to the target's actual critical-zeta norm were adapted; the literal Gamma
product consumers are new. Node 74 itself was not changed or added as a
dependency. Its full import closure is substantially larger than this
analytic step; the target retains the minimal eight-module branch.
The previously inspected Huxley–Ivić equation (2.1) remains a secondary
source formulation, not evidence that the target already proves Lemma 3.

Local adaptation provenance (SHA256, source bytes unchanged):

| Node-74 source | Target module | Source SHA256 |
|---|---|---|
| `PintzDigammaSharp` | `PointMeanDigamma` | `9fc5aaa7ad15686f9a2c525927845213af2ef902eb768eae174eb4b4792a83fe` |
| `PintzGammaHorizontalSharp` | `PointMeanGammaShift` | `0fc39e75ff81073d6f1788021f00c0a2bccef7ee1ea1949cfe5f5bb5fc40a2d4` |
| `Pintz2023GammaExponential` | `PointMeanGammaDecay` | `ab2421401ee3d833e2fb572720b9a45e132a5ff6c36fe7fc046b6ca0ba211790` |
| `HeathBrownGammaKernel` | `PointMeanGammaKernel` | `3236d95fe089a089b810a3cf66df82fa6aee71d0a931a705be55b1a02d557877` |
| `HeathBrownGammaConvolution` | `PointMeanGammaConvolution` | `b4377464ad7abc710e87f20f975e611664ebf99c1bebcebf10bc39c47bc68482` |
| `HeathBrownExponentialOverlap` | `PointMeanExponentialOverlap` | `e332392127765c395a7f748a5303512679718917aa4325bca46af2c150fd23cb` |
| `HeathBrownExponentialIntegralOverlap` | `PointMeanIntegralOverlap` | `9cca1d13b2cdfbcb5f4e1ab18a4a094e16a4e3e03e8effc5428e0febbc4faa60` |

The root imports all eight new production files, the named audit covers
all 38 public declarations, and the exact PowerShell inventory includes
every file. The 46 new tests retain full consumer signatures and concrete
boundary cases. No goal item is crossed out on audit counts alone.

### Historical terminal verification: point-entry kernels and literal overlap

Evaluated the dirty working tree based on commit
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`.
No commit, push, source-pin change, or adjacent-project modification was made.

Commands and terminal results:

```powershell
# Target project directory:
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# Foundation directory E:\Lean\Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes were polled to terminal exit code 0; neither result was
inferred from an unfinished stage or a prior log. Target final status:
`LEAN VERIFICATION PASS`. Foundation final status: `PASS`.

Target transcript:
`logs/tao-trudgian-yang-build-20260921-011317-a71c4c13.log`

SHA256:
`556d87842310dabfe1986f7cad056429e5239fad17c08b72d57a442337ae334c`.

Target coverage: 9,134 default build jobs; 28 required files; all 20
pinned source hashes; all 12 frozen ANTEDB source files; 291 Lean
files in the integrity scope; exact inventory of 280 package files;
deterministic certificate regeneration PASS. Semantic regression PASS,
including 38 new complete theorem-signature tests and eight concrete
boundary/empty/zero/negative-line tests. Exhaustive audit: 2,885
discovered target theorems plus five imported contracts, 2,890 total.
All 38 new public declarations also have explicit named axiom output,
with only the permitted logical axioms. No Lean diagnostic remains.

Foundation transcript:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_011318.log`

SHA256:
`2b0631226d25e98871d70a6fbde781705d9d5473b72800e9bdfcb2f9f8ade897`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_011318.json`

SHA256:
`c8b8761e16af01b696b361ead79fa20449a438f9ce278b6c29a0851170255393`.

The JSON reports `status=PASS`, `failures=[]`; all six recorded
stages have exitCode=0, warnings=0, tacticInfo=0,
informationalBuilds=0, linterFailures=0 and passed=true.
Foundation coverage remains 8,857 jobs, 301 root-graph modules plus
two explicit regressions, zero excluded/unclassified modules,
7,636 explicit public declarations and 14,290 discovered theorems.
Verifier SHA256 remains
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

The three repository-wide Lean scans were rerun. Placeholder and
unsafe scans returned exit 1 with no matches. The postulate scan
matched only comments and the two existing rational structure fields;
there is no prohibited declaration. `git diff --check` returned 0.
Git's LF/CRLF notices are not Lean warnings; no Lean warning was
suppressed or reclassified.

The original `EnergyPoweringObstruction.lean` was rehashed after both
runners, still exactly
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Corrected independent-coordinate powering and the actual Heath–Brown
application were not edited. All eleven target documents are synchronized.
This is a verified kernel/overlap checkpoint, not completion of Lemma 3,
the genuine critical twelfth moment, Add-est or the full goal.

## Heath–Brown point-to-local-mean entry — historical checkpoint

The original Lemma 62 counterexample is preserved byte-for-byte. The corrected
independent cardinality and energy witnesses, and their proved Heath–Brown
application, are unchanged. This checkpoint closes an analytic input to the
remaining zeta/Add-est branch; it does not change the frozen public outputs.

`heathBrownLemmaThree_native` now proves the complete source-shaped estimate:
one absolute C>0 works for every t≥10,

```text
|zeta(1/2+i*t)|^2
 <= C*log(t)*(1 + integral_(-log(t)^2)^(log(t)^2)
      exp(-|u|)*|zeta(1/2+i*(t+u))|^2 du).
```

The proposition and moment definitions unfold to this literal integral.
The proof derives the smoothed divisor Mellin identity, both pole residues,
the infinite shifts, both displaced-line estimates, the finite rectangle's
four edge bounds, the full-to-truncated tail estimate and the compact range.
The strong Gamma reserve makes the nested integral lose only δ⁻¹;
δ=1/log(t) is linked to the source height. None of these estimates is an
analytic hypothesis of the final theorem.

`heathBrown_equation44_native` consumes that theorem and the actual
factor-four exponential-overlap theorem. For R=card(W) it proves

```text
V^2*R <= C*log(T)*(R + 4*integral_(center-G)^(center+G)
                                  |zeta(1/2+i*u)|^2 du).
```

Here T≥10, V>0, G,L≥0; W is unit-separated and contained in
[center-G/2,center+G/2]⊂[10,T]; every t∈W has log(t)^2≤L;
G/2+L≤G; and every t∈W satisfies V≤|zeta(1/2+i*t)|.
All parameters follow the absolute constant. The final consumer has no
Lemma-3 hypothesis and does not discard cluster occupancy.

Nineteen additional production modules are root-reachable and included in
the exact inventory behind `run_tao_trudgian_yang_build.bat`.
There are 129 new public theorem audits and 136 new regressions, including
the unfolded literal source inequality and the endpoints t=10 and t=exp(4).
The adjacent node-74 proof bodies were inspected and adapted to existing
target/native imports; unrelated import chains were not added. No package
pin, source archive, counterexample or adjacent project was changed.

ZL3 is complete for the full source Lemma 3; ZQ44 is complete for its
literal finite peak-to-local-integral consumer. ZGB still needs constructed
occupancy-aware clusters, compatible physical width selection, absorption
of the actual local-source error, and the remaining value ranges.
The installed local-integral superlevel count still has its original
fourth-root width restrictions. ZAT, ZTM, unconditional Add-est,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Keep the complete goal active. Preserve `EnergyPoweringObstruction.lean`
and the independent fifth coordinates; never reintroduce false s-scaling
or a third s-preserving witness. Maintain the principal
`run_tao_trudgian_yang_build.bat`, its backing implementation, root imports,
exact inventory, audits and regressions as the proof grows. After relevant
changes, run both it and the foundation's `run_lake_build.bat`.

### Exact dependency and next-obligation audit

- `heathBrown_smoothed_divisor_eq_right_mellin` proves actual summation/integration
  interchange from absolute convergence and exponential Mellin inversion.
- `heathBrown_zetaSquare_eq_smoothed_sub_residue_sub_leftVertical` consumes
  the two proved pole shifts. The moving double pole is 1-s; the Gamma pole
  is 0. The residue constants and retained line are subsequently bounded.
- `exists_heathBrown_offCritical_plus_strong_le` and its reflected minus
  companion use the actual zeta square and convergent critical-line moment.
  Functional reflection uses the pinned GammaR equation and conjugation.
- `integral_strongKernel_mul_strongMoment_le` proves product-space
  integrability, translation and Fubini with the π/δ bound. The finite
  source rectangle then yields the full weighted moment with only log(t).
- `exists_heathBrownFullCriticalMoment_le_truncated` pays the complete tail
  at log(t)^2. `heathBrownLemmaThree_native` absorbs its constant and
  derives the remaining compact t≥10 range from continuity.
- `heathBrown_equation44_of_lemmaThree` is intentionally a conditional
  finite deduction. `heathBrown_equation44_native` explicitly discharges
  that premise using the new full theorem and retains the literal integral.
- Next construct G-separated centers with the original point multiplicities.
  Choose G in the existing Atkinson source range, derive a local-integral
  excess threshold from each cluster's equation-(44) bound, and apply
  `exists_atkinsonLocalMean_superlevel_card_le` (or its
  `above_fourthRoot` form) with every source error and width condition paid.
  Preserve and sum occupancy classes; thinning points without their
  multiplicities is not an acceptable bridge.
- The lower-value reduction and any upper-value exclusion must use proved
  genuine zeta estimates. Assemble the actual dyadic critical twelfth moment
  before consuming the existing moment-to-LV/energy transfers. Do not replace
  it with a new moment hypothesis or mark Add-est complete from the point-entry
  theorem alone. All other open EPZAE tasks remain part of the full goal.

### Primary source and adaptation provenance

The source is D. R. Heath–Brown, *The twelfth power moment of the Riemann
zeta-function*, Quart. J. Math. 29 (1978), 443–462,
[DOI](https://doi.org/10.1093/qmath/29.4.443);
the [primary-paper PDF](https://wiki.math.ntnu.no/_media/ma3001/2025h/analyticnumbertheory/heathbrowntwelfthmoment.pdf)
was rechecked at printed pp. 455–457 (Lemma 3 and equations (40)–(44)).
The local pinned PDF is unchanged. Equation (44) is followed here through
the bounded-overlap simplification, with its absolute constant exposed.

The new target branch consists of `PointMeanMellinExp`,
`PointMeanDivisorMellin`, `PointMeanDoublePole`, `PointMeanMovingPole`,
`PointMeanGammaPole`, `PointMeanContourBasic`,
`PointMeanMellinHorizontal`, `PointMeanMellinVertical`,
`PointMeanMellinShift`, `PointMeanMellinBounds`,
`PointMeanOffCritical`, `PointMeanReflection`,
`PointMeanOffCriticalStrong`, `PointMeanLemmaThreeStatement`,
`PointMeanLemmaThreeContour`, `PointMeanLemmaThreeDouble`,
`PointMeanLemmaThreeEdges`, `PointMeanLemmaThreeTail`, and
`PointMeanEquation44`.

The local node-74 source hashes are recorded below/in the Reproduction
Manifest. Namespace/import spelling, actual target zeta-norm references,
and provenance comments were adapted. Only needed elementary lemmas were
extracted from the broader Pintz/Ford and finite-loss modules; no theorem
from those larger branches is assumed. The final equation-(44) consumer
uses the literal integral instead of an adjacent local-moment alias.
The node-74 package is not an added dependency and is unchanged.

Local source SHA256 ledger (source files unchanged):

| Node-74 source | Target use | Source SHA256 |
|---|---|---|
| `Pintz2023MellinExp` | `PointMeanMellinExp` | `038f5b0f28bf64faab7d039c42d8baca4f5e4f893a4adffbe70561f03a0ed85d` |
| `HeathBrownSmoothedDivisorMellin` | `PointMeanDivisorMellin` | `7bc3f32b81d5ac1e1408f437b95c2e797bb37fe92b6520d1fb11d832e51b321d` |
| `HeathBrownDoublePoleRectangle` | `PointMeanDoublePole` | `be8037772280da22145a8169dd0cbf5aaf9ec0dd9dbc3e8f2dcf7e69591bb77a` |
| `HeathBrownMovingPole` | `PointMeanMovingPole` | `b1dfec90aaa8a5d9da98f0b3bb33470dfa6612c5fe19be4ec4adf8f576d45f88` |
| `HeathBrownGammaPole` | `PointMeanGammaPole` | `0cb723dea0e3c8687f24d8fcc79095d14795df32051e293b527f684a4ee2bf46` |
| `HeathBrownMellinHorizontal` | `PointMeanMellinHorizontal` | `f25bc447cf84918d9333c665e517fa5d1c8e195852f39a5ba5ba66fc11b93f50` |
| `HeathBrownMellinVertical` | `PointMeanMellinVertical` | `cabc9ee3dd91ce5a7c024c33379a3b18b24c5481c87f0323068c87441cfba3b8` |
| `HeathBrownMellinShift` | `PointMeanMellinShift` | `c8dd0fdc18b9ee08db7f04f717c111f6c39058e9fd28e98c176d4d2ca3b0dd9f` |
| `HeathBrownMellinBounds` | `PointMeanMellinBounds` | `dac7c7175b87d2bf1c27118a9a5e33c303048471c88e5cd035e3f605a595e2cd` |
| `HeathBrownOffCritical` | `PointMeanOffCritical` | `6cf8626e1b6bb3b38569cf81263160bf6ebf3971c419a6344b804e3356eb9f04` |
| `HeathBrownFunctionalReflection` | `PointMeanReflection` | `3d71202f4228a81be01d6860d75923da693eebd5af8406b5821c7adb49319f64` |
| `HeathBrownOffCriticalStrong` | `PointMeanOffCriticalStrong` | `c44116f0d2dfed8fbe0aa549b0f1c5c2b1adc10a7f956b9d2f7fa7b19601a01f` |
| `HeathBrownLemmaThreeStatement` | `PointMeanLemmaThreeStatement` | `ddd69314915d75eb4d542ea82a0e8a88817e2da3649552b157cfa828941c6582` |
| `HeathBrownLemmaThreeContour` | `PointMeanLemmaThreeContour` | `f286661c62cd94f4dfeeb524f4cb17368ef1af12765ebd1c1fec46939a547aca` |
| `HeathBrownLemmaThreeDouble` | `PointMeanLemmaThreeDouble` | `f70c54135cfbdc8e0f6ce6ec4fd01f799d90deb3ba3d9b289f0182f87647ef9e` |
| `HeathBrownLemmaThreeEdges` | `PointMeanLemmaThreeEdges` | `f6c88c628110732e7c44afea694043445e6ee8f93d9980053cda178da0d338ed` |
| `HeathBrownLemmaThreeTail` | `PointMeanLemmaThreeTail` | `ab922be81cbcfa6a009a7dc2b4c93d92fffa0992a9289a1d2ba60798e0b7e2ca` |
| `HeathBrownEquation44` | `PointMeanEquation44` | `6b27671bb029b3a42c027656e9ca88ed49a4f7ab48bf1800e7e8e3453774da36` |
| `Pintz2023MellinHorizontal` | `PointMeanContourBasic (selected decay)` | `d56ec96c6411dd2347adc5a16234fdb791eaab88ba81a5e6937ebd30c95eec57` |
| `FordZetaBasic` | `PointMeanContourBasic (two selected norm lemmas)` | `fd6f4976c85d1466b648f0aa2363f67397f0cb9d08f9b2e04993a8af6381b6eb` |
| `Pintz2023MellinEdges` | `PointMeanContourBasic (selected orientation)` | `1e8631952d39963fb27d6f00356cc18f2b372fd3ed13e2454f049eabb2040a46` |
| `PintzGammaVerticalRatio` | `PointMeanReflection (selected GammaR identity)` | `be2804a57d86faf882abe18e3d0bcf376f689526610e3bab0545abe90de92c20` |
| `PintzZetaAFEKernelBound` | `PointMeanReflection (selected conjugation identity)` | `4dfc68c96a2ed894b59ee80388f25acba9c80eb31bf465ad9765c88b7c2d5e48` |
| `ZeroSumSup` | `PointMeanLemmaThreeEdges (selected logarithmic comparison)` | `8bb2df4beeb90704ebf8fb3eb02e7e093cb581409840bcaf5524337101644440` |
| `HeathBrownFiniteLossAbsorption` | `PointMeanLemmaThreeEdges (selected power comparison)` | `ec149f476f793e6b7ae4f5c97a8b71f4190d1aa4d6724506843608a94e58cdf8` |
| `HeathBrownEquation44Native` | `PointMeanEquation44 (final composition)` | `3f3de2fdc68479f6238315decb4938dca36d6c2d458fb219458d01fbb4163afa` |

### Current terminal verification: full point-to-local-mean entry

The evaluated dirty checkout is based on
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`.
No commit, push, frozen source-pin change or adjacent-project edit was made.

Commands:

```powershell
# Target project directory:
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# Foundation directory E:\Lean\Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both final processes reached exit code 0. Target status is
`LEAN VERIFICATION PASS`; foundation status is `PASS`.
No final failed stage or Lean diagnostic remains.

Target transcript:
`logs/tao-trudgian-yang-build-20260921-014038-81d7c7e7.log`

SHA256:
`91d97f6642fd6b68509db3b9f3931b173efe578d819be0e4d0edac630715585d`.

Coverage: 9,154 default build jobs; 28 required files; 20 pinned source
hashes; 12 frozen ANTEDB files; 310 Lean files in the integrity scan;
exact inventory of 299 package files; deterministic certificate
regeneration PASS. The root includes all 19 new production modules.
All 136 new semantic regressions pass. The exhaustive audit checks
3,099 discovered target theorems and five imported contracts, 3,104 total.
The 129 new public theorems also each appear in named axiom output with
only the permitted logical axioms. The literal source test unfolds
`HeathBrownLemmaThree`, its moment and `zetaMomentCriticalNorm`.

Foundation transcript:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_014317.log`

SHA256:
`4df06c1a54795f785d86a9d96271a439e3ba36c75a4b5e16dc1fb27d8bb4379d`.

Foundation manifest:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_014317.json`

SHA256:
`4f646f5f5c52b12869e891deffa357eb17ed24932cd06759c7c7095cbaa00d2f`.

Its recorded status is PASS and failures is empty. All six stages have
exitCode=0, warnings=0, tacticInfo=0, informationalBuilds=0,
linterFailures=0 and passed=true. Coverage remains 8,857 build jobs,
301 root-graph modules and two explicit regressions, no excluded or
unclassified modules, 7,636 explicit public declarations and 14,290
discovered nonprivate theorems. The foundation verifier is unchanged:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Intermediate failures are not hidden: the initial target transcript
`logs/tao-trudgian-yang-build-20260921-014001-03aeec79.log` and
foundation transcript
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_014002.log`
failed their integrity scan on a prose comment beginning with
“constant inherited”. The comment was reworded and both scripts rerun;
no scan was weakened, no module excluded and no warning suppressed.
A preceding focused audit syntax error in a comment marker was also fixed.

The three repository-wide Lean searches were rerun after the final source
change. Placeholder and unsafe-bypass searches have no matches.
The raw postulate search contains only existing prose comments and two
rational structure fields, not postulated declarations. The principal
integrity scans pass. `git diff --check` returns 0; Git's line-ending
notices are not Lean diagnostics.

After both final runners, the SHA256 of
`EnergyPoweringObstruction.lean` remains exactly
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent-coordinate powering and actual Heath–Brown
energy relation were not edited. All eleven target documents distinguish
the completed source Lemma 3 and finite point-entry consumer from the
still-open occupancy/width/value-range assembly, twelfth moment, Add-est
and complete EPZAE-00–41 goal.

## Occupancy-preserving peak count and derived growth — historical checkpoint

The printed Lemma 62 counterexample is still byte-preserved. The proved
corrected two-witness powering, independent fifth coordinates and actual
Heath–Brown energy application are unchanged.

Three additional EPZAE-21 consumers are now proved:

- `exists_pointValue_card_le_with_width` counts the original unit-separated
  zeta peaks, retaining every cluster occupancy. Half-G floor bins keep
  occupied centers in [H,2H], including the terminal endpoint. Both parity
  classes are G-separated. The actual equation-(44) entry and Atkinson
  excess count bound each occupancy superlevel; exact layer-cake summation
  and the inverse-square sum recover all points with no factor G loss.
- `exists_pointValue_card_le_source_range` constructs
  G=V²/(K log(3H)²), absorbs the actual source error and derives all window
  and width conditions. For δ,κ,ν>0 with δ≤1/4, there are K,D>0 and H₀≥40000,
  chosen before H,V,W, such that for H≥H₀ and V>0,
  `K log(3H)² (2H)^(1/4+κ) ≤ V² ≤ K log(3H)² H^(1/2−δ)`,
  every unit-separated W⊂[H,2H] with |ζ(1/2+it)|≥V satisfies
  `card(W) ≤ D H^ν (H log(3H)^4/V^6 + H² log(3H)^6/V^12)`.
  The fourth-root margin is retained, not removed.
- `exists_zetaMomentCriticalNorm_lt_sixth_power` proves that for every ε>0
  there is H₀≥40000 such that H≥H₀ and H≤t≤2H imply
  |ζ(1/2+it)|<H^(1/6+ε). A singleton peak at H^(1/6+η),
  η=min(ε,1/48), satisfies the proved source range but its cardinality bound
  is eventually less than one. This derives the actual zeta growth estimate;
  it does not assume one or substitute a Dirichlet-block estimate.

The six modules `FiniteOccupancy`, `PointClusters`, `PointClusterEntry`,
`PointClusterCounting`, `PointValueWidth` and `PointValueGrowth` are covered
by the root and exact production inventory. Their 29 public theorems have
named audits, and 37 added regressions check every public type plus actual
endpoints, occupancy, parity and the unfolded zeta-growth conclusion.

Architecture nodes ZOC, ZVW and ZPG record these exact consumers as DONE.
ZGB remains OPEN for the remaining value-range reductions and their
moment-ready aggregation. ZAT's smaller-width/source-form bridge, the genuine
dyadic twelfth moment ZTM, all unconditional Add-est clauses, EPZAE-19/21/37
and the full EPZAE-00–41 goal remain OPEN. This critical-line growth result
does not complete the distinct exponent-pair-to-mu contract EPZAE-15.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation as
needed: root imports, exact inventory, named/exhaustive audits and regressions
must grow together. Run both principal scripts after relevant changes.
Preserve the counterexample and do not restore false s-scaling or a third
s-preserving witness. No dependency pin, source archive or adjacent proof
was changed in this checkpoint.

### Consumer audit and remaining analytic work

The constructed centers are cₙ=H+nG/2. An occupied fiber inherits unit
separation and the original peak threshold. Its points lie in
[cₙ−G/2,cₙ+G/2]; equation (44) is applied with T=3H and
L=log(3H)². The global assumptions G≤H and 2log(3H)²≤G derive
the entire interval and logarithmic-window entry.

For A=V²/(16P log(3H)), the proved peak-mass absorption gives
I(cₙ,G)≥2RₙA. If Rₙ≥m≥1 and the true local error is at most A,
then I(cₙ,G)≥error+mA. Each parity image is injective and G-separated.
The actual source count gives m⁻² and m⁻⁶ superlevel decay, and
`sum_nat_occupancy_eq_sum_superlevel` recovers ΣRₙ=card(W).
Both colors and Σm≥1 m⁻²≤2 are paid in the final constant; neither
maximal occupancy nor a thinning loss appears.

The selected K=16PC+1 makes the actual C G log(cₙ) error at most A.
The amplitude interval derives t^δ≤G≤t^(1/2−δ) and
t^(1/4+κ)≤G for every t∈[H,2H]. No local-mean source estimate,
point-entry theorem, cluster existence or window condition remains as
an analytic hypothesis of the selected-width consumer.

At V=H^(1/6+η), the count simplifies exactly to
D log(3H)^4/H^(5η) + D log(3H)^6/H^(11η).
Positive exponent gaps absorb the logarithms. The singleton contradiction
proves growth directly from the actual local-zeta chain and works at both
closed height endpoints.

Next use this derived growth to control the upper value range and
the first term of the peak count; derive the remaining low-value estimate
from genuine zeta moment inputs. Construct the finite-to-continuous
aggregation with all interval endpoints and separation colors accounted
for, then prove the actual dyadic critical twelfth moment. Only that theorem
can discharge the moment premise of `zetaTwelfth_largeValueBound_of_dyadic`
and `energyClauseOne_of_dyadic_moment`. Their existing conditional proofs
are not evidence that the moment has already been proved.

Continue the full frozen public contract, not a replacement goal consisting
only of these supporting results. All other open EPZAE tasks remain required.

### Source and library reuse for this checkpoint

This is new local composition of the already proved Heath–Brown
equation-(44) entry and `AtkinsonLocalMeanCounting`, not an imported
unproved twelfth-moment claim. The exact finite partition uses the existing
physical floor fibers and Mathlib's `Finset.card_eq_sum_card_image`.
Parity uses `Finset.card_filter_add_card_filter_not`; the convergent
occupancy bound uses `sum_Ioo_inv_sq_le` from
`Mathlib/Analysis/PSeries.lean` at the unchanged pin.
The logarithmic absorption consumes `eventually_const_log_pow_le_rpow`.

The native `GuthMaynard/WeylZeta.lean` was inspected: its critical-line
Weyl block estimates are finite Dirichlet-block bounds, not themselves a
full riemannZeta pointwise bound. No such identification was made.
Instead `PointValueGrowth` supplies the actual zeta theorem via the proved
singleton contradiction. No new external source snapshot or package is
required; the previously frozen source literature remains unchanged.

### Installed proof-source hashes

These six files are new local proofs; all source/dependency pins are unchanged.
SHA256 values below identify the files used by this checkpoint's evaluations.

| Module | Public theorem audits | SHA256 |
| --- | ---: | --- |
| `FiniteOccupancy.lean` | 3 | `341a64b7f3496769184984010fc64275a377a2ebac4efd713a24f1292cdbcecb` |
| `PointClusters.lean` | 11 | `14260addc923d44bc047bc1213e78dd50b033ff9e568dbad1ce840b82cb93367` |
| `PointClusterEntry.lean` | 3 | `e800e4d49721ecd868dbc96e82f9a399df30a1d1988c0a67feeaec116e2de7fb` |
| `PointClusterCounting.lean` | 3 | `15f1e9d9b6d15fb27b2360b510a09b0ea6a2dfbc97798df9a5ad5b10ca617ca7` |
| `PointValueWidth.lean` | 4 | `23f39339835b96614d5fac7f5efd1126d80a576a7ee5afbf03adbd1119af6e50` |
| `PointValueGrowth.lean` | 5 | `418ca89b599e6c3c440cffb1d6efb2a3513e7dd10b6f7b3d37967ffa48d42c92` |

Verification (2026-09-21): both principal runners reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 305 package files, 316 Lean
files in its integrity scan, 3,187 audited declarations (3,182 discovered
target theorems plus five imported contracts), all 29 new named audits and
all 37 added regressions passed. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final evaluations
have zero Lean errors, warnings, tactic suggestions or linter failures.
The counterexample SHA256 is unchanged. Exact logs, hashes and repaired
focused-build diagnostics are recorded in the current Reproduction Manifest.
This verifies the occupancy/width consumers and actual critical-line growth,
not the genuine twelfth moment, unconditional Add-est or the full goal.

### Terminal occupancy/growth reproduction evidence

Commands were run from their respective roots and polled to terminal exit 0:

```powershell
# Tao--Trudgian--Yang folder
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# E:/Lean/Riemann Zeta
cmd /c run_lake_build.bat --no-pause
```

The checkout is the existing dirty `main` tree at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0`; no commit or push was made.
Lean remains 4.30.0 and all dependency/source pins are unchanged.

Target transcript:
`E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/63 Tao-Trudgian-Yang, 2025/logs/tao-trudgian-yang-build-20260921-022304-7efe6399.log`

SHA256:
`e9bb9b24639762bb7d1599900025cb519b3baf835261409c22f0722b13d50271`.

The target confirms 28 required files, 20 pinned source files, 12 frozen
ANTEDB files, byte-stable deterministic certificate regeneration, all
305 package Lean files, a 316-file integrity scan and 9,160 build jobs.
The semantic regressions pass. Its exhaustive dependency audit covers
3,182 discovered target theorems plus five imported contracts, 3,187 total.
Each of the 29 new public theorem names appears in explicit axiom output
with only `propext`, `Classical.choice` and `Quot.sound`.
All 37 new exact-type/boundary regressions pass, including the unfolded
actual riemannZeta conclusion. The complete log contains no Lean diagnostic.

Foundation transcript:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_022305.log`

SHA256:
`12f8ced87262eafeee1cb404f42eabfc62cc4560f692f37ff23d51a26992d029`.

Foundation manifest:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_022305.json`

SHA256:
`2c2f65ed14aa503273eb0c547af212588cf55c821f92f73e63ba2114c3e9131c`.

The JSON status is PASS, with an empty failures array. All six stages have
exitCode=0, warnings=0, tacticInfo=0, informationalBuilds=0,
linterFailures=0 and passed=true. Coverage remains 8,857 build jobs,
301 root-graph modules, two explicit regressions, no excluded or
unclassified modules, 7,636 explicit public declarations and 14,290
discovered nonprivate theorems. The unchanged foundation verifier SHA256 is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Intermediate focused elaboration failures were repaired, including natural/
real exponent casts, finite-filter evaluations and explicit finite-sum
regression notation. A redundant `ring` produced an unused/unreachable
tactic warning; the redundant tactic was removed. The final focused
`PointValueGrowth` and `SemanticRegression` builds and both principal
evaluations have zero Lean warnings. No linter, scanner or module-coverage
gate was weakened, and no failing module was excluded.

Repository-wide placeholder and unsafe-bypass searches return no matches.
The raw postulate search has only existing prose comments and two rational
structure fields, not mathematical postulates; both principal integrity
scans pass. `git diff --check` returns 0. Git's LF/CRLF notices are
line-ending notices, not Lean diagnostics.

After both terminal evaluations, `EnergyPoweringObstruction.lean` retains
SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent witnesses and actual Heath–Brown energy theorem
were not edited. All eleven target documents agree on ZOC/ZVW/ZPG and keep
the remaining value-range aggregation, actual twelfth moment, unconditional
Add-est and full EPZAE-00–41 goal open.

## High-value twelfth moment and fourth-moment reduction — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. Corrected
cardinality/energy powering, the independent ρ/k and ρ*/k witnesses with
independent fifth exponents, and the actual Heath–Brown energy application
remain unchanged.

The following actual-zeta consumers are now proved. Write
S(H,V)={t∈[H,2H] : |ζ(1/2+it)|≥V}. For every ε>0 and sufficiently large H,
uniformly for V≥H^(1/8+ε):

- `exists_pointValue_twelfth_weighted_card_le` gives
  card(W) V^12≤H^(2+ε) for every unit-separated W⊂S(H,V).
  There is no upper-amplitude hypothesis: the proved actual growth estimate
  controls that range, and the source-width and logarithmic margins are paid.
- `exists_volume_pointValueSuperlevel_le` gives
  volume(S(H,V))≤2H^(2+ε)/V^12. A maximal finite separated family is
  constructed from the proved cardinality bound; its closed unit balls
  cover the entire superlevel set, with the factor two accounted for.
- `exists_zeta_twelfth_high_integral_le` proves
  integral over S(H,H^(1/8+ε)) of |ζ(1/2+it)|^12≤H^(2+ε).
  The actual measure bound, actual height-cube bound for |ζ|^12 and exact
  logarithmic layer-cake integral are composed without analytic hypotheses.

`zeta_twelfth_integral_le_high_add_fourth` proves the exact low/high
reduction: the full twelfth moment on [H,2H] is at most the high-set
integral plus V^8 times the unweighted fourth moment on [H,2H].
`zeta_twelfth_dyadic_of_fourth` performs the full deduction but is
explicitly CONDITIONAL on the genuine upstream estimate

```text
for every η>0 there exist C≥0 and H₀, chosen before H, such that
H≥H₀ and H>0 imply integral_H^(2H) |ζ(1/2+it)|^4 dt ≤ C H^(1+η).
```

That unweighted fourth-moment instance is still OPEN. The foundation's
`twistedZetaFourthMoment_native` instead bounds the fourth power of a
short Möbius polynomial multiplied by ζ; its factor cannot simply be
removed. No mollified result is claimed to prove the unweighted estimate.

The six modules `PointValueRanges`, `PointValueMeasure`,
`TruncatedLayerCake`, `PointValueTailIntegral`,
`PointValueHighMoment` and `PointValueLowMoment` are in the root and exact
production inventory. All 24 public theorems have named audits; 30 new
regressions cover their exact signatures, boundary cases and the literal
high-value zeta integral. ZHR/ZHM and the reduction ZLF are DONE; ZGB now
identifies the missing genuine fourth-moment source theorem. ZTM, ZAT,
EPZAE-19/21/37, unconditional Add-est and the full EPZAE-00–41 goal remain OPEN.
No other frozen public output or acceptance test is weakened.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed, including root imports, exact module coverage, named/exhaustive
audits and regressions. Run both principal scripts after relevant changes.
Preserve the counterexample, never restore false s-scaling or a third
s-preserving witness, and keep the full goal active. No source pin,
archive or adjacent/native proof was changed in this checkpoint.

### Proof and source audit for this checkpoint

The counting consumer chooses η=min(ε/16,1/1000), retaining the proved
fourth-root source margin. For nonempty W the actual growth bound gives
V≤H^(1/6+η); the two weighted count terms become
D log(3H)^4 H^(2+7η) and D log(3H)^6 H^(2+η).
All logarithms are absorbed using positive exponent gaps; W=∅ is handled
explicitly. The cardinality-to-measure proof maximizes finite cardinalities
in a bounded finite set of naturals and extends an allegedly non-covering
family by one point. It assumes no compactness or covering theorem that
already contains the desired measure conclusion.

`TruncatedLayerCake` uses the pinned Mathlib
`Integrable.integral_eq_integral_Ioc_meas_le` and proves
integral_0^M C/max(A,t) dt=C(1+log(M/A)) for 0<A≤M.
The actual restricted measure tail at s is at most C/max(V^12,s);
the positive twelfth root converts the upper branch to a zeta superlevel.
The terminal high-set theorem takes η=min(ε/2,1/100), uses the proved
|ζ|^12≤H^3, and absorbs the remaining logarithm. Every actual point of
the measurable superlevel set is included; there is no thinning or
unproved finite-to-continuous aggregation.

The low-set theorem needs no assumption V>0: if that set is nonempty,
its actual nonnegative norm is less than V. The proof derives
|ζ|^12≤V^8|ζ|^4 there and integrates over the actual interval complement.
The full conditional theorem exposes every quantifier of the remaining
fourth-moment estimate.

No external source revision was added. The Mathlib layer-cake, interval
integration and real-power APIs and the local actual-zeta source chain
were inspected directly at the existing pins. The foundation's
`twistedZetaMomentIntegrand` is
|shortMobiusPolynomial · ζ|^4, not |ζ|^4; the distinction remains explicit
in the source obligation and audit.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 311 package files, 322 Lean
files in its integrity scan, 3,232 audited declarations (3,227 discovered
target theorems plus five imported contracts). All 24 new named audits
and all 30 added regressions pass. The foundation reports `PASS`: all six
stages passed, with 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample SHA256 is unchanged; source and runner hashes
were rechecked after both gates. Exact logs, hashes and repaired focused
diagnostics are in the current Reproduction Manifest. These gates verify
the high-value bound and explicitly conditional fourth-moment deduction,
not the missing fourth-moment instance, unconditional Add-est or full goal.

### Terminal high-value moment reproduction record — 2026-09-21

These are fresh terminal results for the six high-value/low-value modules,
their updated root, audit, regressions and runner inventory. The
occupancy/growth records above remain historical; their hashes are not
substituted for this source state.

Commands executed from the indicated roots:

```powershell
# Target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# E:\Lean\Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes were polled to terminal completion and returned exit code 0.
No principal stage failed. No final Lean error, warning, tactic suggestion,
informational-build diagnostic or linter failure remains.

Target terminal evidence:

- Log: [tao-trudgian-yang-build-20260921-025847-e6521065.log](logs/tao-trudgian-yang-build-20260921-025847-e6521065.log).
- Log SHA256: `3c8dda3e7e35769b374c4e3e83efe2b766eda3116817bd8ee67d8a5ffab97df8`.
- Final result: `LEAN VERIFICATION PASS`; default build: 9,166 jobs.
- Inventory: 28 required project files; 20 pinned source files; 12 frozen
  ANTEDB files; all 311 package Lean files covered; 322 Lean files scanned.
- Deterministic certificate regeneration and semantic regression: PASS.
- Exhaustive audit: 3,227 discovered nonprivate target theorems plus five
  imported contracts, totaling 3,232 declarations. Generated helper
  declarations are included; this count is not merely the public list.
- All 24 newly named public audit records were individually checked in
  the full log. Their only axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The 30 new semantic examples pass, including each public
  signature and the unfolded literal high-value integral.
- Root imports and the backing PowerShell inventory contain each of the
  six new production modules exactly once. No module is excluded to pass.

Foundation terminal evidence:

- Log: [foundation_freeze_20260921_025848.log](../../logs/foundation_freeze_20260921_025848.log).
- Log SHA256: `c32d793e65650a09451a148a037eff44b7039fb436c0a3810a40f443267ad0a4`.
- JSON manifest: [foundation_freeze_20260921_025848.json](../../logs/foundation_freeze_20260921_025848.json).
- JSON SHA256: `3288cfb50aff5e86f92885444a27fd05e7f8d2edd25a45a720e0b15bb8159ee2`.
- Canonical verifier SHA256: `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
- JSON status: `PASS`; failures: `[]`. All six process stages have exit
  code 0, `passed=true`, and zero warning, tactic-info, informational-build
  and linter-failure counts.
- Root/default build: 8,857 jobs. Exact publication contract, both retained
  regression stages, transitive axiom/exact-output audit and declaration
  linter gate: PASS.
- Classification: 301 root-graph modules, two explicit regressions,
  zero excluded and zero unclassified.
- Audit: 14,290 discovered nonprivate theorems; 7,636 explicit public source
  declarations. The exact publication types and required outputs pass.
- Checkout: `main`, commit `bda1d96a12d7eddca30079b59c6dde23a82e90e0`, dirty. Existing owner
  changes were preserved; no commit, staging or push was performed.

Focused development evidence and repairs:

Each new production module reached a successful focused build before the
principal evaluation. The final focused
`lake build TaoTrudgianYang2025.SemanticRegression` completed with 9,166
jobs and zero diagnostics. Earlier focused attempts exposed real-power
rewrite/elaboration issues, dependent finite-maximum rewriting, missing
measurability type annotations, and restricted-integrability field
resolution. Those were repaired in the source. The final zero-coefficient
regression initially retained two unnecessary hypotheses and used an
unnecessary `simpa`; it now proves the stronger hypothesis-free boundary
case with `simp`. No linter was disabled and no failure was relabeled.
The principal gates ran after these repairs.

All three repository-wide Lean searches were repeated. There are no
`sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by` or
`unsafe` matches. Raw `axiom|constant` line matches are existing comment
prose and two rational structure fields, not postulated declarations;
both principal scanners independently pass. `git diff --check` returns
0; Git's LF/CRLF notices are line-ending notices, not Lean diagnostics.

The following SHA256 values were rechecked after both terminal gates;
none changed during verification:

| File (relative to this target folder) | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/PointValueRanges.lean` | `2378a44bd914a0f43a6edb359d927ae2d034773a557be9c0d89815e52146af01` |
| `Extension/TaoTrudgianYang2025/PointValueMeasure.lean` | `c9f1bf6f9a2dce2044ff2bb67a10977c172079105a8a4cae9350ffac0ab894c4` |
| `Extension/TaoTrudgianYang2025/TruncatedLayerCake.lean` | `a9f4e2572000c214b754678e84fc14a9dce257a55f0380799572d8d94b288623` |
| `Extension/TaoTrudgianYang2025/PointValueTailIntegral.lean` | `5e341537293f7c2cb72f1623bcc6413734b726534da58e25640d29a2551f9915` |
| `Extension/TaoTrudgianYang2025/PointValueHighMoment.lean` | `dbc4e41d8a7fd4c2b574f6fdb5386f24ebb4052addf64b3f50fe9b7580210a9d` |
| `Extension/TaoTrudgianYang2025/PointValueLowMoment.lean` | `179e029680d98680e00548385f9ae21a15456cc7805d8875f3c95171130d9cf2` |
| `Extension/TaoTrudgianYang2025.lean` | `135bffb68de5d2de49e6bdf7b16c1bd2508c517d914515134617850655893139` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `932f52e31f099efc802230b2cad772c61700c49230d7df113f877fa2ae8a4ee9` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `c6ea26899c409530c0631a3d1216f6b6d6ad13d3ab7406feb93f948062e83d3d` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `3ec5c45a682b46414bdd7491541bb6fdecd55965f1bd405d4341c5b7c3af0ada` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |

The preserved obstruction hash still equals
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent witnesses and actual Heath–Brown energy theorem
were not edited. All eleven target documents are synchronized with the
verified ZHR/ZHM results, the proved conditional deduction ZLF, and the
still-open unweighted fourth-moment source ZGB. The full twelfth moment,
unconditional Add-est and full EPZAE-00–41 goal remain OPEN.

## Actual fourth-moment contour bounds and mixed-line truncation — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. The
authorized corrected cardinality/energy powering, independent ρ/k and
ρ*/k witnesses (with independent fifth exponents), and actual Heath–Brown
energy application remain unchanged. False s-scaling is not restored.

The new source is genuinely unweighted zeta. Write
J(t)=zetaSquareDivisorIntegral(-t)/zetaSquareGammaNormalization(t).
`zetaSquareNorm_eq_two_re_fourthRightPiece` proves
|ζ(1/2+it)|²=2 Re J(t), and `zeta_fourth_le_four_mul_rightPiece_sq`
proves |ζ|⁴≤4|J|². The actual Gamma quotient and pole factors are retained;
the native mollified fourth-moment theorem is not substituted.

`exists_norm_zetaFourthKernel_le` proves, for each c>0, a constant K_c>0
chosen before t and u such that t≥4 and t≥4c imply
|K(t,c+iu)|≤K_c t^c exp(-98u²) on the complete line. Near-height
Gronwall bounds and far-height Gamma bounds are both consumed.
A separate, height-dependent strip bound justifies holomorphy,
integrability and disappearing horizontal sides; it is not advertised
as the uniform moment bound.

`zetaFourthContribution_line_eq` proves equality of each actual
integrated ordinary-divisor contribution on any two positive lines.
`hasSum_zetaFourthContribution` transports the convergent integrated
series from c=1. This does NOT assert pointwise Dirichlet-series
convergence to the left of its half-plane.

For t≥0, a,b>0 and any finite S, the actual source now satisfies
J(t)=Prefix(t,a,S)+Tail(t,b,S). The prefix is proved equal to the
integral of the finite ordinary-divisor polynomial times the actual kernel.
For b>3/2, one constant K_b>0 works for all t≥max(4,4b) and all S:
|Tail|≤K_b t^b Σ_(n∉S) d(n)n^(-1/2-b).
The displayed positive tail is summable, not an assumed small error.
`exists_zeta_fourth_le_prefix_add_weightTail` consumes these results
to bound the literal |ζ|⁴ by eight times the squared prefix norm plus
eight times the squared displayed tail bound.

Twelve new `ZetaFourth*` modules are root-reachable and in the exact
production inventory; 53 public theorems have named dependency audits.
Sixty new regressions cover every signature, zero/empty/singleton cases,
different contour lines and literal critical-zeta consumers. The final
principal-runner evidence is recorded below.

Z4K (uniform kernel) and Z4C (actual mixed-line truncation) are supporting
results, not the unweighted fourth-moment theorem. ZGB still requires the
finite-polynomial mean square, quantitative cutoff-tail decay and their
integrated assembly. Thus ZGB/ZTM/ZAT, EPZAE-19/21/37, unconditional Add-est
and the full EPZAE-00–41 goal remain OPEN. No frozen public contract is
weakened, and no source pin, archive or adjacent/native proof is changed.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed: exact module coverage, root imports, named/exhaustive audits and
regressions are part of the goal. Run it and `run_lake_build.bat` after
relevant changes; a passing audit establishes integrity, not completion
of the missing moment or of all advertised Add-est clauses.

### Contour checkpoint scope and repaired focused diagnostics

The twelve new production modules are:
- `ZetaFourthSource.lean`
- `ZetaFourthGaussian.lean`
- `ZetaFourthKernelBasic.lean`
- `ZetaFourthKernelNear.lean`
- `ZetaFourthKernelFar.lean`
- `ZetaFourthKernel.lean`
- `ZetaFourthContourBounds.lean`
- `ZetaFourthTerm.lean`
- `ZetaFourthTermBounds.lean`
- `ZetaFourthContourShift.lean`
- `ZetaFourthContributionBounds.lean`
- `ZetaFourthTruncation.lean`

Focused compilation checked each module. Initial failures were repaired
in the source: conjugation/norm rewrites, explicit interval endpoints
and measure, arithmetic normalization, explicit exponential monotonicity,
complex argument equality, typed composition, real-to-complex negation,
the zero coefficient's nonnegative real power, nested subtype casts, and
the regression namespace's topology notation. The strip and contour-limit
elaboration timeouts were repaired by reducing inference/unification work,
not by suppressing diagnostics or raising heartbeat limits. No retained
module has an admitted proof or a weakened theorem to bypass these errors.
The final principal evaluations below supersede intermediate failures.

The 53 named audits cover every new public theorem, including the actual
kernel, line independence, convergent series, mixed-line decomposition,
tail bound and literal fourth-power consumer. The 60 regressions repeat
all exact public types and add seven boundary/literal-source tests.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 323 package files, 334 Lean
files in its integrity scan, 3,296 audited declarations (3,291 discovered
target theorems plus five imported contracts). All 53 new named audits
and 60 added regressions pass. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample is byte-preserved; all source/runner hashes
were rechecked after both gates. Exact logs, hashes and the repaired
comment-scanner false positive are in the current Reproduction Manifest.
These gates verify the actual contour and truncation consumers, not the
missing fourth-moment integral, unconditional Add-est or the full goal.

### Terminal runner evidence and reproducibility fingerprints

Commands were run from their respective project directories:

```powershell
cmd /c run_tao_trudgian_yang_build.bat --no-pause
cmd /c run_lake_build.bat --no-pause
```

- Target log: `logs/tao-trudgian-yang-build-20260921-034938-fb6541dc.log`.
  SHA256: `d0f74f65a2591581367bd3b27b62dd8d71e89edbb3942c439c663417da5ca44c`.
  Exit 0; all inventory, pinned-source, frozen-source, shortcut-scan,
  exact-coverage, deterministic-regeneration, default-build, semantic-
  regression and transitive-audit gates passed. The default build checked
  9,178 jobs. Required files: 28; pinned files: 20; frozen ANTEDB files: 12.
- Foundation log: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_035226.log`.
  SHA256: `addafe426ab9d3572cccb06c82f0af90670608091152979c271ba67896497426`.
  Manifest: `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_035226.json`.
  SHA256: `757001f8ff40b3f62487d2982b7a1db676176f7e715cb4515faed2b53667cab8`.
  Exit 0, final PASS, failures=[]; all six stage records have exitCode=0,
  passed=true and zero warning/tactic-info/informational-build/linter fields.
  Root build: 8,857 jobs; 7,636 explicit public declarations and 14,290
  discovered theorems audited. Classification: 301 root-graph files,
  two explicit regressions, zero excluded and zero unclassified.
- Foundation verifier SHA256:
  `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
- Git HEAD: `bda1d96a12d7eddca30079b59c6dde23a82e90e0`, branch `main`,
  dirty working tree. No commit, staging, push or synchronization script
  was performed. Existing changes were preserved.

Intermediate logs are retained, not relabeled as passing:
`logs/tao-trudgian-yang-build-20260921-034906-e074b248.log` and
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_034907.log`
failed the integrity gate because a prose comment line began with
`constant is ...`. That word was changed to `bound` in
`ZetaFourthContourBounds.lean`. The mathematical code and scanner rules
were not weakened; both complete final runs above passed the corrected
source. This was not a Lean postulate, theorem assumption or ignored
failure.

Repository scans were repeated: no placeholder or unsafe-bypass matches.
The 12 raw postulate-pattern matches are the unchanged historical comment
text and two rational structure fields, not postulated declarations.
Both semantic integrity scanners pass. `git diff --check` exits 0;
Git emits its existing LF-to-CRLF conversion notices, not Lean diagnostics.
All 11 documents were read back and checked against the intended edits;
all 12 new source files and four integration files were similarly checked.
The Mermaid nodes are unique and every class refers to a declared node.

Post-gate SHA256 fingerprints (relative to this folder):

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/ZetaFourthSource.lean` | `d50cd2945c7d5d9a421f12b078060031858615e077832286f186f7b9f7dc0698` |
| `Extension/TaoTrudgianYang2025/ZetaFourthGaussian.lean` | `00b17cb429cce0e7241178f2e51cbed663c7e3a60cb9a9ee5618757220cce89c` |
| `Extension/TaoTrudgianYang2025/ZetaFourthKernelBasic.lean` | `f1d8da8be34d6085130651ed0a4710f41cf71ee940a046417ad45b2dfc62452a` |
| `Extension/TaoTrudgianYang2025/ZetaFourthKernelNear.lean` | `d85df3a62c136749cb31faa1ebbd35fa5b550d470443733969552f0064c5e1f0` |
| `Extension/TaoTrudgianYang2025/ZetaFourthKernelFar.lean` | `5b9eb64798a33ff57f6d571096988cb59544896ad7f137a11f00db437db7078c` |
| `Extension/TaoTrudgianYang2025/ZetaFourthKernel.lean` | `54299d1fd18edc2d8ec9beb18b314bf6fd876cdc5972a1c08de2b551389eaae1` |
| `Extension/TaoTrudgianYang2025/ZetaFourthContourBounds.lean` | `a99c80da503e34b080bd45cc6906ad5e09d2b10b6d7a709103ab336c8a03181e` |
| `Extension/TaoTrudgianYang2025/ZetaFourthTerm.lean` | `de1971a1961aeb33e2598c9af7a74e4bd8b04fc95bd0fe07066f20f2f2c74e94` |
| `Extension/TaoTrudgianYang2025/ZetaFourthTermBounds.lean` | `9f2949cf698856a20aca69b1c3af948018b7e8e5cec17640e6b062c0bb76113d` |
| `Extension/TaoTrudgianYang2025/ZetaFourthContourShift.lean` | `08bf9f771e8b5849ba02a27fab2ad03065c9841d8e4ca13659231556eec129b0` |
| `Extension/TaoTrudgianYang2025/ZetaFourthContributionBounds.lean` | `03b86cdc6bd4be63574050a3078de5e4291066e20767c67dfa392efb3b284645` |
| `Extension/TaoTrudgianYang2025/ZetaFourthTruncation.lean` | `522f41b28cae8db69cc2ff48bf4bfa5f0dd0e30b12ffd8c6d6f74d7b908033d6` |
| `Extension/TaoTrudgianYang2025.lean` | `243124cef95ece114f1abe53f6489d02dc4dd133ee0c1e0b21adb034313dd342` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `787da2aaa4df8224ce66dcf079db1ebbdcee5fe8957abe597db188bec936a74b` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `98d9649190a360a985c0ac50ebb8a660a5b82a8545be15868755409eb916b68b` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `322a34031fba8482f1ee30858a402131f1e3c3f55107a2f02c035c7969376ecc` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |

Only the comment clarification changed a source hash after the first,
failed gate. All final source/runner hashes match the corrected-source
snapshot used for the final gates. The counterexample's hash is still
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

## Unweighted moments and Add-est (i) — historical checkpoint

The printed Lemma 62 singleton counterexample is preserved byte-for-byte.
The corrected theorem still returns independent ρ/k and ρ*/k witnesses,
with independent existential fifth coordinates. No false s'/s scaling or
third s-preserving witness is restored.

`zeta_fourth_dyadic` now proves the genuine unweighted estimate: for every
η>0, constants C≥0 and H₀ are chosen before H, and H≥H₀, H>0 imply
integral_H^(2H) |ζ(1/2+it)|⁴ ≤ C H^(1+η).
It consumes the actual normalized divisor-contour source, not the native
mollified fourth moment and not an assumed fourth-moment bound.

The finite prefix is exactly {1,...,2^M}, including its first coefficient.
Unit-modulus endpoint twists prove a mean square uniform under every real
imaginary translation u, including the reflected phase u-t. The ordinary
divisor coefficient-square bound is derived from the native divisor bound.
Weighted Cauchy–Schwarz, product integrability and Fubini are proved for the
actual Gaussian kernel and complete finite polynomial.

The separate right line b=2+2/δ gives an actual bounded tail when
N≥H^(1+δ), uniformly for H≤t≤2H. A dyadic N between H^(1+q) and
2H^(1+q), with q=min(η,1)/20, pays the block-count loss. The exact exponent
1+5q+2q² is at most 1+7q≤1+η. Neither the cutoff error nor the polynomial
mean square remains a theorem parameter.

`zeta_twelfth_dyadic` applies the installed high/low decomposition to this
proved fourth moment. For every ε>0 it gives constants D≥0 and H₀ before H:
integral_H^(2H) |ζ(1/2+it)|¹² ≤ D H^(2+ε).
`zetaTwelfth_largeValueBound` and its short-height companion discharge
the actual Perron consumers: LV_ζ≤2τ−12(σ−1/2) for σ≥1/2, τ≥2,
and for σ≥3/4, τ≥3/2, respectively.

`add_est_i` in `NewAdditiveEnergy.lean` proves the literal printed clause on the entire
closed interval 3/4≤σ≤5/6:

```text
A*(σ)(1−σ) ≤ max((18−19σ)/(2(3σ−1)), 4(10−9σ)/(5(4σ−1))).
```

The actual declarations are `add_est_i`, `add_est_i_bound` and
`add_est_i_zero_energy` in `NewAdditiveEnergy.lean`.
The last exposes ∀ε>0 ∃C≥1 ∃δ>0 ∀T≥C, with the genuine shifted zero
energy at σ−δ, preserving analytic multiplicities and unit tolerance.
The epsilon--delta bound is proved first; the extended-real infimum
inequality is its consequence, not a substitute. At σ=3/4 the rate is
3/2 and A*≤6; at σ=5/6 the rate is 6/7 and A*≤36/7.

The dependency chain consumes corrected powering, the actual Heath–Brown
energy relation, certified general/zeta optimization, the proved twelfth
moment, and the proved endpoint-one zero-energy transfer. The separate
EPZAE-33 endpoint-two theorem is not assumed and remains open.

Seventeen new production modules are root-reachable and explicitly listed
in the batch runner's inventory. All 49 new public theorems have named
dependency audits. Sixty-one new regressions cover every public signature,
literal zeta integrals, coefficient/prefix endpoints, negative translated
intervals, both LV threshold boundaries and both printed energy endpoints.

ZGB, ZTM and clause (i)'s actual zeta/short-energy consumers are proved.
The other eight Add-est clauses, their remaining optimization certificates,
the separate sharp Atkinson source-form theorem, the other EPZAE-19/21
inputs, and the exponent-pair/density outputs remain OPEN. EPZAE-36/37 and
the full EPZAE-00–41 goal are not complete; the frozen contract is unchanged.

Keep `run_tao_trudgian_yang_build.bat` and its backing implementation
synchronized with root imports, exact inventory, named/exhaustive audits
and regressions. Run it and `run_lake_build.bat` after relevant changes.
This checkpoint's terminal gate evidence is recorded in the Reproduction
Manifest; earlier checkpoint PASS records are historical.

Verification (2026-09-21): both principal BAT scripts reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 340 package files,
351 integrity-scanned Lean files and 3,357 audited declarations
(3,352 discovered target theorems plus five imported contracts).
All 49 new named audits and all 61 new regressions pass.
The foundation reports PASS: all six stages passed, with 14,290
discovered theorems audited. Both final logs contain zero Lean errors,
warnings, tactic suggestions or linter failures. The counterexample
SHA256 is unchanged. Exact logs, source/runner hashes and repaired
focused diagnostics are recorded in the current Reproduction Manifest.
These gates verify the genuine moments and full-domain Add-est (i),
not clauses (ii)--(ix) or completion of the full goal.

### Exact terminal reproduction evidence

Both commands were run against the same preserved dirty checkout at
`bda1d96a12d7eddca30079b59c6dde23a82e90e0` on `main`.
No commit, staging, push, source-pin edit or adjacent/native proof edit
was made. The pinned Lean/Mathlib graph is unchanged.

| Command and working directory | Exit / result | Complete log |
|---|---|---|
| `cmd /c run_tao_trudgian_yang_build.bat --no-pause`, this folder | 0 / LEAN VERIFICATION PASS | [target log](logs/tao-trudgian-yang-build-20260921-044424-ec93e5ca.log) |
| `cmd /c run_lake_build.bat --no-pause`, `Riemann Zeta` | 0 / PASS | [foundation log](../../logs/foundation_freeze_20260921_044435.log), [JSON](../../logs/foundation_freeze_20260921_044435.json) |

Target: 9,195 build jobs; 28 required files; all 20 pinned-source checks;
12 frozen ANTEDB files; deterministic certificate regeneration PASS;
340 exact package files and 351 source-integrity files. The exhaustive
audit checks 3,357 declarations, including all 3,352 discovered target
theorems without generated-name exclusions and the five imported contracts.
The 49 newly named audits explicitly include `zeta_fourth_dyadic`,
`zeta_twelfth_dyadic`, both actual LV consumers, `energyClauseOne`
and all three `add_est_i*` source-facing forms.

Foundation: 8,857 build jobs; root graph 301, explicit regressions 2,
excluded 0, unclassified 0; 7,636 explicit public declarations and
14,290 discovered theorems. JSON status PASS, failures [], all six
stages exit 0 with passed=true and zero warnings, tacticInfo,
informationalBuilds and linterFailures. The unchanged verifier SHA256 is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Full-file log hashes after terminal completion:

- Target log SHA256: `25e7dd102de6ad8328781c35055a9d1e3ba0a843cd07abb70e66993153be26b2`.
- Foundation log SHA256: `a9cc575ef6eef9626d1b41729c54e231441befbc2ad09aab6db2a68bfc422f8f`.
- Foundation JSON SHA256: `a5d247010855dba0330353d2de5765c1b01f1de1514da073da14ab7c2c5c6c60`.

Both actual proof runs finished normally. A later read-only
`Get-Content` log-summary command stalled and was cancelled; direct
.NET file reads and `rg` independently recovered the complete terminal
evidence and verified the hashes. A read-only process-inspection attempt
was denied by the environment; no elevated access was needed. Neither
diagnostic affected or replaced a build or audit gate.

### Semantic completion review

The literal fourth and twelfth regressions unfold
`zetaMomentCriticalNorm` to the actual `riemannZeta(1/2+it)` norm.
The fourth theorem retains ∀η>0, ∃C,H₀ before ∀H and has no moment,
mollifier, cutoff-error or mean-square premise. The complete prefix
retains n=1 and its exact phase. Its translation estimate is uniform in u;
the product integral is genuinely integrable before Fubini is used.
The right-line choice is made before H and the geometric tail is bounded,
not merely summable. The final dyadic loss fits every positive η.

The twelfth theorem applies the genuine fourth instance to the installed
actual high/low decomposition. Its downstream Perron consumers use
physical pattern scales, exact coefficient-one sums and the full original
epsilon--delta quantifier order. The short-height consumer covers [1,2],
using actual eventual emptiness below 3/2 and the proved moment above it.

`add_est_i_zero_energy` exposes the actual object:
`zeroAdditiveEnergy (σ-δ) T` is unit-tolerance additive energy of the
imaginary ordinates of `ZeroCopy (σ-δ) T`. That sigma type indexes every
analytic-multiplicity copy of every actual zero with
σ−δ≤Re ρ≤1 and |Im ρ|≤T. No multiplicity or sign half is dropped.
`add_est_i_bound` proves the epsilon--delta predicate; `add_est_i`
then uses its infimum consequence and 1−σ>0. The printed two-function
maximum and both closed endpoints are unchanged.

The proof term consumes `energyClauseOne_of_dyadic_moment` with
`zeta_twelfth_dyadic`. Its general half reaches
`InCardinalityEnergyRegion.energyClauseOneGeneral`, which applies the
actual corrected cardinality cap and `heathBrown_powered`. The zeta
half reaches `energyClauseOneZeta_public_rate_bound_of_twelfth` with
proved cardinality. The final zero transfer is the proved endpoint-one
consumer. The independently open endpoint-two theorem is not an input.

### New production scope and final file hashes

Every listed module is explicitly imported by the root and appears once
in the production inventory. Every public theorem is named in Audit.lean;
FourthTwelfthMomentRegression has 49 exact-signature tests plus 12 literal
and boundary tests. All files were read back after the gates.

| File relative to this folder | SHA256 |
|---|---|
| `Extension/TaoTrudgianYang2025/ZetaFourthTailPower.lean` | `4a5c8290119d7e9976c403bd50f2c0d7b436dcaef3b597bade05629c423f9a26` |
| `Extension/TaoTrudgianYang2025/ZetaFourthTailScale.lean` | `57a0a503f86545b23100f465027b4b4e4ca9e4f2bd4a29d6a6f986976a5695ad` |
| `Extension/TaoTrudgianYang2025/DirichletMeanSquareTranslation.lean` | `219ef321fb3aa0d2c5e30b80d3586df69a8d95ebd45edc2f8473b661fcf8d551` |
| `Extension/TaoTrudgianYang2025/DirichletPrefixBlocks.lean` | `b8ab2338d5d8409567fd585f3c162260643682c77341040c7a441ca931c3942d` |
| `Extension/TaoTrudgianYang2025/DirichletPrefixMeanSquare.lean` | `1b9bf16835ce1ec19ab20554d75c1db606689f2fad11a3da8f81bb930692ee35` |
| `Extension/TaoTrudgianYang2025/ZetaFourthCoefficients.lean` | `f93b600d52fb7d4c7d65db14b7539ad8a4a5dbae47aed763c62e940ae8e74583` |
| `Extension/TaoTrudgianYang2025/ZetaFourthCoefficientMass.lean` | `4241aeb875f038992326efb1f4afe59459d5ccd2058b65d357a430597e74746a` |
| `Extension/TaoTrudgianYang2025/ZetaFourthPolynomialMean.lean` | `85a4af1a9bbb422fb21d16d515addc1ef99b3534aec3e79f7ad6f42624d82909` |
| `Extension/TaoTrudgianYang2025/WeightedIntegralSquare.lean` | `eb10c388900e55238146a4157835d55b1c096291e65935f7ea1ea2fd01d1c5f2` |
| `Extension/TaoTrudgianYang2025/DirichletPrefixBounded.lean` | `2230ad35621a0716ac81529db4ed4ceccefa62e677a8bc110aca8efd1292c1da` |
| `Extension/TaoTrudgianYang2025/ZetaFourthPrefixGaussian.lean` | `461bb6151125d7bd9a014eb91af6d4c1bd393079e96e614b05f9110a0d705887` |
| `Extension/TaoTrudgianYang2025/GaussianPrefixMean.lean` | `95d13ae8988d12935cb5cf643cadd478627ab1ba5433d678875e3d5d1de3e26f` |
| `Extension/TaoTrudgianYang2025/DyadicMomentCutoff.lean` | `e0d1be00b83554e487d8ce6dcb50000fc92c12df085f10b829a25827bf5dd4ce` |
| `Extension/TaoTrudgianYang2025/ZetaFourthDyadicBudget.lean` | `6c5712e2ecd6a92815a87a5e94efbef33d22c4a30f4944d8b622b49bc5132ec9` |
| `Extension/TaoTrudgianYang2025/ZetaFourthMoment.lean` | `5f41c7fd87af6cdd55c6a9d53ae4258d9c1570fe9735ddc60c156ac29e81d538` |
| `Extension/TaoTrudgianYang2025/ZetaTwelfthMoment.lean` | `6f40b139af99b18f671668044a4480fc148e9dbbeb5ace28475e7f1abb066f6b` |
| `Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean` | `5e1d272e573d4c657e38dc1a9d2198b5b017a836cbac77b4db9cb99b45601126` |
| `Extension/TaoTrudgianYang2025.lean` | `a6736e041b7a6c775aae468939e5b27a313bba992a38d5e965f4ab8bf888b4cd` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `f7b6e109ace726e923341ee827bc49ecf8e2c9fdbfb87f9124ea2582a9f92677` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `d3881110404608a612d950c4ead451971c1e746f6f8218e51038faf394898132` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `ccd499ab7219ca2a1f19f5ab508eeb35613e2ba1ab6a1d0938561e244af0ad86` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |

### Failed focused attempts repaired before the principal gates

Early focused builds exposed real-power/cast normalizations, typed
integrability and finite-function-sum elaboration issues, and two
misinferred inequality multipliers in the final fourth assembly.
The proofs were repaired without weakening signatures, adding premises,
raising a heartbeat limit or suppressing diagnostics. The first new
regression build emitted five unnecessary-sequence-focus warnings.
Those five sites were simplified; the two genuinely multi-goal
extended-real endpoint tests retain their required goal sequencing.
The final focused SemanticRegression build and both principal runs
contain no Lean warning, error, tactic suggestion or linter failure.

Repository-wide scans for placeholders and unsafe proof bypasses return
exit 1 with no matches. The broad textual postulate scan returns the same
12 historical non-declarations as the previous checkpoint: ten comment
lines and two rational structure fields. Their sorted match set is
unchanged; both semantic postulate scanners pass. `git diff --check`
returns exit 0. Git's pre-existing LF/CRLF conversion notices are not
Lean diagnostics and are not concealed. No proof-integrity gate was
narrowed or bypassed.

This establishes kernel/project completion of the genuine moments and
Add-est (i), not all of EPZAE-19/21/36/37, all nine clauses, the separate
sharp Atkinson source theorem, or the active full EPZAE-00–41 goal.

## Add-est (ii): repaired powering to actual zero energy — verified checkpoint

Printed Lemma 62 remains disproved. Its singleton counterexample is
byte-preserved (SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The authorized replacement still uses independent cardinality-preserving
ρ/k and energy-preserving ρ*/k witnesses with independent existential fifth
coordinates. No false s'/s scaling or third witness is restored.

`add_est_ii`, `add_est_ii_bound`, and `add_est_ii_zero_energy` in
`NewAdditiveEnergy.lean` prove the complete second printed clause on
the closed interval 7/10 ≤ σ ≤ 3/4:

```text
A*(σ)(1−σ) ≤ max(5(18−19σ)/(2(5σ+3)), 2(45−44σ)/(2σ+15)).
```

The actual shifted-zero epsilon--delta bound is proved first, with analytic
multiplicity and unit-tolerance energy retained. The extended-real
infimum inequality follows from it. At σ=7/10 the rate is 47/26 and
A*≤235/39; at σ=3/4 the rate is 16/11 and A*≤64/11.
These endpoint checks supplement, not replace, the full interval proof.

For general patterns, `energyClauseTwo_general_bound` proves the rate on
2≤τ≤4. Actual mean-square and Guth--Maynard cardinality consumers use the
ρ/k witness at k and k+1. The actual Heath--Brown relation uses independent
energy witnesses at k and k−1, where k is two or three. All nine affine
branches are checked; the exceptional branches consume the first powered
energy inequality. Every height and coordinate is linked to its original
region point. Compactness promotes the region result to a uniform bound.

For zeta patterns, sixth-order decay is applied to the actual critical
Mellin integrand. Both the residue and the complete far tail
240 C₆ N^(11/2)/T⁴ are retained before absorption at T≥N^(11/8).
`zetaTwelfth_lower_short_largeValueBound` consumes the proved dyadic
twelfth moment and this entry bridge for σ≥7/10, τ≥7/5.
Actual cancellation gives eventual emptiness for 1≤τ<2σ on the clause
interval; mean-square powering and the twelfth-moment cap handle
2σ≤τ≤2 through nine exact branches with crossing τ=4σ−1.
`energyClauseTwo_short_zeta` therefore supplies all of [1,2].

`energyClauseTwo` composes the two uniform ranges with the already proved
endpoint-one bounded-range zero-energy transfer. The separate printed
endpoint-two transfer (EPZAE-33) is neither assumed nor marked complete.
Clause (i) remains proved. Clauses (iii)--(ix), the remaining optimization
projections, the source-form sharp Atkinson obligation, the other
EPZAE-19/21 inputs, and the exponent-pair/density/release outputs remain OPEN.
EPZAE-36/37 and the full EPZAE-00–41 objective are unchanged and incomplete.

Eleven new production modules are root-reachable and explicitly included
in the principal runner inventory. Eighty-four new public theorems have
named dependency audits; 92 added regressions cover all signatures and
literal physical/source endpoints. Keep `run_tao_trudgian_yang_build.bat`
and its backing inventory synchronized; run it and `run_lake_build.bat`
after relevant changes. Current gate evidence belongs in the Reproduction
Manifest; earlier PASS records are historical.

Verification (2026-09-21): both principal BATs reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 351 package files, 362
integrity-scanned Lean files and 3,504 audited declarations (3,499 discovered
target theorems plus five imported contracts). All 84 new named audits and
92 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions or linter failures. The
counterexample and all 18 recorded source/runner hashes were rechecked.
Exact log paths and hashes appear in the current Reproduction Manifest.
These gates verify full-domain Add-est (ii), not the other seven clauses or
completion of the unchanged whole-proof goal.

### Exact terminal reproduction evidence

Commands (PowerShell, pinned Lean 4.30.0; each process was followed to terminal
completion without restarting it on an observation timeout):

```powershell
# From this folder
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# From E:\Lean\Riemann Zeta
cmd /c run_lake_build.bat --no-pause
```

Target: exit 0, LEAN VERIFICATION PASS. Log:
`logs/tao-trudgian-yang-build-20260921-053556-5589399e.log`.
SHA256: `fb9185625bca8946eb2df4131662fb61a6cf035bfaf17e477defc3bf31dc6150`.
The default build checked 9,206 jobs; inventory, all 20 pinned source
files, 12 frozen ANTEDB files, deterministic regeneration, semantic
regressions, complete production coverage and transitive audits passed.

Foundation: exit 0, PASS; 8,857 default-build jobs.
Log: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260921_053607.log`.
SHA256: `e74290168d4451c36dd90d7e11411cf2a5190964670235e053bd1dc3ac92bfed`.
JSON: `E:\Lean\Riemann Zeta\logs\foundation_freeze_20260921_053607.json`.
SHA256: `829c24464b95219cd239ef4f5becb3bfdd49d26f3ac2da173ed77ad4e311a22e`.
The JSON reports `failures: []` and all six stages passed with zero errors,
warnings, tactic suggestions, informational-build flags or linter failures.
Root classification remains 301 production graph files and two explicit
regressions, with zero exclusions or unclassified files. The audit covers
14,290 discovered theorems and the 7,636-entry explicit public list.
The canonical verifier SHA256 is unchanged:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

Focused final checks:
`lake build TaoTrudgianYang2025.NewAdditiveEnergy` (9,185 jobs) and
`lake build TaoTrudgianYang2025.SemanticRegression` (9,206 jobs)
both exited 0 without Lean diagnostics. The earlier diagnostic-producing
development attempts were repaired: explicit right-hand division rewriting,
separate finite branch certificates, exact vector reduction, an explicit
max-form cardinality cap, and three regression tactic sequencing fixes.
No warning suppression or heartbeat-limit change was used.
Large console audit output was truncated only by the tool display; both
complete log files were separately inspected.

All three prescribed repository-wide `rg` scans were run. Placeholder
and unsafe-bypass scans returned no matches (exit 1, the normal rg no-match
status). The postulate text scan's twelve historical matches are unchanged:
ten comment lines and two rational structure fields, no postulate.
Both semantic postulate scanners passed. `git diff --check` passed after
removing spaces from blank Mermaid comment lines. Git's existing LF/CRLF
conversion notices are not Lean diagnostics.

HEAD remains `bda1d96a12d7eddca30079b59c6dde23a82e90e0` on main, dirty.
Existing changes were preserved. No staging, commit or push was performed.
The frozen source archives, toolchain and dependency pins are unchanged.
The existing batch launcher is unchanged; its backing inventory now includes
every added production module. Below are the post-gate SHA256 values.

| Relative file | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/EnergyCardinalityBounds.lean` | `90ef35e4bb89f8feeeb2e241963b0b1585b15ddda5588a0368decaa318ab7722` |
| `Extension/TaoTrudgianYang2025/HeathBrownNineBranches.lean` | `d00575434667b097750db1f85bf01417df8288a0eb0cb9f9308c5b3995272497` |
| `Extension/TaoTrudgianYang2025/EnergyClauseTwoCaps.lean` | `de063ea0b7661b360dd78f4215a2df2017cb7378c0acbfde3d506d1b363cb697` |
| `Extension/TaoTrudgianYang2025/EnergyClauseTwoCertificates.lean` | `2779886a11573b4bf0d75d0345050d11af475b3e73d177df00d15675550aac92` |
| `Extension/TaoTrudgianYang2025/EnergyClauseTwoGeneral.lean` | `89f12cb7593f2f6524ae318c6c37984bd2d0854ee0e5064ddd237b2f0989cb9b` |
| `Extension/TaoTrudgianYang2025/ZetaSixthLocalization.lean` | `a0d040661e8126228e85ca51341e0abc5aa314fb7a247f5f258e5731ed657d67` |
| `Extension/TaoTrudgianYang2025/ZetaSixthPerron.lean` | `ca77305944ca94143a336fc28b97f4eac51394965ffcbd99b6d31dc4e8bd51b9` |
| `Extension/TaoTrudgianYang2025/ZetaBelowTwiceSigma.lean` | `452297b938780ad88c9b0002181acf41ba530d240f4c9b69511714a943f47ccb` |
| `Extension/TaoTrudgianYang2025/ZetaTwelfthLowerShort.lean` | `db52774c4523c3c34707cbe323392df07b65b993914fd341414dfd5d4c603fc2` |
| `Extension/TaoTrudgianYang2025/EnergyClauseTwoZetaCertificates.lean` | `ed8db93eeafb1e9b9c924390627dae9435d732439187e3b0170e48d05c5dec9e` |
| `Extension/TaoTrudgianYang2025/EnergyClauseTwo.lean` | `2a3817177d81eda4b1a8505cbb382e7a48471a59c669c0dd0e390932da5697a5` |
| `Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean` | `f3b7af4193160e9f8fa57de2d379d0b812aaaa278d0641deea57b9e95957b012` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `Extension/TaoTrudgianYang2025.lean` | `ac91bd52729c6141edde0e72bb3e5ceb58ff65f7b0eebfb98a63ad7672bee777` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `749c622ed557e31bca625e75dba5198f3f611dfbfd49b0517abd6633af5ec9d0` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `b1550d042427b7992afe6e88299c4600f3525a2bdd67841970f65c63aa385f20` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `1c45aa2fb38d5dd6df5485d6d331f40bcb1eb10edf3fc443fe656ae1d7b20c21` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |

Semantic acceptance: the public `add_est_ii_zero_energy` quantifies
epsilon, then constants and a positive shift, then every sufficiently large
height, for the actual multiplicity-weighted shifted zero energy.
Its proof term consumes the genuine moments, actual Mellin entry,
independent corrected witnesses and the proved endpoint-one transfer.
A rational certificate, endpoint check, positivity statement or assumed
target predicate is not substituted for this conclusion. EPZAE-36/37,
the distinct endpoint-two theorem and the full goal remain open.

## Jutila source entry and uniform powered moments — verified checkpoint

The printed Lemma 62 counterexample is preserved unchanged. Corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Four new production modules advance the missing EPZAE-19 Jutila input:
`JutilaGram`, `JutilaPatternEntry`, `JutilaPoweredMoments`, and
`JutilaReflectedEntry`. They do **not** yet prove Jutila's large-values
estimate or another Add-est clause.

`jutila_smooth_amplified_gram` proves actual phase-aligned smoothed duality,
removes the diagonal before Hölder, and gives, for every positive integer k,
either R V² ≤ 2N² or R² V^(4k) ≤ (2N)^(2k) times the actual off-diagonal
2k-th trace moment. No moment or cardinality bound is assumed.

`LargeValuePattern.jutila_gram_entry` consumes an actual source pattern.
Its fixed smoothed subfamily retains at least a third of the ordinates,
the exact threshold (V−1)/3, unit separation, the actual height, and
N/2 ≤ Q ≤ 2N. The spaced consumer keeps the explicit packing loss
6(2⌈δ⌉+1). `jutila_reflected_pattern_entry` then consumes complete native
reflection on that same subfamily, with one common dual cutoff M.
The main factor uses the actual |u−t|. Mellin truncation, omitted-frequency,
and zero-mode errors all remain in `jutilaReflectionEnvelope`.

`jutila_weighted_power_moment_uniform` proves the actual critical-line
2k-th ordered-difference moment bound. With U=2^k N^k and R=|W|, its RHS is
C (U^η)² T^ε (R² + R U + R^(5/4) T^(1/2)).
C and the height threshold depend only on k, ε, η, and are chosen before
N, T, W. The proof consumes the uniform divisor bound, actual powered
coefficients, dyadic decomposition, coefficient majorant, and the proved
native weighted Heath--Brown theorem. That second-moment theorem is an
input to this deduction, not a substitute for Jutila's large-values theorem.

Remaining: pass from complete reflected prefixes to uniformly bounded
powered difference moments, sum the reflected integrals with all errors,
and perform the local-to-global large-values optimization. Then establish
the actual region and uniform exponent consumers before using them in the
seven remaining energy optimizations. EPZAE-19, 33, 36, 37 and the full
EPZAE-00–41 goal remain open; the distinct endpoint-two transfer, source-form
sharp Atkinson obligation, and other exponent-pair/density/release tasks
are unchanged.

The four modules are included in the root and the exact production
inventory of `run_tao_trudgian_yang_build.bat`. Thirteen new public theorems
have named audits and sixteen regressions cover their exact signatures,
literal diagonal removal, the k=13 power, and all reflected error terms.
Keep that BAT and its backing inventory synchronized, and execute it and
`run_lake_build.bat` after relevant changes. Terminal verification evidence
for this checkpoint is recorded below and in the Reproduction Manifest.

Source check (2026-09-21): the frozen paper cites Matti Jutila,
“Zero-density estimates for L-functions,” Acta Arithmetica 32(1)
(1977), 55–62, equation (1.4). The original
[PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa32/aa3216.pdf) and publisher
download returned HTTP 403; no downloaded Jutila PDF was added or pinned.
The author's [1975–76 survey](https://www.numdam.org/item/SDPP_1975-1976__17_1_A6_0.pdf)
identifies the reflection and coefficient-majorant inputs. Exact formulas
were also checked in the existing local Ivić scan, PDF pages 180–184
(printed pages 175–179), §9.5–6, especially (9.38)–(9.44).
That scan is read-only in node 74's Sources folder; it is not a new pinned
dependency of this package. Current code uses the already pinned native
reflection, divisor, and weighted moment proofs, not an external oracle.

Verification (2026-09-21): both principal BAT runners reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 355 package files, 366
integrity-scanned Lean files, and 3,530 audited declarations (3,525 discovered
target theorems plus five imported contracts). All 13 new named audits and
16 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions, or linter failures. All eleven
recorded source/runner hashes were rechecked unchanged after the gates,
including the original counterexample. Repository scans found no forbidden
proof terms; the twelve raw postulate-pattern matches are the same ten
comments and two rational structure fields already reviewed. Git
`diff --check` passes (Git's LF/CRLF notices are not Lean diagnostics).
Exact commands, logs and hashes are in the Reproduction Manifest.
These gates verify the Jutila entry and powered-moment inputs, not the
remaining Jutila large-values theorem, other seven Add-est clauses, or
completion of the unchanged whole-proof goal.

### Terminal gate ledger: Jutila source entry

Commands, from their respective project directories:

```powershell
$env:ELAN_HOME = 'C:\Users\Naraphim\.elan'
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# From E:\Lean\Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Target: terminal exit 0, LEAN VERIFICATION PASS, 9,210 default-build jobs;
28 required files, 20 pinned source files, 12 frozen ANTEDB files,
deterministic regeneration, exact production inventory, regressions,
integrity scans and dependency audit all PASS.
Log (relative to this folder):
`logs/tao-trudgian-yang-build-20260921-061345-f7f93a41.log`.
Final log SHA256: `4672beda06ad2761716e3ca16dccb033fbf3a1941cfbfffeab9680014c8255f6`.

Foundation: terminal exit 0, PASS; 8,857 default-build jobs; all six stages
have exitCode=0, warnings=0, tacticInfo=0, linterFailures=0, passed=true;
failures=[]. Classification remains 301 root-graph modules, two explicit
regressions, zero excluded or unclassified modules. The audit includes
7,636 explicit public declarations and 14,290 discovered theorems.
Log (relative to the foundation): `logs/foundation_freeze_20260921_061356.log`.
Final log SHA256: `b74be8e66b2477c7c668ae4cfebef8c7ae5d44eb044e7eee91a89cbf7c940340`.
JSON manifest: `logs/foundation_freeze_20260921_061356.json`.
JSON SHA256: `edd3e3162298730ab85452b9f7d94916070427865b61b5d711e201cf7c95e3e2`.
Verifier SHA256 remains
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

All thirteen new named public audits were checked in the terminal target
log; none is missing. Their only axioms are the permitted standard
`propext`, `Classical.choice`, and `Quot.sound`.
The exact-signature examples and three literal regressions compile cleanly.

Focused development initially encountered the missing ELAN_HOME setting,
then ordinary elaboration issues (cardinality normalization, a finite
diagonal-sum rewrite, factor order, power cancellation, and a separation
argument). The first exact-type regression draft exposed unused
quantified-binder diagnostics and an unspecified k; the final tests apply
every binder explicitly and fix k=13. All diagnostics were repaired at
source. No linter option, heartbeat limit, theorem domain, audit coverage,
or runner gate was weakened. One new Mermaid-comment whitespace issue was
also repaired; final `git diff --check` has exit 0.

Post-gate hashes, re-read from the actual files (relative paths use this
folder unless absolute):

```text
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
64a4dddac32cc592a59201ae03813fe41d4e1004c7ce9db2b08660a84745639c  Extension/TaoTrudgianYang2025.lean
dc94e1299aecc53135d8632ff5a7644d229b8b34f42770ca9431f728c016c4cb  Extension/TaoTrudgianYang2025/Audit.lean
33d4d91553d9920790e489d94f8cb4896c76118b98808c9b708cb65488715fe0  Extension/TaoTrudgianYang2025/SemanticRegression.lean
4399a563fcd53d0ec7166edd4288c09b85af4c99d877502245ba7a7dceabc5a6  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

Semantic gate: `jutila_reflected_pattern_entry` starts from an actual
`LargeValuePattern`, constructs the smoothed and δ-separated subfamily,
and consumes the native complete fixed-length reflection theorem before
raising and summing its full envelope. The moment theorem starts from the
actual `heathBrownWeightedPowerMoment` and composes the uniformly quantified
divisor bound with the native weighted mean square. The connection from
these two proved inputs through reflected-prefix moments and the final
large-values optimization remains explicitly OPEN. No additional Add-est
row or EPZAE completion box is claimed by this verification.

Working tree remains dirty, with 135 reported entries confined to this
target folder; existing work was preserved. No commit, staging, push, or
goal-status reduction was performed.

## Jutila reflected-prefix moments and near/far assembly — verified history

The printed Lemma 62 counterexample is preserved unchanged. The corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Six new production modules advance EPZAE-19: `JutilaPolynomialMoments`,
`JutilaPrefixMoments`, `JutilaReflectionIntegrals`, `JutilaTraceBins`,
`JutilaBinnedPatterns`, and `JutilaHybridPatterns`.

`jutila_source_power_moment_uniform` handles arbitrary unit coefficients,
with constants chosen before their values and the physical length.
`jutila_reflected_prefix_moment_uniform` consumes the actual complete
reflected prefix, including n=1. With U=(2M)^k, R=|W|, and L=ceil(log₂ M),
its bound is C (L+1)^(2k) U (U^η)² T^ε
(R² + R U + R^(5/4) T^(1/2)). The constant is uniform in M, T, W and
the translation parameter. Neither the initial term nor a power of U is
discarded.

`jutila_reflected_bin_integral_moment_uniform` applies interval Jensen and
the proved full ordered-pair majorant before restricting to a difference
bin. Its extra interval factor is exactly (2H)^(2k).
`jutila_binned_pattern_bound` connects those estimates to the actual
source pattern, with bin-dependent positive dual lengths and all Mellin,
omitted-frequency, and zero-mode errors retained.

`jutila_hybrid_pattern_bound` additionally consumes native square-root
cancellation of the complete nonzero Poisson tail below the stationary
scale, keeping the separate zero-mode decay. Above that scale it uses the
actual ceiling length max(1,ceil(2^j H/Q)). The same subfamily retains
the packing loss 6(2 ceil(δ)+1), threshold (V−1)/3, N/2 ≤ Q ≤ 2N, the
actual height, and δ-separation. The condition 4H ≤ δ derives reflection
admissibility on occupied bins; it is not an independently assumed bin
estimate. The three new majorant definitions are notation, not proofs.

Remaining: bound this explicit near/far sum at source scale, absorb all
errors and logarithmic losses uniformly, perform the local-to-global
large-values optimization, and prove the exponent/energy-region consumers.
The target remains
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k), k ≥ 1.
Only then can k=13 enter Add-est (iii) and the other remaining optimizations.
EPZAE-19, 33, 36, 37 and the full EPZAE-00–41 goal remain open. The distinct
endpoint-two transfer, sharp source-form Atkinson bridge, exponent-pair,
density, and release obligations are unchanged.

All six modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Seventeen new public theorems have
named audits; 23 regressions cover their exact signatures, the n=1 term at
k=13, zero interval width, the literal ceiling, and both schedule branches.
Both that BAT and `run_lake_build.bat` remain required evaluation gates.
This is finite-scale proof progress, not completion of Jutila or another
Add-est clause.

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 361 package files, 372
integrity-scanned Lean files, and 3,564 audited declarations (3,559 discovered
target theorems plus five imported contracts). All 17 new named audits and
23 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All seventeen
recorded source/build hashes are unchanged after the gates, including the
original counterexample. Repository scans find no forbidden proof terms;
the twelve raw postulate-pattern matches are the previously reviewed ten
comments and two rational structure fields. Git `diff --check` passes.
Exact commands, logs, hashes, and the corrected initial scan failure are
recorded in the Reproduction Manifest. These checks certify the stated
finite-scale scope, not the remaining Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

### Commands and terminal evidence

From the target folder, and then from the foundation, respectively:

```powershell
$env:ELAN_HOME = 'C:\Users\Naraphim\.elan'
cmd /c run_tao_trudgian_yang_build.bat --no-pause
# From E:\Lean\Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Target: terminal exit 0, LEAN VERIFICATION PASS, 9,216 default-build jobs.
All 28 required files, 20 pinned sources, 12 frozen ANTEDB files, exact
production coverage, deterministic regeneration, regressions, integrity
scans, and transitive audits passed.
Log relative to this folder: `logs/tao-trudgian-yang-build-20260921-064926-2dea053d.log`.
Final log SHA256: `6f51f46bc294535c45557fa33bae60c62e2c16797d0cafd3e3cdda7051de4ec0`.

Foundation: terminal exit 0, PASS, 8,857 default-build jobs. All six stages
have exitCode=0, warnings=0, tacticInfo=0, linterFailures=0, passed=true;
failures=[]. Classification remains 301 root-graph modules, two explicit
regressions, zero excluded or unclassified modules. The audit covers
7,636 explicit public declarations and 14,290 discovered theorems.
Log relative to the foundation: `logs/foundation_freeze_20260921_065150.log`.
Final log SHA256: `25830e1e13caaa5974116b30d44d0cc6846d36d160eda97b18c4195aa4d9de4d`.
JSON manifest: `logs/foundation_freeze_20260921_065150.json`.
JSON SHA256: `a3eb38e1ea7238243ef2a8e670feb7d0dcc5f1038180a68a3eec34036ee481e3`.
Verifier SHA256 remains `0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

All seventeen new public names were checked in the terminal target log;
none is missing. Their only axioms are the permitted standard
`propext`, `Classical.choice`, and `Quot.sound`. The 17 exact-signature
tests and six literal boundary/schedule regressions compile cleanly.

Initial verification honestly failed: both first BAT runs rejected a
comment line beginning with the postulate keyword in
`JutilaPrefixMoments.lean:8`. The prose was reworded; neither scanner was
changed. Those historical failures are retained in
`logs/tao-trudgian-yang-build-20260921-064836-a2a86209.log` and the
foundation's `logs/foundation_freeze_20260921_064838.log`. Both complete
reruns above test the corrected source and reached terminal exit 0.

Focused elaboration also required ordinary finite-sum/power rewrites and
style-warning fixes. The final hybrid-pattern theorem has a local
400,000-heartbeat elaboration budget after the default budget timed out.
This changes computation time only; no theorem domain, proof obligation,
linter, inventory, or audit gate was weakened. No warning is suppressed.

Post-gate hashes, reread from the actual files, are unchanged from the
pre-terminal snapshot (paths relative to this folder unless absolute):

```text
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
e9bc7dd30fa2e5953d41c454a7473bdee25bee186a56d14b190ff9d552947a6b  Extension/TaoTrudgianYang2025.lean
e9417cc5f9141998dd7dc98d744610f95d0b399b195d0fe96f6802bb7f5de255  Extension/TaoTrudgianYang2025/Audit.lean
9276ebbbb794d4576d1bec62f2a6aa7eec81b2027615463feb9b56e4578939b3  Extension/TaoTrudgianYang2025/SemanticRegression.lean
437b66be410eb50d26e1e57363ac724ffeb990920edfcf358f3cf45b7167f2c5  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

Semantic gate: `jutila_hybrid_pattern_bound` consumes an actual
`LargeValuePattern`, constructs its smoothed and spaced subfamily, then
uses the powered Gram alternative and the exact off-diagonal bin
partition. Near bins consume the native square-root nonzero-tail theorem
and separate zero-mode decay. Occupied far bins obtain their reflection
conditions from separation, use the literal ceiling dual length, and
consume complete reflection and the uniform prefix integral theorem.
The latter uses arbitrary-coefficient powering, uniform divisor bounds,
the actual weighted Heath--Brown theorem, and interval Jensen. None of
these numerical bounds appears as a theorem hypothesis.

The current green nodes JPF and JHB name only these proved finite-scale
conclusions. JRF remains OPEN for source-scale error/loss absorption,
local-to-global optimization, and the actual LV exponent. No additional
Add-est clause or whole-checklist item is marked complete.

The final working tree has 141 reported entries, all confined to this
target folder; earlier work is preserved. No staging, commit, push, source
pin change, or goal-status reduction was performed.

## Jutila physical-scale smoothing and uniform pattern bounds — verified history

The printed Lemma 62 counterexample remains byte-for-byte unchanged. The
authorized independent cardinality and energy witnesses remain the powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Seven new production modules advance EPZAE-19: `JutilaDualScales`,
`JutilaPhysicalMain`, `JutilaPhysicalPatterns`, `JutilaSmoothingErrors`,
`JutilaSmoothingProfile`, `JutilaSmoothingLosses`, and
`JutilaSmoothedPatterns`.

`jutila_reflection_main_core_le` cancels each actual powered dual length
against its own displacement denominator before imposing the common cap.
`jutila_physical_pattern_bound` consumes the complete near/far pattern
theorem, retaining all main terms, logarithmic/divisor costs, and sharp
reflection errors. The common ceiling is used only for losses.

Native smoothing uses H=max(1,ceil(T^θ)) and derivative order
q=max(2,ceil(4/θ)+1). The zero mode and all three reflection errors are
controlled by proved native estimates, not assumed numerical certificates.
The smoothing-error bridge explicitly requires Q≤2T. The complete profile
is uniformly O(T^(2θ)); its full powered cost, including the bin count,
is O(T^((16k+3)θ)). The actual thinning cost is at most 108 T^θ.

`jutila_smoothed_pattern_bound` chooses positive B and T₀≥2 before every
actual `LargeValuePattern`. For scale≥30, V>1, T≥T₀, and **N≤T**, it
constructs a subset W of the reflected ordinates and Q with N/2≤Q≤2N.
Writing R=|W| and V'=(V−1)/3, the original count is at most B T^ν R,
W is 1-separated in the actual height interval, and either

- R (V')² ≤ 2Q²; or
- R² (V')^(4k) ≤ B T^ν (2Q)^(2k)
  (R²Q^k + R T^k + R^(5/4) T^(1/2) Q^k).

This holds for every k≥1 and ν>0. The choice of θ absorbs both losses
without changing the physical height or assuming the desired LV estimate.
The N≤T restriction derives Q≤2T and is not silently removed.

Remaining: solve the cardinality recurrence with its value threshold,
cover the complementary short-height range, perform the local-to-global
optimization, and prove the actual uniform LV and energy-region consumers.
The unchanged target is
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k).
Only then can k=13 enter Add-est (iii) and the other seven-clause work.
EPZAE-19, 33, 36, 37 and the whole EPZAE-00–41 goal remain open. The
distinct endpoint-two transfer, sharp source-form Atkinson, exponent-pair,
density and release obligations are unchanged.

All seven modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Twenty-one new public theorems
have named audits. Twenty-seven regressions cover every exact signature
plus the actual k=13 source-pattern consumer, its three literal terms,
the empty-family boundary, ceiling padding, genuine zero-mode decay,
and the derived thinning cost. Both that BAT and `run_lake_build.bat`
remain mandatory; build integrity is separate from source completeness.

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 368 package files, 379
integrity-scanned Lean files, and 3,619 audited declarations (3,614 discovered
target theorems plus five imported contracts). All 21 new named audits and
27 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All twenty-four
recorded source/build hashes are unchanged after the gates, including the
original counterexample and all ten earlier Jutila modules. Repository
scans find no forbidden proof terms; the twelve raw postulate-pattern
matches are the previously reviewed ten comments and two rational
structure fields. Git `diff --check` passes. Exact commands, logs and hashes
are recorded in the Reproduction Manifest. These checks certify the
stated finite-pattern scope, not the final Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

### Reproduction evidence for physical-scale smoothing

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target completed 9,223 build
jobs and all 27 new semantic regressions. Its inventory contains 28
required files, 20 verified pinned files, 12 verified frozen files, 368
Lean package files, and 379 integrity-scanned Lean files. Deterministic
certificate regeneration passed. All 3,619 audited declarations (3,614
discovered target theorems and five imported contracts) have only permitted
dependencies; all 21 new named theorem audits appear in the completed log.

Target log:
`logs/tao-trudgian-yang-build-20260921-072909-ba548c42.log`
SHA256: `2cd94d6d89303c5cde857abb5a90e8e52d96ca087c7e74520fc14b7eace83f24`.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and all 14,290 discovered nonprivate
theorems. Classification remains 301 root modules, two retained
regressions, zero excluded and zero unclassified. All stages report
exitCode=0, warnings=0, tacticInfo=0, linterFailures=0; failures=[].

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_072921.log`
SHA256: `7a44641ff684dcf35f24818d90cafedf00f8f2c2d9dfbfd32bf5f9d42fb686a4`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_072921.json`
SHA256: `7c78da854e671e642fecbe14ffdcd2adc05866410d4af83cb61ca2452ffa38fe`.

Verifier SHA256 remains
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
No final log contains a Lean error, warning, tactic suggestion, or linter
failure. The repository-wide placeholder and unsafe-bypass scans have
no matches. The twelve raw postulate-pattern matches are ten comments
and two rational `constant` structure fields, not postulated declarations.
Both runners' integrity gates pass; no scan was weakened.

The twenty-four post-gate hashes below match the pre-gate hashes. They
include every new source module, all ten preceding Jutila modules,
integration/audits, exact runner inventory, both BATs, and the preserved
counterexample.

```text
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
d4a901d769fbc2978a6426ec9d88c8957988804817845ae1ff32c536d73098bf  Extension/TaoTrudgianYang2025.lean
7b575eacf2918fdaa0a7db449fa38f89be3c606c34fa067f9f94d5fd7fd22b33  Extension/TaoTrudgianYang2025/Audit.lean
58bc670d5fe2516c61e8d6bf769ce9a760e1f5f747e13183c3f52a9ae400e6c3  Extension/TaoTrudgianYang2025/SemanticRegression.lean
c91ee25a640609ce8d1f8e7950d7250a0604af7a9a2ce244df82dd40d7db08dc  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

Semantic gate: `jutila_smoothed_pattern_bound` consumes the actual
`LargeValuePattern`, obtains its real spaced subfamily from the prior
Gram/reflection entry, cancels the actual dual scales, bounds near and
far errors, and absorbs all variable losses. Its constants precede the
pattern, and its N≤T condition is explicit. No Jutila estimate or loss
certificate is a premise. JPS is green only for this statement; JRF and
EPZAE-19 remain OPEN until recurrence solution, short-height coverage,
local/global optimization and the exact LV exponent are proved.

The gate logs record HEAD
`bda1d96a12d7eddca30079b59c6dde23a82e90e0` with a dirty checkout.
During documentation finalization an external commit advanced HEAD to
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4` (`Progress Update`).
The agent did not stage, commit, push, or revert that change. The verified
source/runner hashes are the reproducibility identity; the final
documentation adds the completed gate evidence on top of that commit.
No source pin, theorem contract, or whole-goal status was changed.

## Full Jutila theorem and corrected energy-region constraints — verified history

The complete source `jutila-lvt` inequality is now proved, not just its
physical-pattern precursor. For every positive integer k, fixed
1/2 ≤ σ ≤ 1 and τ ≥ 0, `jutila_largeValueBound` gives the uniform
epsilon--delta bound on actual large-value patterns with exponent

```text
max(2-2σ, τ+4-2/k-(6-2/k)σ, τ+(6-8σ)k).
```

`largeValueExponent_le_jutila` gives the paper's least-exponent
conclusion; `zetaLargeValueExponent_le_jutila` gives the valid zeta
specialization. No cutoff, moment estimate, physical absorption threshold,
or assumed cardinality bound remains in these source-facing signatures.

### Mathematical dependency and semantic checks

`jutila_local_pattern_cardinality` consumes both alternatives returned by
the proved `jutila_smoothed_pattern_bound`. It solves the actual Gram
recurrence, pays the thinning loss, and retains the endpoint correction
(V−1)/3. `jutila_local_cardinality_uniform` exposes the three physical
terms N²/(V−1)², T^k N^(2k)/(V−1)^(4k), and
T N^(6k)/(V−1)^(8k), with one arbitrary epsilon loss.

`LargeValuePattern.localized` constructs genuine floor-bin patterns:
coefficients, support, threshold and N are unchanged. Their cards sum to
the original card. `jutila_subdivided_cardinality_native` applies the
local theorem to these objects and uses the already constructed smooth
cutoff. The original T is unrestricted, including T<N and a chosen
local height larger than T.

`jutila_largeValueBound_of_local_exponent` chooses the actual local
height L=N^ℓ, derives the absorption threshold from σ>3/4, and removes
V−1 using the actual exponent windows. Constants and the positive window
radius precede every pattern. The optimized ℓ is
min((4−2/k)σ−(2−2/k), (8k−2)σ−6k+2).
`jutila_optimization_identity` identifies the exact three-term maximum.
The σ≤3/4 range uses the proved obvious bound; ℓ<1 uses the proved
`meanSquare_largeValueBound`, derived from the actual finite MHH
estimate with height padding removed. Thus no short-height gap remains.

`InLargeValueEnergyRegion.rho_le_of_largeValueBound` compares the
uniform bound with actual feasible-region witnesses.
`InCardinalityEnergyRegion.jutila_cardinality_powered` consumes the
cardinality branch of `correctedCardinalityEnergyPowering`, giving
ρ/q ≤ jutilaLargeValueExponent k σ (τ/q) for q≥1.
The literal k=13 consumer gives the two affine terms
τ/q+50/13−76σ/13 and τ/q+78−104σ needed for Add-est (iii).
Different powering applications remain independent. No relation between
either fifth coordinate and s/q is asserted.

### Scope, preservation, and continuation

The full Jutila subnode of EPZAE-19 is DONE. EPZAE-18 and EPZAE-19 as whole
checklist items remain OPEN: the other elementary/classical interfaces
still require their own acceptance tests, including the standalone
uniform Huxley API. EPZAE-36/37 still have Add-est (iii)--(ix) OPEN;
clauses (i)--(ii), corrected two-witness powering, and the full
Heath--Brown energy relation remain proved. The endpoint-two transfer,
sharp Atkinson source-form bridge, exponent-pair/density work, and full
EPZAE-00--41 release contract remain in scope.

The printed Lemma 62 counterexample is preserved byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the paper nor the advertised Add-est statements are changed.

Eleven new production modules are root-imported and included in the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`JutilaRecurrence`, `JutilaLocalCardinality`, `JutilaLocalAlgebra`,
`JutilaLocalUniform`, `LargeValueSubdivision`, `JutilaSubdivision`,
`JutilaPowerWindows`, `JutilaWindowBound`, `ClassicalMeanSquareBound`,
`JutilaLargeValues`, and `JutilaEnergyRegions`.
All 32 new public theorems have named dependency audits. There are
43 new semantic regressions: 32 exact signatures plus 11 localization,
endpoint, short-height, uniform-pattern and corrected-witness consumers.
Both human-facing BATs remain mandatory and must be updated as needed.

### Completed verification

Both mandatory BAT processes terminated with exit 0 and PASS on
21 September 2026. The target ran 9,234 build jobs, all 43 new semantic
regressions, deterministic regeneration, the exact 379-file package
inventory, and the 390-file integrity scan. All 3,669 audited declarations
(3,664 discovered target theorems plus five imported contracts) have
permitted dependencies; all 32 new named theorem audits are present.

The foundation's six stages also passed: 8,857 root build jobs, 7,636
explicit public declarations, and 14,290 discovered nonprivate theorems.
Its classification remains 301 root modules, two regressions, zero
excluded and zero unclassified. Both final gates have zero Lean errors,
warnings, tactic suggestions or linter failures; there are no failed
stages. Only standard Lean/Mathlib logical axioms occur.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
Git `diff --check` passes; Git's LF-to-CRLF notices are file-conversion
notices, not Lean diagnostics. No scan or warning policy was weakened.
All 35 source/integration/runner hashes match across the gates, including
the original counterexample. Exact commands, log paths, hashes and
checkout identity are in the Reproduction Manifest. This verifies the
full Jutila source theorem and the stated consumers, not the seven
remaining Add-est clauses or the unchanged whole-proof goal.

### Reproduction evidence for the full Jutila theorem

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target's final status is
`LEAN VERIFICATION PASS`; the foundation's final status is `PASS`.
No failed stages remain. The 32 named new theorem audits were checked
individually against the complete target log; all appear and use only
`propext`, `Classical.choice`, and `Quot.sound`.
The target retains 28 required files, 20 pinned files and 12 frozen
ANTEDB files, all verified. Deterministic certificate regeneration passes.

Target log: `logs/tao-trudgian-yang-build-20260921-081559-a878375b.log`
SHA256: `6b2a0cf3ca40570ff4f707cb8fbfae3a041377d1496905cfffdb037c374b0b72`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_081610.log`
SHA256: `d2429c452777ec64d45ae0ea589567c329a505b1942f8bc96041477d62ad683f`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_081610.json`
SHA256: `18dfc9288a1cb215c37184c5539622251043bf1dda3d2fc237157fb234d137f0`.

The foundation JSON records six passing stages with exitCode=0,
warnings=0, tacticInfo=0 and linterFailures=0, and failures=[].
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The recorded checkout is branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, dirty.
No stage, commit, push, reset, deletion, source-pin change or unrelated
edit was performed by the agent.

The following 35 file hashes were captured while the gates ran and
rechecked unchanged after both terminal results. Documentation was then
synchronized; it does not change the verified proof/build inventory.

```text
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
c697d5ba9ff40e89505a07579d4582340baf2f5e0d01c44850ce7b078dbcffa8  Extension/TaoTrudgianYang2025.lean
4cc0b585e50dde9eebede701812a7e529a435a0d0b8682a3f91b53641d13ad3f  Extension/TaoTrudgianYang2025/Audit.lean
b93d66dd95acac09344ac5ee402df0827234d5189f4b4cc98453daf474906a63  Extension/TaoTrudgianYang2025/SemanticRegression.lean
e39ad23f8c710326780253f304da15d423f1172447eb24fc891baadae535cce2  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Add-est (iii) from corrected powering — verified history

The complete third printed Add-est clause is now proved on
173/229 ≤ σ ≤ 443/586. `NewAdditiveEnergy.lean` exports
`add_est_iii`, `add_est_iii_bound`, and
`add_est_iii_zero_energy`. Their exact source rate is

```text
max((173−270σ)/(16(93−125σ)),
    (653−890σ)/(10(93−125σ)),
    (1151−1190σ)/(20(15σ−2))).
```

The first theorem bounds A*(σ)(1−σ); the last states the fully quantified
epsilon--delta estimate for `zeroAdditiveEnergy (σ−δ) T`. This is the
actual unit-tolerance energy of the paper's zeros with analytic
multiplicity, not a numerical certificate or an assumed energy estimate.
No large-value, moment, powering, or transfer theorem remains an input.

### Source-to-consumer checks

`InCardinalityEnergyRegion.energyClauseThree_cardinality_caps`
applies the proved k=13 Jutila theorem to separate corrected cardinality
witnesses at q and q+1, with q=2 or 3 linked to the original height.
The companion witness gives ρ/q ≤ 3−3σ. The actual Guth--Maynard
consumer supplies the other cardinality cap.

`InCardinalityEnergyRegion.energyClauseThree_general` consumes
those caps and the independent corrected energy witness: power q at
local height at least 6/5, and power q−1 below 6/5. The nine-branch
Heath--Brown relation is used only through its proved monotonicity in
cardinality. No fifth coordinate is scaled or identified.

The 67 closed-interval rational certificates cover both sigma ranges
split at 241/319, all three short-height pieces, both tall-height
pieces, and the nine short-zeta branches. The first two printed fractions
are explicitly normalized by reversing numerator and denominator signs;
`energyClauseThreeRate_eq_printed` proves the exact displayed formula.
The 4359/5770 equality of the first two rates is regression-checked.

`energyClauseThree_short_zeta` supplies the entire [1,2] range:
actual cancellation below 3/2, then the proved dyadic twelfth moment and
the actual Heath--Brown relation on [3/2,2]. Thus
`energyClauseThree` uses the already proved endpoint-one transfer,
with both general [2,4] and short-zeta hypotheses derived. It does not
assume or complete the independent source endpoint-two corollary.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseThreeCaps`, `EnergyClauseThreeRates`,
`EnergyClauseThreeLowCertificates`, `EnergyClauseThreeHighCertificates`,
`EnergyClauseThreeTallCertificates`, `EnergyClauseThreeBranches`,
`EnergyClauseThreeGeneral`, `EnergyClauseThreeZetaCertificates`, and
`EnergyClauseThree`. The existing public `NewAdditiveEnergy` module
now exports clauses (i)--(iii). All 89 new public theorems have named
audits; 103 new regressions include every exact signature, both closed
sigma endpoints, height transitions, the rate crossover and actual
corrected-witness/region consumers.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The archived paper and all advertised outputs remain frozen.

EPZAE-36/37 now have clauses (i)--(iii) DONE and (iv)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
EPZAE-33's endpoint-two corollary, other classical inputs, the sharp
Atkinson source-form bridge, exponent-pair/density outputs, and every
remaining EPZAE-00--41 acceptance condition stay in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,243 build jobs and all 103 new regressions.
Its complete inventory covers 388 package files and 399 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,780 audited declarations (3,775 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 45 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete third source clause and its real consumers,
not the other six clauses or the whole EPZAE-00--41 goal.

### Reproduction evidence for Add-est (iii)

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target reports
`LEAN VERIFICATION PASS`; the foundation reports `PASS`.
No failed stage or Lean diagnostic remains. The 89 new named public
audits all occur in the complete target log and contain only
`propext`, `Classical.choice`, and `Quot.sound`.
There remain 28 required project files, 20 verified pinned files and
12 verified frozen ANTEDB files. Deterministic regeneration passes.

Target log:
`logs/tao-trudgian-yang-build-20260921-084022-13c08289.log`
SHA256: `8b2d07a9efc32f5f0d2bc711562da0f2f47152e0117b37c8b503bc1d6225e151`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_084034.log`
SHA256: `7faff7ca0f0241d97c5c4c0fc1909b131a3ad417bd37b860f22d8bf61b709961`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_084034.json`
SHA256: `136892c28bd4e72ccaf5cb2febb1433467323e3625f0b5b3947831a492254119`.

The foundation JSON records failures=[] and six passing stages, each
with exitCode=0, warnings=0, tacticInfo=0 and linterFailures=0.
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs use branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, with a dirty checkout.
Pre-existing work was preserved; the agent did not stage, commit, push,
reset, delete files or change any dependency/source pin.

The 45 hashes below match the pre-gate capture. They include all nine
new modules, the modified public output module, every preceding Jutila
module, integration/audits, both BATs, the exact inventory and the
counterexample. Documentation was synchronized after verification.

```text
edb6cd3a7387940341eb7c5c88cc207f3716b7a16699eabeea91431310462f1e  Extension/TaoTrudgianYang2025/EnergyClauseThreeCaps.lean
062cbc2116481c329c9f9e62c628efc60e72d23ed67ebb4d2d2c9b4b3483084c  Extension/TaoTrudgianYang2025/EnergyClauseThreeRates.lean
0e54c91931bb75b82d71abbee73895035afb23e6255e892c5719b504a5ad99ec  Extension/TaoTrudgianYang2025/EnergyClauseThreeLowCertificates.lean
986396e400a2f7d66f1f058693a157d1f0b734c2687fd72b4b4f02c3c643f012  Extension/TaoTrudgianYang2025/EnergyClauseThreeHighCertificates.lean
7b40f65fad7541b5725721772235259a25703b4be554346adbe6d6001d33dddf  Extension/TaoTrudgianYang2025/EnergyClauseThreeTallCertificates.lean
225b2016b0e825a3e4f381b7496f2382905ed388d4a5b56e8362cda447bda13d  Extension/TaoTrudgianYang2025/EnergyClauseThreeBranches.lean
ccdbfef46f5b3a390c669f4aa70823b0c0d7e8b7db0041215eebb208c591bd62  Extension/TaoTrudgianYang2025/EnergyClauseThreeGeneral.lean
4045537febed90f465e20ef9838b364f98dec86dc49e4b9f2a5dab9b3c493085  Extension/TaoTrudgianYang2025/EnergyClauseThreeZetaCertificates.lean
438dcad2ac3de3e69dd8d08376d53c116f9b7c64ea70dc72f2de5b48504dbb0a  Extension/TaoTrudgianYang2025/EnergyClauseThree.lean
0b1db12a902fb2af35b1395ae278cda917ef5e937ba81c2708c57e3ec131f5f4  Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
fddfa8175e3231ed0632a45fc22774ac21602a99d43eb21b0e953edbab123dc2  Extension/TaoTrudgianYang2025.lean
1b0dfd67f213e788c01d1d8797290fbe11c2dd0ca0a17b493a7ec8bfe79c528b  Extension/TaoTrudgianYang2025/Audit.lean
e84890f04c6a49cbfc5ab3369a089f80ff6a2a31a7045c8cfa1beb749ec17e08  Extension/TaoTrudgianYang2025/SemanticRegression.lean
6867f0f8ee34d27c2f9d9dfc62633de91e1fe78dc3103f8928305deb6d50feee  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Add-est (iv) from corrected powering — verified history

The complete fourth printed Add-est clause is now proved on the exact
closed interval 443/586 ≤ σ ≤ 373/493. The public
`NewAdditiveEnergy` module exports `add_est_iv`,
`add_est_iv_bound`, and `add_est_iv_zero_energy`, with rate

```text
max((593−810σ)/(5(171−230σ)),
    4(266−275σ)/(5(55σ−7))).
```

The first public theorem bounds A*(σ)(1−σ). The final consumer gives the
uniform epsilon--delta estimate for the actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height
and with the paper's unit tolerance and analytic zero multiplicities.
No analytic, powering, moment or transfer theorem is accepted as input.

### Source-to-consumer checks

`jutila_twelve_formula` specializes the proved full Jutila theorem to
the literal k=12 maximum. The actual-region consumer
`InCardinalityEnergyRegion.energyClauseFour_cardinality_caps`
applies it to separate corrected cardinality witnesses at q and q+1.
Here q=2 or 3 is chosen from the original τ∈[2,4]; τ/q∈[1,3/2]
and τ/(q+1)≤1 are derived. The companion witness gives
ρ/q≤3−3σ, and the actual Guth--Maynard bridge gives the second cap.

`InCardinalityEnergyRegion.energyClauseFour_general` then consumes
the independent corrected energy witness at q when τ/q≥6/5, or
at q−1 below 6/5. The sigma split is 409/541. All nine Heath--Brown
branches and all three short-height pieces are checked. The 67 exact
closed-interval certificates also cover both tall-height pieces and
all nine short-zeta branches. Numerical exploration is not proof evidence.

`energyClauseFourRate_eq_printed` proves equality with the printed
fractions after explicitly reversing both signs in the first fraction.
Both the Jutila affine-term equality and the two-rate equality at
409/541 are regression-checked, along with denominator signs and every
shared domain endpoint.

`energyClauseFour_short_zeta` supplies all of [1,2]: actual
cancellation below 3/2, and the proved twelfth moment plus the actual
Heath--Brown energy relation on [3/2,2]. `energyClauseFour` uses
the proved endpoint-one transfer with both required energy ranges
derived. The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new production modules are root-imported and covered by the exact
PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFourCaps`, `EnergyClauseFourRates`,
`EnergyClauseFourLowCertificates`, `EnergyClauseFourHighCertificates`,
`EnergyClauseFourTallCertificates`, `EnergyClauseFourBranches`,
`EnergyClauseFourGeneral`, `EnergyClauseFourZetaCertificates`, and
`EnergyClauseFour`. The existing public output module now exports
clauses (i)--(iv). All 89 new public theorems have named audits.
There are 104 new regressions: 89 exact signatures and 15 endpoint,
split, sign, height-transition and actual independent-witness consumers.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the original paper nor any advertised output was changed.
No powered fifth-coordinate bound is reintroduced.

EPZAE-36/37 now have clauses (i)--(iv) DONE and (v)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
The independent endpoint-two transfer, other classical inputs, the
sharp Atkinson source-form bridge, exponent-pair/density outputs, and
all remaining EPZAE-00--41 requirements remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,252 build jobs and all 104 new regressions.
Its complete inventory covers 397 package files and 408 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,888 audited declarations (3,883 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 54 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fourth source clause and its real consumers,
not the other five clauses or the whole EPZAE-00--41 goal.

### Reproduction evidence for Add-est (iv)

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target reports
`LEAN VERIFICATION PASS`; the foundation reports `PASS`.
No failed stage or Lean diagnostic remains. The 89 new named public
audits all occur in the complete target log and contain only
`propext`, `Classical.choice`, and `Quot.sound`.
There remain 28 required project files, 20 verified pinned files and
12 verified frozen ANTEDB files. Deterministic regeneration passes.

Target log:
`logs/tao-trudgian-yang-build-20260921-085922-6f021da2.log`
SHA256: `011f38268c482757e19822a6abefe653aceb61f6c354b678057d931948157369`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_085933.log`
SHA256: `53ce0cbb84aad115d072b183088c09616a168d7dc0486d93f26b37e411646a8e`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_085933.json`
SHA256: `e66a483bf8107bd2dc27fa797e2962a2eb4a55ccd29956dc513076de73c4c8ce`.

The foundation JSON records failures=[] and six passing stages, each
with exitCode=0, warnings=0, tacticInfo=0 and linterFailures=0.
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs use branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, with a dirty checkout.
Pre-existing work was preserved; the agent did not stage, commit, push,
reset, delete files or change any dependency/source pin.

The 54 hashes below match the pre-gate capture. They include all nine
new clause-(iv) modules, the modified public output module, the preceding
clause-(iii) and Jutila modules, integration/audits, both BATs, the exact
inventory and the counterexample. Documentation was synchronized after
verification; no source or build-input hash changed.

Development note: overlapping focused builds briefly encountered a missing
intermediate olean while another build was recompiling it. A subsequent
non-overlapping focused build, the complete semantic regression, and both
mandatory BATs all passed. The final evidence above supersedes that
development artifact race and the subsequently repaired binder diagnostics.

```text
a999f1f29b949423e9d38dcb3776550c7a3ef81f233f346314c2502b053b242a  Extension/TaoTrudgianYang2025/EnergyClauseFourCaps.lean
0c619852b0341c309b578da6fbda0394663937ea0914bfcc0aa5832b959a8f49  Extension/TaoTrudgianYang2025/EnergyClauseFourRates.lean
3200d065b91abf97d267dafd74c6c1e0b2fa26a4a349d7db3f890e737ab279ac  Extension/TaoTrudgianYang2025/EnergyClauseFourLowCertificates.lean
4b7a0da9e667ebeeacb4f12cb967c1b5e3e9e22478430e39f537823040412d10  Extension/TaoTrudgianYang2025/EnergyClauseFourHighCertificates.lean
b159804ef5ff8b8d773ed4fb59c0b74d495956bc8564ec7eb9db8aa84ce4771e  Extension/TaoTrudgianYang2025/EnergyClauseFourTallCertificates.lean
d00d65d8545dfb5aa816f465cb3d2ba3a0965033dc5b21486cc00bbaaffee9ca  Extension/TaoTrudgianYang2025/EnergyClauseFourBranches.lean
e7fccaa1f25d560f35086f13f2e3017edf0bc245c00a7301b4b879e05c053335  Extension/TaoTrudgianYang2025/EnergyClauseFourGeneral.lean
ab7591ed2477873608d0518762942ff4a36e4f270fbcbfdfa4a0b70d67ca29a1  Extension/TaoTrudgianYang2025/EnergyClauseFourZetaCertificates.lean
6fd175c58dc3f11fb4c507f71f6eadd2e809295bf810f82ef56f265e3a0fbf37  Extension/TaoTrudgianYang2025/EnergyClauseFour.lean
edb6cd3a7387940341eb7c5c88cc207f3716b7a16699eabeea91431310462f1e  Extension/TaoTrudgianYang2025/EnergyClauseThreeCaps.lean
062cbc2116481c329c9f9e62c628efc60e72d23ed67ebb4d2d2c9b4b3483084c  Extension/TaoTrudgianYang2025/EnergyClauseThreeRates.lean
0e54c91931bb75b82d71abbee73895035afb23e6255e892c5719b504a5ad99ec  Extension/TaoTrudgianYang2025/EnergyClauseThreeLowCertificates.lean
986396e400a2f7d66f1f058693a157d1f0b734c2687fd72b4b4f02c3c643f012  Extension/TaoTrudgianYang2025/EnergyClauseThreeHighCertificates.lean
7b40f65fad7541b5725721772235259a25703b4be554346adbe6d6001d33dddf  Extension/TaoTrudgianYang2025/EnergyClauseThreeTallCertificates.lean
225b2016b0e825a3e4f381b7496f2382905ed388d4a5b56e8362cda447bda13d  Extension/TaoTrudgianYang2025/EnergyClauseThreeBranches.lean
ccdbfef46f5b3a390c669f4aa70823b0c0d7e8b7db0041215eebb208c591bd62  Extension/TaoTrudgianYang2025/EnergyClauseThreeGeneral.lean
4045537febed90f465e20ef9838b364f98dec86dc49e4b9f2a5dab9b3c493085  Extension/TaoTrudgianYang2025/EnergyClauseThreeZetaCertificates.lean
438dcad2ac3de3e69dd8d08376d53c116f9b7c64ea70dc72f2de5b48504dbb0a  Extension/TaoTrudgianYang2025/EnergyClauseThree.lean
00bc1f1d6d9520b5308a52a364b0f91e6430c9c9da20ec4d1eaa818f444ec4be  Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
8f426ddfd6ab0450231f6cee924d48f6c816740dea297d343e0758b7f9da99b0  Extension/TaoTrudgianYang2025.lean
7baed61cbfc765a11e2a164bd0cf5601f61040a0e89ca50034528ecadcc1fdac  Extension/TaoTrudgianYang2025/Audit.lean
d87df26b19a041aecd630f983be6f865c3fc804b207a8de90c600b725e980d49  Extension/TaoTrudgianYang2025/SemanticRegression.lean
db6eba849436cd91497909ed2bd6585126a2f06a55b8f5876aabcf53a5c5e8c5  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Add-est (v) from corrected powering — verified history

The complete fifth printed Add-est clause is now proved on the exact
closed interval 373/493 ≤ σ ≤ 103/136. `NewAdditiveEnergy` exports
`add_est_v`, `add_est_v_bound`, and `add_est_v_zero_energy`, with rate

```text
max((533−730σ)/(30(26−35σ)),
    3(26−33σ)/(85σ−62),
    (174−185σ)/(31σ+2)).
```

These give the literal A*(σ)(1−σ) inequality and the uniform
epsilon--delta bound for actual `zeroAdditiveEnergy (σ−δ) T`.
The constants precede the height; unit tolerance and analytic zero
multiplicities are preserved. There is no analytic, moment, powering
or transfer theorem parameter.

### Source-to-consumer checks

`jutila_eleven_formula` specializes the proved Jutila theorem to k=11.
`InCardinalityEnergyRegion.energyClauseFive_cardinality_caps`
consumes actual corrected cardinality witnesses at q and q+1, with
q=2 or 3 selected from the original height τ∈[2,4]. It derives
τ/q∈[1,3/2], the literal Jutila cap, the Guth--Maynard cap and
ρ/q≤3−3σ. No property of an independently chosen witness is
silently transferred to another point.

`InCardinalityEnergyRegion.energyClauseFive_general` applies the
independent energy witness at q−1 for short local height and at q
for the middle/tall ranges. The Jutila sigma split is 171/226.
For σ above that split the energy-power switch is
h(σ)=(31σ+2)/22, not the preceding clause's fixed 6/5 switch.
Both the ninth q−1 branch and the first q branch meet the third
printed rate at h(σ); the exact identities are regression-checked.

All 60 closed-interval rational certificates feed actual consumers:
27 low-sigma short certificates, 18 high-sigma short certificates,
two middle certificates, four tall certificates and nine short-zeta
certificates. Numerical exploration is not proof evidence.
`energyClauseFiveRate_eq_printed` proves the first fraction's
simultaneous sign reversal and preserves the complete three-rate maximum.

`energyClauseFive_short_zeta` supplies [1,2] explicitly: actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. `energyClauseFive` then consumes
the proved endpoint-one transfer, with both energy ranges derived.
The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFiveCaps`, `EnergyClauseFiveRates`,
`EnergyClauseFiveLowCertificates`, `EnergyClauseFiveHighCertificates`,
`EnergyClauseFiveTallCertificates`, `EnergyClauseFiveBranches`,
`EnergyClauseFiveGeneral`, `EnergyClauseFiveZetaCertificates`, and
`EnergyClauseFive`. All 85 new public theorems have named audits.
There are 104 new regressions: 85 exact signatures and 19 endpoint,
split, sign, witness-switch and actual independent-witness checks.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged: `EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the frozen source nor an advertised output was altered.
No scaled fifth-coordinate restriction is reintroduced.

Clauses (i)--(v) are proved; (vi)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 acceptance condition remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,261 build jobs and all 104 new regressions.
Its complete inventory covers 406 package files and 417 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,995 audited declarations (3,990 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 85
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 63 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fifth source clause and its real consumers,
not the other four clauses or the whole EPZAE-00--41 goal.

### Reproduction evidence for Add-est (v)

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target reports
`LEAN VERIFICATION PASS`; the foundation reports `PASS`.
No failed stage or Lean diagnostic remains. The 85 new named public
audits all occur in the complete target log and contain only
`propext`, `Classical.choice`, and `Quot.sound`.
There remain 28 required project files, 20 verified pinned files and
12 verified frozen ANTEDB files. Deterministic regeneration passes.

Target log:
`logs/tao-trudgian-yang-build-20260921-093137-47898e68.log`
SHA256: `bdf04daafbff87fc68a74851702172d8b68c70b9142e51937527e0d937c6915f`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_093138.log`
SHA256: `4003e9926b07e0e1546e23642f7ab20f1f8f5c8d6e13e4bf1459aec693f8898c`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_093138.json`
SHA256: `950b4377857bb1e3bfcfcea54da87e54442139f61a69e9e5a520951a45beaf77`.

The foundation JSON records failures=[] and six passing stages, each
with exitCode=0, warnings=0, tacticInfo=0 and linterFailures=0.
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs use branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, with a dirty checkout.
Pre-existing work was preserved; the agent did not stage, commit, push,
reset, delete files or change any dependency/source pin.

The 63 hashes below match the pre-gate capture. They include all nine
new clause-(v) modules, the modified public output module, the preceding
clause-(iii)/(iv) and Jutila development modules, integration/audits,
both BATs, the exact inventory and the preserved counterexample.
Documentation was synchronized after verification; no source or build-input
hash changed.

Development diagnostics were repaired before the final gates: a new helper
was renamed to avoid collision with an existing rational certificate;
the ninth-branch regression now unfolds its actual finite-vector entry;
and unnecessary tactic sequencing and one intentionally unused uniform
upper-domain binder were corrected without suppressing any linter.

```text
49c09bbbdec47fe9b484c2b4954fe43c2f4eb85e31d03f6c8e2aa0fe4d03bbd3  Extension/TaoTrudgianYang2025/EnergyClauseFiveCaps.lean
d38b5324f74b9e29c2d44e4759a3818aa1105906d69dc4029917b15b9e3e77df  Extension/TaoTrudgianYang2025/EnergyClauseFiveRates.lean
6e9e91ae491de3b6b05d829921c4cd30177552701abb01e6fbc888b25b14ba2c  Extension/TaoTrudgianYang2025/EnergyClauseFiveLowCertificates.lean
b247e0e46abba83164689db393217ad2f18aa38a2fefc4f5617d12e64ccebbd7  Extension/TaoTrudgianYang2025/EnergyClauseFiveHighCertificates.lean
f59c130039caee05786828d4fbf134e605421751d46984f350f4eb19dcf8028f  Extension/TaoTrudgianYang2025/EnergyClauseFiveTallCertificates.lean
a8b976a5b0349ad480b1d7be22862c2396508e11045ce079a3f73389625c44b2  Extension/TaoTrudgianYang2025/EnergyClauseFiveBranches.lean
b412a7c830d7bf87c7a6dad79c91201b724a234fc609a62f25fa98e27491a4fd  Extension/TaoTrudgianYang2025/EnergyClauseFiveGeneral.lean
09a45dcae23e902241c33f5bcbb5027b7576e592cb4e09e56128cb04f497d34a  Extension/TaoTrudgianYang2025/EnergyClauseFiveZetaCertificates.lean
8e80d4cf43262e1a04a84667e167486a4af99b64d44b51c551db94a984fee0bc  Extension/TaoTrudgianYang2025/EnergyClauseFive.lean
a999f1f29b949423e9d38dcb3776550c7a3ef81f233f346314c2502b053b242a  Extension/TaoTrudgianYang2025/EnergyClauseFourCaps.lean
0c619852b0341c309b578da6fbda0394663937ea0914bfcc0aa5832b959a8f49  Extension/TaoTrudgianYang2025/EnergyClauseFourRates.lean
3200d065b91abf97d267dafd74c6c1e0b2fa26a4a349d7db3f890e737ab279ac  Extension/TaoTrudgianYang2025/EnergyClauseFourLowCertificates.lean
4b7a0da9e667ebeeacb4f12cb967c1b5e3e9e22478430e39f537823040412d10  Extension/TaoTrudgianYang2025/EnergyClauseFourHighCertificates.lean
b159804ef5ff8b8d773ed4fb59c0b74d495956bc8564ec7eb9db8aa84ce4771e  Extension/TaoTrudgianYang2025/EnergyClauseFourTallCertificates.lean
d00d65d8545dfb5aa816f465cb3d2ba3a0965033dc5b21486cc00bbaaffee9ca  Extension/TaoTrudgianYang2025/EnergyClauseFourBranches.lean
e7fccaa1f25d560f35086f13f2e3017edf0bc245c00a7301b4b879e05c053335  Extension/TaoTrudgianYang2025/EnergyClauseFourGeneral.lean
ab7591ed2477873608d0518762942ff4a36e4f270fbcbfdfa4a0b70d67ca29a1  Extension/TaoTrudgianYang2025/EnergyClauseFourZetaCertificates.lean
6fd175c58dc3f11fb4c507f71f6eadd2e809295bf810f82ef56f265e3a0fbf37  Extension/TaoTrudgianYang2025/EnergyClauseFour.lean
edb6cd3a7387940341eb7c5c88cc207f3716b7a16699eabeea91431310462f1e  Extension/TaoTrudgianYang2025/EnergyClauseThreeCaps.lean
062cbc2116481c329c9f9e62c628efc60e72d23ed67ebb4d2d2c9b4b3483084c  Extension/TaoTrudgianYang2025/EnergyClauseThreeRates.lean
0e54c91931bb75b82d71abbee73895035afb23e6255e892c5719b504a5ad99ec  Extension/TaoTrudgianYang2025/EnergyClauseThreeLowCertificates.lean
986396e400a2f7d66f1f058693a157d1f0b734c2687fd72b4b4f02c3c643f012  Extension/TaoTrudgianYang2025/EnergyClauseThreeHighCertificates.lean
7b40f65fad7541b5725721772235259a25703b4be554346adbe6d6001d33dddf  Extension/TaoTrudgianYang2025/EnergyClauseThreeTallCertificates.lean
225b2016b0e825a3e4f381b7496f2382905ed388d4a5b56e8362cda447bda13d  Extension/TaoTrudgianYang2025/EnergyClauseThreeBranches.lean
ccdbfef46f5b3a390c669f4aa70823b0c0d7e8b7db0041215eebb208c591bd62  Extension/TaoTrudgianYang2025/EnergyClauseThreeGeneral.lean
4045537febed90f465e20ef9838b364f98dec86dc49e4b9f2a5dab9b3c493085  Extension/TaoTrudgianYang2025/EnergyClauseThreeZetaCertificates.lean
438dcad2ac3de3e69dd8d08376d53c116f9b7c64ea70dc72f2de5b48504dbb0a  Extension/TaoTrudgianYang2025/EnergyClauseThree.lean
258d8bb31f4943c2ea88216739360bf2565f0d6132228a785773ee78d3ca210c  Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
97a9cc7219d0695e5058bb31c3c84ba0a1ecf5ed46302af22caf056af04e0221  Extension/TaoTrudgianYang2025.lean
247e9ed9c1bc7adac0469185c912369168d5cde8651a9d06f4a8a718099774b0  Extension/TaoTrudgianYang2025/Audit.lean
17e199d47cc63a4496a72c0a7f75dfa0e8c0dd722a92c9191c88d917ef7e83ff  Extension/TaoTrudgianYang2025/SemanticRegression.lean
92e4d646e12747f91737ca172dc98d35ffdd55605238268cf0dd8c63e57894a0  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Add-est (vi) from corrected powering — verified history

The complete sixth printed Add-est clause is proved on the exact
closed interval 103/136 ≤ σ ≤ 42/55. `NewAdditiveEnergy` exports
`add_est_vi`, `add_est_vi_bound`, and `add_est_vi_zero_energy`,
with the unchanged rate

```text
max((72−91σ)/(7(11σ−8)),
    5(18−19σ)/(2(5σ+3))).
```

The proof also establishes the larger blueprint theorem
`imp-energy-bound4` on its full interval [664/877,31/40].
`energyClauseSix` gives the actual uniform zero-energy bound there;
`energyClauseSix_blueprint` gives the literal source-facing A*
maximum, with (1−σ) inside both printed denominators.
`energyClauseSixRate_div_eq_blueprint` proves that normalization.
The paper theorem is a proved interval restriction, not a weaker
replacement for the blueprint statement.

### Source-to-consumer checks

`jutila_ten_formula` specializes the full Jutila theorem to k=10.
`InCardinalityEnergyRegion.energyClauseSix_cardinality_caps`
derives the literal cap from the actual corrected cardinality witness
at q, and the companion cap ρ/q≤3−3σ from a separate witness at q+1.
It derives τ/q∈[1,3/2] from the original τ∈[2,4] with q=2 or 3.
The actual Guth--Maynard bridge supplies the tall-height cap.

`InCardinalityEnergyRegion.energyClauseSix_general` consumes the
independent energy witness at q−1 below the moving switch and at q
above it. The sigma split is 281/371; the two switches are
77σ/2−28 and (14σ+1)/10. Their agreement at the split and the
actual branch-balance identities are regression-checked.
The companion cardinality point is never identified with the
energy-preserving point, and no fifth coordinate is scaled.

All 53 exact closed-interval certificates feed the actual consumers:
18 low-sigma short, 18 high-sigma short, four middle, four tall and
nine short-zeta certificates. Numerical exploration is not evidence
for any theorem. The low switch realizes the first rate; the tall
cardinality crossover realizes the second rate.

`energyClauseSix_short_zeta` supplies all of [1,2], using actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. The final source theorem consumes
the proved endpoint-one transfer with both required energy ranges
derived. It does not assume the independent endpoint-two corollary.
The epsilon--delta public conclusion uses actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height,
unit tolerance, and analytic zero multiplicities.

### Inventory and remaining whole-proof scope

Nine production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseSixCaps`, `EnergyClauseSixRates`,
`EnergyClauseSixLowCertificates`, `EnergyClauseSixHighCertificates`,
`EnergyClauseSixTallCertificates`, `EnergyClauseSixBranches`,
`EnergyClauseSixGeneral`, `EnergyClauseSixZetaCertificates`, and
`EnergyClauseSix`. All 80 new public theorems have named audits.
There are 102 new regressions: 80 exact signatures and 22 source/paper
endpoint, normalization, switch, height and actual-witness checks.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The frozen paper and all advertised outputs are unchanged.

Clauses (i)--(vi) are proved; (vii)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,270 build jobs and all 102 new regressions.
Its complete inventory covers 415 package files and 426 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,094 audited declarations (4,089 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 80
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 72 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete sixth source clause, its real consumers and
the full blueprint `imp-energy-bound4`, not the other three clauses
or the whole EPZAE-00--41 goal.

### Reproduction evidence for Add-est (vi)

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target reports
`LEAN VERIFICATION PASS`; the foundation reports `PASS`.
No failed stage or Lean diagnostic remains. The 80 new named public
audits all occur in the complete target log and contain only
`propext`, `Classical.choice`, and `Quot.sound`.
There remain 28 required project files, 20 verified pinned files and
12 verified frozen ANTEDB files. Deterministic regeneration passes.

Target log:
`logs/tao-trudgian-yang-build-20260921-100129-10d4ef0d.log`
SHA256: `2b1c11f5f30a56ca93023049a551d5656882a49f9d001dd98bb413b147fd3169`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_100130.log`
SHA256: `857d4e73856f6ed01889ff76053d67353a9a9d4be0ecd9b2e005600ea9f93be1`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_100130.json`
SHA256: `070d41cd1b8e939a5dc2dbdf40467bdd179aee2338586921767b1bc86a2e576c`.

The foundation JSON records failures=[] and six passing stages, each
with exitCode=0, warnings=0, tacticInfo=0 and linterFailures=0.
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs use branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, with a dirty checkout.
Pre-existing work was preserved; the agent did not stage, commit, push,
reset, delete files or change any dependency/source pin.

The 72 hashes below match the pre-gate capture. They include all nine
new clause-(vi) modules, the modified public output module, the preceding
clause-(iii)--(v) and Jutila development modules, integration/audits,
both BATs, the exact inventory and the preserved counterexample.
Documentation was synchronized after verification; no source or build-input
hash changed.

Development diagnostics were repaired before the final gates. Intentionally
irrelevant uniform upper-domain binders are explicitly marked as such,
without linter suppression. The two low-sigma witness-switch regressions
use explicit cancellation of the positive denominator before ring
normalization. Their final focused regression build and both final BATs
pass; the earlier failed tactic attempts are not verification evidence.

```text
55e19ff096e48f03b0565f018244b30202e7d0daa45f31678695aa3e54e77d8d  Extension/TaoTrudgianYang2025/EnergyClauseSixCaps.lean
361873bdb4c7b4c9be0843c17c1fd2b57c6cb142ef13b7c2d36b34dee774e49c  Extension/TaoTrudgianYang2025/EnergyClauseSixRates.lean
8835b9f5ac0ef07dd32b7862fb2391854c47363fb2806744c77014b5798cc12f  Extension/TaoTrudgianYang2025/EnergyClauseSixLowCertificates.lean
0d0e34d9a849fd8f7db24e5f27b757ddd8348c863e313905604b0f90e63de84c  Extension/TaoTrudgianYang2025/EnergyClauseSixHighCertificates.lean
a68c4e2fe60d2ff15488aa2cb513b18e1151553a6da6f027dda94a29860ca7ae  Extension/TaoTrudgianYang2025/EnergyClauseSixTallCertificates.lean
7fa7ca9088494a341165e3d1457f6f20d586dcc787c7f4b1e00becfad493cc9a  Extension/TaoTrudgianYang2025/EnergyClauseSixBranches.lean
99531931ae33f9d0f1d5d0833bc654376f0854dcfa0426ff568ae0461f4eb902  Extension/TaoTrudgianYang2025/EnergyClauseSixGeneral.lean
a8ca0640d892bb50ae9d6d0761e7ab158db45f3833cfe706ecbc77cdb0056b21  Extension/TaoTrudgianYang2025/EnergyClauseSixZetaCertificates.lean
cc600e9cfa2972e96e3fabed5c80116d2f0604a3f117380cf6bea016d2482169  Extension/TaoTrudgianYang2025/EnergyClauseSix.lean
49c09bbbdec47fe9b484c2b4954fe43c2f4eb85e31d03f6c8e2aa0fe4d03bbd3  Extension/TaoTrudgianYang2025/EnergyClauseFiveCaps.lean
d38b5324f74b9e29c2d44e4759a3818aa1105906d69dc4029917b15b9e3e77df  Extension/TaoTrudgianYang2025/EnergyClauseFiveRates.lean
6e9e91ae491de3b6b05d829921c4cd30177552701abb01e6fbc888b25b14ba2c  Extension/TaoTrudgianYang2025/EnergyClauseFiveLowCertificates.lean
b247e0e46abba83164689db393217ad2f18aa38a2fefc4f5617d12e64ccebbd7  Extension/TaoTrudgianYang2025/EnergyClauseFiveHighCertificates.lean
f59c130039caee05786828d4fbf134e605421751d46984f350f4eb19dcf8028f  Extension/TaoTrudgianYang2025/EnergyClauseFiveTallCertificates.lean
a8b976a5b0349ad480b1d7be22862c2396508e11045ce079a3f73389625c44b2  Extension/TaoTrudgianYang2025/EnergyClauseFiveBranches.lean
b412a7c830d7bf87c7a6dad79c91201b724a234fc609a62f25fa98e27491a4fd  Extension/TaoTrudgianYang2025/EnergyClauseFiveGeneral.lean
09a45dcae23e902241c33f5bcbb5027b7576e592cb4e09e56128cb04f497d34a  Extension/TaoTrudgianYang2025/EnergyClauseFiveZetaCertificates.lean
8e80d4cf43262e1a04a84667e167486a4af99b64d44b51c551db94a984fee0bc  Extension/TaoTrudgianYang2025/EnergyClauseFive.lean
a999f1f29b949423e9d38dcb3776550c7a3ef81f233f346314c2502b053b242a  Extension/TaoTrudgianYang2025/EnergyClauseFourCaps.lean
0c619852b0341c309b578da6fbda0394663937ea0914bfcc0aa5832b959a8f49  Extension/TaoTrudgianYang2025/EnergyClauseFourRates.lean
3200d065b91abf97d267dafd74c6c1e0b2fa26a4a349d7db3f890e737ab279ac  Extension/TaoTrudgianYang2025/EnergyClauseFourLowCertificates.lean
4b7a0da9e667ebeeacb4f12cb967c1b5e3e9e22478430e39f537823040412d10  Extension/TaoTrudgianYang2025/EnergyClauseFourHighCertificates.lean
b159804ef5ff8b8d773ed4fb59c0b74d495956bc8564ec7eb9db8aa84ce4771e  Extension/TaoTrudgianYang2025/EnergyClauseFourTallCertificates.lean
d00d65d8545dfb5aa816f465cb3d2ba3a0965033dc5b21486cc00bbaaffee9ca  Extension/TaoTrudgianYang2025/EnergyClauseFourBranches.lean
e7fccaa1f25d560f35086f13f2e3017edf0bc245c00a7301b4b879e05c053335  Extension/TaoTrudgianYang2025/EnergyClauseFourGeneral.lean
ab7591ed2477873608d0518762942ff4a36e4f270fbcbfdfa4a0b70d67ca29a1  Extension/TaoTrudgianYang2025/EnergyClauseFourZetaCertificates.lean
6fd175c58dc3f11fb4c507f71f6eadd2e809295bf810f82ef56f265e3a0fbf37  Extension/TaoTrudgianYang2025/EnergyClauseFour.lean
edb6cd3a7387940341eb7c5c88cc207f3716b7a16699eabeea91431310462f1e  Extension/TaoTrudgianYang2025/EnergyClauseThreeCaps.lean
062cbc2116481c329c9f9e62c628efc60e72d23ed67ebb4d2d2c9b4b3483084c  Extension/TaoTrudgianYang2025/EnergyClauseThreeRates.lean
0e54c91931bb75b82d71abbee73895035afb23e6255e892c5719b504a5ad99ec  Extension/TaoTrudgianYang2025/EnergyClauseThreeLowCertificates.lean
986396e400a2f7d66f1f058693a157d1f0b734c2687fd72b4b4f02c3c643f012  Extension/TaoTrudgianYang2025/EnergyClauseThreeHighCertificates.lean
7b40f65fad7541b5725721772235259a25703b4be554346adbe6d6001d33dddf  Extension/TaoTrudgianYang2025/EnergyClauseThreeTallCertificates.lean
225b2016b0e825a3e4f381b7496f2382905ed388d4a5b56e8362cda447bda13d  Extension/TaoTrudgianYang2025/EnergyClauseThreeBranches.lean
ccdbfef46f5b3a390c669f4aa70823b0c0d7e8b7db0041215eebb208c591bd62  Extension/TaoTrudgianYang2025/EnergyClauseThreeGeneral.lean
4045537febed90f465e20ef9838b364f98dec86dc49e4b9f2a5dab9b3c493085  Extension/TaoTrudgianYang2025/EnergyClauseThreeZetaCertificates.lean
438dcad2ac3de3e69dd8d08376d53c116f9b7c64ea70dc72f2de5b48504dbb0a  Extension/TaoTrudgianYang2025/EnergyClauseThree.lean
a20b28628aeeadc548cc9dbc5afb793aeb604d7f15bcffe52b25a2541fed6baa  Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
a73428cedecef709c060aa1fc1b5f984e7b4eacd6aa6f54a8045dcb69a6d35f9  Extension/TaoTrudgianYang2025.lean
0a05828907b9f3a6ed35c7aaa0cc3956934f2e9e299f2751f35351a88f13c5ac  Extension/TaoTrudgianYang2025/Audit.lean
df62ed52d3708ae6c38a4dc701ab3ecd64ffcccf57fd1ede53d57d9737ba4173  Extension/TaoTrudgianYang2025/SemanticRegression.lean
4b39fe5a5ecbc148b3b431b3476d7c24ba22d1d0e5b62ce6fc193fcffcc80e56  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Add-est (vii) and (viii) from corrected powering — verified history

The exact seventh and eighth printed Add-est clauses are proved on
their full closed intervals. `NewAdditiveEnergy` exports
`add_est_vii`, `add_est_vii_bound`, `add_est_vii_zero_energy`,
`add_est_viii`, `add_est_viii_bound`, and
`add_est_viii_zero_energy`.

For [42/55,79/103], the unchanged rate for A*(σ)(1−σ) is

```text
max((18−19σ)/(6(15σ−11)), 3(18−19σ)/(4(4σ−1))).
```

For [79/103,84/109], it is

```text
max((18−19σ)/(2(37σ−27)), 5(18−19σ)/(2(13σ−3))).
```

`energyClauseSeven_blueprint` and `energyClauseEight_blueprint`
also give the literal full-source conclusions of `imp-energy-bound6`
and `imp-energy-bound7`, respectively. Their (1−σ) factors occur
inside both printed denominators, with proved normalization identities.
The public epsilon--delta conclusions use actual
`zeroAdditiveEnergy (σ−δ) T`, analytic zero multiplicities and unit
tolerance; constants and the positive sigma loss precede the height.

### Actual witnesses and complete interval consumers

The full Jutila theorem is specialized to k=6 for clause (vii) and
k=5 for clause (viii). The respective sigma splits are 97/127 and
33/43. Each `energyClauseSeven_cardinality_caps` /
`energyClauseEight_cardinality_caps` theorem derives both the literal
Jutila cap at q and the companion bound ρ/q≤3−3σ at q+1 from
actual corrected cardinality witnesses. The energy witness is separate.

For τ∈[2,4], the proved cover chooses q=2 or 3 and derives τ/q∈[1,3/2].
Below the diagonal-cardinality crossover, the proof consumes the actual
q−1 energy witness and all nine Heath--Brown branches. Above it, the
actual q energy witness supplies the two proved small-height branches.
The crossover pairs are 46σ−34 and (11σ−5)/3 for clause (vii), and
38σ−28 and (18σ−8)/5 for clause (viii). The companion-cap crossover
pairs are 45σ−33 and (8σ−2)/3, and 37σ−27 and (13σ−3)/5.
The second q-energy branch realizes the corresponding printed rate
at each companion crossover; exact identities are regression-checked.

Each clause has 35 kernel-checked interval certificates: nine low-sigma
short, nine high-sigma short, eight tall, and nine short-zeta certificates.
All feed actual region consumers and uniform bounds. The independent
power ratio is bounded at 2/3 only for branch 0 and at 1/2 for the other
eight branches; the sign-sensitive branch 2 has an explicit regression.
No fifth coordinate is scaled or identified across the witnesses.
Numerical exploration is not proof evidence.

For both clauses the full short-zeta range [1,2] is derived from actual
cancellation below 3/2 and the proved twelfth moment above it. The final
theorems consume the proved endpoint-one transfer with τ₀=2.
For clause (viii), this is a documented proof refactoring: the blueprint
uses a varying τ₀, whereas Lean derives all required bounds on [2,4]
and [1,2] directly. The exact source conclusion is unchanged; no
varying-height intermediate bound or endpoint-two corollary is assumed.

### Inventory and unchanged whole-proof scope

Eighteen production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`. Each
`EnergyClauseSeven` / `EnergyClauseEight` family contains `Caps`,
`Rates`, `LowCertificates`, `HighCertificates`, `TallCertificates`,
`Branches`, `General`, `ZetaCertificates`, and the final assembly.
All 122 new public theorems have named audits. There are 172 new
regressions: 122 exact signatures and 50 endpoint, normalization,
crossover, height and actual-witness checks.

The original counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The original paper and source pins are unchanged.

Clauses (i)--(viii) are proved; (ix) remains open. EPZAE-36/37 remain
unchecked as whole items. The independent endpoint-two transfer,
remaining classical inputs, sharp Atkinson source-form bridge,
exponent-pair/density outputs and every other unfinished EPZAE-00--41
requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,288 build jobs and all 172 new regressions.
Its complete inventory covers 433 package files and 444 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,249 audited declarations (4,244 discovered target theorems and five
imported contracts) have permitted dependencies; all 122 new named audits
were checked in the complete target log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 90 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete seventh and eighth paper clauses, their real
consumers and their full blueprint conclusions. Clause (ix) and all other
unfinished EPZAE-00--41 requirements remain in the unchanged active goal.

### Reproduction evidence for Add-est (vii) and (viii)

Commands:

```powershell
# In this target folder:
cmd /c run_tao_trudgian_yang_build.bat --no-pause

# In E:/Lean/Riemann Zeta:
cmd /c run_lake_build.bat --no-pause
```

Both processes terminated with exit 0. The target reports
`LEAN VERIFICATION PASS`; the foundation reports `PASS`.
No failed stage or Lean diagnostic remains. All 122 new named public
audits occur in the complete target log and contain only
`propext`, `Classical.choice`, and `Quot.sound`.
There remain 28 required project files, 20 verified pinned files and
12 verified frozen ANTEDB files. Deterministic regeneration passes.

Target log:
`logs/tao-trudgian-yang-build-20260921-102820-60f30e34.log`
SHA256: `a3c2d2cef6e9cdd926042424e05a6ae9a6070b5f1c830ea8b605e6825753177f`.

Foundation log:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_102820.log`
SHA256: `27bde36496f555b86079e47639ed81c25d3c7a53a02618e637134bd024fb8f03`.

Foundation JSON:
`E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_102820.json`
SHA256: `ba93889dc4f813691c66fa11ac2f16c3db7c2fc4661cf67df05dda04a4e0f718`.

The foundation JSON records failures=[] and six passing stages, each
with exitCode=0, warnings=0, tacticInfo=0 and linterFailures=0.
Verifier SHA256:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
Both runs use branch `main`, HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, with a dirty checkout.
Pre-existing work was preserved; the agent did not stage, commit, push,
reset, delete files or change any dependency/source pin.

The 90 hashes below match the pre-gate capture. They include all eighteen
new clause-(vii)/(viii) modules, the modified public output module,
preceding clause-(iii)--(vi) and Jutila development modules,
integration/audits, both BATs, the exact inventory and the counterexample.
Documentation was synchronized after verification; no source or build-input
hash changed.

Development diagnostics were repaired before final verification:
the sign-sensitive branch-2 certificate now uses the actual upper bound
a=1/2; intentionally irrelevant uniform upper-domain binders are explicitly
marked without linter suppression. Clause-(viii) endpoint regressions were
rewritten with their literal source coefficients, and a denominator
cancellation regression was made explicit. The final focused regression
build completed 9,288 jobs with no diagnostics. Earlier failed development
attempts are not verification evidence, and no source conclusion was weakened.

```text
30009425681111855fd37bf7225c630d794c77c49c9bda25ae6eecd91ff69951  Extension/TaoTrudgianYang2025/EnergyClauseEightCaps.lean
e0763b843cfb232540b7e3fe7c458ec2ad338c6a7c17f64368915aca626e4101  Extension/TaoTrudgianYang2025/EnergyClauseEightRates.lean
04ce205190ae950c8f3cc70d1e7038d607d8ec1adc5d5e76f0a41ba3473c2354  Extension/TaoTrudgianYang2025/EnergyClauseEightLowCertificates.lean
0de7555d2cf9cf77a6fb541a779a63ff06c0984e5006764b33b764fa4b0d931d  Extension/TaoTrudgianYang2025/EnergyClauseEightHighCertificates.lean
6970ce2f2ceb4766ac222f50e516c0dbacd9aede11a82507040352ead3cd1b62  Extension/TaoTrudgianYang2025/EnergyClauseEightTallCertificates.lean
ebf7d603b31ad41ea727c8cbbbd2d68e9275d9e3dd54cd05331fec05175588f7  Extension/TaoTrudgianYang2025/EnergyClauseEightBranches.lean
8c16cef366184391d2924ef696a3139d089c9e9a9d4040f7d3a4695ec3145962  Extension/TaoTrudgianYang2025/EnergyClauseEightGeneral.lean
7142ef2e77d4b1224e142fe2de94113f4f04dba6973cec09a2df3bece0ff412c  Extension/TaoTrudgianYang2025/EnergyClauseEightZetaCertificates.lean
6c5239185d504f40cdd8e660844d2fa9ec0ebef43cedb534dd45a0105131cb44  Extension/TaoTrudgianYang2025/EnergyClauseEight.lean
8dda496b5614c62df1caab57742165127212d62a3ad94cae1afbe452e6e3da55  Extension/TaoTrudgianYang2025/EnergyClauseSevenCaps.lean
3d438d78eb9b37263f8b1cd495ca1169f18b381c916ee17fb18fb9692aa29a95  Extension/TaoTrudgianYang2025/EnergyClauseSevenRates.lean
959256089cad05062e3bbeff43cb4f2f36dc8a9b27c0dfbe3fc99e0d1c871ae1  Extension/TaoTrudgianYang2025/EnergyClauseSevenLowCertificates.lean
fc0a200455c3794bdd87a043ddf6ff19bdc192a768d69680588012b1cacc2dcc  Extension/TaoTrudgianYang2025/EnergyClauseSevenHighCertificates.lean
07adf70d61d7fa54dcdc01b0632678ec52d8a548075546ec372662f433e9b1a0  Extension/TaoTrudgianYang2025/EnergyClauseSevenTallCertificates.lean
e2c6bda901a34c631d44aa3ef55125dc217a5d0672da26a429cf0e5b8e7ab3ae  Extension/TaoTrudgianYang2025/EnergyClauseSevenBranches.lean
d7c31b74eba6e074e243bce8a242e82ed6c3c0f38fd88dd0f4dd16fb51effeba  Extension/TaoTrudgianYang2025/EnergyClauseSevenGeneral.lean
bcad4f3a70d4850d2c2c536dae904594c976ad87cd2f7a9f807d620e706ae5f4  Extension/TaoTrudgianYang2025/EnergyClauseSevenZetaCertificates.lean
d84a732dacc6cb6de78b2460997dcd280b9170c7272a02ffaabd21f0e1e8f007  Extension/TaoTrudgianYang2025/EnergyClauseSeven.lean
55e19ff096e48f03b0565f018244b30202e7d0daa45f31678695aa3e54e77d8d  Extension/TaoTrudgianYang2025/EnergyClauseSixCaps.lean
361873bdb4c7b4c9be0843c17c1fd2b57c6cb142ef13b7c2d36b34dee774e49c  Extension/TaoTrudgianYang2025/EnergyClauseSixRates.lean
8835b9f5ac0ef07dd32b7862fb2391854c47363fb2806744c77014b5798cc12f  Extension/TaoTrudgianYang2025/EnergyClauseSixLowCertificates.lean
0d0e34d9a849fd8f7db24e5f27b757ddd8348c863e313905604b0f90e63de84c  Extension/TaoTrudgianYang2025/EnergyClauseSixHighCertificates.lean
a68c4e2fe60d2ff15488aa2cb513b18e1151553a6da6f027dda94a29860ca7ae  Extension/TaoTrudgianYang2025/EnergyClauseSixTallCertificates.lean
7fa7ca9088494a341165e3d1457f6f20d586dcc787c7f4b1e00becfad493cc9a  Extension/TaoTrudgianYang2025/EnergyClauseSixBranches.lean
99531931ae33f9d0f1d5d0833bc654376f0854dcfa0426ff568ae0461f4eb902  Extension/TaoTrudgianYang2025/EnergyClauseSixGeneral.lean
a8ca0640d892bb50ae9d6d0761e7ab158db45f3833cfe706ecbc77cdb0056b21  Extension/TaoTrudgianYang2025/EnergyClauseSixZetaCertificates.lean
cc600e9cfa2972e96e3fabed5c80116d2f0604a3f117380cf6bea016d2482169  Extension/TaoTrudgianYang2025/EnergyClauseSix.lean
49c09bbbdec47fe9b484c2b4954fe43c2f4eb85e31d03f6c8e2aa0fe4d03bbd3  Extension/TaoTrudgianYang2025/EnergyClauseFiveCaps.lean
d38b5324f74b9e29c2d44e4759a3818aa1105906d69dc4029917b15b9e3e77df  Extension/TaoTrudgianYang2025/EnergyClauseFiveRates.lean
6e9e91ae491de3b6b05d829921c4cd30177552701abb01e6fbc888b25b14ba2c  Extension/TaoTrudgianYang2025/EnergyClauseFiveLowCertificates.lean
b247e0e46abba83164689db393217ad2f18aa38a2fefc4f5617d12e64ccebbd7  Extension/TaoTrudgianYang2025/EnergyClauseFiveHighCertificates.lean
f59c130039caee05786828d4fbf134e605421751d46984f350f4eb19dcf8028f  Extension/TaoTrudgianYang2025/EnergyClauseFiveTallCertificates.lean
a8b976a5b0349ad480b1d7be22862c2396508e11045ce079a3f73389625c44b2  Extension/TaoTrudgianYang2025/EnergyClauseFiveBranches.lean
b412a7c830d7bf87c7a6dad79c91201b724a234fc609a62f25fa98e27491a4fd  Extension/TaoTrudgianYang2025/EnergyClauseFiveGeneral.lean
09a45dcae23e902241c33f5bcbb5027b7576e592cb4e09e56128cb04f497d34a  Extension/TaoTrudgianYang2025/EnergyClauseFiveZetaCertificates.lean
8e80d4cf43262e1a04a84667e167486a4af99b64d44b51c551db94a984fee0bc  Extension/TaoTrudgianYang2025/EnergyClauseFive.lean
a999f1f29b949423e9d38dcb3776550c7a3ef81f233f346314c2502b053b242a  Extension/TaoTrudgianYang2025/EnergyClauseFourCaps.lean
0c619852b0341c309b578da6fbda0394663937ea0914bfcc0aa5832b959a8f49  Extension/TaoTrudgianYang2025/EnergyClauseFourRates.lean
3200d065b91abf97d267dafd74c6c1e0b2fa26a4a349d7db3f890e737ab279ac  Extension/TaoTrudgianYang2025/EnergyClauseFourLowCertificates.lean
4b7a0da9e667ebeeacb4f12cb967c1b5e3e9e22478430e39f537823040412d10  Extension/TaoTrudgianYang2025/EnergyClauseFourHighCertificates.lean
b159804ef5ff8b8d773ed4fb59c0b74d495956bc8564ec7eb9db8aa84ce4771e  Extension/TaoTrudgianYang2025/EnergyClauseFourTallCertificates.lean
d00d65d8545dfb5aa816f465cb3d2ba3a0965033dc5b21486cc00bbaaffee9ca  Extension/TaoTrudgianYang2025/EnergyClauseFourBranches.lean
e7fccaa1f25d560f35086f13f2e3017edf0bc245c00a7301b4b879e05c053335  Extension/TaoTrudgianYang2025/EnergyClauseFourGeneral.lean
ab7591ed2477873608d0518762942ff4a36e4f270fbcbfdfa4a0b70d67ca29a1  Extension/TaoTrudgianYang2025/EnergyClauseFourZetaCertificates.lean
6fd175c58dc3f11fb4c507f71f6eadd2e809295bf810f82ef56f265e3a0fbf37  Extension/TaoTrudgianYang2025/EnergyClauseFour.lean
edb6cd3a7387940341eb7c5c88cc207f3716b7a16699eabeea91431310462f1e  Extension/TaoTrudgianYang2025/EnergyClauseThreeCaps.lean
062cbc2116481c329c9f9e62c628efc60e72d23ed67ebb4d2d2c9b4b3483084c  Extension/TaoTrudgianYang2025/EnergyClauseThreeRates.lean
0e54c91931bb75b82d71abbee73895035afb23e6255e892c5719b504a5ad99ec  Extension/TaoTrudgianYang2025/EnergyClauseThreeLowCertificates.lean
986396e400a2f7d66f1f058693a157d1f0b734c2687fd72b4b4f02c3c643f012  Extension/TaoTrudgianYang2025/EnergyClauseThreeHighCertificates.lean
7b40f65fad7541b5725721772235259a25703b4be554346adbe6d6001d33dddf  Extension/TaoTrudgianYang2025/EnergyClauseThreeTallCertificates.lean
225b2016b0e825a3e4f381b7496f2382905ed388d4a5b56e8362cda447bda13d  Extension/TaoTrudgianYang2025/EnergyClauseThreeBranches.lean
ccdbfef46f5b3a390c669f4aa70823b0c0d7e8b7db0041215eebb208c591bd62  Extension/TaoTrudgianYang2025/EnergyClauseThreeGeneral.lean
4045537febed90f465e20ef9838b364f98dec86dc49e4b9f2a5dab9b3c493085  Extension/TaoTrudgianYang2025/EnergyClauseThreeZetaCertificates.lean
438dcad2ac3de3e69dd8d08376d53c116f9b7c64ea70dc72f2de5b48504dbb0a  Extension/TaoTrudgianYang2025/EnergyClauseThree.lean
150b7e21f13fb1cd0585ab46fe1937b627d247628bff61b368d7fc8ca57f0aad  Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean
82bdb70f8b6c4f6dafa1e7eb9741202077cd3bd22a074985c8b77f73f7764038  Extension/TaoTrudgianYang2025/JutilaRecurrence.lean
2749a36c0e314626a68cfdb4093635c223dd6010ea2cb1fadc2f4c98f53d3b3f  Extension/TaoTrudgianYang2025/JutilaLocalCardinality.lean
156ead8883fbe4fdb10158b1e9a66ff4a7f0f788504f466cb126603af624abbb  Extension/TaoTrudgianYang2025/JutilaLocalAlgebra.lean
cd76535980089e0f410656c05d5a2a906ddf5b22f4ef2c0d05b8d6339458b9bc  Extension/TaoTrudgianYang2025/JutilaLocalUniform.lean
81a445106244f53e1bc4523eff7a9663e3a49ddc4dc15d5abcb917c748065838  Extension/TaoTrudgianYang2025/LargeValueSubdivision.lean
746fedc2e41e2db22662a94e96fbef75c07f870135054ce50dbdb8f67ff04d19  Extension/TaoTrudgianYang2025/JutilaSubdivision.lean
1ebcafd78db0e195752b56e2b8a393e959b3390e289ba6bbf1f4747d7ece62fe  Extension/TaoTrudgianYang2025/JutilaPowerWindows.lean
52865d41cd92ae8a22d5435579d3d3bb1453f72cf02daac7fd4803d043051f95  Extension/TaoTrudgianYang2025/JutilaWindowBound.lean
644353d52aa4bc698e8ca56de28ca4e6fcb2065a88bab2d55cf825452ec122da  Extension/TaoTrudgianYang2025/ClassicalMeanSquareBound.lean
fcc030eaaf37b691fa1c4a8f80158ba6c50dc2160d193a403b5b474c61cf7056  Extension/TaoTrudgianYang2025/JutilaLargeValues.lean
5b8f9d660faa88f79973cdc9096923576c3f127dd3f350fdc5920ddaa03521c1  Extension/TaoTrudgianYang2025/JutilaEnergyRegions.lean
fa99ec0fc59e14a254fc3296e3cf20782b42f911a8e16865304b186603f65f1e  Extension/TaoTrudgianYang2025/JutilaDualScales.lean
bb095955d6ebce8d708a0e89ebae57c0c6747392ee7b62632915dd22026ef274  Extension/TaoTrudgianYang2025/JutilaPhysicalMain.lean
b521abdab7b8b071407bac7b96c2a62af838fa84b3fd124a58006f0ff338b60d  Extension/TaoTrudgianYang2025/JutilaPhysicalPatterns.lean
4e1acd1ba15a5babc0ac05260938ac450dc20f7fa5f1dba445061c20263e3656  Extension/TaoTrudgianYang2025/JutilaSmoothingErrors.lean
5c53b1a85fd645bd18a0b579f820f1205e8bd00da05334658eb6b4e82efe7154  Extension/TaoTrudgianYang2025/JutilaSmoothingProfile.lean
d9e5eb5dfdce9c7bfb814ce5f414426d2d68ba9ad4a02c32cae3479a1a1d5ea0  Extension/TaoTrudgianYang2025/JutilaSmoothingLosses.lean
a224cb810087d3d5ee05bde4846d93eefa0750d8a076f976a6d249d50fd7a281  Extension/TaoTrudgianYang2025/JutilaSmoothedPatterns.lean
bb9027344bcb61f0334a86af8cb52a5ba1e5f372fc01dadc7ec0f74debbd9436  Extension/TaoTrudgianYang2025/JutilaPolynomialMoments.lean
3a4776b9c08864082e8c7c66fde144ef4e6bd695613c610ca7b97946464c5506  Extension/TaoTrudgianYang2025/JutilaPrefixMoments.lean
221c90825aa77e12aeb5549a13c9f1a3419d9b1b6f745c336591f24c77a0e2c6  Extension/TaoTrudgianYang2025/JutilaReflectionIntegrals.lean
8a2c3b2dfeab768668b6313848e8bd27a16f19e764402275fdfdd3b831a15962  Extension/TaoTrudgianYang2025/JutilaTraceBins.lean
cc3da2c0b322c58c3319082edf92a7f76ad110e76d99cdb7949daf2a74ceb3c7  Extension/TaoTrudgianYang2025/JutilaBinnedPatterns.lean
fdcedc1a264fb69f488425ba03b5480c27749d13e5bbfc1e3bb5c71cec316761  Extension/TaoTrudgianYang2025/JutilaHybridPatterns.lean
c8d552d56b32e4a61927c2f907f460ebba1323d088a29ea12e015d039fbd150f  Extension/TaoTrudgianYang2025/JutilaGram.lean
740af0147829aaaf632eff96cc28a0b81b4df89370607fdadff00346a5afbecc  Extension/TaoTrudgianYang2025/JutilaPatternEntry.lean
61f930fc62d50bfd1d99c302be8d5ad62ab8a33a4a1f58b779af5087bda70f6f  Extension/TaoTrudgianYang2025/JutilaPoweredMoments.lean
6c22bb0b26ae0cb08b6fafb3d64a2e7836809edd5632e07c6c3dc1d5ef0ec252  Extension/TaoTrudgianYang2025/JutilaReflectedEntry.lean
eb43f378d4425100b4ee76f3815f2233f2a1123574911b6448355bade5f3a644  Extension/TaoTrudgianYang2025.lean
33e66d20fa11a043692b4d4fbb1ee61d0c1b9fa47543ed8a6a839105be052f91  Extension/TaoTrudgianYang2025/Audit.lean
a482eede21bfde6edbaf6e7ee651c52c041ae454397147fad930837e55bd2b63  Extension/TaoTrudgianYang2025/SemanticRegression.lean
bb1879279a91c21f96281fe1ce8876d62d857ad4d7a1ed5fbba190b36b3c4869  Tools/run_tao_trudgian_yang_build.ps1
6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098  run_tao_trudgian_yang_build.bat
76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487  Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean
a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303  E:/Lean/Riemann Zeta/run_lake_build.bat
```

## Double-zeta source bounds and Bourgain algebra — verified history

The corrected powering theorem and Add-est (i)--(viii) remain proved.
The printed Lemma 62 counterexample is byte-for-byte unchanged:
SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

Four new modules advance the remaining clause-(ix) route:

- `HeathBrownDoubleZetaFinite` proves the uniform finite double-zeta bound
  on actual closed-support patterns, with the one-endpoint error and
  reflected interval proved explicitly.
- `HeathBrownDoubleZeta` proves the full frozen `hb-double` conclusion
  `s ≤ max(max(ρ+1,2ρ),5ρ/4+τ/2)+1` for actual region points,
  including τ=0. Its small-height and diagonal-equality consumers are proved.
- `MixedDoubleZeta` proves the mixed Cauchy--Schwarz inequality with the
  actual kernel at **t−u**, and consumes actual patterns with common support.
- `BourgainLargeValueAlgebra` proves witness elimination and the exact
  certificate for the row `ρ ≤ 9−12σ+2τ/3`. The resulting cardinality
  bound is **conditional on the explicitly displayed Bourgain dichotomy**;
  the finite analytic selection and its limiting bridge remain OPEN.

The row certificate uses α₁=(τ+9−12σ)/6 and
α₂=max(0,4σ+4τ/3−5), a proved alternative to the table's α₂.
All five branches are checked on the complete stated closed row.
A rational regression at σ=771/1000 detects the gap in simply extrapolating
the previous Jutila/HB local peak rate; numerical sampling is not evidence
for clause (ix).

There are 25 new named audits and 35 new regressions. All four modules are
in the root imports and the `run_tao_trudgian_yang_build.bat` PowerShell
inventory. No source archive, dependency pin, public Add-est statement,
or counterexample was changed. In particular, no constraint on s′/s
has been reintroduced.

Add-est (ix), its actual Bourgain input and final general/zeta optimization,
the other public outputs, and every remaining EPZAE-00--41 acceptance test
remain OPEN. EPZAE-19, 36 and 37 are not checked off by these supporting results.

### Current verification evidence

On dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  437 package Lean files, 448 integrity-scanned files, 9,292 build jobs,
  4,277 discovered target theorems and 4,282 audited declarations.
  All 25 new named audits permit only the standard logical axioms.
  Log: `logs/tao-trudgian-yang-build-20260921-110817-ade1e44e.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: PASS, exit 0;
  all six verification stages pass, with 301 root modules, 2 explicit
  regressions, 0 unclassified files, and 14,290 discovered theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_110818.log`;
  manifest: `logs/foundation_freeze_20260921_110818.json`.

Both runs have zero Lean errors, warnings, tactic suggestions or linter failures.
There are no remaining failed verification stages. These are build/integrity
results for the installed scope, not a claim that clause (ix) or the whole goal
is complete. The reproduction manifest records hashes of the tested sources.

### Tested source and log hashes

The existing 90-file source/integration snapshot was checked before work;
these four added files and four changed integration files identify this pass.
A 94-file snapshot was taken before the two runners. No Lean source or runner
was changed during or after those runs; the following edits synchronize prose.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025.lean` | `b449622559bf98b7ddaa96e28e97abca28308342d0049a580f9588dd31e7fe27` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `09cc2a08830d606eff7384b54f68334b6b87aeba6a40aa5b248ddd526393904b` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `fae89322ff5a8350477c04fbbec30d28fbca7a4b69907db7170a090c06e04dab` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `87ebdacf90371d46ca89139db161193971aa7c13d3b0c7658a170b6162af1af1` |
| `Extension/TaoTrudgianYang2025/HeathBrownDoubleZetaFinite.lean` | `fb832881381ffc2c6fa06fb7e90c179425a667aa60b2968f63588c7bf012fb2c` |
| `Extension/TaoTrudgianYang2025/HeathBrownDoubleZeta.lean` | `654929ff666d92898fe6ae4827cf212c8783162206e47614fb04165062ff8417` |
| `Extension/TaoTrudgianYang2025/BourgainLargeValueAlgebra.lean` | `27b2c3953d65e8b74fdebcf07fd15720fc16b4e68b442cf086d87bcac7edbc54` |
| `Extension/TaoTrudgianYang2025/MixedDoubleZeta.lean` | `0287cd666af0309518b40dcb3600dfea6c13acafdabaa0f4c5c31563a4bd8bd6` |

Target log SHA256: `fafb5001151de70317b0edda02f928da00ba377be18b724bfec779481052b63d`.

Foundation log SHA256: `0522e4565d7fc81986b7ebba8a5f5ac52c83fbaddc08213a4df348654fbb306e`.

Foundation manifest SHA256: `603a192de5101f663a55025bf50656821c707666a1eb88a56d67bea63edaafd1`.

The counterexample SHA256 remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

## Bourgain difference counts and actual zeta moments — verified history

The corrected independent cardinality/energy powering route and Add-est
(i)--(viii) are preserved. The printed Lemma 62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No fifth-coordinate scaling or third witness has been restored.

Five production modules now prove actual upstream inputs to Bourgain's
remaining analytic dichotomy:

- `BourgainDifferenceCounts`: the strict ordered-pair count
  Δ(ℓ)=#{(t,u)∈W²: |t−u−ℓ|<1}, a finite support cover, exact double
  counting, ΣΔ≤2|W|², and ΣΔ²≤2|W|³ for two-separated W.
  The cover may contain zero-count integers; these are not fabricated
  positive bins.
- `BourgainDifferenceLevels`: genuine nonempty dyadic level selection
  from positive weighted mass, with the exact log₂|W|+1 loss and
  2ʲ|Dⱼ|≤2|W|². No selector is assumed.
- `BourgainIntegerWindows`: overlap at most 2⌈H⌉+1 and the real-difference
  to integer-bin integral bridge. The latter explicitly enlarges H to H+1;
  it does not assert a same-radius replacement.
- `BourgainZetaDifferenceMoments`: actual local critical-line zeta-square
  integrals and multiplicities, their Cauchy--Schwarz/fourth-moment
  reduction, positive-mass level selection, and the actual real-pair
  consumer with the unit window enlargement.
- `BourgainFourthMoment`: the genuine symmetric fourth moment, derived
  from the proved dyadic theorem, compact initial interval and conjugation;
  it supplies the actual weighted-moment bound below.

Writing M(W,H)=Σℓ Δ(ℓ) ∫[-H,H] |ζ(1/2+i(ℓ+u))|² du, the final consumer
proves, for every η>0, uniform positive C and T₀≥1 such that

```text
M(W,H)² ≤ C H (2⌈H⌉+1) |W|³ (T+H+1)^(1+η)
```

for T≥T₀, H≥0, two-separated W⊂[0,T]. Constants precede W, T and H.
The global fourth moment is proved, not an extra theorem parameter.
The exact window loss is retained; no small-power absorption or logarithmic
large-values limit is being claimed here.

There are 31 new named audits and 45 new regressions, including strict
endpoints, empty/zero-radius cases, and a one-separated four-point set
where Δ(2)=5>|W|=4. This guards the necessary stronger separation.
All five modules are root-imported and included in the exact production
inventory behind `run_tao_trudgian_yang_build.bat`.

The retained-zeta source estimate (Bourgain (4.7)), zeta-superlevel/common-shift
selection, the full finite dichotomy and its actual-pattern logarithmic
bridge remain OPEN. The earlier `bourgain_ninth_row_of_log_dichotomy`
still has its explicit dichotomy premise. Add-est (ix), EPZAE-19/36/37
as whole items, and every other unfinished EPZAE-00--41 requirement remain
in the unchanged goal. These supporting theorems do not close those items.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: 442 package
  Lean files, 453 integrity-scanned files, 9,297 build jobs,
  4,322 discovered target theorems and 4,327 audited declarations.
  All 31 new named audits have only permitted logical dependencies,
  and all 45 new regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-115007-09779b5b.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages
  pass, 301 root modules, 2 explicit regressions, 0 excluded or
  unclassified files, 8,857 build jobs and 14,290 discovered
  nonprivate theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_115008.log`;
  manifest: `logs/foundation_freeze_20260921_115008.json`.

There are zero Lean errors, warnings, tactic suggestions, linter failures
or remaining failed verification stages. All 99 checked source,
integration and runner hashes match before and after the gates,
including the preserved counterexample. No source pin or public
Add-est statement changed. The Reproduction Manifest records the
exact evidence and hashes.

These gates establish integrity of the installed scope. The full
Bourgain dichotomy, Add-est (ix) and the unchanged whole-proof goal
are not complete.

### Reproduction hashes and coverage

| Evidence | SHA256 |
| --- | --- |
| Target log `tao-trudgian-yang-build-20260921-115007-09779b5b.log` | `d809c10cb44355c9055ab7d04b5420f7bcd24e22171ab883287a6e198afb3e62` |
| Foundation log `foundation_freeze_20260921_115008.log` | `506436dca95edfae8562256d24b4be61e34f5c6e4c07033d148a0f63b6f622c2` |
| Foundation manifest `foundation_freeze_20260921_115008.json` | `9c7fcaa688e3f4cf3abad2ac36941633ba38da1a72ab2ab75ac94c6c86d0fb8c` |

The nine new/updated proof-integration files at these gates are:

| File relative to this folder | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainDifferenceCounts.lean` | `7cd20bbd607277b080a33d37691b0d6c1b735558221ae0e28b46e2d4826708db` |
| `Extension/TaoTrudgianYang2025/BourgainDifferenceLevels.lean` | `94e0ac4beca9867eb90c63246d6b525a6d335e684ad202c9ba6db62c7962c30d` |
| `Extension/TaoTrudgianYang2025/BourgainIntegerWindows.lean` | `bc6042bc3f3b9f961c109a3e7eaa4fddcf8770a517ae87fe12a806dbcaafc0be` |
| `Extension/TaoTrudgianYang2025/BourgainZetaDifferenceMoments.lean` | `34e88da986c57d35a03f726767015fec96a7c56ab266bd2d2fae27634ccc2eb4` |
| `Extension/TaoTrudgianYang2025/BourgainFourthMoment.lean` | `423be60136279afbf6df8cb9d415a1eadbc62e390b2faeecd837f6fd2af05d12` |
| `Extension/TaoTrudgianYang2025.lean` | `5cace9c6b66d989d74c9173e84683a7ff19043dbb77e392985d4ee8b2e8fab5f` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `11171b2f1a5080ae5ea0ba2b74b45216080c8b01bba4778110cbbe15c5dfb21f` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `7d6dfa4e456bb93a007bc48614a671d33910fe5dec6403bfe5ee1f0560f87ea6` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `26970af8d6d6dbfb6e4e6554075385f1beea7723da362652d3d746de6881b6ed` |

All 99 checked source/integration/runner hashes were identical before
and after both gates. The other 90 files retain the preceding verified
checkpoint's hashes, including the BAT launchers and counterexample.
The five new modules occur in both the root imports and exact PowerShell
inventory. The 31 theorem names are explicitly audited; 45 new examples
in `BourgainDifferenceRegression` test exact signatures and semantics.

The canonical diagram has 141 distinct nodes and 352 dependency edges,
with no dangling endpoint. The three new green helper nodes are BCT
(actual counts/levels), BWI (window overlap and real-pair bridge), and BZM
(actual weighted moment using the symmetric fourth moment). BDI remains
red: its retained-zeta source entry, superlevel/common-shift selection and
full finite/logarithmic assembly are not proved. EPZAE-19/36/37 remain
unchecked as whole tasks.

Repository scans find no admitted placeholders or unsafe proof bypasses.
Raw postulate-pattern matches remain the reviewed ten comments and two
rational structure fields, not postulated declarations.
`git diff --check` exits 0; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning or proof-integrity gate was weakened.

## Bourgain critical-block Mellin localization — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Five new production modules supply a genuine retained-zeta estimate for
finite critical dyadic blocks:

- `BourgainCriticalMellin`: real-power weighting and physical dilation of
  an actual compact smooth test, exact critical-line Mellin identity, and
  its moving-pole residue. The kernel norm is scale independent; the
  residue has its explicit square-root scale factor.
- `BourgainMellinLocalization`: all polynomial Mellin moments are
  integrable; the actual zeta/Mellin tail is bounded at arbitrary order.
  The local norm estimate separates residue, local zeta integral and tail,
  with constants independent of L, t and H.
- `BourgainSmoothedPolynomial`: the fixed profile
  w(x)=`zetaIntervalCutoff 1 2 x`, equal to one on [1,2] and zero at and
  outside [1/2,5/2], produces a genuine finite-support critical polynomial.
  Its square bound consumes the Mellin theorem and interval
  Cauchy--Schwarz; its pair moment consumes the actual H-to-H+1 bridge.
- `BourgainSmoothedMoments`: proved distance-shell occupancy bounds the
  reciprocal-square overlap by four. For every positive integer q the
  complete pole sum is at most 4|W|, not an assumed diagonal estimate.
- `BourgainCriticalMajorant`: the actual finite block is zero-extended
  onto the smooth support and consumed by the native positive-kernel
  coefficient majorant. This is a full ordered-pair argument, not a
  pointwise or arbitrarily restricted-pair majorization.

The public consumer
`bourgain_critical_block_retained_zeta_moment` proves: for each integer
q >= 1 there is C_q > 0, independent of all physical parameters, such that
for L > 0, B,T,H >= 0, one-separated W in [0,T], finite
I contained in [L,2L], and |a_n| <= B n^(-1/2),

```text
sum_(t,v in W) |sum_(n in I) a_n n^(-i(t-v))|^2
 <= C_q B^2 [
      L |W| + H M(W,H+1)
      + |W|^2 (1+T)^2 / (1+H)^(2q)
    ],
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

Here Delta is the previously proved strict integer difference count, and
M is the actual finite weighted zeta-square moment. The H+1 enlargement,
coefficient factor B^2, pole term and tail are all retained. No moment,
contour shift, residue estimate, smoothness certificate or selector is
assumed. One-unit separation suffices for this consumer; the earlier
Delta <= |W| and fourth-moment count bounds still require two-unit
separation as documented.

This does **not** yet prove Bourgain (2000), equation (4.7), or the full
analytic dichotomy. The actual reflected-prefix fourth-power convolution,
dyadic assembly and Gram/reflection consumer must still feed this block
estimate. The zeta-superlevel/common-shift and local-mean lower bound,
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are not closed by
these supporting results.

All five modules are added to the root import graph and the exact
production inventory used by `run_tao_trudgian_yang_build.bat`.
The explicit audit adds 30 public theorems; 44 new regression examples
cover their exact signatures, support/plateau endpoints, the nontrivial
scale-one polynomial, the surviving diagonal and empty sets. Continue
maintaining this BAT, its PowerShell driver and the foundation
`run_lake_build.bat` whenever proof/build coverage changes. Neither
runner's warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  447 package Lean files, 458 integrity-scanned files, 9,302 build jobs,
  4,374 discovered target theorems and 4,379 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 44 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-123028-c1ae7ae1.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_122534.log`;
  manifest: `logs/foundation_freeze_20260921_122534.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 104 checked source,
integration and runner hashes match before and after these gates, including
the preserved counterexample. The Reproduction Manifest records full log
hashes and the five new/four updated build-integration file hashes.

These are integrity checks for the installed scope, not completion of
source-(4.7), the Bourgain dichotomy, Add-est (ix), or the whole-proof goal.

### Current evidence hashes

| Artifact | SHA256 |
|---|---|
| Target log `tao-trudgian-yang-build-20260921-123028-c1ae7ae1.log` | `55b60141866c9c0389a082277e368b3430eefe73fa2479094f41c01cb677f0ef` |
| Foundation log `foundation_freeze_20260921_122534.log` | `46114f2dc6056f97babb5bb9bd657998e8e0df5905dc79aa7bce0869230543d6` |
| Foundation manifest `foundation_freeze_20260921_122534.json` | `1fda1a64daf51f896761500785dec7b15dc0446e70a7c426fd61da6b3357c9cf` |

The target log is under this folder's `logs/`; foundation artifacts are
under the `Riemann Zeta/logs/` directory. These hashes cover the completed
files, not the foundation manifest's pre-final-summary log digest.

| New or updated integration artifact | SHA256 |
|---|---|
| `Extension/TaoTrudgianYang2025/BourgainCriticalMellin.lean` | `f187ae20915a5725f487780a06964c72cf989adf92d310bfdc5e4b217898e4d1` |
| `Extension/TaoTrudgianYang2025/BourgainMellinLocalization.lean` | `6053ce98f612449ac66dcb5f232cb565aef21e9998e802cfd89d20bc2a8bcaac` |
| `Extension/TaoTrudgianYang2025/BourgainSmoothedPolynomial.lean` | `5bf3806a3463e0012ed3b7dcc530e079b8fbed1d63d1084ecfcada0548b8b867` |
| `Extension/TaoTrudgianYang2025/BourgainSmoothedMoments.lean` | `afe6f346806bb392bd7959830288964b1fc921ebdad2a5a466b604ad47e8c88f` |
| `Extension/TaoTrudgianYang2025/BourgainCriticalMajorant.lean` | `6927943b9ba2fe3904b5f9e52de928f15439c7d078db9053c2c9eb3bcb2e7149` |
| `Extension/TaoTrudgianYang2025.lean` | `b8d18f80f1779fb0e725d48b19a4193a2fb7154b0680fcbfe93fca15c000928a` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `5dc482d2ed78a91bb748a02ea4dd6bcb7294e5850891f4a0744175d797095965` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `5c7c32210e6dfcc4d55ad4e806b3dad531d9d65de10835b994a92789f467c2e6` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `05725823b80f8049fd19e2bdb7726d596fca90ccbf03a6cd849d0bae4e60d5cb` |

The 104-file before/after audit also covers the retained Add-est branches,
corrected powering chain, exact public statements, toolchain and BATs.
Only the five new production modules and the four integration artifacts
above changed in Lean/build scope during this increment. The counterexample
hash remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The postulate regex has twelve benign matches: ten comment lines and two
rational structure fields named `constant`; the declaration-aware runner
passes. `git diff --check` exits 0. Its sixteen Git LF/CRLF notices are
conversion notices, not Lean diagnostics; no warning gate was weakened.
The proof diagram has 144 unique nodes and 361 edges, with no dangling
references. EPZAE-19/36/37 and the full goal remain open.

## Bourgain retained-zeta pattern entry — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Twelve new production modules now consume the previously proved critical
block estimate in actual source-pattern bounds:

- `BourgainWeightedMoments`, `BourgainPolynomialMoments` and
  `BourgainPrefixMoments`: exact phase/half-weight bridges, genuine
  powered coefficients, all dyadic prefix pieces and the literal n=1
  term. The native reflected prefix is **unweighted**. Its factor
  U=(2M)^k is retained; it is not silently treated as a critical prefix.
- `BourgainReflectionIntegrals`, `BourgainTraceBins`,
  `BourgainPatternEntry` and `BourgainHybridEntry`: interval Jensen,
  actual difference bins, native reflection and source Gram subfamilies,
  with the actual ceiling dual length and all reflection errors.
- `BourgainPhysicalMain` and `BourgainPhysicalPatterns`: the
  unweighted-prefix factor is cancelled against its own displacement
  scale before taking terminal length bounds. Near bins, the retained
  main term and all three reflection errors are assembled.
- `BourgainSmoothingErrors` and `BourgainSmoothedPatterns`: native
  smoothing discharges the Mellin tail and reflection errors; logarithmic,
  divisor and integration-length costs are absorbed uniformly.
- `BourgainRetainedCardinality`: the quadratic recurrence is solved
  with the actual zeta moment retained. Exact source-power and
  value-threshold identities account for every numerical factor.

For every integer k>0 and nu>0,
`bourgain_smoothed_pattern_retained` supplies theta,B,T0 independently
of the actual pattern, with 0<theta<=min(1,nu), B>0 and T0>=2.
For scale>=30, V>1, T>=T0 and N<=T, it constructs a genuine
two-separated W in the reflected ordinates, contained in [0,T], and
a positive integer Q with N/2<=Q<=2N. Write

```text
R = |W|, V0 = (V-1)/3, Z = B*T^nu,
H = heathBrownSmoothingHeight T theta,
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

It proves |P.ordinates|<=Z*R and the alternative

```text
R*V0^2 <= 2*Q^2
  OR
R^2*V0^(4k) <= Z*(2Q)^(2k) *
  [ R^2*Q^k + R*T^k + Q^k*M(W,H+1) ].
```

The actual integer-window moment, two-unit separation, H+1 enlargement
and source endpoint V-1 are explicit. No analytic moment or reflection
estimate is a theorem premise.

For k=2, `bourgain_high_value_pattern_retained` solves this alternative
under the additional **numerical high-value condition**

```text
2*[Z*(4N)^4]*(2N)^2 <= V0^8.
```

With D=Z*(4N)^4, its actual subfamily satisfies

```text
|P.ordinates| <= Z * [
  2*(2N)^2/V0^2 + 2*D*T^2/V0^8
  + sqrt(2D)*(2N)*sqrt(M(W,H+1))/V0^4
].
```

This is a proved high-value retained-moment consumer, **not the full
parameter range of printed Bourgain (2000), Lemma 4.1/(4.7)**. Its
absorption condition must be derived in the intended asymptotic range;
the unrestricted source statement needs additional control of the near
contribution. Neither obligation is concealed by the exact algebra.

The zeta-superlevel/common-shift and local-mean lower bound, actual
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are unchanged.

All twelve modules enter the default root, the target BAT's exact production
inventory, 30 explicit public-theorem audits and 43 semantic regressions.
The regressions include actual unweighted prefixes at lengths 0, 1 and 2,
the surviving literal-one pair moment, empty sets, zero radius and the
zero retained-moment specialization. Continue maintaining
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat`; no warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  459 package Lean files, 470 integrity-scanned files, 9,314 build jobs,
  4,429 discovered target theorems and 4,434 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 43 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-131005-aaa8691f.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_131248.log`;
  manifest: `logs/foundation_freeze_20260921_131248.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 116 checked source,
integration and runner hashes match before and after the final gates,
including the preserved counterexample.

The first foundation attempt,
`logs/foundation_freeze_20260921_130845.log`, exited 1: a prose line
beginning with the word "constant" matched its postulate scan. Rewording
that comment resolved the match; the proofs and scanner policy were not
changed. The complete rerun above is the current verification evidence.

These are integrity checks for the installed scope, not completion of
the full source-(4.7) range, Bourgain dichotomy, Add-est (ix), or the
whole-proof goal.

### Reproduction hashes and scope

Final target log SHA256:
`7fd14e51a9a7784641b8386eb26b49a1bab66a2d279c49f6d4fd6dc1daefe8bc`.

Final foundation log SHA256:
`d6e1b4e5cb39b276a8da9e844790f95a3070412fc20ec737cca1c917cfc4655d`.

Final foundation manifest SHA256:
`74f7c69fd8be98f65d11ad078dd17f746385a75c9a26a70b77677ee8ba661836`.

The twelve new production files and four updated integration artifacts
have these SHA256 hashes:

```text
6399e29154f21e89940b58a580da16c57a5fa3460d6918514a47245d14261d08  Extension/TaoTrudgianYang2025/BourgainWeightedMoments.lean
4cf44d2397efd243040a39b585e27bfe9c43177a00eabeb8382d551be467a33f  Extension/TaoTrudgianYang2025/BourgainPolynomialMoments.lean
38e8a626092799d38a251069be257a7c533e6d7bc75dd2452e5423221e17a8ae  Extension/TaoTrudgianYang2025/BourgainPrefixMoments.lean
d5b6536f9ef1978ad8dfd1aea91655bba69b86481b93af0b99908605e34181e7  Extension/TaoTrudgianYang2025/BourgainReflectionIntegrals.lean
3dfece7d4d6762ed303b10d1388be5a4ed2134e5ee43cae2a8aa0058324f14bc  Extension/TaoTrudgianYang2025/BourgainTraceBins.lean
2b8345ae8e676bb452a1b93b70665f93be2ede935887adf3e267f96e725678e2  Extension/TaoTrudgianYang2025/BourgainPatternEntry.lean
2e90c6a1102930be16662c7370038500c3c64c2e2f95a3270106a250bfa3c16e  Extension/TaoTrudgianYang2025/BourgainHybridEntry.lean
42dcdda0604385160eab4f06629e1f5d6845dded9ee307803fc4cecc3e85f2e1  Extension/TaoTrudgianYang2025/BourgainPhysicalMain.lean
863fda3bb9529464df8cf10635f03d6b8a3634c10d47d744e6d57ee8cd88d24c  Extension/TaoTrudgianYang2025/BourgainPhysicalPatterns.lean
e1c04c0573606c5704d0eff9ca77923c2942d98e3bec3a32183918278d8fb8b3  Extension/TaoTrudgianYang2025/BourgainSmoothingErrors.lean
4bc7cccf8424beeb3f34b8467edffa1ad443dd99b1d8fe391a277b103fce4efd  Extension/TaoTrudgianYang2025/BourgainSmoothedPatterns.lean
19c87d9ba34a913c8a0695c172f9e24875170ca7f26490721732419ff094ae6b  Extension/TaoTrudgianYang2025/BourgainRetainedCardinality.lean
c98b3b4e61bc786054fef9ca422a4eaac19bb6690f8a931ba446b68d51cdb1c8  Extension/TaoTrudgianYang2025.lean
9a3d0925119d938ef8308fe22508e15f748f3b069a22dc0ed113f23ce8cd7900  Extension/TaoTrudgianYang2025/Audit.lean
65fed3307ef6c627d164c3ebe622b59cdce107455cf4ae4854bc9f401d3f9fe0  Extension/TaoTrudgianYang2025/SemanticRegression.lean
22dde297250b24af1e010924760a9079301f6cf34a38b315dc5386b415450a9a  Tools/run_tao_trudgian_yang_build.ps1
```

All 116 checked source/build hashes are stable across the final gates.
The previous 104-file baseline was revalidated before this increment.
Existing Add-est branches, corrected powering, exact public statements,
dependency pins and BAT entry points are preserved. The runner's
PowerShell production inventory gains all twelve new modules; neither
BAT is renamed or bypassed.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The postulate regex has twelve benign matches: ten comment lines and two
rational structure fields named `constant`; the declaration-aware gates
pass. `git diff --check` exits 0. Its sixteen LF/CRLF conversion notices
are Git notices, not Lean diagnostics; no warning gate was weakened.
The architecture has 148 unique nodes and 370 edges, with no dangling
references. EPZAE-19/36/37 and the full goal remain open.

## Bourgain power windows and mass-level alternative — verified history

The authorized two-witness powering repair and Add-est (i)--(viii) remain
intact. `EnergyPoweringObstruction.lean` is unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Six new production modules advance the actual Bourgain source chain:

- `BourgainMomentWindows`: monotonicity of the genuine local zeta
  integrals and weighted difference moment; the native integer smoothing
  radius plus one fits a larger small power at a proved threshold.
- `BourgainRetainedUniform`: all constants and the square-root loss
  are absorbed into one physical epsilon loss. Its intermediate numerical
  high-value threshold remains visible.
- `BourgainRetainedPowerWindows`: exact three-term powers and their
  bounds from the same physical N,T,V and retained moment.
- `BourgainRetainedSource`: derives the numerical threshold and V-1
  endpoint loss from sigma>3/4 and the actual power windows. The abstract
  cutoff is discharged by the existing constructed smooth cutoff.
- `BourgainSmallMass`: solves the three-quarter-power recurrence,
  including zero cardinality, and derives the exact small-mass powers.
- `BourgainMassDichotomy`: consumes the actual source subfamily,
  either obtains the small-mass cardinality estimate or selects an
  actual nonempty dyadic integer difference level with all losses.

For sigma>3/4, any fixed real tau and epsilon>0,
`bourgain_retained_source_power_bound` supplies C>=1 and delta>0
before the pattern. If

```text
C <= N <= T, T <= N^(tau+delta), N^(sigma-delta) <= V,
```

it constructs two-separated W contained in the reflected source ordinates
and in [0,T]. With R0=|P.ordinates|, R=|W| and the genuine moment

```text
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
```

the conclusion is

```text
R0 <= C*N^epsilon*R,
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(3-4sigma+epsilon)*sqrt(M(W,N^epsilon))
].
```

The numerical high-value condition is no longer a premise here. The proof
chooses a positive exponent gap, dominates its actual constant, absorbs
V-1, and links T to N before bounding the smoothing radius. It retains
N<=T explicitly and permits tau=1 whenever that physical condition holds.
The exact regression at sigma=84/109 checks the strict gap
8sigma-6=18/109; no endpoint of Add-est (ix) was discarded.

The stronger actual-pattern consumer
`bourgain_retained_difference_level_dichotomy` chooses the same W
before any real alpha. Put h=N^(epsilon/8). For every alpha it proves
one of the following:

```text
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(-2alpha+tau+12-16sigma+epsilon)
]
```

or an actual integer j with D=bourgainDifferenceLevel W j such that

```text
L_R = Nat.log 2 R + 1, 0 <= j < L_R, D nonempty,
2^j <= R, 2^j*|D| <= 2*R^2,
N^(-alpha)*R^(3/2)*N^(tau/2) < M(W,h),
M(W,h) <= L_R*2^(j+1)*
           sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

The index condition is exactly
`j in Finset.range (Nat.log 2 W.card + 1)`; no logarithmic limit has
been taken. The small branch uses the actual subset-cardinality bridge
from R to R0.
The large branch derives positive mass and consumes the proved selector.
No analytic mass bound, auxiliary set or selector is postulated.

This is the **small-mass/heavy-difference-level alternative**, not the
full frozen Bourgain logarithmic dichotomy. Zeta superlevel selection,
subdivision with common parameters/shift, the local-mean lower bound and
the final mixed-moment comparison still have to be assembled. The
unrestricted low-value range of printed Lemma 4.1/(4.7), remaining physical
range bridges, the finite/logarithmic transfer, ninth-row discharge and
Add-est (ix) remain open. EPZAE-19/36/37 and the full EPZAE-00--41 contract
are not closed by this increment.

All six modules enter the root import graph and the exact production
inventory used by `run_tao_trudgian_yang_build.bat`. Twelve explicit
public-theorem audits and 23 regression examples cover the full signatures,
zero/empty windows, the native ceiling, zero-cardinality recurrence and
the exact sigma=84/109, tau=1 source-window specialization. Both the target
BAT and foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  465 package Lean files, 476 integrity-scanned files, 9,320 build jobs,
  4,441 discovered target theorems and 4,446 audited declarations.
  All 12 new explicit audits use only permitted logical dependencies;
  all 23 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-133945-11e430fe.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_133728.log`;
  manifest: `logs/foundation_freeze_20260921_133728.json`.

Both completed logs have zero Lean errors, warnings or tactic-info
diagnostics. Every foundation stage also records zero linter failures.
There are no remaining failed verification stages. All 122 checked
source, integration and runner hashes are unchanged across the final
gates, including the preserved printed-Lemma-62 counterexample.
The Reproduction Manifest records the full log and new-source hashes.

This verifies the installed theorem scope, not the full source-(4.7)
range, the complete Bourgain logarithmic dichotomy, Add-est (ix), or
the unchanged whole-proof goal.

### Reproduction hashes and scope

Target log SHA256:
`85b96bef1cb02c8031f8b9897755d11c2550a5acffdfd09d9ff753c3fc296896`.

Foundation log SHA256:
`5c038f4dcffed6f6fbfc0ca10d3ef38bc42b3104c38b71ccd1ada05b29281e9b`.

Foundation manifest SHA256:
`75e2a72c1225d39dd2eac89017efafe22418b5b03799bfd6278d7a0272fc713b`.

The six new production files and four updated integration artifacts have
these SHA256 hashes:

```text
5bd3e5b3d112ef086f8e855c01d9c60c6089f9faf930e4a5d4c143d431a080de  Extension/TaoTrudgianYang2025/BourgainMomentWindows.lean
fc258867c7dbab568c23153c1fcd000dbc280cd4278c47c47a090c22427f1fb7  Extension/TaoTrudgianYang2025/BourgainRetainedUniform.lean
5b0664d5e27300ec3d9b020fd02e3bebafae60bc1eee21d3ec775daae5dbbcc8  Extension/TaoTrudgianYang2025/BourgainRetainedPowerWindows.lean
883893ee86b743660035922c7bce2b17547f66159208a50b985ae177f57eafee  Extension/TaoTrudgianYang2025/BourgainRetainedSource.lean
b12f14c3a5141ae313d5d609441afbf93885a8b5148aeab5bd055a5cff9ba356  Extension/TaoTrudgianYang2025/BourgainSmallMass.lean
99324e19000afc8da51001a837a84a79813405654fe5edf2630ed3c8e05de5ce  Extension/TaoTrudgianYang2025/BourgainMassDichotomy.lean
d0492f097c9dccc45ef055eca076f02f134c15c2afa3bb566c502491763d7d4c  Extension/TaoTrudgianYang2025.lean
6734e14c88c3f7badcdbb0196b314f3205590e6cbf1a85490796f74039e48cb3  Extension/TaoTrudgianYang2025/Audit.lean
eea0b613b9b1007eafecb60a44bc27c7bf0e1da1322261989c5da1ae430839ff  Extension/TaoTrudgianYang2025/SemanticRegression.lean
3cabd0fe50506afe556003a5cc7c06f3a9004e00918e2c398f756b9adf816b8e  Tools/run_tao_trudgian_yang_build.ps1
```

All 122 checked source/build hashes are stable across the final gates.
The previous 116-file baseline and all eleven documentation hashes were
revalidated before this increment. Existing Add-est branches, corrected
powering, exact public statements, dependency pins and BAT entry points
are preserved. The PowerShell production inventory adds all six new
modules; neither human-facing BAT is renamed or bypassed.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The postulate regex has twelve benign matches: ten comment lines and two
rational structure fields named `constant`; declaration-aware gates pass.
`git diff --check` exits 0. Its sixteen LF/CRLF conversion notices are
Git notices, not Lean diagnostics; no warning gate was weakened.
The architecture has 152 unique nodes and 376 edges, with no dangling
references. EPZAE-19/36/37 and the full goal remain open.

## Bourgain actual zeta bands and shifted slices — verified history

The authorized independent cardinality/energy powering repair and
Add-est (i)--(viii) remain intact. The printed-Lemma-62 counterexample is
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness is restored.

Eight new production modules extend the genuine Bourgain large-mass chain:

- `BourgainZetaBands`: actual critical-line amplitude bands, measurable
  finite support, the proved fourth-moment measure bound and a genuine
  global linear growth majorant.
- `BourgainBandOccupancy`: literal translated integer counts, finite
  interval integrability, and both cardinality and integer-overlap bounds.
- `BourgainDyadicBands`: half-open amplitude partition and an explicit
  ceiling-logarithmic terminal count derived from actual zeta growth.
- `BourgainBandSelection` and `BourgainPositiveBand`: integration,
  finite maximization, and a positive band selected from the actual mass.
  The low-amplitude contribution is retained, then absorbed by a proved
  choice of floor; no selector or growth estimate is assumed.
- `BourgainBandShift`: the first moment method selects a real shift
  for a finite weighted family, and an actual nonempty integer slice for
  positive band mass.
- `BourgainBandCorrelation`: the normalized occupancy is defined from
  actual mass, measure and cardinality; its identity and finite bounds
  are proved.
- `BourgainPatternBand`: consumes the same W and heavy difference level
  returned by the existing actual-pattern dichotomy and assembles all
  these conclusions.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_zeta_band_dichotomy` supplies B>0, C>=1 and delta>0
before the actual pattern. Under
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`,
it chooses two-separated W in the reflected ordinates and [0,T],
with `|P.ordinates|<=C*N^epsilon*|W|`, before every real alpha.

The small branch retains the three previously proved cardinality powers.
In the large branch put R=|W| and use the returned integer j and
D=bourgainDifferenceLevel W j. The theorem retains
`j<log_2(R)+1`, D nonempty, `2^j<=R`, and `2^j*|D|<=2R^2`.
Define the actual quantities

```text
h = N^(epsilon/8), U = T+h+1,
L = sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
a = sqrt(L/(4h|D|)),
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

Then L,a>0, and some q<J gives v=a*2^q>0. The band and its mass are

```text
S = {t in [-U,U] : v <= |zeta(1/2+it)| < 2v},
I = integral_(-h)^h #{l in D : l+u in S} du,
mu = Lebesgue measure(S), K_h = 2 Nat.ceil(h)+1,
K = 2 (Nat.log 2 R+1) 2^(j+1) J (2v)^2.
```

The assembled actual-pattern theorem proves

```text
I>0, mu>0,
N^(-alpha) R^(3/2) N^(tau/2) < K I,
v^4 mu <= C U^(1+epsilon),
I <= 2h|D|, I <= K_h mu.
```

The floor has the exact identity `2h a^2 |D|=L/2`; the other half
selects the band. Spatial enlargement U is derived from the actual
difference support, including its unit integer-rounding loss. The
extra final dyadic band handles equality at powers of two.

For the actual correlation `r=I/(sqrt(mu)*sqrt(|D|))`:

```text
r>0, I=r sqrt(mu) sqrt(|D|),
r^2 <= 2h K_h,
r^2 mu <= 4h^2 |D|,
r^2 |D| <= K_h^2 mu.
```

There is a real u in (-h,h] for which
`D_u={l in D : l+u in S}` is nonempty and
`N^(-alpha) R^(3/2) N^(tau/2) < K (2h) |D_u|`.
This is a genuine shifted slice, not an abstract mass witness.
The separate weighted-family shift theorem uses one shift for the whole
supplied finite family; common band parameters across source subdivisions
have **not** yet been constructed.

The ceiling-logarithmic J and all finite losses remain explicit. No
uniform logarithmic absorption, full source subdivision, local-mean
lower estimate, final mixed-moment comparison, frozen logarithmic
dichotomy or ninth-row discharge is claimed. The unrestricted printed
Lemma 4.1/(4.7) range and remaining physical-range bridges also remain
open. Add-est (ix), EPZAE-19/36/37 and the whole EPZAE-00--41 goal
retain their existing acceptance tests.

All eight modules enter the root imports and the exact BAT inventory.
There are 29 new explicit public-theorem audits and 43 semantic
regressions, including full signatures, empty/zero windows, half-open
band boundaries, exact dyadic counts, the half-mass identity and
weighted common shifts. The target
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat` remain mandatory; no verification gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  473 package Lean files, 484 integrity-scanned files, 9,328 build jobs,
  4,476 discovered target theorems and 4,481 audited declarations.
  All 29 new explicit public audits have only permitted logical dependencies;
  all 43 new semantic regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-141745-d2685809.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_141746.log`;
  manifest: `logs/foundation_freeze_20260921_141746.json`.

Both completed logs have zero Lean errors, warnings or tactic diagnostics.
Every foundation stage also records zero linter failures. There are no
remaining failed verification stages. All 130 checked source, integration
and runner hashes are unchanged across the gates, including the preserved
counterexample. Repository scans found no prohibited proof shortcut;
the broad postulate search has only the same ten prose and two rational
structure-field matches. `git diff --check` passes; its 16 LF/CRLF notices
are Git normalization notices, not Lean diagnostics.

This verifies the installed scope. It does not complete the full Bourgain
source range/dichotomy, Add-est (ix), or the unchanged whole-proof goal.

### Reproduction hashes for this checkpoint

```text
7e81dee9bdd5e0b0a2b4dd6d872f7bd31bfd0007b6622c1f7afd4d468fad9d17  logs/tao-trudgian-yang-build-20260921-141745-d2685809.log
d8cdabf78bb5641a6d338c87a166de99c0aae85fb05604da98542524e6294eee  FOUNDATION/logs/foundation_freeze_20260921_141746.log
b357b99146511eef119d4f4c8a78bf5fa02e4e0cc22fbf98cb3b04628f91d6e2  FOUNDATION/logs/foundation_freeze_20260921_141746.json
1e92e9d4f9721f491de8689bf44a2c3314cf9db76cf70179e5d780d935804c97  Extension/TaoTrudgianYang2025/BourgainZetaBands.lean
bd24c1bb54b7a35f82b7286078913f367da118abcbc4ed48429310673d09075a  Extension/TaoTrudgianYang2025/BourgainBandOccupancy.lean
501b6fe309c9507d1bc2d9e0b682391ef12d52c41d1163a1cd417494a09f9a50  Extension/TaoTrudgianYang2025/BourgainDyadicBands.lean
47090331d41d95dcda46381b1fceac93a842a75219863b9dd8d52cd38eb4b652  Extension/TaoTrudgianYang2025/BourgainBandSelection.lean
e5f8e155158edc7853550bd1833770b5855be7ecde2b3f81db91db247e43bc41  Extension/TaoTrudgianYang2025/BourgainPositiveBand.lean
e0f133bd9f75b4a3d28b585eb8030b7e5ebf244ab59a1ff5c41db6f4f13cad3a  Extension/TaoTrudgianYang2025/BourgainBandShift.lean
d80dbabdae06779b3bd3a7b13b2b03c359aac9e6ea85dd23cf92c5ef508096f0  Extension/TaoTrudgianYang2025/BourgainBandCorrelation.lean
a2a2025c93217869382b1273a91b0e6dbc823df5b5a3d426cc8e4755f5fd7b30  Extension/TaoTrudgianYang2025/BourgainPatternBand.lean
59d653a7a8cd8ef79be453ed363f6077f4abd06d7f5c70b97f74d9394ebeeeb2  Extension/TaoTrudgianYang2025.lean
4c3c34d6ea4268af9240153c1878dbe59f4994f13453fe334ce73e5657c23d9f  Extension/TaoTrudgianYang2025/Audit.lean
6bd191615cff1793b66e66378d8f48f19c9a978ab5f405b910744a2c77e46674  Extension/TaoTrudgianYang2025/SemanticRegression.lean
d96ec861217649c4fa356c04f9e385f716e726c6b4059882f7bcd4bb35b66087  Tools/run_tao_trudgian_yang_build.ps1
```

`FOUNDATION/` denotes `E:/Lean/Riemann Zeta/`, not the target folder.
No toolchain, external dependency, source archive or pin was changed.

## Bourgain shared grids and actual subdivision — verified historical checkpoint

The corrected independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. The printed-Lemma-62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The false fifth-coordinate scaling and third witness remain excluded.

Six new production modules advance the actual Bourgain source chain:

- `BourgainSharedFloor`: a physical amplitude floor independent of the
  selected difference set, local mass and component. Its doubled low-value
  cost is bounded using the actual source cardinality and heavy-level bounds.
- `BourgainFixedBand`: selection on this supplied common floor. Its
  explicit low-mass condition is discharged in the actual-pattern consumer.
- `BourgainBandLogBounds`: the exact ceiling-logarithmic band count is
  bounded by a linear logarithm, and by an arbitrary small positive power
  with fixed-parameter constants.
- `BourgainSharedGrid`: the existing actual source dichotomy now selects
  its bands on that shared grid, retaining the complete measure, occupancy,
  correlation and shifted-slice conclusions.
- `BourgainRetainedPullback`: inverse local reflection preserves actual
  cardinality, separation, the original coefficient polynomial and every
  strict ordered integer difference count. Local source bins, and retained
  subsets pulled back into distinct bins, are disjoint.
- `BourgainSubdivisionGrid`: constructs retained subfamilies in every
  actual localized pattern and assembles their disjoint original-source union
  with exact cardinality and packing cost.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_shared_grid_dichotomy` gives B>0, C>=2 and
0<delta<=1 before the pattern. It retains the physical conditions
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`.
The same W is selected before every real alpha. Its small branch is
unchanged; its large branch now uses

```text
A = |alpha|+4|tau|+epsilon+20,
a = N^(-A), h = N^(epsilon/8), U = T+h+1,
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

This a is independent of W, the difference index j, D and its actual local
mass L_D. For the returned heavy level the proof derives

```text
2 (Nat.log 2 |W|+1) 2^(j+1) [2h a^2 |D|]
  <= N^(-alpha) |W|^(3/2) N^(tau/2)
  < M(W,h)
  <= (Nat.log 2 |W|+1) 2^(j+1) L_D.
```

Thus `2(2h a^2 |D|)<L_D`, so the fixed-floor selector genuinely
applies. The floor's crude numerical margin is proved, including negative
alpha and tau; no new mass estimate is postulated.

The proved physical radius bound and actual-pattern count conclusion are

```text
U <= 3 N^(|tau|+epsilon+1),
J <= 2 + [log(4B+1) + (|tau|+epsilon+1+A) log N]/log 2.
```

For fixed B,A,u and any eta>0, the separate uniform theorem bounds J by
C_eta N^eta whenever 0<=U<=3N^u and N is sufficiently large.
Those constants may depend on A, hence on alpha; no uniform-in-alpha
small-power absorption is asserted.

The new public subdivision theorem `bourgain_subdivided_shared_grid`
uses the actual `P.localized L hL i` patterns, with unchanged N,
threshold, support and coefficients. Here L is the chosen local height;
tau controls L, **not the unrestricted original height P.T**. It assumes
`N<=L<=N^(tau+delta)` and the same scale/value conditions. It constructs
W_i for every local component, before alpha. All components therefore use
the same a,h,U=L+h+1,J, though their chosen amplitude index q may differ.

For I=range(floor(P.T/L)+1), let

```text
S_i = { (P.localized L hL i).intervalRight - w : w in W_i },
S = union_(i in I) S_i.
```

The source consumer proves S is contained in P.ordinates, S is one-separated,
the original negative-phase polynomial is large at every point of S, and

```text
|S| = sum_(i in I) |W_i|,
|P.ordinates| <= C N^epsilon |S|,
Delta_(S_i)(l) = Delta_(W_i)(l) for every integer l.
```

The count identity uses inverse reflection and swapping the ordered pair,
so the strict unit boundary and the same integer bin are preserved.
One must use these pulled-back subsets for the global source union;
normalized reflected sets from different components can overlap.

Common amplitude indices, relative difference levels and correlation levels
across the large components are still open. The shared grid and actual
subdivision do not by themselves prove source (4.43)--(4.47). The remaining
local-mean lower estimate, mixed-moment comparison, logarithmic transfer,
ninth-row discharge, unrestricted source-(4.7) range and other required
physical-range bridges remain open. Add-est (ix), EPZAE-19/36/37 and the
whole EPZAE-00--41 completion contract are unchanged.

All six modules are included in the root and the target BAT's exact
inventory, with 22 new explicit public-theorem audits and 37 semantic
regressions. Tests cover full signatures, common physical floors/counts,
unchanged localized coefficients, empty unions, inverse reflection and
strict integer-bin endpoints. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-145545-b9986edf.log`.
  All 479 package Lean files are covered, 490 Lean files scanned, and
  9334 build jobs pass. The audit checks 4501 discovered target theorems
  plus five imported boundary declarations: all 4506 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_145042.log`
  with its matching JSON manifest. All six stages pass; 301 root modules,
  two explicit regressions and no exclusions remain classified.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 22 newly explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 37 new semantic regressions
pass. Both full logs contain zero Lean errors, warnings or tactic
suggestions. Repository-wide shortcut scans found no prohibited proof term
or postulate; broad textual matches are existing prose or rational
structure-field names. The 136 recorded source/integration/runner hashes
are unchanged across verification, including the preserved counterexample.
The architecture has 160 distinct nodes and 397 resolved edges.
`git diff --check` passes; Git emits 16 existing LF/CRLF normalization
notices, not Lean diagnostics.

This verifies the installed supporting theorem scope, not the remaining
Bourgain dichotomy, Add-est (ix), or whole-proof completion.

### Shared-grid checkpoint SHA256 evidence

These hashes identify the verified files above; earlier checkpoint hashes
remain historical. The other 123 entries of the 136-file comparison were
also unchanged between the pre-gate snapshot and post-gate read.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainSharedFloor.lean` | `5b68ceb70ca0791b1006b39302e045326f4df6b192f3ec2daabc68e40853b6e3` |
| `Extension/TaoTrudgianYang2025/BourgainFixedBand.lean` | `d8e56dbe6992c35eeb446a38d96b3e5b9cf6330b0fd309e2fe85e8c042c675e4` |
| `Extension/TaoTrudgianYang2025/BourgainBandLogBounds.lean` | `9cd04b1232e47caac292d8195e3ce8601282a885d1a9c3bcbd59f328a6407cd4` |
| `Extension/TaoTrudgianYang2025/BourgainSharedGrid.lean` | `7cef56d26330a5213cac8acee785427e4ef9e8184f34d2c045bdea0c9aa3e7b0` |
| `Extension/TaoTrudgianYang2025/BourgainRetainedPullback.lean` | `6c81535fd0ae9d1165ef60b2fa2e6b5a8d1abfe3e7de22a100795ac6dddbcba5` |
| `Extension/TaoTrudgianYang2025/BourgainSubdivisionGrid.lean` | `dcf4199746dddf0a12f1b48b65b893d745da32a0e475776951cf102178f2e465` |
| `Extension/TaoTrudgianYang2025.lean` | `00d1a6ab39b87b3c50eb1ca86fd5dab5df812be85ffea389d77df4f613af8748` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `5ae371e0071d72f2cc779063d6f9f5abbeeab49ce8a3a754bb71fc759da8c9d2` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `7cbf6c0a7aa51735c367c563bcee84059dab66246dffcc2b168ca3713fe7087b` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `b895de2b4b3b099ece31929afc53ba01827073965c4d7fc87a377c40b2155f51` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `E:/Lean/Riemann Zeta/run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `logs/tao-trudgian-yang-build-20260921-145545-b9986edf.log` | `d20fed9d07a0b190e83974f54c56e1adf13b838040767f3afa369484f9c27832` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_145042.log` | `d4303616972bc563c9db6c4bf043a2f7957b4fb4de30ca38182d024303250b9d` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_145042.json` | `d4e33812a263c587d8e7dd02679923a454e2f90c145948562250f1471004ab2f` |

## Bourgain common component levels and correlation product — verified historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses, unrestricted fifth
coordinates, and Add-est (i)--(viii) remain unchanged. No false scaling or
third witness is restored.

Five production modules advance the actual Bourgain component selection:

- `BourgainComponentSelection` proves weighted finite-fiber selection and
  the small/large partition estimate with its exact counting cost.
- `BourgainCommonBand` consumes `bourgain_subdivided_shared_grid`,
  selects one common actual zeta-amplitude index on the large components,
  and constructs their original-source union.
- `BourgainRelativeLevels` regrids the relative multiplicity
  `2^j/|W|`, with a shared physical floor, logarithmic count, and
  factor-four bounds on the actual ordered integer difference counts.
- `BourgainCorrelationProduct` derives a finite relative/correlation
  product lower bound from actual component mass and the fourth moment.
- `BourgainCommonLevels` consumes the common-band family, performs the
  second weighted selection, and derives that product inequality on the
  actual retained components.

The named proposition `BourgainComponentBand` records literal difference
sets, zeta-band integrals, measures, correlation and shifted-slice data.
It is a specification, not a theorem by itself. Both public subdivision
consumers construct these witnesses from the existing analytic theorem;
they do not accept that proposition as an analytic input.

The strongest consumer is `bourgain_subdivided_common_levels`.
For sigma>3/4, fixed real tau and epsilon>0, its constants B>0, C>=2 and
0<delta<=1 precede the pattern. It keeps
`C<=N<=L`, `L<=N^(tau+delta)`, and `N^(sigma-delta)<=P.V`.
The retained W_i are chosen before alpha. Here tau controls the local
height L, not the unrestricted original height P.T.

For fixed alpha let I=range(floor(P.T/L)+1), m=|I| and

```text
h=N^(epsilon/8), U=L+h+1,
a=N^(-(|alpha|+4|tau|+epsilon+20)),
J=bourgainZetaBandCount B U a,
Q=bourgainRelativeLevelCount N tau,
F=C [N^(2-2sigma+epsilon)+N^(2tau+4-8sigma+epsilon)
     +N^(-2alpha+tau+12-16sigma+epsilon)].
```

The theorem selects a common q<J, p<Q, and actual component indices A
contained in I. Every selected component has original local cardinality
strictly larger than F. Set V=a*2^q and d=N^(-(|tau|+2))*2^p.
For each selected i, D_i is the actual heavy difference level j_i of W_i,
R_i=|W_i|, and

```text
0<d<=1,
d R_i <= 2^j_i < 2 d R_i,
d R_i <= Delta_(W_i)(ell) < 4 d R_i  (ell in D_i),
d |D_i| <= 2 R_i.
```

The common relative index is not an absolute difference index.
The proved uniform count is

```text
Q <= 2+[log 5+(|tau|+2) log N]/log 2.
```

Writing r_i for the actual normalized band occupancy and
Z_i=Nat.log 2 R_i+1, the consumer also proves

```text
N^(-2alpha) N^tau < 1024 Z_i^2 J^2 C U^(1+epsilon) d r_i^2.
```

This follows by squaring the actual large-mass inequality, using
V^4 times the actual band measure <= C U^(1+epsilon), and cancelling
the positive R_i^3. No correlation lower bound is assumed.

Let S be the union of the retained sets pulled back into their original
local bins. The consumer proves S is contained in P.ordinates,
one-separated, and large for the unchanged original negative-phase
coefficient polynomial. Its cardinality is exactly sum_(i in A) R_i;
each component's strict ordered integer difference counts are preserved.
The original total satisfies

```text
|P.ordinates| <= m F + C N^epsilon J Q |S|.
```

The selected family may be empty when the small bound suffices. No
nonempty large family or unaccounted logarithmic loss is silently assumed.

Common correlation-level selection and its finite/logarithmic losses,
the full integer-slice common-shift inequality, the local-mean lower
estimate and actual mixed-moment comparison remain open. So do the
finite/logarithmic Bourgain dichotomy, its remaining physical-range
bridges and Add-est (ix). EPZAE-19/36/37 and the whole EPZAE-00--41
completion contract remain open and unchanged.

The root and exact target BAT inventory include all five modules,
with nine new explicit theorem audits and 23 semantic regressions.
Both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` remain mandatory, with unchanged coverage,
integrity and zero-warning gates.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-152459-3040905f.log`.
  All 484 package Lean files are covered, 495 Lean files scanned, and
  9339 build jobs pass. The exhaustive audit checks 4517 discovered target
  theorems and five imported boundary declarations: all 4522 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_152045.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All nine new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 23 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
the broad text search matches only existing prose and rational structure
fields. All 141 checkpoint source/integration/runner hashes are unchanged
between the pre-target-gate snapshot and post-gate check, including the
preserved counterexample. The architecture has 164 distinct nodes and
406 resolved edges. `git diff --check` passes; the 16 Git LF/CRLF
normalization notices are not Lean diagnostics.

Semantic edge check: CSEL is realized by
`bourgain_subdivided_common_band`, which consumes the actual subdivision
and weighted partition theorem. CRG is realized by
`bourgain_retained_relative_level` and
`bourgainRelativeLevelCount_log_bound`. CCP is the derived
`BourgainComponentBand.relative_correlation_lower`, not a field assumed
in the component predicate. CLEV is
`bourgain_subdivided_common_levels`, which constructs its selected
family from those actual outputs and derives the product inequality on it.

This verifies the installed supporting theorem scope, not the remaining
correlation selection, Bourgain dichotomy, Add-est (ix), or whole-proof goal.

### Common-component checkpoint SHA256 evidence

These identify the verified files above; earlier checkpoint hashes remain
historical. The other 129 entries of the 141-file source/integration/runner
comparison were also unchanged across the target-gate snapshot and final read.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainComponentSelection.lean` | `24b8732e75a6c6df566ade36df027b79451ec8b52c506a7922f23db856ede4a8` |
| `Extension/TaoTrudgianYang2025/BourgainCommonBand.lean` | `b005d7f2bd0ee8a151d4a47adc880a6daddd1b28dcd4fcb2f72b9a1fe2326a24` |
| `Extension/TaoTrudgianYang2025/BourgainRelativeLevels.lean` | `7335326e0990bfb5721d6236063b5ebfde1e398cdfba121b8070fadeba405282` |
| `Extension/TaoTrudgianYang2025/BourgainCorrelationProduct.lean` | `dcc7472399c510ef2185823fcaae28a556b1f4c81576a402d8a2921b59916a36` |
| `Extension/TaoTrudgianYang2025/BourgainCommonLevels.lean` | `a554b9e5d48defcda94501d257f94a7f1f931851a4ca9935416a86ee0889af97` |
| `Extension/TaoTrudgianYang2025.lean` | `26aa39de273e862435cb2c18565d33c1d32dc43248d60e54d8c7402f8c56c5e5` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `0bc9d5cb7f18c2722b537df3af78c4fd21f3d3037abe99f7531df413741aba2a` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `2b71d4841ee4b9dea83a3b05bed79062b0fdcc768ff7d7017e8b62fd715cb141` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `dd46b466fbfc6dac352f57c2692c56a4af7e3c0e235bc40995886524535bea60` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `E:/Lean/Riemann Zeta/run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `logs/tao-trudgian-yang-build-20260921-152459-3040905f.log` | `936d082713dd09a2b0b9312722feb03e74c0e7f5f9259a6a55195a970c3f389d` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_152045.log` | `7d3858dd0d933791984445b84e89d576f7058f29425ac307da73e895e7076eeb` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_152045.json` | `588db3083b00a2eacbf2abd3feeead65dddfdd38142dcd9aa5042c4a0d4a11ff` |

## Bourgain common correlation and uniform selection losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. False fifth-coordinate scaling and a third
witness remain excluded.

Five new production modules complete the next finite selection step:

- `BourgainCorrelationScales`: a coarse polynomial amplitude-count
  bound and shared inverse-power correlation floor, with proved exponent
  margin and coefficient balance.
- `BourgainCorrelationWindow`: actual retained cardinality, spatial
  enlargement and mass/fourth-moment data force each component's correlation
  into that shared physical window.
- `BourgainCorrelationGrid`: a genuine finite correlation grid, its
  logarithmic count and fixed-parameter small-power bound, and actual
  component selection with two-sided occupancy bounds.
- `BourgainCommonCorrelation`: consumes the actual common-amplitude/
  relative-level family and performs the third retained-cardinality-weighted
  selection, preserving the original-source union.
- `BourgainSelectionLosses`: proves a joint arbitrary-small-power
  bound for all three actual selection counts.

The prior common-level module's introductory comment now scopes its
remaining work to downstream consumers; its theorem statement is unchanged.

For the already fixed B>0, C>=2, alpha, tau and epsilon>0, define

```text
u=|tau|+epsilon+1,
A0=|alpha|+4|tau|+epsilon+20,
E=2(|tau|+1)+2(u+A0)+u(1+epsilon),
A1=|alpha|+|tau|+E+1,
K0=4096 C (4B+2)^2 3^(1+epsilon)+1,
b=N^(-A1)/K0, h=N^(epsilon/8).
```

The floor b is independent of the local component, difference level,
local mass and band index. The proved actual-component window is
`0<b<r_i<=4h`. Its lower endpoint follows from the existing actual
correlation-product inequality, not an assumed correlation estimate.
The proof bounds its coefficient by `(K0-1)N^E` and proves

```text
(K0-1) N^E b^2 <= N^(-2alpha) N^tau.
```

The shared finite count and its bound are

```text
Kc = bourgainZetaBandCount (4K0) (h-1) (N^(-A1)),
Kc <= 2+[log(16K0+1)+(epsilon/8+A1) log N]/log 2.
```

The terminal bound is strict, including exact dyadic endpoints.
For fixed parameters and any eta>0, the count is <=D_eta N^eta
beyond a proved threshold. Alpha is an allowed dependency; no
uniform-in-alpha threshold is asserted.

The main consumer `bourgain_subdivided_common_correlation` retains
sigma>3/4, `C<=N<=L<=N^(tau+delta)`,
`N^(sigma-delta)<=P.V`, and `0<delta<=1`.
B,C,delta precede the pattern; the same W_i precede alpha.
Tau still describes the local height L, not the unrestricted original P.T.

It constructs common indices q<J, p<Q and k<Kc and actual selected bins.
All previous component data remain available. With
V=N^(-A0)2^q, d=N^(-(|tau|+2))2^p, s=b2^k,
U=L+h+1, actual difference set D_i, actual band measure mu, and
actual correlation r_i, each selected component satisfies

```text
0<s,  s<=r_i<2s,  s<=4h,
s sqrt(mu) sqrt(|D_i|) <= actual band occupancy
  < 2s sqrt(mu) sqrt(|D_i|),
N^(-2alpha) N^tau
  < 4096 (Nat.log 2 |W_i|+1)^2 J^2 C U^(1+epsilon) d s^2.
```

The factor 4096 is derived from the prior product bound and the
two-sided correlation band; it is not added as a field in the source
component predicate.

Let m=floor(P.T/L)+1 and F be the unchanged three-term small-component
bound from the preceding checkpoint. The selected original-source union S
has exact cardinality sum_i |W_i|, is one-separated, and is large for the
unchanged original coefficient polynomial. Every component's strict ordered
integer difference counts are preserved. The proved global bound is

```text
|P.ordinates| <= m F + C N^epsilon J Q Kc |S|.
```

The family may be empty when the small bound suffices. No nonempty large
family is silently assumed. The main consumer retains the finite counts;
their absorption is proved separately by
`bourgain_selection_counts_uniform_power`: for fixed B,C,alpha,tau,epsilon
and every eta>0, constants D,N0 precede the actual pattern and its
physical-window parameter, and for N>=N0, `J Q Kc<=D N^eta`. For the selected
family this applies to the actual localized pattern of height L.

The full integer-slice common-shift inequality, local-mean lower estimate,
actual mixed-moment comparison, finite/logarithmic Bourgain dichotomy and
remaining physical-range bridges are still open. Add-est (ix),
EPZAE-19/36/37 and the whole EPZAE-00--41 contract remain open.

The root and exact target BAT inventory include all five modules, with
17 new explicit theorem audits and 31 semantic regressions. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-155221-a509a790.log`.
  All 489 package Lean files are covered, 500 Lean files scanned, and
  9344 build jobs pass. The exhaustive audit checks 4543 discovered target
  theorems and five imported boundary declarations: all 4548 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_154836.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 17 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 31 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 146 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 168 distinct nodes and 417 resolved edges.
`git diff --check` passes; 16 Git LF/CRLF normalization notices are
not Lean diagnostics.

Semantic edge check: CSCL is realized by
`bourgain_component_correlation_window`, consuming the actual component
product, retained-cardinality bound and proved floor balance.
CGR is realized by `bourgain_component_correlation_grid`,
`bourgainCorrelationLevel_terminal` and
`bourgainCorrelationLevelCount_log_bound`.
CCOR is `bourgain_subdivided_common_correlation`, which consumes the
actual prior family, derives all component grid witnesses and constructs
the third weighted fiber and original-source union.
SLOSS is `bourgain_selection_counts_uniform_power`, whose conclusion
uses the actual counts and linked physical height of the supplied pattern.
These are supporting results; the full integer-slice shift, Bourgain
dichotomy, Add-est (ix), and whole-proof contract remain unfinished.

### Common-correlation checkpoint SHA256 evidence

These identify the verified files above; earlier checkpoint hashes remain
historical. The other 133 entries of the 146-file source/integration/runner
comparison were also unchanged across the target-gate snapshot and final read.
The prior common-level module changed only its scope comment, not its theorem.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainCorrelationScales.lean` | `20a400f2ee52f2a328b1a10d69acc18dcd8d338609e824897d14c009c6dbea55` |
| `Extension/TaoTrudgianYang2025/BourgainCorrelationWindow.lean` | `ccc2d59170b74d562d4b8e18fcead3692f72bd7a1fcbf87b6bae5625fac78df0` |
| `Extension/TaoTrudgianYang2025/BourgainCorrelationGrid.lean` | `ef480505c519618049d2a76ad523c2071013a5bc7edfe9ca2b1c6b8903a19874` |
| `Extension/TaoTrudgianYang2025/BourgainCommonCorrelation.lean` | `547b4d940bd4b0e23fae6041b983fdbc899fb950c03c68130879007027b95181` |
| `Extension/TaoTrudgianYang2025/BourgainSelectionLosses.lean` | `c855d1592e5a9c4b10b7724271782bd2ef58e2e46a94a7ee02de92117cc9369a` |
| `Extension/TaoTrudgianYang2025/BourgainCommonLevels.lean` | `a34be7c56a90383c6781a7a259c1f09a15f5bb36a4df27300f9191a122520534` |
| `Extension/TaoTrudgianYang2025.lean` | `fa3e8a6efa8109ad8852a51787d41249306499b1f22735851e1db62867b4c0e3` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `24a6e21838553c4e0df44952248cad040fab6e81ea8c7d6b12e162df4fafa8bf` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `b6a8e24efb5537ae8d5d4d9a2fec2a8cb7fd37331c89a78809a6b2a685a75504` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `e5e98878e932b2ab3eab00abcfd43308b6c4908c231b7386c628103abfeaa95b` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `E:/Lean/Riemann Zeta/run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `logs/tao-trudgian-yang-build-20260921-155221-a509a790.log` | `981704c272a69eda1da91d15d1d22dc0f5639432c8e5bef3be92200cf04285d1` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_154836.log` | `2c125e72239a2b9722e8b1172bebf3ee7bed88220aaed575d91703a953db9408` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_154836.json` | `83a700aca63e660cda497037f9e8534804232b2db5f723bdbd47f0a4b4b936b9` |

## Bourgain full integer slice and source mixed lower bound — historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses and Add-est (i)--(viii)
are unchanged. False fifth-coordinate scaling and a third witness stay excluded.

Twelve new production modules prove a full two-term common shift for the
actual selected family, a power-window local mean for the original polynomial,
and their actual source-pattern mixed lower-bound consumer:

- `BourgainIntegerSlice`, `BourgainSliceSelection`: the complete integer
  slice, its integrated cardinality and square-root bounds, and simultaneous
  weighted selection against both profiles.
- `BourgainComponentMass`, `BourgainFamilySlice`, `BourgainCommonSlice`:
  derive both weighted mass lower bounds from actual component occupancy,
  fourth moment and common levels, then consume the actual three-level family.
- `BourgainSliceGeometry`: the real image has the same cardinality, is
  one-separated, and has proved spatial bounds and shifted zeta membership.
- `BourgainLocalMean`, `BourgainPowerMean`, `BourgainLocalSquare`:
  frequency-center the original closed-support negative-phase polynomial,
  consume the native finite exponential-sum Fourier estimate, absorb its tail,
  and prove the displaced local-square estimate.
- `BourgainMixedLower`, `BourgainMixedFamily`, `BourgainCommonMixed`:
  preserve strict ordered difference counts and original-source pullbacks,
  sum over the disjoint bins, and assemble the actual mixed lower bound.

### Exact finite physical statement and semantic edges

Write h=N^(epsilon/8), U=L+h+1, Vb for the selected common zeta amplitude,
mu for the measure of its actual band, and K=2 ceil(h)+1. The full slice is

```text
Z(u) = {ell in [-ceil(U+h),ceil(U+h)] in Z : ell+u belongs to the band}.
```

For every u in [-h,h] it contains every integer whose translate lies in the
band, not just the integers from one component's difference level.
`bourgainIntegerSlice_integral_card_le` and
`bourgainIntegerSlice_integral_sqrt_card_le` prove, over [-h,h],

```text
integral |Z(u)| <= K mu,
integral sqrt(|Z(u)|) <= sqrt(2h K mu).
```

Let R_i=|W_i|, D_i be the actual heavy difference level, d the common relative
multiplicity, s the common correlation level, J the actual amplitude count,
and Zlog=3+(|tau|+1) log(N)/log(2). Define

```text
beta = N^(-alpha) N^(tau/2) / [32 Zlog J d sqrt(C U^(1+epsilon))],
a = s^2/(8hK),    b = beta/[4 sqrt(2hK)].
```

The theorem `BourgainComponentBand.weighted_mass_lower` derives its two
mass inequalities from the actual band, not from assumed desired lower bounds.
`bourgain_component_family_slice` consumes them and the complete slice
moments. `bourgain_subdivided_common_slice` constructs the actual selected
family and proves either the genuine small-component bound or a common
u in (-h,h] with nonempty Z=Z(u) and

```text
a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)
  < sum_i R_i |D_i intersect Z|.
```

Here S is exactly the disjoint union of retained sets pulled back into their
original bins; |S|=sum_i R_i. The common levels, unchanged original
coefficients, source containment, one-separation, strict difference counts,
and global packing cost m F + C N^epsilon J Q Kc |S| are retained.
No nonempty selected family is assumed; the empty case gives the small bound.

For every eta>0, `bourgain_power_window_displaced_square` provides constants
M>0 and N0>=2 before the actual pattern and points, and proves

```text
P.V^2 <= M N^eta integral_[-r,r] |F_P(x+v)|^2 dv,
r=1+2 pi N^eta,
```

when N>=N0, sigma>=0, delta<=1, N^(sigma-delta)<=P.V, and x is within one
unit of an actual large ordinate. The underlying exact modulation is
exp(i log(N)t) F_P(t); its frequencies are log(N)-log(n), of absolute value
at most one on the literal closed support [N,2N]. It uses the already
kernel-checked native `norm_gmFiniteExpSum_le_localIntegral_add_tail`,
then absorbs the actual tail using P.V>=N^(-1). No analytic local-mean
hypothesis is supplied by a caller.

This is a directly proved **power-window** route to the needed mixed lower
bound, not a proof of the printed logarithmic-window lemma (4.48).
That sharper printed statement is not marked complete.

The strongest consumer `bourgain_subdivided_mixed_lower` retains
sigma>3/4, epsilon>0, eta>0, C<=N, N0<=N,
N<=L<=N^(tau+delta), N^(sigma-delta)<=P.V and 0<delta<=1.
B,C,delta,M,N0 precede the actual pattern; W_i still precede alpha.
Tau governs the local L, not the unrestricted original P.T.
On its large branch it constructs the same nonempty full slice and proves

```text
P.V^2 d [a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)]
  < M N^eta integral_[-r,r] sum_(t in S) sum_(ell in Z)
      |F_P(t-ell+v)|^2 dv.
```

The strict-bin first-coordinate injection uses each W_i's two-separation.
The proof transports each component's ordered counts into its original bin
and sums over the disjoint source union. It does not identify the union's
total difference count with the sum of component counts.

This closes the finite physical common-shift and source mixed **lower**
steps (the roles of source (4.47) and (4.53)). It does not yet combine the
mixed upper bound with Heath--Brown, prove (4.57)--(4.63), or discharge
the ninth-row logarithmic-dichotomy premise. Add-est (ix), EPZAE-19/36/37,
and the whole EPZAE-00--41 goal remain open.

Root imports, the exact target BAT inventory, explicit audit and semantic
regressions include all twelve modules: 39 new public theorem audits and
59 new regression examples, including closed endpoints, strict excluded
difference boundaries, zero amplitude, unchanged coefficients and both
source-facing consumer types. Both `run_tao_trudgian_yang_build.bat` and
foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-164830-0fe87f33.log`.
  All 501 package Lean files are covered, 512 Lean files scanned, and
  9356 build jobs pass. The exhaustive audit checks 4601 discovered target
  theorems and five imported boundary declarations: all 4606 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_164601.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 39 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 59 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 158 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 172 distinct nodes and 428 resolved edges.

Semantic green-node check: ISL uses
`bourgainIntegerSlice_integral_card_le`,
`bourgainIntegerSlice_integral_sqrt_card_le` and
`bourgainRealSlice_separated`/`bourgainRealSlice_bounds` on the defined
complete slice. CSH is `bourgain_subdivided_common_slice`, which consumes
the actual common-correlation family and derived weighted mass bounds.
LPM is `bourgain_power_window_displaced_square`, using the proved exact
modulation, native Fourier estimate, tail absorption and interval translation.
MLB is `bourgain_subdivided_mixed_lower`, which unpacks the actual source
family and composes CSH, LPM, strict difference counts and original pullbacks.
These statements preserve the stated parameter ranges and constant order.
The full mixed upper assembly, Bourgain dichotomy, Add-est (ix) and
whole-proof contract remain open; audit counts do not close those obligations.

### Full-slice and mixed-lower checkpoint SHA256 evidence

These identify the verified files above; earlier checkpoint hashes remain
historical. The other 139 entries of the 158-file source/integration/runner
comparison were also unchanged across the target-gate snapshot and final read.
All twelve new source texts were also checked against the individually
compiled versions. No existing mathematical module changed this iteration.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainIntegerSlice.lean` | `6709f08f22c1d7796ff649768a73dcdbd4312e660c1a59969c23a1e1224b93e9` |
| `Extension/TaoTrudgianYang2025/BourgainSliceSelection.lean` | `406af91bae81d2c56fa8df79638ce242cfb00d9f7fb373f00dfec57cae45dc01` |
| `Extension/TaoTrudgianYang2025/BourgainComponentMass.lean` | `7263bc559a936f6bde4840943a89898f35ce460b0122617322ae7629b8d346b9` |
| `Extension/TaoTrudgianYang2025/BourgainFamilySlice.lean` | `3b8539138ae2f0969c92d4179b3ff909dbcfb32d550661c12f13f4a37e77da73` |
| `Extension/TaoTrudgianYang2025/BourgainCommonSlice.lean` | `378a4cc414410844acd21eeac795a2c467f2dae55490fd11241217a532920ace` |
| `Extension/TaoTrudgianYang2025/BourgainSliceGeometry.lean` | `d524580b19414309576f457314cf2813dc78fd2826c0c100b42401675c62c856` |
| `Extension/TaoTrudgianYang2025/BourgainLocalMean.lean` | `c8552d3608b47b375c1caf0f2e98f5e50dbfc2155158a3b08efc9d34d4d17545` |
| `Extension/TaoTrudgianYang2025/BourgainPowerMean.lean` | `2c06e5b518b1c96031fd298a3e5c1f9bbf49de80873d306c28e5aa06e365cff2` |
| `Extension/TaoTrudgianYang2025/BourgainLocalSquare.lean` | `31733e4df6ece31f3fa9e45a0355ac05bc9833520561c4a354ee5724122453c6` |
| `Extension/TaoTrudgianYang2025/BourgainMixedLower.lean` | `fd4f7806d671b2d561064dd005e7026a6ce4014e13cae99bb1ddc0518c27360c` |
| `Extension/TaoTrudgianYang2025/BourgainMixedFamily.lean` | `edbf9c03794332e3d57d595fa4c00585726393cbf1ae6e744af8b8d9d2f7e2c3` |
| `Extension/TaoTrudgianYang2025/BourgainCommonMixed.lean` | `de09b31a3464c44142cdcc776c91ef84e997b97cff16e0b6d80c60d9970fd52d` |
| `Extension/TaoTrudgianYang2025.lean` | `f05c1b94bafcc418e69aa8335cf30846b4d4dfa32316df706c62bfb8c985eabb` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `e42b92c29860d5dd6f3fa5536c58417a99edba986595f7256b64d0c32825d6cc` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `b87267e5508f17897d7d5a7ee90315450fa01870f5e5faeb45408286d1aba5b7` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `2f5c1c24180df30c519bd22067119e6343b7d666545184afad1f80d71518bb7d` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `E:/Lean/Riemann Zeta/run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `logs/tao-trudgian-yang-build-20260921-164830-0fe87f33.log` | `b489a96d59dc2d2376e99d4232782cf31f9179920e7cf7bb9c3a0f45c992305a` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_164601.log` | `b27f1332ab56428bbaf56d018f2cf88f78b70b3e7ac21c36d9831331f17f96f6` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_164601.json` | `8c8742ddbe616533389a463c58e46b881569d70451d1d33c446218f61de84f04` |

## Bourgain Heath–Brown comparison and linked subdivision — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est (i)--(viii)
are preserved; false fifth-coordinate scaling and a third witness stay excluded.

Ten new production modules advance the actual mixed lower bound through
Heath--Brown, remove the common multiplicity/correlation levels, and link
the subdivision to the original physical height:

- `BourgainSeparatedSelf`: the native Heath--Brown self-moment bound on
  arbitrary one-separated sets, with the original polynomial's closed support
  and explicit endpoint error. The auxiliary slice is not falsely made into
  a large-value pattern for the original polynomial.
- `BourgainMixedShift`, `BourgainMixedUpper`: exact unit-norm coefficient
  twist, integer-to-real sum bridge, integration length, and the actual
  source-set/full-slice mixed upper bound.
- `BourgainCommonComparison`: consumes the already constructed selected
  family and both actual analytic estimates.
- `BourgainLevelElimination`, `BourgainLevelFreeComparison`: use the
  genuine component product to remove correlation and multiplicity from
  the first coefficient; cancel multiplicity exactly in the second; replace
  the component three-halves sum by the retained union's cardinality,
  paying the square root of the actual bin count.
- `BourgainPhysicalUpper`, `BourgainPhysicalComparison`: prove the
  slice's enclosing height is at most 8 times the original height when
  N<=L<=T and epsilon<=8; absorb the constant-factor enlargement uniformly.
- `BourgainSubdivisionScale`, `BourgainLinkedComparison`: link
  L=T/N^chi with both original-height power bounds, prove the finite bin
  count, and instantiate the actual comparison at the ninth-row choice.

### Source-facing physical comparison

The strongest general linked consumer is
`bourgain_linked_subdivision_comparison`. It assumes sigma>3/4,
chi>=0, lambda=tau-chi>1, eta>0, theta>0 and 0<epsilon<=8.
Its positive constants B,C,M,D,N0 and
0<delta<=min(1,(lambda-1)/2) precede the actual pattern.

For N>=max(C,N0), N^(tau-delta)<=T<=N^(tau+delta),
N^(sigma-delta)<=P.V and the literal L=T/N^chi, it derives N<=L<=T,
the required local upper-height bound, and

```text
m = floor(T/L)+1 <= 2 N^chi.
```

The local band/selection constructions use **lambda**, not global tau.
The same genuine reflected W_i are chosen before alpha. For every alpha
the consumer preserves all three common levels, every actual component band,
the disjoint original-source union S, exact cardinality, one-separation,
the unchanged original polynomial and the strict ordered difference counts.

Write h=N^(epsilon/8), U=L+h+1, K=2 ceil(h)+1,
Zlog=3+(|lambda|+1) log(N)/log(2), J for the actual amplitude count,
R=|S|, and x=|Z(u)| for the nonempty complete integer slice.
Define the two level-free coefficients

```text
gamma = N^(-2alpha) N^lambda /
  [32768 h K Zlog^2 J^2 C U^(1+epsilon)],
beta = N^(-alpha) N^(lambda/2) /
  [128 Zlog J sqrt(C U^(1+epsilon)) sqrt(2hK)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The exact Lean names are `bourgainEliminatedCardCoefficient`,
`bourgainSliceSqrtCoefficient ... 1`, and `bourgainSecondBudget`.
Both lower coefficients are proved positive. Either the actual original
cardinality obeys the small-component bound m F, or S is nonempty and the
consumer constructs u in (-h,h] and the nonempty full slice satisfying

```text
P.V^2 [gamma x R + beta sqrt(x) R^(3/2)/sqrt(m)]
  < M N^eta 2(1+2 pi N^eta) D T^theta
      sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

F is the unchanged three-term small-component bound, now with local lambda.
The companion global selection inequality remains
`|P.ordinates| <= m F + C N^epsilon J Q Kc R`, with actual finite counts.
No Heath--Brown, local-mean, desired correlation, or mixed-bound hypothesis
is left for the caller to provide. Both height hypotheses and coefficient
normalization are discharged on the actual objects.

This is the full finite physical mixed comparison with the third
Heath--Brown term retained. It is not a claim that the paper's simplified
two-term display holds without its additional range assumptions.

### Ninth-row entry and exact remaining work

`bourgain_ninth_row_local_height_margin` proves that
chi=max(0,4sigma+4tau/3-5) is nonnegative and tau-chi>1 from sigma>3/4,
16sigma-11<=tau and 20sigma+tau/3<=16.
`bourgain_ninth_row_physical_comparison` actually instantiates the linked
source consumer at that choice. This closes that row's interior local-height
entry, not the row's large-values conclusion.

Next remove the finite/logarithmic losses with correctly ordered constants:
bound gamma and beta below by the required small-power expressions, use
the proved m bound, transfer the retained union back to total cardinality,
control the slice-cardinality exponent, and pass the actual comparison to
the frozen logarithmic dichotomy. Then discharge
`bourgain_ninth_row_of_log_dichotomy` and finish Add-est (ix).

The unrestricted printed-(4.7) range and other classical/source obligations
remain open. The printed logarithmic-window (4.48) is still not claimed:
the comparison uses the already proved power-window route.
EPZAE-19/36/37, Add-est (ix), and the full EPZAE-00--41 goal remain open.

The root imports, exact target BAT inventory, explicit audit and semantic
regressions include all ten modules: 31 public theorem audits and 45 regression
examples. Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, including coverage, dependency, integrity and
zero-warning gates. No frozen source or dependency pin changed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-172415-5a54834a.log`.
  All 511 package Lean files are covered, 522 Lean files scanned, and
  9366 build jobs pass. The exhaustive audit checks 4645 discovered target
  theorems and five imported boundary declarations: all 4650 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_172230.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 31 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 45 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 168 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 177 distinct nodes and 444 resolved edges.
`git diff --check` passes; the 16 Git LF/CRLF normalization notices
are not Lean diagnostics.

Semantic green-node check: HBSET is
`bourgain_separated_self_moment`, applying the native moment to the
actual reflected arbitrary set and paying the closed-support endpoint.
SHCS is `bourgain_slice_mixed_integral_cauchySchwarz`, using the
proved exact twist, support-only coefficient bound and complete integer image.
MCOMP is `bourgain_subdivided_mixed_comparison`, composing the actual
selected-family lower bound with the proved upper estimate on its source union
and full slice. LELIM is `bourgain_subdivided_level_free_comparison`;
its first coefficient is derived from the real component product, its second
uses exact multiplicity cancellation, and its power-sum loss uses the actual
disjoint-union cardinality and bin count.
PSCALE is `bourgain_linked_subdivision_comparison` and
`bourgain_ninth_row_physical_comparison`, deriving local ranges and
the original-height enclosure from the literal subdivision and shrinking
the allowed delta explicitly. No desired analytic estimate is a premise.

These are finite source-comparison results. Finite-loss absorption, the
logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain
unfinished; dependency integrity is not a claim of those endpoints.

### Heath--Brown/linked-subdivision checkpoint SHA256 evidence

These identify the verified files above; earlier checkpoint hashes remain
historical. The other 151 entries of the 168-file source/integration/runner
comparison were also unchanged across the target-gate snapshot and final read.
All ten new source texts were checked against their individually compiled
versions. No prior production theorem module changed in this iteration.

| File | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainSeparatedSelf.lean` | `ab29efcac629632d2209e31dbbd1dcc97a3e25de8d46ccc0ed37090a4dcce03a` |
| `Extension/TaoTrudgianYang2025/BourgainMixedShift.lean` | `eaed91e6f7cdadbdaa6b5e83e8ddda33031a1db0b9fdfb6be43abc3811a7e736` |
| `Extension/TaoTrudgianYang2025/BourgainMixedUpper.lean` | `c24926bc99134d8bba7b9ae477090232b0daf32e07fafb7515229ff073a71968` |
| `Extension/TaoTrudgianYang2025/BourgainCommonComparison.lean` | `6b30d1cc357722c767c0c05501a83f7c6c94c6b6971b91f38e47955f34847604` |
| `Extension/TaoTrudgianYang2025/BourgainLevelElimination.lean` | `0966e4ea94871bb93d32b71f0fe657054e56f4c93601a0db18ffe4264d2f87c4` |
| `Extension/TaoTrudgianYang2025/BourgainLevelFreeComparison.lean` | `107ab5d50ea8adae69f304d8affe127b947c2a8db4ba6fc9b72cb99eb8329f9c` |
| `Extension/TaoTrudgianYang2025/BourgainPhysicalUpper.lean` | `f62d5a4417c745980d8be957728dfeba5bd66f661a81c310faff5a83a13d30b2` |
| `Extension/TaoTrudgianYang2025/BourgainPhysicalComparison.lean` | `5c25362b175c4b30c27a0f16788091ed7f62a883b3a367385e5a9ec0810fbe9a` |
| `Extension/TaoTrudgianYang2025/BourgainSubdivisionScale.lean` | `88fc8b7f79605a019e45b5978404650320d8f2573b18dafaea8b67a57ccffbfe` |
| `Extension/TaoTrudgianYang2025/BourgainLinkedComparison.lean` | `5a6de1dd61642123a82ea9b2e9a5ca6221ec62302a5e36f62bfc8decf65d5a50` |
| `Extension/TaoTrudgianYang2025.lean` | `bf9c4c8278ffeaf609164aca668ba47c283647b6f1377545fe1329022f4844b4` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `7ead039c78dc6618437cdaf8b30876ff03a1f54791ffa7386f3d1bf200667d22` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `811fb8629ec1ad85f28c1f5ce2091d805361b04d48ad33e6f259f23ae86213e4` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `f7a9ead474bf971979b202b7505c13d1be00ee2d46ee11c14a082b93c58df061` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `E:/Lean/Riemann Zeta/run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `logs/tao-trudgian-yang-build-20260921-172415-5a54834a.log` | `5d287b490e03ede67d2d9b393a1c85a458916eca8cb974783b158d98a6b937b8` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_172230.log` | `88a623956370f0dc6a22f22b3be9f0da19ecd0022677bef7e2c398e32f1962c5` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_172230.json` | `bbcc3becfacafcb7cb3c99eb8b2d49c211861dada63b690ebc7b180274ac14a5` |

## Bourgain uniform finite power losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged
(SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The corrected independent cardinality and energy witnesses, Heath--Brown
energy relation and Add-est (i)--(viii) remain preserved. No false
s'/s fifth-coordinate scaling or third powering witness is introduced.

Five production modules now express the actual comparison's finite losses
as explicit powers, with constants chosen before the physical pattern:

- `BourgainCoefficientIdentity` proves beta^2=gamma exactly, including
  the zero fourth-moment-constant boundary, and beta=sqrt(gamma).
- `BourgainComparisonLogLoss` bounds the literal difference logarithm
  and amplitude count jointly by an arbitrary positive power.
- `BourgainCoefficientLosses` derives the ceiling-window product,
  enlarged local-height power and both coefficient lower bounds.
- `BourgainComparisonPowerBudget` bounds the square-root bin factor
  and original-height integration factor, and proves explicit slack control.
- `BourgainLinkedPowerLoss` consumes the actual constructed family,
  retained original-source union and complete integer slice.

### Exact finite consumer and parameter order

`bourgain_linked_power_loss_comparison` fixes
sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta,
and 0<epsilon<=8 before its constants B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta). Alpha is a permitted constant dependency;
this theorem does not assert uniformity in alpha. The earlier stronger
family-before-alpha construction is unchanged.

For the actual pattern, N>=max(C,N0), L=T/N^chi,
N^(tau-delta)<=T<=N^(tau+delta), and N^(sigma-delta)<=P.V,
the theorem derives L>0 and N<=L<=T. All local grids use lambda;
the Heath--Brown budgets retain the original T.

Write R=|S|, h=N^(epsilon/8), U=L+h+1, x=|Z(u)|, and

```text
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
F = C [N^(2-2sigma+epsilon)
       + N^(2lambda+4-8sigma+epsilon)
       + N^(-2alpha+lambda+12-16sigma+epsilon)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The real selected set S is a one-separated subset of the original ordinates,
with the original polynomial large at every member. Its packing inequality is

```text
|P.ordinates| <= 2 N^chi F + C H N^(epsilon+kappa) R.
```

Either |P.ordinates|<=2 N^chi F, or S is nonempty and a genuine grid level q
and u in (-h,h] give a nonempty complete integer slice with

```text
N^(2sigma-2delta) [
  N^(-2alpha-E)/G * x R
  + N^(-alpha-E/2-chi/2)/sqrt(2G) * sqrt(x) R^(3/2)]
< K N^(2eta+(tau+delta)theta)
    sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

The coefficient bounds come from the actual denominators, not assumed
certificates. The joint J Q Kc bound is applied to the actual localized
pattern; the bin factor comes from floor(T/L)+1<=2N^chi. The source comparison
at its original delta is specialized using monotonicity to the smaller
requested tolerance, while the new loss estimates use the smaller delta.
No caller supplies an analytic bound, desired correlation, or slice witness.

### Remaining acceptance work

This proves the finite power-loss reduction, not the logarithmic dichotomy.
Choose the small parameters in the required order, absorb the remaining fixed
constants in the limiting argument, control/extract the nonempty slice's
logarithmic cardinality, and use the actual packing inequality to relate R
to the original count. Discharge `bourgain_ninth_row_of_log_dichotomy`,
then the ninth energy projection and Add-est (ix).

The unrestricted printed-(4.7) source range, printed logarithmic-window
(4.48), other open classical/density/exponent-pair work, EPZAE-19/36/37,
and the full EPZAE-00--41 goal remain open. The power-window route is retained;
no public contract, source pin or dependency pin changes.

The root import graph, exact BAT production inventory, explicit axiom audit
and semantic regressions include these five modules and all 11 public theorems.
There are 20 new regressions: 11 exact signatures and nine boundary/slack cases.
Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, with complete coverage and unchanged integrity,
dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-175120-bcf6f466.log`.
  All 516 package Lean files are covered, 527 Lean files scanned, and
  9371 build jobs pass. All 4657 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4662-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_175131.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 11 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 20 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The first foundation attempt, `foundation_freeze_20260921_175009.log`,
failed its text scan on a prose-comment line beginning "constant boundary".
The comment was clarified; no proof or scan gate was weakened. That failed log
is retained as failed historical evidence, not substituted for the current PASS.

All 173 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 178 distinct nodes and 448 resolved edges.
Repository shortcut scans find no prohibited proof term or postulate;
remaining broad text matches are existing prose and rational structure fields.

Semantic green-node check: FPOWER is exactly
`bourgain_linked_power_loss_comparison`. Its proof unpacks
`bourgain_linked_subdivision_comparison`, applies the uniform coefficient
bounds to the derived local physical scale, applies the actual selection-count
bound to `P.localized L hL 0`, and uses the genuine bin count and original T.
It retains the source small alternative and the original polynomial, and
constructs the same complete zeta slice rather than assuming one.
The arbitrarily small tolerance is derived by shrinking the source delta.
No desired analytic estimate or limiting dichotomy is a premise.

This verifies finite power-loss reduction and dependency integrity only.
The logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain open.

### Current reproduction hashes

The following SHA256 values cover the five new production modules, all changed
integration files, both principal BAT entry points and the preserved counterexample.

| Path (relative to this node) | SHA256 |
| --- | --- |
| `Extension/TaoTrudgianYang2025/BourgainCoefficientIdentity.lean` | `9a5aa60db13744c4e35ff101ebe5876ad2a815ca6c7bd3a86e4b38e66d96b737` |
| `Extension/TaoTrudgianYang2025/BourgainComparisonLogLoss.lean` | `7fae8e29f2da147c9e3fcb998a491a6c395cbf08d0fe59a8258126270c05c2f3` |
| `Extension/TaoTrudgianYang2025/BourgainCoefficientLosses.lean` | `aadcb42065112e714e85d78b2b84421110e52fd4fec38c5d21a62a6d1efe4590` |
| `Extension/TaoTrudgianYang2025/BourgainComparisonPowerBudget.lean` | `d6bbe6be1c73d0bf17592e0c60b02b0f9351627e880d568ebdd14793dbe1ac22` |
| `Extension/TaoTrudgianYang2025/BourgainLinkedPowerLoss.lean` | `dda2913c7e0909092525ff9c1d779dcf77160389cd25972196456335e1cb2c34` |
| `Extension/TaoTrudgianYang2025.lean` | `bf3c3c8f87cfa5661728e354b7b6decf386042fded4eb7fc3d8801ff0be9d607` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `c54c8b25f9e82f08544d0bdad68098e338d9b17324554bf0f19cf1cfe044e638` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `06a91ff1f3b119075cbf20f2ac60945ba9b2a8f983f54954081c7279b024aa25` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `65a856080a94d59a7dcd81baf578076d2b7a35fd11c2ff27d36ff9d4b5e3bb13` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `../../run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |

| Verification artifact | SHA256 |
| --- | --- |
| `logs/tao-trudgian-yang-build-20260921-175120-bcf6f466.log` | `6bc467922a8a327f9d6bf59073563e0047fe5c267de6b61db643bc55f0fc71a7` |
| `../../logs/foundation_freeze_20260921_175131.log` | `6d053dcb509d8a815ba8fcc05de7cc0aaced6eec67ca96ff7b20b16a1f40d498` |
| `../../logs/foundation_freeze_20260921_175131.json` | `0868f9f856ffce423b6ff72841771a14c280e1074b549bc0cd28bdb7870573eb` |

The other 161 checkpoint source/integration hashes were also unchanged
across both gates. The foundation verifier remains SHA256
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
No dependency, frozen source or publication contract changed.

## Bourgain finite logarithms and slice compactness — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent corrected cardinality/energy witnesses, Heath--Brown relation,
and Add-est (i)--(viii) remain preserved. The false fifth-coordinate scaling
and third witness remain excluded.

Seven new production modules continue from the actual finite power-loss
comparison. They prove the physical slice-cardinality bound, translate both
comparison terms and the original-source packing inequality into logarithms,
and extract both real cardinality coordinates along one common subsequence.

### Actual finite logarithmic alternative

`bourgain_linked_logarithmic_comparison` consumes
`bourgain_linked_power_loss_comparison` on the original pattern, with the
same parameter order and an explicit nonempty-original-set restriction.
This restriction is needed because Mathlib gives log(0)=0; the theorem never
treats that convention as a logarithmic exponent for an empty set.

Fix sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta
and 0<epsilon<=8. Uniform B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta) precede the physical pattern. For the same
literal subdivision L=T/N^chi and original-height/amplitude hypotheses,
write

```text
rho = log_N |P.ordinates|, r = log_N |S|, x = log_N |Z(u)|,
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
Bsmall = max(chi+2-2sigma, -chi+2tau+4-8sigma,
             -2alpha+tau+12-16sigma),
HBexp(t,y) = max(2y+1, y+2, 5y/4+t/2+1).
```

Either rho<=Bsmall+epsilon+log_N(6C), or the actual nonempty retained subset
S and actual nonempty complete integer slice satisfy

```text
0 <= r <= tau+delta+log_N(2),
0 <= x <= lambda+delta+log_N(9),
rho <= log_N(6C+CH) + max(Bsmall+epsilon, epsilon+kappa+r),

max(-2alpha+2sigma+x+r-E-2delta-log_N(G),
    -alpha-chi/2+2sigma+x/2+3r/2-E/2-2delta-log_N(2G)/2)
< log_N(3K)+2eta+(tau+delta)theta
    + HBexp(tau+delta,r)/2 + HBexp(tau+delta,x)/2.
```

The source set remains one-separated and the original polynomial is large
at its members. The common grid level q and shift u remain genuine witnesses,
not separately supplied scalar cardinalities. All three Heath--Brown terms
are retained.

### Geometry, compactness and supporting limit algebra

`BourgainLogCardinality` proves the full slice has at most 2(U+h)+1
integers using its actual translated band, hence at most 9 N^(lambda+delta)
on the physical local scale. Positivity and logarithmic bounds are derived
from actual nonemptiness.

`BourgainBudgetLogarithm` proves the literal three-term budget is at most
3 N^HBexp at an actual cardinality, and proves joint continuity of HBexp and
its delta/2 height-slack bound. `BourgainComparisonLogarithm` takes logarithms
of both positive finite summands. `BourgainLogPacking` recovers exactly the
frozen first-branch maximum from the three small-component powers and keeps
the retained-to-original count loss explicit.

`bourgain_source_slice_log_subsequence` in `BourgainSliceCompactness`
derives a fixed box from actual pattern/subset/slice geometry and returns
one strictly increasing subsequence for both coordinates:
0<=r<=tau+2 and 0<=x<=lambda+5. No bounded-log-coordinate certificate is an
input. The harmless box constants do not replace the sharper finite bounds.

`BourgainComparisonLimits` proves fixed log_N multipliers tend to zero
when N tends to infinity. Its `bourgain_fixed_logarithmic_limit` passes an
explicit eventual finite logarithmic comparison and supplied coordinate
limits to the corresponding fixed-accuracy inequality. This is supporting
conditional limit algebra, not an assembled source-family dichotomy.

### Remaining source assembly

Construct the actual realizing family and select the small/large branch on
an appropriate subsequence. Apply the common compactness and limit results
to that selected family, use the original-count packing to identify the
retained exponent with the source exponent as the accuracy parameters
vanish, and remove epsilon/eta/theta/kappa/delta in their allowed order.
Then prove the frozen logarithmic dichotomy, discharge
`bourgain_ninth_row_of_log_dichotomy`, and assemble Add-est (ix).

The finite logarithmic alternative is not the zero-loss source theorem.
EPZAE-19/36/37, the ninth projection and clause (ix), all other unfinished
exponent-pair/density/public/release obligations, and the full EPZAE-00--41
goal remain open. The printed logarithmic-window (4.48) and unrestricted
printed-(4.7) range are not claimed.

All seven modules are in the root imports and exact BAT inventory, with
explicit audits for 21 public theorems and 31 new semantic regressions
(21 exact types plus ten boundary/source-form checks). Maintain
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
including full coverage, integrity, dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-182850-36f5160d.log`.
  All 523 package Lean files are covered, 534 Lean files scanned, and
  9378 build jobs pass. All 4683 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4688-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_182901.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 21 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 31 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The earlier foundation run at 182402 also passed but preceded the last source
edit; the 182901 run above supplies the final-source evidence.

All 180 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 180 distinct nodes and 455 resolved edges.
The runner inventory grew by exactly seven modules; source/dependency pins,
permitted axioms, foundation verification gates and both BAT launchers are
unchanged. No proof shortcut, postulate or warning suppression was introduced.

Semantic green-node checks:

- BLOG is `bourgain_linked_logarithmic_comparison`. It consumes the
  actual `bourgain_linked_power_loss_comparison`, derives the local scales
  from the original T and L=T/N^chi, and takes logarithms of the actual
  original/retained counts and complete integer slice. Nonemptiness,
  geometry, original-source packing, and both comparison terms are retained.
  The caller supplies no desired comparison or independent scalar witness.
- BSCOMP is `bourgain_source_slice_log_subsequence`. It derives a common
  compact box from the physical height and subset/slice hypotheses and
  returns one strictly increasing subsequence for both actual coordinates.
  It does not itself choose a realizing family or select the source branch.
- `bourgain_fixed_logarithmic_limit` is explicitly conditional supporting
  algebra: the eventual finite comparison and coordinate limits are inputs.
  It is not used to mark the full analytic source dichotomy green.

This verifies the finite logarithmic alternative, geometric compactness and
fixed-constant limit algebra only. Source branch selection, zero-loss limiting
assembly, Add-est (ix), and the unchanged whole-proof contract remain open.

### Current logarithmic checkpoint hashes

The seven new modules, four synchronized integration files, two preserved BAT
launchers and preserved counterexample have the following SHA256 values.
The other 166 entries in the 180-file checkpoint retain their previously
recorded values; all 180 match the snapshot taken before both final BAT runs.

| Artifact (relative to this node unless stated) | SHA256 |
|---|---|
| `Extension/TaoTrudgianYang2025/BourgainLogCardinality.lean` | `d3afcb2526ba0fc3fbc75e85737434145ead8400249dd21303e2d36fc86f2cae` |
| `Extension/TaoTrudgianYang2025/BourgainBudgetLogarithm.lean` | `acfd2c918036a9b459301c54abbcc8061069bd5258fc8412ce1ae66e5409c816` |
| `Extension/TaoTrudgianYang2025/BourgainComparisonLogarithm.lean` | `7299b4bab144bb51137505c9dfe44667d46398e17a02732d081fdb764ae5b871` |
| `Extension/TaoTrudgianYang2025/BourgainLogPacking.lean` | `93f9ab1cea7de86d1bfec0570a88c1068c8bebd14aaccc2e4ccd0ecb969f4159` |
| `Extension/TaoTrudgianYang2025/BourgainLinkedLogarithm.lean` | `1f8e4c4544cf01f883ed84aa2aebbb9d533bff28ee5831dfaa19adda2cc4beaa` |
| `Extension/TaoTrudgianYang2025/BourgainSliceCompactness.lean` | `d9b44ae7c52cbc8a9da365915fc4539e37500c27a3929ec6ea45a87dc7ff456f` |
| `Extension/TaoTrudgianYang2025/BourgainComparisonLimits.lean` | `0593909b75f214f2bf2de1ddce0730f5469d6d81f64a171655bcd112888dbf27` |
| `Extension/TaoTrudgianYang2025.lean` | `86575d527abf6d79de32fae41f1202c6bfa207b691cb65d36b21f26ee361ac17` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `d8392998e54a0f893a609ebff0f378e0e949f0c4205c432ed42f6e6938ea68cb` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `231c1cc531d7da91048357d8313e06f9c79ee1322045a14932190888bcca5525` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `ecab452bae137a2cbdc2374298c862723c7b22527509c7b648717b9351ccab43` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `../../run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |

| Verification artifact | SHA256 |
|---|---|
| `logs/tao-trudgian-yang-build-20260921-182850-36f5160d.log` | `a7b10846c237380e1ed01a2a03067985bc0a6b799ca9876da15130237d9acb12` |
| `../../logs/foundation_freeze_20260921_182901.log` | `baba4eaff81332f21f3c36b379dd584db405c40fd49260e3f3230786eef2a85c` |
| `../../logs/foundation_freeze_20260921_182901.json` | `75e3ee645111024af717e88aab0cb685c8cdffca1495cb829ef11b211db66e50` |

The retained counterexample hash is the original accepted hash, not a new
replacement. The current passes certify installed source scope, not completion
of Add-est (ix) or the full paper.

## Bourgain source dichotomy and optimized region rows — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses, the Heath--Brown
relation and Add-est (i)--(viii) are preserved. No fifth-coordinate scaling
or third powering witness has been restored.

### Actual source-family construction and zero-loss limit

`exists_bourgain_region_family` chooses actual patterns from
`InCardinalityEnergyRegion` after arbitrary positive physical tolerances
and arbitrary scale thresholds. Its cardinality logarithms converge to the
source rho by the region's power sandwiches.

`exists_bourgain_diagonal_family` applies the proved finite logarithmic
alternative at accuracy `poweringAccuracy n`, choosing all analytic constants
before the patterns. One finite sum of exponential thresholds absorbs the
five varying factors G, 2G, 3K, 6C and 6C+CH. If rho>Bsmall, the source count
limit rules out the small branch on a tail. The retained source subsets,
original polynomial values and complete integer slices are actual witnesses,
not independent scalar inputs.

The resulting family has source packing

```text
rho_n <= epsilon_n + max(Bsmall+epsilon_n, 2epsilon_n+r_n)
```

and, for the same actual retained/slice cardinalities,

```text
max(-2alpha+2sigma+x_n+r_n,
    -alpha-chi/2+2sigma+x_n/2+3r_n/2)
<= (2tau-chi+12)epsilon_n
   + HBexp(tau,r_n)/2 + HBexp(tau,x_n)/2.
```

The explicit diagonal loss tends to zero. Joint geometric compactness
extracts r and x along one common subsequence. Subset monotonicity gives
r<=rho; the original-source packing and rho>Bsmall give rho<=r.
Thus r=rho, and continuity gives the exact zero-loss comparison.

The public consumer
`InCardinalityEnergyRegion.bourgain_log_dichotomy` now proves

```text
rho <= Bsmall
or exists x>=0,
  max(-2alpha+2sigma+x+rho,
      -alpha-chi/2+2sigma+x/2+3rho/2)
  <= HBexp(tau,rho)/2 + HBexp(tau,x)/2,
```

from actual region membership, sigma>3/4, chi>=0 and tau-chi>1.
It takes no source family, branch-stability assertion, coordinate-limit
certificate or analytic dichotomy as a premise. This closes the formerly
open source branch selection and zero-loss assembly in that physical range.

### Optimized region rows

Classical cardinality bounds discharge rho<=1 for tau<=3/2.
`InCardinalityEnergyRegion.bourgain_ninth_row` consumes the actual
dichotomy and the existing exact scalar certificate; its powered version
uses the corrected cardinality-preserving witness.

Three additional optimized rows follow from the same actual dichotomy.
For all rows below, sigma>3/4 and 1<=tau<=3/2; the listed additional cell
conditions are retained exactly.

| Row | Cardinality bound | Additional cell conditions |
|---|---|---|
| First affine | rho <= (16-20sigma+tau)/3 | 14sigma-10<=tau<=16sigma-11; 5tau<=4+4sigma |
| Mixed affine | rho <= 5-7sigma+3tau/4 | 4+4sigma<=5tau; 48-60sigma<=tau<=8-8sigma |
| Diagonal | rho <= 2-2sigma | tau<=14sigma-10; tau<=3sigma-1 |
| Ninth row | rho <= 9-12sigma+2tau/3 | 16sigma-11<=tau; 20sigma+tau/3<=16 |

The first-affine and diagonal height-one boundaries use the classical
estimate, not a weakened strict-margin hypothesis. The mixed cell itself
forces tau>1. Exact regressions include the common affine corner
(sigma,tau,rho-bound)=(59/76,27/19,12/19), the original 84/109 endpoint,
the height-one boundary and the actual power-two consumer.

### Remaining acceptance work

Add-est (ix) is still open. The frozen ANTEDB
`prove_zero_density_energy_7()` recipe uses tau0=8sigma-4, Bourgain and
Jutila-k=5 cardinality inputs, powers 2 through 5, the zeta moment and
Heath--Brown energy. Continue with actual corrected witnesses and exact
general/zeta energy projection over the entire interval [84/109,5/6].
Do not treat the proved cardinality row as the final energy bound.

The complete unrestricted Bourgain source range, its uniform LV-facing
assembly, any additional optimized cells required by that projection,
EPZAE-19/36/37, the other unfinished exponent-pair/density/public/release
obligations and the full EPZAE-00--41 goal remain open. Neither the printed
logarithmic-window (4.48) nor the unrestricted printed-(4.7) range is claimed.

Six new modules are root-imported and included in the exact BAT inventory.
All 15 public theorems have explicit audits and 24 new semantic regressions
(15 exact signatures and nine endpoint/object checks). The old
`NewAdditiveEnergy` module comment was corrected to say (i)--(viii), matching
its already proved theorem surface. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
with no exclusions, weakened scans, changed dependency pins or warning suppression.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-190824-8fa4580d.log`.
  All 529 package files are covered, 540 Lean files scanned and 9384
  build jobs pass. The exhaustive audit passes 4723 discovered target
  theorems plus five imported boundary declarations, 4728 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_190824.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and all declaration linters.

All 15 new public audits report only `propext`, `Classical.choice`
and `Quot.sound`. All 24 new regressions pass. Both complete final logs
contain zero Lean errors, warnings or tactic suggestions. Repository-wide
shortcut scans have no prohibited proof-term match; the broad declaration
search matches only existing prose and the two genuine rational structure
fields, also accepted by the contract-aware scanners.

All 186 checkpoint source/integration/runner hashes match the snapshot
taken before the final BAT runs. The counterexample and both BAT launchers
are unchanged. Only five existing integration/status files changed; the
remaining new Lean work is in the six named modules. No source/dependency
pin, permitted-axiom policy or verification gate was weakened.

The architecture has 183 distinct nodes and 464 resolved edges.
Semantic green-node checks:

- BDFAM is `exists_bourgain_diagonal_family`: it consumes actual region
  realizations and the finite analytic alternative, absorbs constants by
  its chosen physical scales, and derives branch selection on a tail.
- BDICH is `InCardinalityEnergyRegion.bourgain_log_dichotomy`: it invokes
  that constructor and `BourgainDiagonalFamily.source_witness`; the latter
  consumes actual geometric compactness and original-source packing to
  prove r=rho before taking the zero-loss limit.
- BROWS consists of the four stated actual-region row theorems and
  `bourgain_ninth_row_powered`. They consume the proved dichotomy,
  classical side-condition bridge, exact scalar algebra and corrected
  cardinality witness. The height-one cases are handled explicitly.

These passes verify the installed region dichotomy and specified cardinality
cells, not the full Bourgain source range, Add-est (ix), or whole-proof
completion. The energy projection and all other open goal obligations remain open.

### Current source-dichotomy checkpoint hashes

The six new modules, five synchronized integration/status files, two preserved
BAT launchers and preserved counterexample have these SHA256 values. The other
172 entries retain their previously recorded values. All 186 source checkpoint
hashes were revalidated after both final BAT runs.

| Artifact (relative to this node unless stated) | SHA256 |
|---|---|
| `Extension/TaoTrudgianYang2025/BourgainRegionRealization.lean` | `6dc294182ac1745865d3810ddeef162d3408793f56008fb0dbab44a10632b141` |
| `Extension/TaoTrudgianYang2025/BourgainDiagonalLoss.lean` | `db53afc086f730134766c8c06906558bed75f4967d47a15bb0742c225d2d8cfb` |
| `Extension/TaoTrudgianYang2025/BourgainDiagonalFamily.lean` | `cb6680d96cbca1d2433f0566d3e9e1563564437cd91ddd316801c632edfb56d2` |
| `Extension/TaoTrudgianYang2025/BourgainRegionDichotomy.lean` | `4070773ffd13f84445cd40d465c2b22130011f421e8aaa90ed41285fa4dfbb49` |
| `Extension/TaoTrudgianYang2025/BourgainNinthRow.lean` | `61f89edf6cc666c9a9b55bf2303b4ae32f35456128a1ac91b6fa24f232f04276` |
| `Extension/TaoTrudgianYang2025/BourgainLowHeightRows.lean` | `b32b049be5c61d3f02b2cb79476426e769b9533d3b36533988be845e1e6591a3` |
| `Extension/TaoTrudgianYang2025.lean` | `d8d06ef945eea21500797e8d08885db5ac9f171cbf3d99977a304e32837de434` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `94000758449fed64fd40278417b177e977298aa1b07ffc9d22373d3026cfbfb6` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `0551c5f72aab00b3625ada814e167abff80ef5840f3043d43ee385bec3c258cb` |
| `Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean` | `53c4d2c8e36c8de74283050de71c09447c352fb5d9c918e81b7503b6d5d1f85c` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `3241cd7c880b5c21f32ac08ec7c46a2c423156521ab1873d1d9574263df02d61` |
| `run_tao_trudgian_yang_build.bat` | `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098` |
| `Extension/TaoTrudgianYang2025/EnergyPoweringObstruction.lean` | `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487` |
| `../../run_lake_build.bat` | `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303` |

| Verification artifact | SHA256 |
|---|---|
| `logs/tao-trudgian-yang-build-20260921-190824-8fa4580d.log` | `f0d9f1f735c4c488f1eb3ae4341ef95236c5b52a946f624e5af56e89305a5349` |
| `../../logs/foundation_freeze_20260921_190824.log` | `b07b7ee8b13c06fa0ab3e49ecf0275826e891fc006cfcbdadce1174bf5da8918` |
| `../../logs/foundation_freeze_20260921_190824.json` | `e59c9a626210870609acd06e45b2d2c92b21147d1be0bc4987951c89f61d3038` |

The complete current logs and JSON, not historical checkpoint counts, support
the verification claims above. No commit or push was performed.

## All nine Add-est clauses recovered by corrected powering — historical checkpoint

### Result and preserved obstruction

The authorized repair now recovers every printed Add-est clause (i)--(ix).
The original singleton counterexample in `EnergyPoweringObstruction.lean`
is unchanged (SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
Printed Lemma 62 remains false as printed: its fifth-coordinate scaling
has not been restored or assumed. The archived source and public output
statements have not been changed.

`correctedCardinalityEnergyPowering` supplies separate cardinality- and
energy-preserving witnesses. Their fifth exponents remain independently
existential. The actual Heath--Brown consumer uses the appropriate witness,
and cardinality monotonicity supplies the other coordinate's upper bound.
This is not a claim that an arbitrary four-coordinate polytope is preserved.

### Exact final-clause consumer

On the entire closed interval `84/109 <= sigma <= 5/6`, write

```text
B(sigma) = max((18-19sigma)/(9(3sigma-2)),
               4(10-9sigma)/(5(4sigma-1))).
```

The new public declarations are:

- `add_est_ix_bound`: `IsZeroDensityEnergyBound sigma (B(sigma)/(1-sigma))`.
- `add_est_ix`: the literal printed extended-real inequality
  `A*(sigma)(1-sigma) <= B(sigma)`.
- `add_est_ix_zero_energy`: for every positive epsilon, one constant and
  one positive sigma-shift bound the actual multiplicity-aware zero energy
  by `C T^(B(sigma)+epsilon)` for every sufficiently large T.
- `energyClauseNine_blueprint`: the exact divided blueprint normalization.

These theorems have only the stated sigma interval hypotheses. They do not
accept an energy estimate, cardinality theorem, source dichotomy, moment,
or optimization result as an analytic theorem premise.

The full general range `8sigma-4 <= tau <= 2(8sigma-4)` is derived by
`InCardinalityEnergyRegion.energyClauseNine_general`. Below sigma=4/5,
the exact power cover chooses q=2 or 3. Independent cardinality witnesses
at q and q+1 give rho/q<=3-3sigma. At t=tau/q<=6/5, Jutila k=5 and the
energy witness at q-1 feed all nine Heath--Brown branches. For
6/5<=t<=3/2, the actual corrected cardinality witness consumes the proved
Bourgain first-affine, mixed-affine or ninth row, while the independent
q-energy witness supplies the two energy branches. Above 3/2, all six
q-energy branches use the cardinality cap. For sigma>=4/5, the already
proved clause-(i) general rate is compared exactly with B.

The middle-height cover is exact, not sampled. Its sigma split is 17/22;
its switching lines are (81-96sigma)/5, (13-8sigma)/5, 16sigma-11,
(4+4sigma)/5, 48-60sigma, (27sigma-18)/2 and (16sigma-8)/3.
All overlaps and boundary cases are included. The proof needs no additional
high-height Bourgain row or unrestricted Bourgain theorem.

`energyClauseNine_zeta_bound` derives the complete interval
`1 <= tau <= 8sigma-4`: actual emptiness below 3/2, the proved twelfth
moment with cubic energy on [3/2,2], and the actual clause-(i) zeta
Heath--Brown consumer above 2. `energyClauseNine` then invokes the proved
endpoint-one bounded-range transfer with the source cutoff tau0=8sigma-4.
No endpoint-two source corollary is assumed.

### Coverage, source fidelity and remaining goal

Nine new modules are installed: `EnergyClauseNineRates`,
`EnergyClauseNineShortCertificates`, `EnergyClauseNineMiddleCertificates`,
`EnergyClauseNineTallCertificates`, `EnergyClauseNineBranches`,
`EnergyClauseNineRegion`, `EnergyClauseNineGeneral`,
`EnergyClauseNineZeta` and `EnergyClauseNine`.
There are 42 new closed-range branch certificates, 71 explicitly audited
public theorems including the three new `NewAdditiveEnergy` exports, and
85 new semantic regressions (71 exact signatures and 14 endpoint/object
checks). Every module is root-imported and listed in the exact BAT inventory.

The literal rate and domain were checked against frozen TeX label
`Add-est`, clause (ix), and the paper-time ANTEDB
`prove_zero_density_energy_7()` recipe with tau0=8sigma-4. Numerical
exploration was used only for discovery. Lean checks every certificate
and every actual-region consumer. The repaired proof is not a claim to
replay the archived Python's false five-coordinate powering transformation.

EPZAE-36 and EPZAE-37 now meet their mathematical acceptance tests: all
nine clause projections feed actual general/zeta consumers, and every
printed interval has an audited source-facing theorem and actual-zero
epsilon--delta consequence. EPZAE-06 remains open for deterministic
projection-recipe reproduction, rather than missing energy mathematics.
EPZAE-19's unrestricted Bourgain source range and uniform LV assembly,
EPZAE-33's separate source endpoint-two corollary, the other exponent-pair,
density, public-assembly and release obligations, and the full EPZAE-00--41
goal remain open.

Both `run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`
remain required acceptance interfaces. Maintain their exact inventory and
explicit audits whenever modules change; no exclusion, dependency-pin
change, relaxed warning rule or fifth-coordinate shortcut is permitted.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-194712-b1ebacdc.log`.
  All 538 package files are covered, 549 Lean files scanned and 9393
  build jobs pass. The exhaustive audit passes all 4809 discovered target
  theorems plus five imported boundary declarations: 4814 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_194607.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and the declaration-linter gate.

Every one of the 71 new explicit public audits was found in the final
target log and has only permitted standard logical dependencies
(`propext`, `Classical.choice`, `Quot.sound`, or subsets). All 85 new
semantic regressions pass. The complete final logs contain zero Lean
warnings, errors or tactic suggestions. The repository shortcut scans
have no prohibited proof-term match; broad declaration matches are
existing prose and the two genuine rational structure fields.

All 195 checkpoint source/integration/runner hashes match the snapshot
taken before the final target BAT run. The counterexample, both BAT
launchers, frozen sources and dependency pins are unchanged. Relative to
the preceding checkpoint, exactly five existing integration/status files
and the nine new Lean modules carry the implementation. All 186 dirty
worktree entries remain within node 63; unrelated work was not changed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 187 distinct nodes and 481 resolved edges.
The semantic green-node checks are:

- EC9C: the 42 explicit short/middle/tall branch inequalities, together
  with the rate/sign lemmas, are exact on their complete stated ranges.
  `energyClauseNine_short_branch`, the middle consumers and
  `energyClauseNine_tall_branch` apply them to the actual branch outputs.
- EC9G: `InCardinalityEnergyRegion.energyClauseNine_general` consumes
  genuine region membership, derives the power cover and cardinality caps,
  unpacks the corrected cardinality witness, and invokes the independent
  Heath--Brown energy witness. `energyClauseNine_general_bound` supplies
  the uniform epsilon-loss estimate by the proved region realization.
- EC9Z: `energyClauseNine_zeta_bound` consumes actual short-pattern
  emptiness, the proved twelfth moment and the actual zeta-region
  Heath--Brown consumer. No zeta-energy estimate is assumed.
- EC9/NAE: `energyClauseNine` consumes both full uniform ranges at
  tau0=8sigma-4. The three `add_est_ix` exports preserve the literal
  paper maximum, its full closed sigma interval, the real shifted zero
  multiset and analytic multiplicities. Alongside the already audited
  (i)--(viii) exports, this completes the nine-clause Add-est acceptance
  test, not the other public theorem families or the whole goal.

The mathematical completion of EPZAE-36/37 and the integrity-gate PASS
are separate conclusions; neither is inferred merely from audit counts.

### Current verification artifact hashes

| Artifact | SHA-256 |
|---|---|
| `logs/tao-trudgian-yang-build-20260921-194712-b1ebacdc.log` | `e405f9e886dd83922c750c23e8ef6e33db5aeb608d7022e73bd2beaaff0ab890` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_194607.log` | `bdd6cbf63e1c5c3ff4b6dd8c80d4a9acd7230b63b8f53301c823b4a1e657c914` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_194607.json` | `25a041c18689e1ea5d3d4058fd88c8f3603abcc8ca97fb1bf1be585e33b517c9` |

### Final-clause implementation hashes

The older checkpoint rows remain historical. The following are the current
changed/new implementation files; the remaining checkpoint files were
revalidated byte-for-byte against the preceding 186-file snapshot.

| File | SHA-256 |
|---|---|
| `Extension/TaoTrudgianYang2025/EnergyClauseNineRates.lean` | `de3159eb63738ecc761551e75a08b1e3df8a010f812791ccd6a386745e884b71` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineShortCertificates.lean` | `1c1ec2a259d038bdb7d6784b8b7457181e8ad94efa61a97ba6f1366872ca4d6f` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineMiddleCertificates.lean` | `6d33fc39404a60ccef08482cbed47e729913e0d87e81ff684a26f667105fc72f` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineTallCertificates.lean` | `b6513aced62919bde7409c51990f68ec31587c4c2bcbcbc8e513fa24697b5b05` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineBranches.lean` | `d3fc633825c2a06e43ad50218215f2505c1743be742a088f8a86251af153fab0` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineRegion.lean` | `86eb243d957d80b5523afe205942e8c175d08f90c90b5a3de768ec816d379edd` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineGeneral.lean` | `8b06cffc234d9eb277f65688a5e250d47a8ace6d33c030733630baa1bd6b5014` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNineZeta.lean` | `fe67a16f33fd3a953f5ef412ff2310524d59f616244a557e872d7e1ed5984131` |
| `Extension/TaoTrudgianYang2025/EnergyClauseNine.lean` | `3eb448a59a827f80fbc42235d67be8eda2daa76d8c0e987bcf3147c9832af281` |
| `Extension/TaoTrudgianYang2025/NewAdditiveEnergy.lean` | `f2cf0a34387ef1414daeb37f31637af2be9a27cb1bf5f4a9f74b01dc06c80741` |
| `Extension/TaoTrudgianYang2025.lean` | `20bb55182acb13c8b9e73327520598554bcfbf53fcc477fdd4bda23ff0afbd26` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `5493255ea3ac1cbd8fa836c0284a33b5905c8b6a9312d4ffc9330482f781dcd3` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `8f132fff211cb84e7cee24d01a3e230cb9544e7578ce73998a9b1d8aa4324843` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `dbe442ea9af85ef8709a035d58fc7937b7504af2de8b9da4f56163f934abbcfd` |

The archived-paper counterexample and both BAT launchers retain the
unchanged hashes recorded in the preceding checkpoint. The foundation
verifier SHA-256 remains
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

## Closed beta duality from actual model-phase sums — historical checkpoint

### Exact mathematical result

`exponentPair_iff_beta_bound` proves frozen TeX label `beta-duality`
with its full closed range: for every candidate in the source triangle,
the actual analytic `ExponentPair k l` predicate is equivalent to
`beta(alpha) <= k + (l-k)*alpha` for every `0 <= alpha <= 1`.
This is not polygon membership or an assumed exponent-pair estimate.

The converse, `isExponentPairEstimateNonAsymptotic_of_beta_bound`,
takes a finite subcover of the compact alpha interval. Minimum phase
tolerance, maximum derivative order and maximum threshold supply one
uniform set of constants for every physical pair `1 <= N <= T`.
The proof links alpha to `log_T N` and proves the exact real-power
identity with the original epsilon losses.

For the forward endpoint, the actual approximate-model condition gives
`c_sigma <= -F'' <= sigma+1` on the interior, with
`c_sigma = sigma*2^(-sigma-1)/2 > 0`.
`betaModelSample_secondDifference_bounds` transports this curvature
to the physical samples `-2*pi*T*F((A+n)/N)`.
`norm_exponentialSumAt_le_secondDerivative` consumes that result,
the native Guth--Maynard finite second-difference estimate, the proved
complex-conjugation/radians bridge, and all three boundary terms. It yields

```text
||sum_{a <= n <= b} e(T F(n/N))||
  <= K_sigma (sqrt(T) + N/sqrt(T))
```

for `T,N >= 1`, `T <= N^2`, the original dyadic endpoints, and
the stated approximate-model tolerance. The estimate is not a premise.
The non-asymptotic ANTEDB interface then gives
`exponentSumGrowthExponent_one_le_half`.
Together with the existing forward theorem on alpha<1, this proves
`exponentSumGrowthExponent_le_exponentPairLine_closed`.
`exponentSumGrowthExponent_zero` also proves beta(0)=0.

### Semantic status and remaining obligations

EPZAE-09's convex closure and exact closed-interval two-way duality are
proved. EPZAE-09 remains OPEN: the source reflection identity
`beta(1-alpha)=1/2-alpha+beta(alpha)` and the lower endpoint bound
`1/2 <= beta(1)` are not claimed here. The finite second-derivative
estimate is not the source dual-phase B transformation, and does not
complete EPZAE-10's B-process, the A/C/D processes, the derivative inputs,
the beta table, or any of the four new exponent-pair outputs.

Seven modules are installed: `BetaUniformity`, `BetaSecondDerivative`,
`BetaDiscreteCurvature`, `BetaBProcessMajorant`, `BetaFiniteSum`,
`BetaModelSumBound` and `BetaClosedDuality`.
Their 21 public theorems have explicit dependency audits and exact-type
regressions; six additional checks cover the closed endpoints, the uniform
physical estimate and an actual closed-interval model sum at T=N.
All seven modules are root-imported and listed in the exact principal BAT
inventory.

The permanent singleton counterexample to printed Lemma 62 is unchanged.
The corrected independent rho/k and rho*/k witnesses, Heath--Brown
consumers, and all nine proved Add-est clauses remain intact.
No fifth-coordinate scaling or third witness has been restored.
EPZAE-36/37 remain DONE; the whole EPZAE-00--41 objective and its other
open acceptance tests remain unchanged.

`run_tao_trudgian_yang_build.bat` remains the target's principal
acceptance interface, alongside foundation `run_lake_build.bat`.
Maintain their exact module inventory, explicit audits, warning gate and
source-integrity checks as work continues. This checkpoint is concrete
progress toward the original whole-proof goal, not a replacement goal.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-202605-c2073498.log`.
  All 545 package files are covered, 556 Lean files scanned and 9400
  build jobs pass. The exhaustive audit passes 4840 discovered target
  theorems plus five imported boundary declarations: 4845 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_202606.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

All 21 new explicit public audits were found in the final target log;
each has only `propext`, `Classical.choice` and `Quot.sound`.
All 27 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 204 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. The 195-file preceding snapshot has
only the four expected integration/runner changes; coverage also adds
seven new Lean modules and the two existing module headers corrected
to describe the now-proved equivalences. The permanent counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, frozen archives and dependency pins are unchanged.
All 195 dirty worktree entries remain within node 63. No unrelated
user changes were reverted, staged, committed or pushed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 193 distinct nodes and 496 resolved edges.
Its new green-node checks are:

- DUC: `ExponentPair.convexCombination` is the previously proved
  analytic convex-closure theorem, not just triangle closure.
- DUU: `isExponentPairEstimateNonAsymptotic_of_beta_bound` consumes
  actual ANTEDB beta bounds at every alpha and derives uniform physical
  constants through a finite subcover; N and T are linked by log_T N.
- DUS: `norm_exponentialSumAt_le_secondDerivative` consumes the
  actual approximate-model phase, derived curvature, physical discrete
  differences, conjugation identity and three boundary terms.
- DUE: `exponentSumGrowthExponent_zero` proves beta(0)=0, and
  `exponentSumGrowthExponent_one_le_half` consumes the complete
  finite estimate through the genuine non-asymptotic beta definition.
- DUF: `exponentPair_iff_beta_bound` assembles both directions for
  the exact source triangle and every alpha in the closed unit interval.
  It does not assume an exponent-pair estimate in the converse or a
  beta reflection theorem in the endpoint proof.

DUR and aggregate EPZAE-09 remain open for the exact reflection identity
and beta(1)>=1/2. The named source `beta-duality` lemma is proved,
but this does not complete its broader Checklist item, the remaining
public-output families or the whole goal. Mathematical/source
completeness and dependency-integrity PASS are separate conclusions.

### Current verification artifact hashes

| Artifact | SHA-256 |
|---|---|
| `logs/tao-trudgian-yang-build-20260921-202605-c2073498.log` | `32fde85b7f313397661ec343ab263b93268eeb9f7f61e1d5920aecb00fa6e6c6` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_202606.log` | `4694e03a39cd7b95186f8de948bddaffe12d30378166bbec4ebcd30ab8cceab9` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_202606.json` | `11ba0f18d18e3610c162e1829049e6313816c2d7dad03b4207c8684b566a4b6a` |

### Closed-duality implementation hashes

Older checkpoint rows are historical. These are the changed or new files
for the current duality checkpoint; all 204 covered source hashes were
revalidated against the final pre-gate snapshot.

| File | SHA-256 |
|---|---|
| `Extension/TaoTrudgianYang2025/BetaUniformity.lean` | `236fc77e6958c6179416af759075a6644b1a08bd740ad1c9d6e6894ffe8e8ef5` |
| `Extension/TaoTrudgianYang2025/BetaSecondDerivative.lean` | `405316470ef10cf23502cef6558990d921dc4ff69297eab08c31eefb59521507` |
| `Extension/TaoTrudgianYang2025/BetaDiscreteCurvature.lean` | `e83248803c0090494d9bc7c643268e3fa3e94acb93b3b7fbc951b95ebe5bc155` |
| `Extension/TaoTrudgianYang2025/BetaBProcessMajorant.lean` | `f9b21ad359730fecb3d91490b997abe67c30e1070ca9665efda59b7565dae7fc` |
| `Extension/TaoTrudgianYang2025/BetaFiniteSum.lean` | `2d613a5c51eae3c219429468ce7af391b70ca83c58da2f83a442bd01442744cf` |
| `Extension/TaoTrudgianYang2025/BetaModelSumBound.lean` | `dd13d0a92e18284bec5a97005ff02d50ff212be741637e9ca1a1b57e7dee90bb` |
| `Extension/TaoTrudgianYang2025/BetaClosedDuality.lean` | `ca8aa4428721830dd2a5950119357386a5c7d335338e29f2ab6c920d05c062ba` |
| `Extension/TaoTrudgianYang2025/ExponentPair.lean` | `b3c55c85e224c126cfe6bed34eacc4ff4e2cce63d41cb6cba0493a3d5373d789` |
| `Extension/TaoTrudgianYang2025/BetaDuality.lean` | `0cfdeae1c39a0d738a8c0acab0a2ef30014d061e618cf3547c8dcb911f6f2adb` |
| `Extension/TaoTrudgianYang2025.lean` | `b401537f7984848f0b430ce67dc4a69e1cd4dcf5cde369a3b1193eb3b3758b55` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `411c05def733ecaacec4c8e59421cd5ca0ed62a4ed65d0f237c5d677abc326e1` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `29d7646a05eb53ff0b2b4ce466a1500d2ae60d8604a5f81cb0e87c6257d9c66c` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `3ebe17a178d810b349e9b8f38a82f87cf51b3af31a979e52a9693a01b81eaad2` |

Both BAT launchers retain their prior hashes. The unchanged foundation
verifier SHA-256 is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

## Exact beta endpoints and classical second-derivative pair — historical checkpoint

### Exact mathematical results

`exponentSumGrowthExponent_endpoints` now proves the complete frozen
`beta-end` statement: beta(0)=0 and beta(1)=1/2.
`half_le_exponentSumGrowthExponent_one` supplies the missing lower bound
from the actual logarithmic model phase, without a mean-square estimate
as an assumption.

For every natural m, set N=T=16(m+1)^2 and use the closed integer interval
[N,N+m]. For each 0<=j<=m, the proved elementary logarithm inequalities give

```text
|N log((N+j)/N)-j| <= j^2/N <= 1/16.
```

Cosine periodicity removes the integer j in the real part of the original
oscillatory factor. The remaining angle has absolute value at most one,
so each term has real part at least 1/2.
`norm_logPhase_resonant_sum_lower` therefore proves, for this actual sum,

```text
||sum_{N <= n <= N+m} e(N log(n/N))|| >= sqrt(N)/8.
```

The scale is unbounded, both dyadic endpoints are derived, and N=T gives
the exact power-asymptotic exponent one. The audited ANTEDB logarithmic
lower-bound consumer yields beta(1)>=1/2. Together with the prior
second-derivative upper bound, this proves equality. This is an alternate
proof of the exact endpoint claim; it does not claim to formalize the
paper's separate L2 proof of beta(alpha)>=alpha/2 for every alpha.

`isExponentPairEstimateNonAsymptotic_half_half` also proves the genuine
uniform estimate for the classical pair (1/2,1/2).
For T<=N^2 it consumes the actual model-phase second-derivative estimate;
N<=T bounds N/sqrt(T) by sqrt(T). For T>N^2, the original finite sum is
bounded by 3sqrt(T) using its cardinality. The phase tolerance, derivative
order and constant depend only on the source parameters, and every
epsilon loss is retained.
`exponentPair_half_half` converts this to the original asymptotic
predicate. Closed duality then proves
`exponentSumGrowthExponent_le_half` and the combined bound
`exponentSumGrowthExponent_le_min_self_half` on 0<=alpha<=1.

### Coverage and remaining whole-proof obligations

Four new modules are installed: `BetaLogCoherence`, `BetaResonantSum`,
`BetaEndpoints` and `ClassicalSecondDerivativePair`.
Their 18 public theorems have explicit audits and exact-signature
regressions, plus six additional actual-sum, analytic-predicate and
endpoint checks. The root imports and the exact PowerShell inventory
behind `run_tao_trudgian_yang_build.bat` cover every module.

EPZAE-09 now has proved convex closure, full closed-interval two-way
duality, and both exact beta endpoints. Its sole remaining acceptance
obligation is the reflection identity on the whole unit interval.
The two endpoint reflection regressions do not establish the interior
identity. The classical seed is not the full B transformation; all
unproved A/B/C/D process, derivative, beta-table, advertised new-pair,
density, public-assembly and release obligations retain their status.
The whole EPZAE-00--41 goal remains active and unchanged.

The original Lemma 62 counterexample is preserved byte-for-byte.
Corrected independent rho/k and rho*/k powering, the Heath--Brown
consumers, and all nine Add-est clauses are unchanged; EPZAE-36/37
remain DONE. No scaled fifth coordinate or third witness is assumed.

Keep both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` as mandatory acceptance gates. Continue updating
the exact module inventory, root imports, explicit audits and semantic
regressions whenever the proof graph changes; never bypass their
warning or proof-integrity checks.

### Current-checkout verification and semantic audit

Both required commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-204634-0b462a03.log`.
  All 549 package files are covered, 560 Lean files scanned and 9404
  build jobs pass. The exhaustive audit passes 4870 discovered target
  theorems plus five imported boundary declarations: 4875 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_204635.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

Each of the 18 new explicit public audits was found in the final target
log with only `propext`, `Classical.choice` and `Quot.sound`.
All 24 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 208 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. Relative to the preceding 204-file
checkpoint, only the four integration/runner files changed, and the four
new production modules extend the hash coverage. The counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, dependency pins, frozen sources and all existing
energy-proof modules are unchanged. All 199 dirty worktree entries
remain within node 63; no unrelated changes were reverted, staged,
committed or pushed. `git diff --check` passes; Git's CRLF-conversion
notices are not Lean diagnostics.

The architecture has 195 distinct nodes and 503 resolved edges.
Its changed green-node checks are:

- DUL: `norm_logPhase_resonant_sum_lower` derives the lower bound
  for the literal ANTEDB sum at the actual natural scale and endpoints.
  The logarithmic remainder, integer periodicity, real-part estimate,
  term count and square-root normalization are proved.
- DUE: `half_le_exponentSumGrowthExponent_one` supplies an unbounded
  logarithmic model family, proves its dyadic endpoints and N=T relation,
  and invokes the genuine beta lower-bound consumer.
  `exponentSumGrowthExponent_endpoints` combines it with the already
  proved zero endpoint and endpoint-one upper bound.
- CSP: `isExponentPairEstimateNonAsymptotic_half_half` derives one
  uniform model-phase estimate on the whole 1<=N<=T domain by the two
  complementary scale cases. `exponentPair_half_half` returns the
  actual analytic predicate, and the beta corollaries consume closed
  duality. No exponential-sum estimate is assumed as a terminal premise.

The existing closed-duality proof needs only the upper endpoint bound;
it does not rely on the new logarithmic lower-bound construction.
DUR and aggregate EPZAE-09 remain open solely for the full reflection
identity. The classical seed does not close EPZAE-10's general processes.
The other open Checklist items and the original whole-proof goal remain
open. These semantic conclusions are independent of the audit count.

### Current verification artifact hashes

| Artifact | SHA-256 |
|---|---|
| `logs/tao-trudgian-yang-build-20260921-204634-0b462a03.log` | `e8340e4c07c198113387dd8ec7682433b1cc4157b4fde5ca244dafa09949d051` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_204635.log` | `4c6a1101f5fba7e4615c1dfc3cb8eab3dab007b942a645492a502abd53adc660` |
| `E:/Lean/Riemann Zeta/logs/foundation_freeze_20260921_204635.json` | `5a73222227b09f4e1fe299e4e520f9e53e70391486241871b59c23f67b53ebe2` |

### Exact-endpoint implementation hashes

Older checkpoint rows are historical. These are the changed or new files
for this checkpoint; all 208 covered source hashes were revalidated
against the final pre-gate snapshot.

| File | SHA-256 |
|---|---|
| `Extension/TaoTrudgianYang2025/BetaLogCoherence.lean` | `b58d102fc21f9277426f36349cf4321a486049d06e0ea6caeb362b1ecafa6039` |
| `Extension/TaoTrudgianYang2025/BetaResonantSum.lean` | `aa468ef72d4ed8906d1f4ccbc99030729896f1c20c1f052a0b83a263b1fde0e4` |
| `Extension/TaoTrudgianYang2025/BetaEndpoints.lean` | `4ffb41860f2f26902b8e0806159134939f2e00f2000e6839aa934c0cbc40897b` |
| `Extension/TaoTrudgianYang2025/ClassicalSecondDerivativePair.lean` | `52432a8c824da8bd62ac7723daeab17cecfe148ad60e32d599252abb46883e27` |
| `Extension/TaoTrudgianYang2025.lean` | `9e6d457f2356cb2368f84161a4b7db4b335eee37582be2a07446e89c7bbf68b1` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `cc4127d10293e40db5e0fcc1322e0ec718d6e2945fca142a38ad94a66b1b2fc3` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `41fb94d741d2684f17808a4519e81993d513563cbff464f79bed50ec2eb3359f` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `ac3367a794e8dc72818fb77f12bf375bfb2519fdbf194aacadb408107a4f9a70` |

Both BAT launchers retain their prior hashes. The unchanged foundation
verifier SHA-256 is
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

## Actual inverse and Legendre phases — historical checkpoint

Four new modules are installed: `BetaSlopeInverse`,
`BetaLegendreDual`, `BetaInverseStability` and `BetaStationaryPoint`.
The root imports, exact PowerShell production inventory, explicit audits
and semantic regressions cover all four. There are 37 new public audits
and 42 new regression examples (37 exact types plus five actual-model
checks). The full source conclusions and limitations are recorded in
the latest Goal Prompt section.

The 212-file checkpoint hash set extends the previous 208-file set
with these four modules. Only the four expected integration/runner
files changed among the previous checkpoint files. No existing energy
module, counterexample, frozen dependency, archive or BAT launcher changed.
Full beta reflection and the general B-process transformation remain
open despite successful phase-side consumers. The full goal is unchanged.

### Current-checkout verification

Both mandatory BAT commands passed with exit code 0 on 21 September 2026,
at dirty HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  `logs/tao-trudgian-yang-build-20260921-211419-4caca476.log`.
  Coverage: 553 package files, 564 scanned Lean files, 9408 build jobs,
  4924 discovered target theorems plus five imported boundaries (4929 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  `Riemann Zeta/logs/foundation_freeze_20260921_211419.log` and matching JSON.
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 37 new public audits were found with only the permitted logical axioms;
all 42 new regression examples pass. Repository scans found no prohibited
proof terms; broad postulate matches are existing prose and rational fields.
All 212 checkpoint source/integration/runner hashes agree before and after
both final runs. The counterexample and both BAT launchers are unchanged.
All 203 dirty worktree entries remain within node 63. No files were staged,
committed or pushed. Full source completeness remains separate from runner PASS.

### Reproduction hashes

The final target log SHA-256 is
`8738f7955628ce73f4ed79eeb346236cf3ecf3707ce245b7fc2077bc34a18549`.
Foundation final log:
`989b57c80bbc3e125d8e194e76e5c3e863e5496cd6284fd9d5a2dee4efce292f`.
Foundation JSON manifest:
`00a810218f150c90274429aea8a46fb3c6514905cd8a8387ee09fd9ac2f09751`.

The new module hashes are:

| Module | SHA-256 |
| --- | --- |
| `BetaSlopeInverse` | `299aa15e5576f8cb4d74c4a3cf449a0fa65c7318551da831675cd51bb2ea65e2` |
| `BetaLegendreDual` | `ff8f214dbadef5364f3a525982f439feb7cf8dc0fd9736ece4b5de4a9439e0f3` |
| `BetaInverseStability` | `78a766bf772117355d13495c3248abb6cb0a77622e5be4dead49494613febdaa` |
| `BetaStationaryPoint` | `feecc46db8bb2bcf9814d69ad3e62cc133ad5cc8058a1c2200eb5819ea05d6c1` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
The foundation verifier hash and all frozen source pins are unchanged.

## Uniform all-order Legendre model control — historical checkpoint

Eight new production modules extend the checkpoint hash set from 212
to 220 files. Among the preceding 212 files, only the four expected
root-import/audit/regression/PowerShell-inventory files changed.
The new module source, root imports and exact runner inventory agree.
There are 44 new public audits and 52 new regression examples.

The initial target run
`logs/tao-trudgian-yang-build-20260921-215033-a21d36d8.log`
and contemporaneous foundation run found a comment line starting with
`constant`. The sentence was reworded without changing any proof,
declaration, scanner or diagnostic policy. Those runs are retained as
historical failures. Final evidence below refers to runs started after
the last Lean-source edit.

The actual all-order compact phase-control consumer is proved; canonical
[1,2] extension and the transformed-sum theorem remain OPEN. Exact
quantifiers and source limitations are in the latest Goal Prompt section.
The original counterexample, authorized powering repair and all nine
Add-est clauses remain unchanged, as does the whole-proof objective.

### Current-checkout verification

Both mandatory BAT commands passed with exit code 0 on 21 September 2026,
at dirty HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  [final target log](logs/tao-trudgian-yang-build-20260921-215130-00a61f53.log).
  Coverage: 561 package files, 572 scanned Lean files, 9416 build jobs,
  5021 discovered target theorems plus five imported boundaries (5026 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  [final foundation log](../../logs/foundation_freeze_20260921_215409.log)
  and [JSON manifest](../../logs/foundation_freeze_20260921_215409.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 44 new public audits were found with only the permitted logical axioms;
all 52 new regression examples pass. Initial scans rejected a comment
starting with `constant`; the comment was reworded without weakening
the scanner. Both final runs started after that last Lean-source edit.

All 220 checkpoint source/integration/runner hashes agree before and
after both final runs. The counterexample, existing energy-proof modules,
both BAT launchers, foundation verifier and frozen pins are unchanged.
All 211 dirty worktree entries remain within node 63. No files were staged,
committed or pushed. Full source completeness remains separate from runner PASS.

### Reproduction hashes

Final target log SHA-256:
`74b5bf0256e7a21ab4474c2cc6b21ecbed4dcdd0668772a43350f045712575bd`.
Final foundation log SHA-256:
`5c3b6d01fb85164984921f62674e8acbeba38421f85c30c6999de79dcabd3e7e`.
Final foundation JSON manifest SHA-256:
`7eb03f1bdd0f7f7e27ad7e549f8be8c65cec7e02ddd1e20ae826b45de7f0feb2`.

The new module hashes are:

| Module | SHA-256 |
| --- | --- |
| `BetaInverseExpressions` | `4b43362917fbb074579fee1d39f5d70726da712485a539eaaba4433e696bdf40` |
| `BetaInverseJets` | `d9ec364cffc441b63575927d9462672c88889f4faf4c2e24c4156903d9a6e1a3` |
| `BetaReferencePhase` | `46e6292b80b1805827c69bc421d6d8f7021f70e70d564599c5f5048a3514c8ea` |
| `BetaModelJetEstimates` | `73dc60888dc80e665efb6c998183c9561a90a01e39828bd7e491966dedb0d0f4` |
| `BetaInverseJetBounds` | `f7dbfec463d3ec62c419707f410bb9a63e07e98d90d845ea8110c2486d6cce98` |
| `BetaLegendreAllOrders` | `cfa7ea995f2646b9c7c9d2bc20411d00df7499651ff1738e02b3a2ef010a8534` |
| `BetaLegendreCompact` | `a1ff081c400d68976d504952867c2cbd82bac607026f25d3cb0c139416004739` |
| `BetaLegendreAnchoring` | `f20a92c2c4a2d85d1cb982ee5471c7ba48784b57692539aa16fd7029c2c0218d` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

## Canonical Legendre extension and finite model families — historical checkpoint

The checkpoint hash set grows from 220 to 228 files with eight new
production modules. Only the four expected root-import, audit,
semantic-regression and PowerShell-inventory files changed among the
preceding files. All new modules are root-imported and explicitly covered.
There are 27 new public audits and 35 new regression examples.

The checkout began clean at commit
`8a2cf7ab11a19ac206716066ba604ee5857c5481`; the final working tree contains
only the scoped node-63 changes. Focused compilation exposed and fixed
proof elaboration errors, deprecated API names and one regression tactic
style warning. Final BAT evidence below postdates the last source edit.
No warning, coverage or integrity policy was weakened.

DHC's exact canonical compact-window extension and actual finite-cover
model-family consumer are proved. The actual transformed-sum theorem
and full beta reflection remain open; the whole-proof objective is unchanged.
The original counterexample and entire repaired energy chain are preserved.

### Current-checkout verification

Both mandatory BAT commands passed with exit code 0 on 21 September 2026,
at dirty HEAD `8a2cf7ab11a19ac206716066ba604ee5857c5481`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  [final target log](logs/tao-trudgian-yang-build-20260921-222922-4233a5f3.log).
  Coverage: 569 package files, 580 scanned Lean files, 9424 build jobs,
  5053 discovered target theorems plus five imported boundaries (5058 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  [final foundation log](../../logs/foundation_freeze_20260921_222922.log)
  and [JSON manifest](../../logs/foundation_freeze_20260921_222922.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 27 new public audits were found with only permitted logical axioms;
all 35 new regression examples pass. The earlier focused regression's
tactic-style warning was fixed before both final runs.
Repository scans found no prohibited proof terms; broad postulate matches
are unchanged prose and rational structure fields.

All 228 checkpoint source/integration/runner hashes agree before and
after both final BAT runs. The permanent counterexample, existing
energy-proof modules, BAT launchers, foundation verifier, dependency pins
and frozen sources are unchanged. All worktree changes remain in node 63.
No files were staged, committed or pushed. Mathematical/source completeness
remains separate from runner PASS.

### Reproduction hashes

Final target log SHA-256:
`5bf661ce4e3eac6f5eab6d73223238d19948f64e49b784b4ac39fd75cbdddfb2`.
Final foundation log SHA-256:
`874cbf736269d7ad424302f75889f43077eeb615389d726168eb133f8df0cfbe`.
Final foundation JSON manifest SHA-256:
`1c08546bdc0d6cded6a8e0dce6affa56ffca1b8ad791289ceb9d13281f756d30`.

The new module hashes are:

| Module | SHA-256 |
| --- | --- |
| `BetaSmoothCutoff` | `4146fced62f9d9eefa879f7e8bfbfc1f94a98f8ffe52c9a55b81534b7c484d3a` |
| `BetaCutoffEstimates` | `1a6be210a3d4d77cb1851cfd9532f8ad18ec673dd0b38dcec4afd9b8cc7f0628` |
| `BetaLegendreCorrection` | `15bc53429647a56ca828a6787573aa5061ecdd71dcbe2b700219da366f3a436d` |
| `BetaPhaseNormalization` | `905dc2451554f20392470d214dc602e40fb2ba8831369bea635e089a5c1c99f2` |
| `BetaCanonicalLegendre` | `5d09d6d7690ccc6aadffc4fa38dc6ea15de202dfe9aaca6ed7c40a03360eda5a` |
| `BetaLegendreCover` | `2d04ea2151ecd4dafa058fc11bb2118e7fc5455f9547735991219839f69d5527` |
| `BetaLegendreFamily` | `e74d6367be9253d82e4d95c7f5228f20b0ecc3ef88592945b66c0426811c474a` |
| `BetaLegendreModelCover` | `56fd0eeb329c126d6a76c55dcea55ab4c5389a940579cae1ebf855e17cd74a50` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The architecture has 208 distinct nodes and 540 resolved edges.

## Exact Poisson source entry and physical dual sums — historical checkpoint

The six modules prove exact original-source Poisson entry, absolute
convergence and physical dual/stationary-sum identities. They do not
prove uniform stationary integral approximation or the full B process.
See the latest Goal Prompt for the semantic completion boundaries.

### Current-checkout verification

Both mandatory BAT commands passed with exit code 0 on 21 September 2026,
at dirty HEAD `8a2cf7ab11a19ac206716066ba604ee5857c5481`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  [final target log](logs/tao-trudgian-yang-build-20260921-231301-8d992207.log).
  Coverage: 575 package files, 586 scanned Lean files, 9430 build jobs,
  5119 discovered target theorems plus five imported boundaries (5124 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  [final foundation log](../../logs/foundation_freeze_20260921_231301.log) and [JSON manifest](../../logs/foundation_freeze_20260921_231301.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 32 new public audits were found with only permitted logical axioms;
all 40 new regression examples pass. Initial focused regression failures
were repaired before both final runs; no gate was weakened.
Repository scans found no prohibited proof terms; broad postulate matches
remain unchanged comments and rational structure fields.

All 234 checkpoint source/integration/runner hashes agree before and
after both final BAT runs. The permanent counterexample, existing
energy-proof modules, BAT launchers, foundation verifier, frozen sources
and dependency pins are unchanged. All worktree changes remain in node 63.
No files were staged, committed or pushed. Mathematical/source completeness
remains distinct from runner PASS. The full goal remains active.

### Reproduction hashes

Final target log SHA-256:
`bd075bdd6895c17f4794826231f783c0672cabe66f06645b3c303f4e14431db2`.
Final foundation log SHA-256:
`1b6c987bf49c7c34e4e5e0c74c243651e1661e6e9118dca9e97705c1a4c16c51`.
Final foundation JSON manifest SHA-256:
`e5112e964185d1cbec9ba693c1349c0cb7cf26245f552a8e4df8f41472dacaa1`.

| Module | SHA-256 |
| --- | --- |
| `BetaDualScales` | `6bd961a63598a8c947a1bb21d5ccd1f739d3d692be0f62e686d6cdd8523e98d0` |
| `BetaModelPoisson` | `3f264b7e54758f130c0fa59b0635403e5cc32becd3ec85242323d5f51dd88902` |
| `BetaSharpCutoff` | `13b63c87b6ee626cc30df0abfb9b63433ec6bbf5bf459704e66470db3d17af86` |
| `BetaFourierModes` | `2f91cd0b81a2d158da38abf409b50784d940aa871ae3e9a053d3f505f4b63f63` |
| `BetaPoissonBoundary` | `a59268f958e9c35ac74bb475aeec1c94977da9be3e5864b82d74c250413c4fd8` |
| `BetaStationarySum` | `988c623377c1a672e67babbfa12c638c5b294f80110abac17a4aa8f5ed167499` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The architecture has 213 distinct nodes and 555 resolved edges.

Git's existing LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration was changed. The two verification logs themselves are
diagnostic-free. The full EPZAE-00--41 objective is unchanged.

## Stationary amplitudes, source beta consumers and quadratic coordinates — historical checkpoint

The eight new modules prove actual curvature-amplitude control,
constructed-chart beta bounds for the literal stationary main block,
and an exact quadratic coordinate with its critical derivative.
They do not prove the uniform inverse/transformed-integral estimates
or the full B process. Exact semantic boundaries are recorded in
the latest Goal Prompt.

### Current-checkout verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
at dirty HEAD `8a2cf7ab11a19ac206716066ba604ee5857c5481`:

- Target: `run_tao_trudgian_yang_build.bat --no-pause`;
  [final target log](logs/tao-trudgian-yang-build-20260922-000055-22681e8e.log).
  Coverage: 583 package files, 594 scanned Lean files, 9438 build jobs,
  5198 discovered target theorems plus five imported boundaries (5203 audited).
- Foundation: `run_lake_build.bat --no-pause`;
  [final foundation log](../../logs/foundation_freeze_20260922_000107.log) and
  [JSON manifest](../../logs/foundation_freeze_20260922_000107.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 46 new public audits were found once each with only permitted logical
axioms; all 54 new regression examples pass. Focused development errors
were repaired before these final runs; no gate was weakened.
Repository scans found no prohibited proof terms. Broad postulate matches
remain unchanged comments and rational structure fields, not postulates.

All 242 checkpoint source/integration/runner hashes match the verification
snapshot. The eight new module texts and four integration/runner texts
also match their exact compiled sources after line-ending normalization.
The permanent counterexample, existing energy-proof modules, both BAT
launchers, foundation verifier, frozen sources and dependency pins are
unchanged. All 37 worktree entries remain in node 63; 29 pre-existing
dirty entries were preserved and eight new proof modules were added.
No files were staged, committed or pushed. Mathematical/source completeness
is distinct from runner PASS. The full goal remains active.

### Reproduction hashes

Final target log SHA-256:
`2931f6a4892ff4a55fe3ea177c1d5089e0fc01ee48fe63a453d3aac7e6bbf098`.
Final foundation log SHA-256:
`dfd2b744bb330adae1e4c85d207907a136f2f63ec9011d7031f2c2b9422cfb54`.
Final foundation JSON manifest SHA-256:
`f6bdac2856eb76233aec4a9867cd38d21cb8c18d8394554f4adebebd995c657f`.

| Module | SHA-256 |
| --- | --- |
| `BetaCurvatureAmplitude` | `3032931539ddf8316a2670ca0d2d328e3423e59f08fe96947b9dfeb081ae9f8b` |
| `BetaAmplitudeMonotonicity` | `65afbfcda5a6c439261bda438bd91b3c1e38b11bf881b0049ec713a224fdee47` |
| `BetaAmplitudeVariation` | `8328cfcb8e8101beb714ae9a7c1c2acd3dccf73279a423a176885a748b388049` |
| `BetaStationaryMain` | `1efc75c319ab7c5eb99ad31e9dfe75b122891adf8cd0e14d88c8a6fa9b916cc4` |
| `BetaAmplitudePartialSummation` | `e885a2663658eb557fc0f2ec82cdb35cbb23c22746b65ca125f985728d375caa` |
| `BetaStationaryBetaBound` | `f2b84ebc5bce4422d6fad9a19f7446376bb194232ca802af1126d6ad414fdf86` |
| `BetaStationaryDeficit` | `d1f09126f2be95b28596ced00333901a7ff1ab0f992b9866e37c80f03ae7e327` |
| `BetaMorseCriticalPoint` | `fc8e2674192e726a6833ef5e3c30e3f08a40aeb08698cec4a8c4b3c2a8c4862d` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The architecture has 220 distinct nodes and 578 resolved edges.

Git's existing LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration was changed. Both verification logs are diagnostic-free.
The full EPZAE-00--41 objective is unchanged.

## Smooth quadratic inverse and original-mode remainder — historical checkpoint

Eleven new production modules establish actual Taylor-average and
smooth-inverse calculus, uniform first-derivative bounds, original
Poisson-cutoff change of variables and exact physical remainder
normalization. They do not prove a uniform stationary remainder bound,
higher-derivative budgets, smooth zero-extension or full beta reflection.
The exact consumers and semantic boundaries are in the latest Goal Prompt.

### Current-checkout verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
at dirty HEAD `8a2cf7ab11a19ac206716066ba604ee5857c5481`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`
  from this folder;
  [final target log](logs/tao-trudgian-yang-build-20260922-010958-9aae1d59.log).
  Coverage: 594 package files, 605 scanned Lean files, 9449 build jobs,
  5267 discovered target theorems plus five imported boundaries (5272 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`
  from `Riemann Zeta`;
  [final foundation log](../../logs/foundation_freeze_20260922_010947.log) and
  [JSON manifest](../../logs/foundation_freeze_20260922_010947.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 54 new public audits were found once each with only permitted logical
axioms; all 63 new regression examples pass. Focused development errors
were repaired before these final runs; no gate was weakened.
Repository scans found no prohibited proof terms. Broad postulate matches
remain unchanged comments and rational structure fields, not postulates.

All 253 checkpoint source/integration/runner hashes match the verification
snapshot. The eleven new module texts and four integration/runner texts
also match their compiled proof texts after line-ending and terminal
blank-line normalization; raw file hashes remain unchanged across both runs.
The permanent counterexample, existing energy-proof modules, both BAT
launchers, foundation verifier, frozen sources and dependency pins are
unchanged. All 48 worktree entries remain in node 63; 37 pre-existing
dirty entries were preserved and eleven new proof modules were added.
No files were staged, committed or pushed. Mathematical/source completeness
is distinct from runner PASS. The full goal remains active.

### Reproduction hashes

Final target log SHA-256:
`5fbed89e2f227046f2a45673ca7858c68e9656b52ba048f0bd41a56553dd4730`.
Final foundation log SHA-256:
`21b2789ce78b58ecab6236b6190bfdd13a7e19b271d13ea3c2991f543dae171d`.
Final foundation JSON manifest SHA-256:
`a578dd87e45cc90c09e87e267a4c9a8605f2d066f3e273ddb6df896502c80598`.

| Module | SHA-256 |
| --- | --- |
| `BetaTaylorAverage` | `cea44ead18d130375b08b92663e68b730182d5a76f1a747acd69f52577f272f9` |
| `BetaTaylorIdentity` | `6884eb11f3f7080754643b60db672a77a9038164da7c9b60d58ab2510c9311d9` |
| `BetaAveragedCurvature` | `b16758ad349834796e48f336e71fd17dc662ec6f92b1e92831a90a8a07325ac0` |
| `BetaMorseMonotonicity` | `20c9bdceb53d2bab2dc23f1b77b2d8fb9aa0bc9502ca44aac3d2ead33ccfb923` |
| `BetaMorseInverse` | `b73343f418b6bb9bb8f21f20af036fa2d370ec9169e199fb7e79dd3f2f314d32` |
| `BetaMorseDerivativeBounds` | `989306022898ccae4cdf6d7467d55da32b122237eda0fc95e21999269d9fc68c` |
| `BetaMorseChangeVariables` | `f9aa630b2e4d3652589b9476a15dc448a5c14ed46cf6b4cc6e6407da6b478e61` |
| `BetaMorseAmplitude` | `cbf4c14fd86f3ec214d7999004df235f2a21781bba2f71701e42b7dc19174db8` |
| `BetaMorseFourier` | `5a9d930a9d071f5fd6ab0eff9d4909856c6cdd2636b6e282d959222ecec4d322` |
| `BetaMorsePoisson` | `1ee904750dd56a61a6413a32cba5fcfcfdb35f1462daff3ab6d64acc64abd3c1` |
| `BetaMorseRemainder` | `d7b08f7854f5a8d563df3dd2b096ac2a7ab58a24955568cfb817d10c0c1a8aaf` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The architecture has 228 distinct nodes and 611 resolved, nonduplicate edges.

All eleven synchronized documents preserve historical checkpoints.
Git's existing LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration was changed. Both complete verification logs are
diagnostic-free. The full EPZAE-00--41 objective is unchanged.

## Uniform smooth weights and stationary remainder bounds — historical checkpoint

Sixteen new production modules prove the actual smooth zero-extension,
uniform all-order coordinate/inverse/weight derivatives, a quantitative
whole-line quadratic remainder and its original-source consumer.
The physical C*N/T stationary estimate is uniform for each fixed cutoff,
retains chi(g(r*N/T)) and e(-1/8), and does not yet give uniform
varying-lattice cutoff budgets. Nonstationary modes, weighted stationary
assembly, moving boundary bands and full beta reflection remain open.
The counterexample, independent two-witness repair and all nine Add-est
clauses are unchanged.

### Current-checkout verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
at dirty HEAD `8a2cf7ab11a19ac206716066ba604ee5857c5481`:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`
  from this folder;
  [final target log](logs/tao-trudgian-yang-build-20260922-021704-cf554732.log).
  Coverage: 610 package files, 621 scanned Lean files, 9465 build jobs,
  5397 discovered target theorems plus five imported boundaries (5402 audited).
- Foundation: `cmd /c run_lake_build.bat --no-pause`
  from `Riemann Zeta`;
  [final foundation log](../../logs/foundation_freeze_20260922_021704.log) and
  [JSON manifest](../../logs/foundation_freeze_20260922_021704.json).
  All six stages pass; 301 root modules plus two regressions, 8857 jobs,
  7636 explicit declarations and 14290 discovered project theorems.

Both complete logs have zero Lean warnings, errors or tactic suggestions.
All 75 new public audits were found once each with only permitted logical
axioms; all 85 new regression examples pass. Focused development errors
were repaired before these final runs; no gate was weakened.
Repository scans found no prohibited proof terms. Broad postulate matches
remain unchanged comments and rational structure fields, not postulates.

All 269 checkpoint source/integration/runner hashes match the verification
snapshot. The sixteen new module texts and four integration/runner texts
also match their compiled proof texts after line-ending normalization,
including terminal newlines; raw file hashes are unchanged across both runs.
The permanent counterexample, existing energy-proof modules, both BAT
launchers, foundation verifier, frozen sources and dependency pins are
unchanged. All 64 worktree entries remain in node 63; 48 pre-existing
dirty entries were preserved and sixteen new proof modules were added.
No files were staged, committed or pushed. Mathematical/source completeness
is distinct from runner PASS. The full goal remains unfinished.

### Reproduction hashes

Final target log SHA-256:
`4df678a225f115eefe461d217e2e58da406e318589c2059e5cf7b8e5027dbbd2`.
Final foundation log SHA-256:
`3ef717c69e0f76f2e05cffdf4bbdf47cf7e734034bdf2faf2ed5a37124993c16`.
Final foundation JSON manifest SHA-256:
`4cc50a51c025afd3d1a01b74f9113afb516cf863f54ef17d2c036ea56bdc7f8b`.

| Module | SHA-256 |
| --- | --- |
| `BetaMorseSupport` | `9473a44ace248017b8a25e69612c2974192b6039e4794ae53bcdff844c8a9215` |
| `BetaTaylorJets` | `ea2792df3d5ca12afcb47979f893b450d782fa81e401f7c856e3c2f2afa90f76` |
| `BetaMorseGlobalIntegral` | `540268edf5501b7005c1abdfdc2046731ef840675d3317b86ec585ba21d2503a` |
| `BetaMorseJets` | `348f9edae4c164533fd1d28c862dc87768472c09787cf63e8faf25ad6784d6fa` |
| `BetaMorseJetBounds` | `cee8133dc24286a108744451702e2f05bdb092b978fb089d964a1ada954d817b` |
| `BetaMorseInverseJets` | `4d4a5c3d06ea0fbfa22daf962785fbb183ed646d807ea43685a75e54ffac75b6` |
| `BetaMorseInverseJetBounds` | `609b59ff5890f0141b21fb364a77b4a56e94d68a62e861fe01238c6a42a24cb6` |
| `BetaMorseWeightJets` | `264b28135b82a0676a576b3910dfb9c8b551a9359fd684589fa6d079b6d259f9` |
| `BetaMorseWeightBounds` | `ca90127af92af4e548a3eddd3c8caef62a4ccf180ec8fd7f10cfcc392f002727` |
| `BetaTaylorGlobal` | `79d8f9275be61f4f880fccb75fdf8b7097c6421d2d17becbf7dab1bdcf6255dd` |
| `BetaQuadraticKernel` | `41ba6318ccbd16e83dc910aecc901a76b644899a258d655ebaa9adf69747db6e` |
| `BetaQuadraticParts` | `f6cd7e969f728a5cf3423f0ae82f9e295b6398ca385ab49fec85b6e43aef8c7d` |
| `BetaQuadraticTaylor` | `6328a3df912ccd2168172a428797ff8cd8b610f3826536bca3974367101e0ce6` |
| `BetaQuadraticRemainder` | `2041620e484008c471ed9c797595c617a105b83bc0fbcaf7880138ae44609a5e` |
| `BetaMorseStationaryEstimate` | `b822536560f04a7001ef378893dd5eae950659944ccf33b6bfcb98ffd9aee7f5` |
| `BetaMorseSourceEstimate` | `8f97fa83a5f7153e010e32b19dc169a769db49350085e103a3d624307d2203b6` |

The permanent `EnergyPoweringObstruction.lean` SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT: `6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT: `a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.
The architecture has 234 distinct nodes and 638 resolved, nonduplicate edges.

All eleven synchronized documents preserve historical checkpoints.
Git's existing LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration was changed. Both complete verification logs are
diagnostic-free. The full EPZAE-00--41 objective is unchanged.

## Controlled cutoff families and weighted Fourier bounds — historical checkpoint

Date: 22 September 2026 (America/Vancouver).
Baseline HEAD: `c1656d25781ca47831cc8730a0a742b6309cd717`.
The worktree was clean at the start of this turn; the owner had committed
the preceding checkpoint. The final 30 changed/untracked entries are
confined to node 63: fifteen new modules, four integration/runner files
and eleven documents. No staging, commit or push was performed here.

The installed estimates are controlled source smoothing <=4*N*eta+2,
sharp actual order-n transformed-weight jets C*eta^(-n), stationary
mode errors C*N/(T*eta^3), actual cutoff-weighted beta main blocks
and nonstationary physical-gap bounds 4/(pi*d).
The source and phase predicates, public outputs and all energy proofs
are unchanged. Summed-error balance, quantitative far tails and moving
boundary bands remain open; the full objective is not complete.

### Verification and preservation

Both mandatory launchers were run after the final Lean, root-import,
audit, regression and backing-inventory edits, on 22 September 2026:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0;
  [complete target log](logs/tao-trudgian-yang-build-20260922-085137-4fb8b007.log).
  All 20 pinned source files and 12 frozen ANTEDB files pass integrity;
  636 Lean files scanned; 625 production package files covered;
  deterministic regeneration and 9480-job default build pass.
  Semantic regressions pass. The audit checks 5511 discovered target
  theorems plus five imported declarations, 5516 total.
- `cmd /c run_lake_build.bat --no-pause` from the foundation root:
  exit 0; [complete foundation log](../../logs/foundation_freeze_20260922_085138.log) and
  [machine-readable manifest](../../logs/foundation_freeze_20260922_085138.json).
  All six stages pass: root/default build, exact publication contract,
  both retained regressions, transitive audit and declaration linter.
  Coverage remains 301 root modules plus two explicit regressions;
  8857 jobs; 7636 explicit declarations and 14290 discovered theorems.

Both full physical logs were scanned, not merely their truncated terminal
display. They contain zero Lean warnings, errors or tactic suggestions.
Each of the 50 new explicitly audited public declarations appears once
and depends only on permitted logical axioms. The 66 new regressions
comprise 50 exact signatures and 16 source/degenerate/width-degree checks.
Development errors and warnings were repaired before the final successful
regression build and BAT runs. No proof, coverage or diagnostic gate was weakened.

All 284 checkpoint source/integration/runner hashes are unchanged across
the final verification runs. The fifteen new source texts and four
integration texts also match their compiled proof texts exactly after
CRLF normalization, including terminal newlines. The counterexample,
existing energy proofs, both BAT launchers, foundation verifier,
frozen sources and dependency pins are unchanged.

This turn started from a clean worktree at
`c1656d25781ca47831cc8730a0a742b6309cd717`; prior checkpoint work had
already been committed by the owner. The completed checkpoint has
30 entries, all in node 63: fifteen new proof modules, four modified
integration/runner files and eleven synchronized documents.
No files were staged, committed or pushed by this turn.
Runner PASS verifies the installed scope; it does not assert that DBT,
full reflection or the whole EPZAE-00--41 objective is complete.

### Reproduction identities

| Evidence | SHA-256 |
|---|---|
| [Final target log](logs/tao-trudgian-yang-build-20260922-085137-4fb8b007.log) | `fdec73fc8baafdffd500221e7e921de26e406c06d0f05b097decbb756bc1ba60` |
| [Final foundation log](../../logs/foundation_freeze_20260922_085138.log) | `83e8542fd0df00a04da0808bb5c492ad87c7002206097badb6e31fb1acee1f8d` |
| [Final foundation JSON](../../logs/foundation_freeze_20260922_085138.json) | `8ae11126c27c228ee018ea09338a9c9f2f03db5c07242571779c67a0a90e1e6e` |

The Lean toolchain remains `leanprover/lean4:v4.30.0`.
The Mathlib pin remains `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
All twenty frozen source and twelve frozen ANTEDB integrity checks pass.

The following RAW source-file SHA-256 values match the pre-run and
post-run snapshots. Each new module is both root-imported and present
in the exact production runner inventory.

| New production module | Raw SHA-256 |
|---|---|
| `BetaBufferedCutoff` | `04885370608cb1dae7c363d5dd64a7270b46a0fbb10292084144abcccc522853` |
| `BetaBufferedJets` | `4e2d592c8609d48e6015cc64ded92bb15def404ed2e1ea6b56a8a643121cc942` |
| `BetaJetPolynomial` | `90e1523649695b54a4e4ef319a5d23a3e007da8097d7caa3db531f65d985fd67` |
| `BetaBufferedMorseBounds` | `addd651d5ea0d97103d7f950e3fb8d5cdf9f8fe01f65ba646fea1850ae254501` |
| `BetaBufferedBoundary` | `9381bf4270c1eebd7eeb4398a221ed74bd2be05fd6248fd3ea268f66dc7c4369` |
| `BetaBufferedStationary` | `e4fdddbe2e9be5293d547dacbe75c84bfa3dd842accce7a2fbf468a6f6133e78` |
| `BetaBufferedSource` | `5aacb6126069a97a4f379bb3a18e5e9a8afd08ff0fdba4f6749af38fa0bc5376` |
| `BetaBufferedVariation` | `753416469632dd7431c2d59e226a0155879a502c625c40ad580db7b1315dd21f` |
| `BetaBufferedMain` | `5e274092bf356822d543b64cd9bbdb2bcb42a4ac82322dad0a5156b0c0018290` |
| `BetaBufferedBetaBound` | `31a7945850687d614ae1995eaf1a3838c5388f49a96b12c4f2ddecda11cce36a` |
| `BetaWeightedPrimitive` | `2ab2292cbf26878d346c31e8ec7b07cc88800f732b265c49b784f90b7f7f6453` |
| `BetaWeightedPhase` | `3485e0165880b34bfcf3dd3080fb36cec42546bf012715f23d7e2e176395ac7f` |
| `BetaBufferedNonstationary` | `0b5d481f4538a513b875ef48179baf94e2db5e906de691fbdd3aa75f58728297` |
| `BetaBufferedFrequencyGap` | `1948fa31d42e52e19e6a4482acebbf1e7e2dae9fb792aec0cb46c17e390229bb` |
| `BetaMorseWidthDegree` | `7292ec96c9a599ccda470bc4d1f465003bddac26b92c537321c254940a474c01` |

| Integration file | Raw SHA-256 |
|---|---|
| `Extension/TaoTrudgianYang2025.lean` | `272351147de74786c9a4817a466dc15c180d2d7a1b9bd51854e462efb50dfd83` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `490fe6dd9c4e61a51b17b9671081abc3bd708c96dd5f272211c25d3c351b2397` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `7c00d070d022ca4893b656ccbbba3ca8e07c23799a636df08a0f77acb7b4e4ee` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `5b9b28d3c95a5d153b66c9193209045534d158124ea47d9dc3ac6174099fdd66` |

Permanent `EnergyPoweringObstruction.lean`:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT:
`6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT:
`a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

All 284 checkpoint source/integration/runner hashes remain stable after
the final runs and document synchronization. All nineteen compiled texts
match after CRLF normalization, including terminal newlines.
The architecture has 240 distinct nodes and 661 resolved, nonduplicate
edges. The 42 aggregate checklist entries are unchanged.
Eleven synchronized documents retain the previous checkpoint as history.
Git LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration changed. Both complete verification logs are diagnostic-free.

## Quantitative Fourier tails and the actual core expansion — historical checkpoint

Date: 22 September 2026 (America/Vancouver).
Baseline HEAD: `c1656d25781ca47831cc8730a0a742b6309cd717`.
The 30 existing dirty/untracked entries were preserved. Ten new modules
bring the total to 40, all in node 63. No staging, commit or push
was performed. The four integration files and eleven documents are
updated without removing previous proof work or historical checkpoints.

The actual source now has a quantitative infinite-tail bound,
logarithmic exterior blocks, an exact physical core reduction and a
stationary-core expansion. The expansion retains its unestimated
inner-core nonstationary sum. The stationary/source power-saving balance,
moving inner-core bands, canonical chart assembly and full reflection
remain open under the unchanged objective.

### Verification and preservation

Both mandatory BATs were run after the final Lean, import, audit,
regression and backing-inventory edits, on 22 September 2026:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0;
  [complete target log](logs/tao-trudgian-yang-build-20260922-094603-f91c6946.log).
  All 20 pinned source files and 12 frozen ANTEDB files pass integrity;
  646 Lean files scanned; 635 production package files covered;
  deterministic regeneration and the 9490-job default build pass.
  Semantic regressions pass. The audit checks 5582 discovered target
  theorems plus five imported declarations, 5587 total.
- `cmd /c run_lake_build.bat --no-pause` from the foundation root:
  exit 0; [complete foundation log](../../logs/foundation_freeze_20260922_094604.log) and
  [machine-readable manifest](../../logs/foundation_freeze_20260922_094604.json).
  All six stages pass: root/default build, exact publication contract,
  both retained regressions, transitive audit and declaration linter.
  Coverage remains 301 root modules plus two explicit regressions;
  8857 jobs; 7636 explicit declarations and 14290 discovered theorems.

Both full physical logs were scanned, not merely truncated terminal
output. They contain zero Lean warnings, errors or tactic suggestions.
All 29 new explicit public audits occur once each, with only permitted
logical axioms. All 41 new regressions pass: 29 exact signatures and
twelve source/degenerate checks. Two regression style warnings were
repaired before the final warning-free regression build and BAT runs.
No proof, integrity, coverage or diagnostic gate was weakened.

All 294 checkpoint source/integration/runner hashes are unchanged across
the final verification runs. The ten new source texts and four integration
texts also match their compiled proof texts after CRLF normalization,
including terminal newlines. The permanent counterexample, existing
energy proofs, both BAT launchers, foundation verifier, frozen sources
and dependency pins are unchanged.

Baseline HEAD remains `c1656d25781ca47831cc8730a0a742b6309cd717`.
This turn started with 30 existing dirty/untracked node-63 entries.
Their work is preserved; ten additional production modules make 40
entries in total, all in node 63. Eleven documents are synchronized
with historical checkpoint content retained. The 42 aggregate checklist
entries are unchanged. No files were staged, committed or pushed.
Runner PASS verifies the installed scope, not the unresolved inner-core
estimates, full reflection or the whole EPZAE-00--41 objective.

### Reproduction identities

| Evidence | SHA-256 |
|---|---|
| [Final target log](logs/tao-trudgian-yang-build-20260922-094603-f91c6946.log) | `cf4daf5bdd6c1bb5e69868fe1dc80135466e7cef09dc32ebf54409acd1a5a7aa` |
| [Final foundation log](../../logs/foundation_freeze_20260922_094604.log) | `6aa34d2d68cc6e81aaf5df6922b2f0e28e24940639c7402d0da9f6124f600386` |
| [Final foundation JSON](../../logs/foundation_freeze_20260922_094604.json) | `3e98b82c678f4bd0f9e24216a3cf62e355856711d6f356ea9c7b355de5025054` |

The toolchain remains `leanprover/lean4:v4.30.0`.
The Mathlib pin remains `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
All twenty source and twelve frozen ANTEDB integrity checks pass.

These RAW source-file hashes match the final pre-run and post-run
snapshots. Every listed module is root-imported and appears exactly
once in the production backing inventory.

| New production module | Raw SHA-256 |
|---|---|
| `BetaFourierCarrierBounds` | `7a2f9f0974c4e81aa26a2dd65dfdb7586995d6a67434ac4db33d33da7ba16a8e` |
| `BetaBufferedKernelJets` | `e93ba0a521ec036ce775309be78e586d456ff38abe97585c2ca7e73e6b52b6d1` |
| `BetaBufferedFourierDecay` | `ae7f6ee4ff9552f1e2076840a184df85eb183ca4d354a1d0f318e348f328dc6e` |
| `IntegerFourierTails` | `3b6c913c106a189b6f03b46268edd5e22f4343a7779e6da1df9b132a90a2a7bb` |
| `BetaBufferedFourierTail` | `5584d267ed8effae40f9f5bbd39dc79fcffcdb9234e9466866c62def2d6659a9` |
| `BetaBufferedNonstationarySums` | `0f58fa88a98aae9550702662ebbed839ab922b64d626a1fe423e928fcc80658f` |
| `IntegerFourierWindows` | `af452d82d78a86a0e3114a7de3ca88b133b6ac678c9458b9e218d84f1516fba2` |
| `BetaBufferedCore` | `da1088fd0aeacf2a464077ff241bf9197cdb4613455646d19f0351428f253624` |
| `BetaBufferedCoreStationary` | `8334bbc26fb490a741b2b8e688907af656ddff46ec6c1b43ee14185e8c23cf23` |
| `BetaBufferedCoreExpansion` | `2f8026c0d8325ca8be17dc6a6d47752dece29e7dc121f5f65806393c9e11e9e8` |

| Integration file | Raw SHA-256 |
|---|---|
| `Extension/TaoTrudgianYang2025.lean` | `61174d130ba4f657d5b594a1bcb65850419f7d45324fb380bcf95f4192f79f65` |
| `Extension/TaoTrudgianYang2025/Audit.lean` | `2c7378d3c46d6800839e4775cd18228a133612072d9d03dcdb8d594a784837e5` |
| `Extension/TaoTrudgianYang2025/SemanticRegression.lean` | `6e67a2cf9bd4628809de6d71fde7fe787ce7f9ad81e20279068c5cc4503f5017` |
| `Tools/run_tao_trudgian_yang_build.ps1` | `1663e41b666ace558d9d4b03058ed352c41b998d9ab07c85161d517c5a52e8d7` |

Permanent `EnergyPoweringObstruction.lean`:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Target BAT:
`6bf52b0784baf7758375bb68de12ad9b691bd9884f6d48a87ddf3c7822961098`.
Foundation BAT:
`a726c1afbc7870391088977cc5be23cf7df9741713b18a7f830e9bfd6850d303`.
Foundation verifier:
`0bafd5bd2ff5847da4dd40e4af713472c38ccd162fc78127b8f98b84214af1a7`.

All 294 checkpoint hashes remain stable after verification and document
synchronization; all fourteen compiled texts match after CRLF normalization,
including terminal newlines. The architecture has 246 distinct nodes and
682 resolved, nonduplicate edges. The six new DONE nodes have explicit
source-consuming semantic checks in the Goal Prompt.
All 42 aggregate checklist entries are unchanged.
Git LF-to-CRLF notices are not Lean diagnostics; no line-ending
configuration changed. The original full goal is unfinished.

## Width-independent curvature and the bounded inner core — historical checkpoint

| Module | Actual checked contribution |
|---|---|
| `PhaseSlopePartition` | Derived slope cut points and curvature-controlled width |
| `PhaseSecondDerivativeIntegral` | Threshold and optimized actual integral bounds |
| `PhaseWeightedCurvature` | Weighted consumer through every prefix primitive |
| `BetaBufferedCurvature` | Original all-frequency modes: C_sigma*N/sqrt(T) |
| `BetaClosedSlope` | One-sided endpoint derivatives and exact slope image |
| `BetaEndpointNonstationary` | Genuine endpoint gaps and harmonic/log blocks |
| `BetaEndpointCore` | Exact stationary integer interval and disjoint complement |
| `BetaCoreNonstationary` | Fully bounded actual inner-core nonstationary sum |
| `BetaBufferedStationaryExpansion` | Original source with only actual stationary main terms |

The original Fourier modes now satisfy C_sigma*N/sqrt(T), uniformly in
every real frequency and original cutoff width. Genuine derivatives
within [1,2] at the endpoints give the exact slope image. If
L=floor((T/N)*s_F(2)) and U=ceil((T/N)*s_F(1)), the actual stationary
core is precisely the open integer interval (L,U). Its complement is
[A,L] disjoint-union [U,B], not an assumed or approximated selection.

The two nearest modes use curvature; all others use derived actual
endpoint gaps and harmonic sums. The full complement is bounded by

```text
2*C_sigma*N/sqrt(T)+(8/pi)*(1+log(3*T/N+3)).
```

The new source consumer contains only the original cutoff-weighted
stationary main terms over (L,U). Its paid errors include original
smoothing, far-tail/exterior reduction, the stationary remainder, and
the displayed complete nonstationary-core bound.

### Scope and regression coverage

Nine new production modules are root-imported and listed in the exact
backing inventory. The 32 new public theorems each have an explicit
axiom audit and an exact-signature regression. Ten additional examples
cover a negative quadratic integral, collapsed interval, zero-threshold
partition, overlapping width-two cutoff, both nearest endpoint modes,
actual slope endpoint exclusion, empty/singleton stationary intervals,
and the concrete one-sided reference slope: 42 new tests in total.

The source and integration texts are compared to their compiled snapshots,
including CRLF-normalized terminal newlines. The preserved checkpoint
now tracks 303 source/integration/runner files: the previous 294 plus
nine new modules. Only the four intended integration files differ from
the previous source snapshot. The counterexample and all existing energy
proofs are unchanged. Git baseline HEAD remains
`c1656d25781ca47831cc8730a0a742b6309cd717`.

The turn began with 40 existing dirty/untracked node-63 entries, all
preserved. Nine new proof modules bring the expected total to 49 entries:
15 modified and 34 untracked, all in node 63. No staging, commit or push
was performed. Existing historic checkpoints remain explicitly historical.
The architectural graph adds six exact supporting nodes and seventeen
dependency edges, with no unresolved or duplicate identifiers.

DBT/full beta reflection remain OPEN. The original source loss
4*N*eta+2 and stationary loss D*eta^(-3)*(1+N/T) still need a sharp
physical-scale balance. Actual stationary-frequency assembly through
the canonical dual charts, moving/reference endpoint conventions,
and alpha-to-1-alpha epsilon/power-window transport remain required.
No aggregate EPZAE checkbox or source theorem is marked complete here.

### Verified build evidence

On 22 September 2026, after the final Lean and integration edits:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  [complete target log](logs/tao-trudgian-yang-build-20260922-103135-cc078125.log). Coverage is 655 scanned Lean files,
  644 production package files and 9499 build jobs. The audit checks
  5649 discovered target theorems plus five imported declarations, 5654 total.
- `cmd /c run_lake_build.bat --no-pause` from the foundation root:
  PASS, exit 0; [complete foundation log](../../logs/foundation_freeze_20260922_103132.log) and
  [machine-readable manifest](../../logs/foundation_freeze_20260922_103132.json). All six stages pass;
  301 root modules plus two regressions, 8857 jobs, 7636 explicit
  declarations and 14290 discovered theorems retain their verified status.

Both complete physical logs contain zero Lean warnings, errors or tactic
suggestions. All 32 new explicit audits occur once, with permitted logical
axioms only. The final 9499-job focused regression build is warning-free;
all 42 new examples pass. The target also verifies all 20 pinned source
files, 12 frozen ANTEDB files and deterministic certificate regeneration.
No coverage, integrity, dependency, warning or output gate was weakened.
Runner PASS verifies the installed scope, not full beta reflection or
the unfinished whole-proof goal.

### Hash and worktree preservation

The final target log SHA-256 is
`9ea21d0a4389c4a4b1a4d22e8683ad0e56850c07c448bee8d7ad59f7a97b5449`.
The foundation log SHA-256 is
`6bfbbe945c69d01ecf3e1ea062cb7791168232d6307a8c1cc6b00ecc2c87f5f3`;
its JSON SHA-256 is
`ca41fcb250aa2413d7723aa2ff1969f48f4bf334a372d1b8d470d59a9af19cba`.

All 303 checkpoint source/integration/runner hashes agree before and
after the final BATs. The nine new source texts and four integration
texts match their compiled snapshots after CRLF normalization, including
terminal newlines. The counterexample, existing energy proofs, both BAT
launchers, foundation verifier, frozen sources and dependency pins are
unchanged.

The first direct sandboxed build could not resolve ELAN_HOME; approved
access to the installed pinned toolchain resolved that execution issue.
During test development, two generated signatures were repaired after
they were truncated at a Lean let expression. The quadratic regression's
simplification and subsequent style warnings were fixed before the final
warning-free build and principal BATs. No warning suppression or proof
weakening was used.

Baseline HEAD remains `c1656d25781ca47831cc8730a0a742b6309cd717`.
Forty pre-existing dirty/untracked node-63 entries were preserved; nine
additional proof modules bring the total to 49 entries, all in node 63:
15 modified and 34 untracked. Eleven documents are synchronized with
historical checkpoint material retained. All 42 aggregate checklist
checkboxes are unchanged. The graph has 252 nodes and 699 edges, with
no duplicate or unresolved identifiers. No files were staged, committed
or pushed.

### New compiled-source SHA-256 snapshots

| Module | SHA-256 |
|---|---|
| `PhaseSlopePartition.lean` | `a19dfa9094b07a48787e83cbe381083f15021ef95d30eae796aba5ed7d1e37cb` |
| `PhaseSecondDerivativeIntegral.lean` | `fbedd4c12e9de66e0a65d8030744ffda28f773aa7f3e3eca3d4da3d8d0b9bc00` |
| `PhaseWeightedCurvature.lean` | `3df1ee3d414486c8c76c7b43a98489a2fc07b8981a4061d4807ed9d4b83fc7cf` |
| `BetaBufferedCurvature.lean` | `9264747667475ace460a9646d90bda147cfaf1d99c7dbcf90e2a88955a00f8b3` |
| `BetaClosedSlope.lean` | `25adf065de4d694dd33544351f9a65c414c990f06b5eb75f0499678e9e2647a0` |
| `BetaEndpointNonstationary.lean` | `1e7724c7011072387d27132fdfe9088e29cb11bc2952f1563d2f3b988df4a25a` |
| `BetaEndpointCore.lean` | `ef896dbe5bf6055addf6eafa2b484545e5437efda56c3abb24c74dedd3e5663c` |
| `BetaCoreNonstationary.lean` | `d5beafad5edde6d368134f4ff23ced1000ebeb6c768f75aad21c4ae813e21208` |
| `BetaBufferedStationaryExpansion.lean` | `4e183c79d0b2a46f5bdaf61128afc15306006709a61833c0c8a437405023fb47` |

Permanent `EnergyPoweringObstruction.lean` SHA-256:
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

## Sharp stationary source expansion and interior logarithmic sums — previous checkpoint

The ORIGINAL source now has a sharp interior C_sigma*N/(T*d) error,
a logarithmic sum over the actual plateau integers, a proved transition
count, and support-exterior harmonic bounds. The assembled source theorem
chooses eta=T^(-1/2), giving nonlogarithmic error
(4+6*E)*N/sqrt(T)+3+2*E*(sigma+1), with every remaining logarithm and
the polynomial far-tail radius explicit. The actual short-interval source
branch is also proved. No eta^(-3) stationary loss is needed in this route.

Public consumers:
`modelPhaseBufferedFourierMode_interior_uniform`,
`modelPhaseBufferedInteriorBlock_error`,
`modelPhaseBufferedTransition_error`,
`modelPhaseBufferedSharpCore_error`,
`modelPhase_buffered_source_inverse_sqrt_expansion`, and
`norm_exponentialSumAt_le_buffered_short`.

Uniform logarithmic budgets, the actual moving canonical dual-chart
assembly, alpha-to-1-alpha power-window transport, full beta reflection,
and the general B process remain OPEN under EPZAE-09/10. No aggregate
checkbox changes. The full EPZAE-00--41 objective remains unfinished.
See the latest Goal Prompt for exact hypotheses, constants, formulas
and the six green-node semantic checks.

All 12 new modules enter the default imports and exact runner inventory;
44 public axioms audits and 49 regressions accompany them.
The counterexample and corrected powering/Heath--Brown/optimization/
nine-clause Add-est chain are preserved. Both build BATs remain mandatory.

### Production modules

- `Extension/TaoTrudgianYang2025/BetaQuadraticLocalRemainder.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedMorseLocal.lean`
- `Extension/TaoTrudgianYang2025/BetaMorseWindowIntegral.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedLocalNonstationary.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedWindowTails.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedInteriorStationary.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedInteriorFrequency.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedInteriorSum.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedSupportGap.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedTransitionBands.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedSharpCore.lean`
- `Extension/TaoTrudgianYang2025/BetaBufferedSharpSource.lean`

### Explicit public audits

- `abs_segmentTaylorAverage_le_closed`
- `abs_quadraticTaylorCoefficient_le_local`
- `abs_deriv_quadraticTaylorCoefficient_le_local`
- `norm_integral_sq_mul_betaQuadraticKernel_le_local`
- `norm_quadratic_window_remainder_le_local`
- `quadraticRemainderConstant_le_inverse_window`
- `modelPhaseMorseWindow_mem_and_inverse`
- `iteratedDeriv_bufferedMorseWeight_of_flat`
- `bufferedMorseWeight_local_jet_bound`
- `bufferedLocalStationaryOrder_pos`
- `bufferedMorseWeight_local_window_remainder`
- `bufferedMorseWeight_local_window_remainder_inverse`
- `integral_inverseMorse_window`
- `modelPhaseMorse_window_integral`
- `IntervalC1Bound.fourierChar_of_closed_slope_gap`
- `norm_buffered_subinterval_nonstationary`
- `modelPhaseMorseInverse_window_slope_gaps`
- `norm_bufferedNormalizedMode_sub_window_le`
- `bufferedNormalizedMode_interior_window_remainder`
- `modelPhaseBufferedMorseRemainder_interior_uniform`
- `modelPhaseBufferedFourierMode_interior_uniform`
- `modelPhaseInverseSlope_interior_of_gap`
- `modelPhaseBufferedFourierMode_interior_frequency_uniform`
- `sum_range_two_edge_reciprocals`
- `norm_sum_range_le_two_edge_harmonic`
- `modelPhaseBufferedInteriorRange_error`
- `modelPhaseBufferedInteriorBlock_error`
- `modelPhaseBufferedNormalizedMode_eq_interval`
- `norm_modelPhaseBufferedFourierMode_of_support_gap`
- `sum_norm_bufferedModes_support_right_le_harmonic`
- `sum_norm_bufferedModes_support_left_le_harmonic`
- `norm_bufferedModes_support_blocks_le_log`
- `modelPhaseBufferedBand_endpoints`
- `modelPhaseBufferedBand_card_bounds`
- `modelPhaseBufferedTransition_card_le`
- `modelPhaseBufferedSupport_inside_core`
- `modelPhaseBufferedTransition_error`
- `modelPhaseBufferedSupportCore_error`
- `modelPhaseBufferedSharpCore_error`
- `modelPhase_buffered_source_sharp_expansion`
- `bufferedTransitionCost_eq`
- `bufferedTransitionCost_inverse_sqrt`
- `modelPhase_buffered_source_inverse_sqrt_expansion`
- `norm_exponentialSumAt_le_buffered_short`

Turn-start HEAD was `c1656d25781ca47831cc8730a0a742b6309cd717`.
The owner committed during this implementation; final verification used
`6b19864d9be669882d1762e263ebb43ed7915d04`. All existing changes
were preserved. Twelve new production modules were developed; eleven
are now in the owner commit, and `BetaBufferedSharpSource.lean` remains
untracked. No agent staging, commit or push was performed.

### Verification

Both mandatory BAT runners passed on 22 September 2026 with exit code 0,
zero Lean warnings/errors/tactic suggestions, and passing integrity and
dependency gates. The target covers 656 production-package files,
scans 667 Lean files, and audits 5778 imported/target declarations.
All 44 new explicit audits and 49 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-113320-9230abb9.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_113331.log).
All 315 checkpoint source/integration/runner hashes agree before and
after the BATs. The graph has 258 nodes and 713 resolved, nonduplicate
edges; all 42 aggregate checklist checkboxes are unchanged.
The full goal remains unfinished.

The focused command was `lake build TaoTrudgianYang2025.SemanticRegression`:
exit 0, 9511 jobs, no Lean warnings. Exact-type regressions retain the
full original objects, constant quantifier order, finite model order,
support/plateau rounding, source endpoints, and physical factors.
All 44 public audits occur once and use only permitted
`propext`, `Classical.choice`, and `Quot.sound` dependencies.

The target command was
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`.
It discovered 5773 nonprivate target theorems plus 5 imported anchors,
for 5778 audited declarations. Its log SHA-256 is
`f36440ad86bad8b5ecf55e0397c518f5f3fb8d9ad17a0c04806906a9d724a3cb`.

The foundation command was `cmd /c run_lake_build.bat --no-pause`.
All six manifest stages passed: root build, exact publication contract,
two retained regressions, transitive/output audit and declaration linter.
It covers 301 root modules plus 2 explicit regressions, with 8857 jobs,
7636 explicit public declarations and 14290 discovered nonprivate
theorems. The complete physical log has no Lean diagnostics.
Log SHA-256:
`e601aacc443e1db0bb96b7c44413de12eaa075a1b21f51ac68eed67eeec05fe0`.
Manifest SHA-256:
`db3abcb8b9597c7f52d9cb8d5ccce6005f3c6ff9d273ece12fb202583b29dbb9`.

The twelve new source texts and four integration texts match their
verified snapshots after line-ending normalization. The counterexample,
existing energy proofs, both BAT launchers, foundation verifier, frozen
sources and dependency pins are unchanged. Repository scans match only
ordinary comments and two genuine rational structure fields named
`constant`; no prohibited postulate or proof term was found.

The turn began at HEAD `c1656d25781ca47831cc8730a0a742b6309cd717`.
An external owner commit, `6b19864d9be669882d1762e263ebb43ed7915d04`
("Progress Update", 11:21:37 Pacific), occurred during implementation.
No agent staging, commit or push was performed, and no source contents
were reverted or lost. The final verified checkout is at that new HEAD,
with 15 modified node-63 files and one untracked new production file,
`BetaBufferedSharpSource.lean`; the other eleven new modules were
included by the external commit. The 49 dirty entries present at turn
start were preserved through the work, not reset.

## Uniform source power error and full moving-slope geometry — previous checkpoint

The original source now satisfies the uniform comparison
C_sigma,epsilon*(N/sqrt(T)+T^epsilon), with constants chosen before all
physical data. The actual retained plateau integers are used in the long
branch; the genuine source cardinality pays for the entire short branch.
Every retained frequency has a derived actual critical point and an
explicit positive endpoint margin.

The full actual slope image, under delta<=min(2^(-sigma)/2,1), lies in
[2^(-sigma)/2,2]. Inverse-point stability and every original derivative
comparison at the explicit reciprocal reference point now hold there,
including outside the strict reference interval. This does not assume
smoothness of the original phase outside [1,2].

Public consumers: `modelPhase_source_sharp_comparison`,
`modelPhaseSharpStationarySet_critical_geometry`, and
`modelPhaseInverse_iteratedDeriv_expanded_reference_error`.
See the latest Goal Prompt for exact signatures, bounds and green-node
checks. Higher inverse/Legendre errors on the expanded window, exact
moving canonical charts, physical power-window transport, full beta
reflection and the general B process remain OPEN under EPZAE-09/10.
All 42 aggregate checkboxes are unchanged.

Six new modules, 23 public audits and 27 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/nine-clause Add-est chain are unchanged.
Both build BATs remain mandatory and must track production coverage.

Production additions:

- `BetaBufferedLogBudget.lean`
- `BetaBufferedUniformError.lean`
- `BetaBufferedPowerError.lean`
- `BetaBufferedRetainedGeometry.lean`
- `BetaExpandedInverseStability.lean`
- `BetaExpandedModelJets.lean`

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 662 package files, scans 673
Lean files and audits 5817 discovered target theorems plus 5 imported
anchors (5822 declarations). All 23 new explicit audits occur once and
use only permitted standard logical axioms; all 27 regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-120938-14509d95.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_120949.log).
All 321 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 262 nodes and 722 resolved,
nonduplicate edges; all 42 aggregate checkboxes are unchanged.
The counterexample and repaired energy chain remain unchanged.

The focused command `lake build TaoTrudgianYang2025.SemanticRegression`
passed with 9517 jobs and zero diagnostics. Exact-type regressions retain
the original objects, quantifiers, physical scales and finite model order.
The target command was
`cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
its log SHA-256 is `233b63a9b474dfbd4add564812905e4566c9e853d7f4122c8b2f37513d76152c`.

The foundation command was `cmd /c run_lake_build.bat --no-pause`.
All six manifest stages passed: root build, exact publication contract,
two retained regressions, transitive/output audit and declaration linter.
It covers 301 root modules plus two regressions (8857 jobs), with 7636
explicit public declarations and 14290 discovered nonprivate theorems.
Foundation log SHA-256: `2a29a874777bdedb2d3ce3fe7c62c0743a038a0d09caf5dfeda90346d0ba7090`.
Manifest SHA-256: `a321a4e4c6293b122c96bfa09ca9ff7cdab7a39e5d34b58d0c0f856473b46a1f`.

Repository-wide scans match only ordinary comments and two genuine
rational structure fields named `constant`; no prohibited proof term or
postulate was found. `git diff --check` passes; Git's LF-to-CRLF notices
are not Lean diagnostics. HEAD remains
`6b19864d9be669882d1762e263ebb43ed7915d04`.
The pre-existing dirty worktree is preserved. No agent staging, commit
or push was performed. This is a verified implementation checkpoint,
not completion of the full EPZAE-00--41 goal.

## Moving canonical Taylor extensions and retained-frequency coverage — previous checkpoint

The actual Legendre error now has a globally smooth moving-endpoint
Taylor extension, exact on its retained plateau, with uniform finite
derivative bounds independent of the shrinking buffer width. Full-image
inverse/reference jet estimates and a five-region proof supply the bounds;
no exterior regularity of the original phase is assumed.

`modelPhase_source_canonicalTaylorPhase` chooses its model tolerance
before the source data, derives h=min(c_sigma,1)/(4*sqrt(T)) and the anchor
F'(3/2), proves the full closed-[1,2] canonical model condition, and proves
exact phase identities for EVERY retained stationary integer.
It does not assert that all integers belong to one multiplicative chart.

The finite positive-slope chart partition, whole stationary main-sum beta
bound, physical power-window transport, beta reflection and general
B process remain OPEN under EPZAE-09/10. All 42 aggregate checkboxes are
unchanged. See the latest Goal Prompt for the exact formulas, finite input
orders, constant dependencies and four green-node semantic checks.

Eighteen modules, 53 public audits and 60 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain are preserved.
Both build BATs remain mandatory and must track production coverage.

Production additions:

- `BetaExpandedReferenceJets.lean`
- `BetaExpandedJetBounds.lean`
- `BetaExpandedAllOrders.lean`
- `BetaExpandedAnchoring.lean`
- `BetaTaylorPolynomialJets.lean`
- `BetaTaylorPolynomialRemainder.lean`
- `BetaTaylorCutoffBudget.lean`
- `BetaTaylorTransitionBudget.lean`
- `BetaLegendreTaylorTransition.lean`
- `BetaTaylorPastedExtension.lean`
- `BetaTaylorPolynomialBudget.lean`
- `BetaTaylorPastedTransitionBounds.lean`
- `BetaTaylorPastedUniform.lean`
- `BetaExpandedEndpointGeometry.lean`
- `BetaLegendreTaylorExtension.lean`
- `BetaCanonicalTaylorLegendre.lean`
- `BetaTaylorRetainedCoverage.lean`
- `BetaSourceTaylorPhase.lean`

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 680 package files, scans 691
Lean files and audits 5904 discovered target theorems plus 5 imported
anchors (5909 declarations). All 53 new explicit audits occur once and
use only permitted standard logical axioms; all 60 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-130811-0ad529b7.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_130808.log).
All 339 checkpoint source/integration/runner hashes match before and after
the BATs. Eighteen source texts and four integration texts also match
their normalized snapshots. The graph has 266 nodes and 732 edges, with
no duplicate nodes or unresolved endpoints; all 42 aggregate checkboxes
are unchanged. The counterexample and repaired energy chain remain unchanged.

Target log SHA-256:
`8c4b6ae5f9f0f5f471ef6f23d176809009069aa2b2e76fe1472750631561b566`.
Foundation log SHA-256:
`6895a34b32a29065de84b494519181776acfc44f29ba75689ca62ebb26fceea9`.
Foundation JSON SHA-256:
`68033d003c3c5768c80c59216f37a9dceedb529805d0e7f376630b8219edcbe1`.
The foundation manifest records six passing stages, a 301-module root
graph plus two explicit regressions, 8857 build jobs, 7636 explicit
public declarations and 14290 discovered theorems. The target default
build completes 9535 jobs. Repository-wide shortcut scans retain only
ordinary comments and the two genuine rational-valued `constant`
fields, not mathematical postulates. `git diff --check` exits 0;
Git's LF-to-CRLF advisories are not Lean diagnostics.

## Full source chart assembly and the analytic B-process — previous checkpoint

The exact finite positive-slope grid now partitions EVERY original
retained stationary integer into contiguous natural-number chart blocks.
The moving Taylor phases, actual amplitude variation and upstream beta
bounds are assembled, with physical dual windows derived from N,T.
`sourceExponentialSum_reflection_estimate` proves the complete original
sum bound, including C*(N/sqrt(T)+T^epsilon) source error.

The resulting nonasymptotic reflection bound has exponent
max(0,beta+1/2-alpha). Its max is removed only when the reflected exponent
is proved nonnegative. The full beta-reflection identity remains OPEN.

`ExponentPair.bProcess` now proves the paper's analytic transformation
(k,l)->(l-1/2,k+1/2); its target affine line is nonnegative by the triangle
conditions. It does not assume the still-open exact reflection identity.
The next reflection obligation is a genuine beta lower bound sufficient
to remove the zero envelope. A and C processes remain open, so EPZAE-10
is not crossed out. All 42 aggregate checkbox states are unchanged.

Eleven modules, 35 public audits and 41 regressions are integrated.
The printed counterexample, corrected independent powering witnesses,
Heath--Brown energy relation, exact optimization and all nine repaired
Add-est clauses are unchanged. BOTH build BATs remain mandatory and
their imports, inventory and audits must track production changes.
See the current Goal Prompt for quantifiers and all five green-node tests.

Installed production modules:

- `PositiveSlopeCharts.lean`
- `PositiveSlopeChartFibers.lean`
- `BetaSourceChartPartition.lean`
- `BetaTaylorStationaryMain.lean`
- `BetaSourceChartBound.lean`
- `BetaDualPowerWindows.lean`
- `BetaSourceChartPhysical.lean`
- `BetaSourceMainBound.lean`
- `BetaSourceReflectionEstimate.lean`
- `BetaReflectionEnvelope.lean`
- `ExponentPairBProcess.lean`

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 691 package files, scans 702
Lean files and audits 5960 discovered target theorems plus 5 imported
anchors (5965 declarations). All 35 new explicit audits occur once and
use only permitted standard logical axioms; all 41 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-135040-f8df686c.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_135036.log).
All 350 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match
their normalized snapshots. The graph has 270 nodes and 740 edges, with
no duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain remain unchanged. These checks verify this recorded scope;
they do not assert whole-goal completion.

Target log SHA-256:
`bafbe968aff73e71023f1dfe09c2bb8f1b1348408ebb0a8d11be274bad3b227d`.
Foundation log SHA-256:
`237acb4477c6eee1b8d8c1046c13e7c81b5041e514af39b833419c7222fab077`.
Foundation JSON SHA-256:
`1e2d43eac58b0d8883d762432b4129a309bd7ea3363f63e00df85d11d2369369`.
The foundation manifest records six passing stages, a 301-module root
graph plus two explicit regressions, 8857 build jobs, 7636 explicit
public declarations and 14290 discovered theorems. The target default
build completes 9546 jobs. Repository-wide shortcut scans match only
ordinary comments and the two genuine rational-valued `constant`
fields, not mathematical postulates. `git diff --check` exits 0;
Git's LF-to-CRLF advisories are not Lean diagnostics.

## Exact beta reflection from coherent source sums — previous checkpoint

`exponentSumGrowthExponent_reflection` now proves the exact printed
identity beta(1-alpha)=1/2-alpha+beta(alpha) for every 0<=alpha<=1,
including endpoints. Convex closure, closed two-way duality and the
endpoint values were already proved; all EPZAE-09 mathematical
acceptance clauses are now supplied.

The new lower-bound proof is independent of reflection and the B-process.
It constructs actual phases log(u)+c*(u-1) with integral linear
oscillation at integer N, controls every finite model jet, and sums
a genuine closed coherent block. Beyond every threshold it produces
T^alpha=N and norm(original sum)>=T^(alpha-1/2)/8, proving
beta(alpha)>=alpha-1/2. This removes the zero envelope from the
previous complete original-source estimate; the two reflected
inequalities then give equality. No stronger alpha/2 bound is claimed.

Six modules, 18 public audits and 24 regressions are integrated.
EPZAE-10 remains OPEN: its general B-process is proved, A and C are not.
Continue with those analytic processes and the remaining whole-proof
obligations; this checkpoint does not complete the full goal.

The printed counterexample, corrected independent powering witnesses,
Heath--Brown relation, exact energy optimization and all nine repaired
Add-est clauses remain unchanged. BOTH build BATs remain mandatory,
and production imports, inventory and audits must track source changes.
See the current Goal Prompt for quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 697 package files, scans 708
Lean files and audits 5990 discovered target theorems plus 5 imported
anchors (5995 declarations). All 18 new explicit audits occur once and
use only permitted standard logical axioms; all 24 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-141433-3e901ee8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_141443.log).
All 356 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 274 nodes and 748 edges, with no
duplicate nodes or edges and no unresolved endpoints. There are still
42 aggregate checkboxes: only EPZAE-09 changes to complete; all others
retain their status. The counterexample and completed repaired energy
chain are unchanged. These checks verify this recorded scope, not
whole-goal completion.

Target log SHA-256:
`82967e30036458f8f1f9e54d267b2a0693e6ef9d7fb7306cd6d9d95f9c92c1e3`.
Foundation log SHA-256:
`5970bd5ae7f8f7731c960b71618652bffcb85e60d05e8323618321e56aa110bf`.
Foundation JSON SHA-256:
`cd69a2842a4fcf1bcb511a90bffbe618539f8178efeed0ed13e94af2366dce5b`.
The foundation manifest records six passing stages, a 301-module root
graph plus two explicit regressions, 8857 build jobs, 7636 explicit
public declarations and 14290 discovered theorems. The target default
build completes 9552 jobs. Repository-wide shortcut scans match only
ordinary comments and the two genuine rational-valued `constant`
fields, not mathematical postulates. `git diff --check` exits 0;
Git's LF-to-CRLF advisories are not Lean diagnostics.

## Domain-preserving A-process models and source differencing — previous checkpoint

The A-process now has a domain-preserving shifted-model constructor,
exact original-source correlation identities, and a summed-correlation
Weyl inequality on the literal source exponential sum.

The constructed phase uses affine compression inside [1,2] and has
model parameter sigma+1, with every requested finite derivative and
both endpoints controlled by one tolerance chosen before the source.
Its physical parameters are exactly N'=N-r and T'=sigma*T*r/N;
the reindexed integers and conjugation are proved, including empty
overlaps. The analytic exponent-pair consumer derives its model and
endpoint conditions but explicitly retains C<=T' and N'<=T'.

`source_exponentialSum_weyl` constructs the actual padded source
sequence and keeps 2*H times the SUM of nonzero correlations. It has
no assumed analytic estimate. The small-dual-parameter branch and
integer shift optimization remain OPEN; A is not yet proved.
EPZAE-09 and the B-process remain complete. C remains open.
All 42 aggregate checkbox states are unchanged.

Eleven modules, 32 public audits and 39 regressions are integrated.
The printed counterexample and the corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain remain unchanged. BOTH build BATs
remain mandatory and must track production imports, inventory and audits.
See the current Goal Prompt for exact quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 708 package files, scans 719
Lean files and audits 6069 discovered target theorems plus 5 imported
anchors (6074 declarations). All 32 new explicit audits occur once and
use only permitted standard logical axioms; all 39 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-150004-71e72f6e.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_150014.log).
All 367 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match their
normalized snapshots. The graph has 280 nodes and 760 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain are unchanged. These checks verify this recorded scope,
not the still-open A-process or whole-goal completion.

Target log SHA-256:
`36df9abf688bbc2ec810eda70c09f8708c1a612391609095be417b46e13b9b65`.
Foundation log SHA-256:
`7681b49842893de408ccfbd635eb9ae072d062c424798838142a2be6ea05a6ca`.
Foundation JSON SHA-256:
`a4ac6da13e48d4ae6e030b31cc8750d3e4bb346b4e35cc39bdfe250eb42b7f79`.
The foundation manifest records six passing stages, a 301-module root
graph plus two explicit regressions, 8857 build jobs, 7636 explicit
public declarations and 14290 discovered theorems. The target default
build completes 9563 jobs. Repository-wide shortcut scans match only
ordinary comments and the two genuine rational-valued `constant`
fields, not mathematical postulates. `git diff --check` exits 0;
Git's LF-to-CRLF advisories are not Lean diagnostics.

## General analytic A-process from original source sums — previous checkpoint

The classical A-process is now proved for the paper's actual analytic
exponent-pair predicate:

    ExponentPair k l
      ==> ExponentPair (k/(2*k+2)) (l/(2*k+2)+1/2).

The public consumer is `ExponentPair.aProcess`. Its proof derives the
closed shifted model, source reindexing and conjugation, all positive
dual-height estimates, summed correlations, the original-source Weyl
bound, a genuine natural-number shift and the full epsilon budget.
It does not assume a transformed-phase estimate, a dual-height window,
an optimization certificate, or the output exponent-pair estimate.

The formerly open small-height branch is proved by the full closed-source
`norm_exponentialSumAt_le_firstDerivative`; curvature handles transition
heights, and `ExponentPair.allPositiveHeight_bound` combines every positive
height with the actual input pair. `sourceShiftCorrelation_normalized_bound`
links the result back to N,T,r, including the N^2/(T*r) term.
`sum_sourceShiftCorrelation_le` retains its harmonic sum.
`source_exponentialSum_differencing_bound` consumes the literal source sum.

`integer_shift_optimization` uses an actual floor-comparable natural H;
when that scale is too small, the original sum's cardinality supplies
the separate branch. `aProcessOptimizationScale_balance` and
`aProcessOptimizationScale_cost` link the optimum exactly to N,T.
The logarithmic loss is absorbed by `aProcess_power_budget`.
`source_exponentialSum_aProcess_bound` and
`isExponentPairEstimateNonAsymptotic_aProcess` assemble every source
interval, empty interval and bounded-N case with constants chosen first.

Fifteen production modules, 33 explicit public-theorem audits and 40
regressions are integrated. The extra fixtures include actual A/A/B
compositions yielding (1/6,2/3), (1/14,11/14), and (2/7,4/7), the H=0/H=1
harmonic endpoints, and two optimization-scale checks.

EPZAE-09 and both A/B processes are complete; C remains OPEN, so EPZAE-10
remains unchecked. D, Heath--Brown derivative inputs, certified beta
tables, the four advertised pairs and the remaining density/public
release obligations remain in the whole-proof goal. All 42 aggregate
checkbox states are unchanged.

The printed counterexample, corrected independent rho/k and rho*/k
witnesses, unrestricted fifth coordinates, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
preserved. BOTH build BATs remain mandatory; keep their production
imports, PowerShell inventory, audits and regression coverage synchronized.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 723 package files, scans 734
Lean files and audits 6118 discovered target theorems plus 5 imported
anchors (6123 declarations). All 33 new explicit audits occur once and
use only permitted standard logical axioms; all 40 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-155044-98a95e32.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_155054.log).
All 382 checkpoint source/integration/runner hashes match before and after
the BATs. Fifteen source texts and four integration texts also match their
normalized snapshots. The graph has 281 nodes and 762 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. This verifies the exact analytic A-process,
not C or whole-goal completion. The counterexample and the completed
repaired energy chain remain unchanged.

### Exact reproduction evidence

- Target command: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`; exit 0,
  `LEAN VERIFICATION PASS`, 9578 build jobs, 723 package files, 734 scanned
  Lean files, 6118 discovered + 5 anchors = 6123 audited declarations.
  Log SHA-256: `1bbba3e7c64a3954372b664410c9f588437c292b66105e6ab551317df5e1e2f7`.
- Foundation command: `cmd /c run_lake_build.bat --no-pause`; exit 0,
  `PASS`, all six stages pass, 301 root modules + 2 retained regressions,
  8857 build jobs, 7636 explicit declarations and 14290 discovered theorems.
  Log SHA-256: `5f330bbf4d03a358d393dd746248d178933bb4482b2558e456dd5e3f6190a2f4`.
  JSON SHA-256: `6a3ff641de27ef1f66234af654588e16def1073a224f10466fac20dda1a2b63c`.
- All 33 new public audits occur exactly once with no prohibited dependency.
  Complete physical logs contain zero Lean warnings/errors/suggestions.
- All 382 source/integration/runner hashes match before and after both BATs.
  All 15 new source texts and four integration texts match normalized snapshots.
- Counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
  BATs and the foundation verifier are unchanged; the target's backing
  production inventory now includes every new module.
- Owner HEAD remains `6b19864d9be669882d1762e263ebb43ed7915d04`.
  The worktree is dirty; nothing was staged, committed or pushed.
  Repository shortcut scans find only ordinary comments and the two genuine
  rational structure fields named `constant`, not mathematical postulates.

## Native Heath–Brown derivative input and exact source beta bound — previous checkpoint

The source `heath-brown-2017` conclusion is proved by
`exponentSumGrowthExponent_le_heathBrown` for every natural k >= 3
and every real alpha > 0, with the exact displayed three-branch formula.
Its public signature has no derivative theorem or beta bound parameter.
The native input is `GafniTao.heathBrownKthDerivativeTheorem_native`.

The nine-module bridge derives signed model-jet bounds, the physical
scale lambda = c*T/N^k, smoothness on the actual closed interval, exact
translation and conjugation of the tail sum, and restoration of the
first endpoint. It includes singleton and empty intervals. Constants,
model accuracy and derivative order precede all actual phases, heights,
scales and source endpoints. The source window and epsilon budget give
the non-asymptotic beta predicate, then the exact ANTEDB growth exponent.

The pinned dependency contains 460 unchanged mathematical source modules
with documented import-path adaptations and two proved PNT prefixes.
It inherits the canonical foundation and its existing pins, without a
second or shadow foundation. Its ledger verifies 469 files and its root
reaches all 463 Lean modules. The audit also checks every nonprivate
theorem defined in those pinned modules, including the global PNT names.
The first compatibility build that exposed unrelated admitted Wiener
preliminaries is not accepted evidence; the proved prefixes avoid that
monolithic import without editing the canonical external checkout.

All ten new production modules, 42 named public audits, four explicit native/PNT
boundary audits and 51 semantic regressions are integrated. The fixtures
include the actual beta bounds beta(1/2) <= 5/12 and beta(1/3) <= 11/36,
plus exact formula, source-table endpoints and closed-singleton checks.

`HeathBrownBetaTable` proves the first two source beta-table rows from
this analytic bound, including alpha zero and both joining endpoints.
The second affine segment is proved on the larger closed interval
[1/4,2/5], then restricted to the printed endpoint 890/3277. These are
proved analytic rows, not a claim that the full beta table is complete.

EPZAE-12 is complete. EPZAE-09 and A/B remain complete; C and D remain
open, so EPZAE-10 and EPZAE-11 stay unchecked. Certified beta-table
assembly, the four advertised exponent pairs, density and release
obligations remain in the unchanged whole-proof contract. Only the
EPZAE-12 checkbox changes among the 42 aggregate items.

The permanent printed Lemma 62 counterexample and completed corrected
cardinality/energy powering, Heath--Brown energy relation, exact energy
optimization and all nine Add-est clauses are unchanged. The two powering
witnesses still have independent, unrestricted fifth coordinates.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
source verifiers, root imports, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, import,
dependency, audit or runner changes. A passing build does not complete
the remaining whole-proof outputs.

### Compatibility failures excluded from acceptance evidence

The first native compatibility run exposed `prelim_decay_2` and
`prelim_decay_3`, unrelated admitted declarations in the monolithic PNT
Wiener import. An overlapping focused build also encountered a temporary
missing dependency artifact. Neither run is clean verification evidence.
Both processes ended before the serialized rebuild. The installed package
now imports the documented proved PNT prefixes, with no changes to the
canonical external checkout and no new assumption. Subsequent Lake builds
sharing these native artifacts are serialized. The final physical logs
below, not the failed intermediate runs, establish the recorded result.

### Physical evidence hashes

| Evidence | SHA-256 |
|---|---|
| Target full log | `36a48f252ae09ccbe2c0b95d3d87467c23bfd3dc063d3489a4da6935159af678` |
| Foundation full log | `184809ec2d7b8132f7477163170453740c25d8318965ba241b11da71f55e6b06` |
| Foundation manifest | `86bdd63abb3721edae4395e7ca5ad7ff2be1b2f858b221fe1da5d7ef43be8931` |
| Source checkpoint JSON | `fc22ee1bb0eac175ea9ee5bacff7a238764fe31bd80fd8b8c1a5de8cd7c84745` |

The source checkpoint includes the 1,228 before/after hashes, 15 normalized
source snapshots, all 42 new named theorem signatures and both evaluation
results. The source snapshot commit is `6b19864d9be669882d1762e263ebb43ed7915d04`;
the evaluated checkout reports `ca06d579f67fac68c1ffcd1696f3d46ae40578f2` with a
dirty worktree. No agent commit or push was performed.

Scoped `.gitattributes` rules preserve the exact bytes of pinned Sources,
ANTEDB/native dependency files, the generated certificate and the permanent
counterexample across Git checkouts. The runner requires this policy file.
No repository Git configuration was changed. A read-only comparison of
509 protected files against HEAD found 507 byte-identical; the only two
differences are the documented native README correction and its ledger.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), each
with exit code 0. Their complete physical logs contain no Lean warnings,
errors, tactic suggestions or linter failures. The target covers 733
package files and scans 1,207 Lean files; its default build checks 10,065
jobs. The audit checks 6,191 discovered target theorems, 6,240 pinned
source theorems and 5 imported anchors: 12,436 declarations in total.
All 42 new named public audits and all four native/PNT boundary audits
occur exactly once and use only permitted standard logical axioms.
All 51 new semantic regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-174454-55b1abae.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_174825.log).
The foundation's six stages pass with zero diagnostics: 301 root modules,
two retained regressions, 8,857 build jobs, 7,636 explicit public declarations
and 14,290 discovered theorem dependencies.

All 1,228 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Ten source modules and five integration/verifier files match
their normalized snapshots. The complete [source checkpoint record](logs/tao-trudgian-yang-heath-brown-20260922-174454-55b1abae.json)
records these hashes and the exact new public signatures. The synchronized
graph has 286 nodes and 772 edges, with no duplicate or unresolved links.
Only EPZAE-12 changes among the 42 aggregate checkbox states. The permanent
counterexample and completed repaired energy branch are unchanged.
This verifies the recorded scope, not whole-goal completion.

## Robert–Sargos fourth-power near-count — previous checkpoint

`card_sargosFourthNearSolutions_le_log` proves, for every natural N >= 1,

    card {q in (N,2N]^4 :
      |q0²+q1²-q2²-q3²| <= N,
      |q0⁴+q1⁴-q2⁴-q3⁴| <= N³}
      <= 4096 N² (1+log N).

The finite set contains actual integer quadruples. No counting bound,
moment estimate or exponent-pair conclusion is a theorem parameter.
The geometric calculation derives |q0*q1-q2*q3| <= 5N and a bounded
sum displacement, then injects the quadruples into four integer linear
coordinates. The two difference coordinates satisfy |u*v| <= 11N.
The signed hyperbola count is proved via an injective sign/absolute-value
encoding, actual natural-number fibers, division bounds and the harmonic
sum. Zero fibers and all signs are included.

Four production modules contain 17 public theorems. All have explicit
audits and exact-signature regressions; nine additional fixtures check
N=0/1/2 counts, zero fibers, both signs and coordinate encoding.
This proves the counting assertion in Robert–Sargos section 5
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)),
with an explicit constant and a stronger N >= 1 domain.
It does not yet prove the fourth-moment integral, the sixth-moment
bootstrap or the analytic C-process. Those remain under EPZAE-10.
D, remaining beta rows/pairs, density and public-release obligations
also remain open. All 42 aggregate checkbox states are unchanged.

The counterexample, independent corrected powering witnesses and
completed Heath--Brown energy/optimization/all-nine-Add-est chain
are unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic
beta-table rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Both it and the foundation `run_lake_build.bat` remain mandatory after
proof/integration/runner changes. Retain the scoped byte-preservation
rules for the pinned inputs, generated certificate and counterexample.

The focused four-module count, 17 public boundaries and 26 regression cases
compile without warnings. Intermediate syntax/API errors were repaired;
only the final full physical logs below are acceptance evidence. The source
and tool snapshots are compared before and after both serialized BATs.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 737 package files, scans
1,211 Lean files and completes 10,069 default-build jobs. Its audit checks
6,232 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,477 declarations. The 17 new explicit public audits occur once
with only permitted standard logical axioms; all 26 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-181839-3e1844f8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_182203.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,232 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Four source texts and four integration texts match normalized
snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-count-20260922-181839-3e1844f8.json)
contains the hashes, exact theorem signatures and both evaluation results.
The synchronized graph has 290 nodes and 779 edges, with no duplicates,
unresolved endpoints or unclassified nodes. All 42 aggregate checkbox
states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

### Physical evidence hashes

| Evidence | SHA-256 |
|---|---|
| Target full log | `869f0ca2b7ab326e0c60ec110e2bd2431124aa8e833974edf45920fca0f25afe` |
| Foundation full log | `f7895da81a754a8784d3fec2411a05072e6983759eb252dcf883b21b9662e15d` |
| Foundation manifest | `540614b6a231e4d40c0a069669289bc7a653198ece39b02f8c1c363828a8c013` |
| Source checkpoint JSON | `8c1820c779e32d063918badfa97f12a57ebe5161f1ff1b4cedafc84d1859f6cb` |

The evaluated HEAD is `ca06d579f67fac68c1ffcd1696f3d46ae40578f2`,
with a dirty worktree. No agent commit or push was performed.
The previous native-derivative evidence record remains preserved.

## Robert–Sargos rectangular windows and fixed-sum fourth moment — previous checkpoint

`sargosQuartic_fourth_moment` proves, for every natural N >= 1,
every fixed complex coefficient sequence with |z_n| <= 1 on (N,2N],
and every real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      |sum_{N<n<=2N} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|^4
      <= 131072 Delta/N (1+log N).

The sum, both physical windows and the four-variable count are literal.
No counting bound, moment estimate, kernel identity or exponent-pair
conclusion is assumed. The fixed coefficients may be arbitrary on the
source interval but do not depend on the integration parameters.

Fourteen new production modules prove whole-line sinc-square
integrability, its real-frequency tent Fourier transform, shifted-window
normalization, exact two-dimensional finite Gram integration, cutoff to
actual near pairs, and the source ordered-pair square. The rectangular
mean-square factor is exactly 16*delta*lambda. The source fourth moment
then consumes the proved 4096 N^2(1+log N) quadruple count, with
lambda=2/N^3. Both translated centers and non-integral frequencies are
included. No pinned native source was modified.

All 68 new public boundaries have explicit axiom audits and exact-signature
regressions. Fourteen additional fixtures cover tent/kernel normalization,
cutoff endpoints, a non-integral shifted frequency, N=1/2 source intervals
and sums, zero coefficients, and a concrete fourth-moment specialization.

This is the fixed-sum part of the Robert–Sargos section 4--5 analytic
transfer ([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
It does not yet prove the maximum over prefixes in source Lemma 2,
the slowly varying phase extension, the sixth-moment bootstrap, or the
analytic C-process. EPZAE-10 stays open. D, the remaining beta rows,
the four advertised pairs, density and release obligations remain open.
All 42 aggregate checkbox states are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy witnesses, Heath--Brown energy relation, exact energy
optimization and all nine repaired Add-est clauses are unchanged.
EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Retain the scoped byte-preservation rules
for pinned inputs, the generated certificate and the counterexample.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 751 package files, scans
1,225 Lean files and completes 10,083 default-build jobs. Its audit checks
6,330 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,575 declarations. All 68 new explicit public audits occur once
with permitted standard logical axioms only; all 82 new regressions pass.
The intermediate fixture warning and conversion error were fixed before
these accepted full runs; they are not acceptance evidence.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-191919-9f77a11b.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_192240.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,246 recorded proof/configuration/tooling hashes are unchanged across
both serialized BATs. Fourteen source texts and four integration texts
match their normalized snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-moment-20260922-191919-9f77a11b.json)
contains the hashes, all exact new public signatures and both evaluation
results. The synchronized graph has 293 nodes and 784 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

### Physical evidence hashes

| Evidence | SHA-256 |
|---|---|
| Target full log | `b7c568ec0efe06b8424fd7bc3af94c3b01624b724dba18c60075cfee206fa247` |
| Foundation full log | `284d6b98b0dc5050f9cc6185d08483c50d81accaef33bb6f973df23a479a3487` |
| Foundation manifest | `d995cd304eb785a8bd8caee61b0de70d539a21acdc5c2cb758b34ce7c6cbfaac` |
| Source checkpoint JSON | `c7c98ca376502bbcf0376c8e03b5f545306b984ccf90e1aeec84535e8dc8f4f5` |

The evaluated HEAD is `ca06d579f67fac68c1ffcd1696f3d46ae40578f2`,
with a dirty worktree. No agent commit or push was performed.
The previous near-count and native-derivative evidence records are preserved.

## Robert–Sargos maximal-prefix fourth moment — previous checkpoint

`sargosQuartic_maximal_fourth_moment` proves, for every natural N >= 1,
fixed coefficients |z_n| <= 1 on (N,2N], and real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^4
      <= 10616832 Delta/N (1+log N)^5.

H is an integer, every source prefix is present, and the maximum is
attained. The extra H=0 prefix is the proved zero sum. This bounds the
pointwise maximum before integration, not merely each fixed-prefix
integral. Empty and zero-coefficient cases are retained and tested;
the estimate itself requires N >= 1.

Thirteen production modules prove exact finite Fourier inversion on
ZMod N, the geometric kernel and unit-circle gap, and a prefix-independent
nonnegative coefficient majorant with total mass at most 3(1+log N).
Two finite Cauchy--Schwarz inequalities give the fourth-power bound.
A proved residue bijection identifies the literal integer interval.
Every completed mode is the original sum with unit-modulus coefficient
twists independent of alpha and gamma. Maximum continuity, rectangle
integrability and finite integral interchanges are proved. The final
estimate consumes the earlier fixed-sum theorem and its literal
four-variable count, without assuming any count or moment estimate.

All 61 new public boundaries have explicit audits and exact-signature
regressions. Fifteen further fixtures cover zero-frequency kernels,
N=1/2/3 majorant masses, residue endpoints, proper/full/empty prefixes,
zero coefficients and a concrete maximal-moment specialization.

This establishes the weighted maximal fourth-moment assertion of
Robert–Sargos section 5 for natural N, with an explicit constant and
1+log N normalization
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
The parameter-dependent slow-phase extension, higher-moment window
transfer, sixth-moment bootstrap and analytic C-process remain open.
EPZAE-10 stays unchecked. D, remaining beta rows/pairs, density and
release obligations remain open. All 42 aggregate checkbox states
are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy powering witnesses, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows
are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Keep byte-preservation rules for the
pinned inputs, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0 with no Lean errors, warnings, tactic
suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [complete target log](logs/tao-trudgian-yang-build-20260922-220844-6863d940.log);
  764 production modules, 1238 scanned Lean files, 10096 build jobs,
  6425 target plus 6240 pinned theorems and five imported boundaries
  audited (12670 total). Each of the 61 new public audits appears once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_221514.log)
  and [manifest](../../logs/foundation_freeze_20260922_221514.json);
  all six stages pass, 8857 build jobs, 301 root modules and two
  retained regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-maximal-20260922-220844-6863d940.json) records
1259 physical source/configuration/tooling hashes, unchanged across
both runs, plus 17 normalized module/integration hashes. The 469-file
native pin and its 463-module closure pass. No earlier proof file was
changed: only the root, audit, regressions and runner inventory were
extended. The synchronized graph has 295 nodes and 787 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged (22 checked). The counterexample SHA-256
remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Target log | `75348507a99d8f4f950a6060cf8bd6bf251239986ceefbda995162e9ffdda00f` |
| Foundation log | `44f07d204e0bedeea17078e656d87ebc62076b13da0656163c7e1b0c341b449a` |
| Foundation manifest | `f39b4e0bc6157866c072949a194a42bcda8605cdcb34c3eb7c5c594e187d8b43` |
| Source checkpoint JSON | `ba5142df66a43329caba2a5422c03f54b537121da1fee725d068319da5cd1f7b` |

The evaluated HEAD is `ca06d579f67fac68c1ffcd1696f3d46ae40578f2`,
with a dirty worktree. No agent commit or push was performed.
Previous fixed-sum, near-count and native-derivative evidence is preserved.

## Robert–Sargos parameter-dependent slow phase — previous checkpoint

The literal quartic prefixes now admit the actual phase
alpha*n^2+gamma*n^4+phi(alpha,gamma,n), with fixed source coefficients.
For N >= 1, K >= 0 and Delta >= 1/N, assume only the genuine local
derivative data on x in [N,2N] and on the integration rectangle:

    |d phi(alpha,gamma,x)/dx| <= K/N.

`sargosSlowQuarticMaximum_le` derives the pointwise bound by
(1+2*pi*K) times the unperturbed prefix maximum. The proof uses the
global character Lipschitz bound, exact integer-interval reindexing,
and finite Abel summation. Its adjacent variation is at most 2*pi*K;
no moment estimate or conclusion-equivalent variation bound is assumed.

`sargosSlowQuartic_upper_fourth_moment` then proves

    upper integral over [0,Delta] x [-N^-3,N^-3]
      (max_{0<=H<=N} |sum_{N<n<=N+H}
        z_n exp(2*pi*i*(alpha*n^2+gamma*n^4+phi(alpha,gamma,n)))|)^4
      <= (1+2*pi*K)^4 * 10616832 Delta/N (1+log N)^5.

There is no measurability hypothesis on the phase family here.
`sargosUpperIntegral` is the infimum of nonnegative integrals of
almost-everywhere measurable majorants. Its monotonicity and equality
with the ordinary nonnegative integral on measurable integrands are
proved. The result therefore does not exploit the default value of an
undefined Bochner integral.

For an almost-everywhere strongly measurable actual fourth-power
integrand, `integrable_sargosSlowQuarticFourth` proves integrability
from the existing majorant, and `sargosSlowQuartic_fourth_moment`
proves the ordinary iterated-integral estimate via Fubini. Continuity
of the actual maximum follows from continuity of each sampled phase.
The linear-phase consumers derive the derivative data for
phi(alpha,gamma,x)=u(alpha,gamma)*x/N; the upper-integral consumer
allows an arbitrary bounded, possibly nonmeasurable u.

Seven production modules contain 29 explicitly audited public theorems.
There are 29 exact-signature regressions and nine additional fixtures,
including a sin(alpha)-dependent phase, a bounded family without a
measurability assumption, Dirac upper integration, zero phase,
zero coefficients, the empty prefix and N=0 definitions.

This realizes the slow-phase removal used in Robert–Sargos section 4,
and composes it with the proved section 5 fourth moment
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S4)).
The printed variation sentence has an extra 1/N: a derivative of size
K/N over an interval of length N gives variation of size K. The proof
uses the correct explicit constant. The arbitrary higher-moment and
two-window comparison in Lemma 1, the sixth-moment argument and the
analytic C-process remain open. EPZAE-10 remains unchecked.

The permanent printed Lemma 62 counterexample and the completed
corrected powering -> Heath--Brown energy -> exact optimization ->
all nine repaired Add-est clauses are unchanged. A/B, EPZAE-09,
EPZAE-12 and the first two analytic beta rows are preserved.
All 42 aggregate checkbox states are unchanged.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, explicit audits, regressions and source verifiers
synchronized. Run it and the foundation `run_lake_build.bat` after
proof, integration, dependency or runner changes; preserve the pinned
bytes, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-223544-52ff7f68.log); 771 production modules,
  1245 scanned Lean files, 10103 build jobs; 6474 target and 6240 pinned
  theorems plus five imported boundaries audited (12719 total).
  All 29 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_223848.log) and
  [manifest](../../logs/foundation_freeze_20260922_223848.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-slowphase-20260922-223544-52ff7f68.json) records
1266 physical source/configuration/tooling hashes, unchanged across
both runs, and 11 normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, every earlier proof file is unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 297 nodes and 790 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Target log | `9a0cb97d7c12c8bc385a9e1f1c0a895ee1b54361a86f661f291c7e8addcb22be` |
| Foundation log | `1c7ff856ef2229b81197c3027b94b62f3a92fb8edb6a625031535b841175a4e4` |
| Foundation manifest | `2aa009a481c2ab8df7a2ec7859b0a254bd378bebd8994ec774148d6dc52d438b` |
| Source checkpoint JSON | `721a68e8db38dfe508c499240b1175ce3b31cc0b7614ebe96a56be91cd376836` |

The evaluated HEAD is `ca06d579f67fac68c1ffcd1696f3d46ae40578f2`,
with a dirty worktree. No agent commit or push was performed.
All earlier maximal-prefix, fixed-sum and source-count evidence is preserved.

## Robert–Sargos small-alpha sixth moment — previous checkpoint

`sargosQuartic_small_sixth_moment` proves, for every natural N >= 1,

    integral_{alpha=0}^{1/sqrt(N)} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^6
      <= 44845498368 (1+log N)^5.

This is the literal unweighted sum and its actual attained prefix
maximum, not a bound for arbitrary bounded coefficients. Every
integration and interval comparison has a proved integrability argument.
There is no sixth-moment, counting or cancellation hypothesis.

The quartic second difference is computed exactly. Its fourth-degree
coefficient is at most 110 N^2 on the actual sample range. With
|gamma| <= N^-3 and alpha >= 128/N, this gives positive curvature
between alpha and 3 alpha before conversion to radians.
The existing local discrete second-derivative theorem is applied to
the exact prefix and gives |S| <= 64 N sqrt(alpha), for alpha <= 1.
The conversion from the additive character to radians is proved.

A two-window split suffices. On [0,128/N], the trivial |S|^2 <= N^2
multiplies the proved maximal fourth moment. On [128/N,1/sqrt(N)],
the curvature bound gives |S|^2 <= 4096 N^2/sqrt(N), and the fourth
moment is bounded on the larger [0,1/sqrt(N)] window. The exact scale
identity N*(1/sqrt(N))^2=1 removes N. This yields log^5 directly,
without the extra logarithm from counting dyadic windows.

`sargosQuartic_small_sixth_moment_log_six` gives the (1+log N)^6
version. `sargosQuartic_small_sixth_moment_source` proves the literal
logarithm convention for N >= 2, with absolute constant

    44845498368 (1+1/log 2)^6

multiplying (log N)^6. Thus the exact source small-alpha assertion
is a proved consumer, including the logarithmic normalization bridge
([Robert–Sargos, section 5, Lemma 3](https://arxiv.org/html/2307.03554v1#S5)).
The cutoff 128/N is deliberately verified; the printed 16/N does not
uniformly guarantee positive quartic curvature. Changing this internal
cutoff changes only the absolute constant, not the public source result.

Six production modules contain 22 public theorem boundaries, each with
an explicit audit and exact-signature regression. Nine additional
fixtures test the sign issue, exact quartic difference, verified cutoff,
empty intervals, N=0 definitions, a literal full prefix, and the N=1/2
moment and source-normalization specializations.

The full higher-moment/window comparison, global sixth-moment bootstrap,
quartic B/Legendre transfer and analytic C-process remain open.
EPZAE-10 stays unchecked; this is the section 5 input, not the full
sixth-moment theorem or C-process. All 42 aggregate checkbox states
remain unchanged.

The maximal fourth moment and parameter-dependent slow-phase upper
and ordinary integral theorems are preserved. The permanent printed
Lemma 62 counterexample and completed corrected powering ->
Heath--Brown energy -> exact optimization -> all nine repaired Add-est
clauses remain unchanged, as do A/B, EPZAE-09, EPZAE-12 and the first
two analytic beta rows.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell inventory,
root imports, explicit audits, semantic regressions and source
verifiers synchronized. Run it and the foundation
`run_lake_build.bat` after proof, integration, dependency or runner
changes. Preserve pinned bytes and the permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-230214-7730af3c.log); 777 production modules,
  1251 scanned Lean files, 10109 build jobs; 6516 target and 6240 pinned
  theorems plus five imported boundaries audited (12761 total).
  All 22 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_230522.log) and
  [manifest](../../logs/foundation_freeze_20260922_230522.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-sixth-20260922-230214-7730af3c.json) records
1272 physical source/configuration/tooling hashes, unchanged across
both runs, and ten normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, all earlier proof files are unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 299 nodes and 795 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Target log | `6101121bb44e0ccf007cc3f5b3d7c11ea4194c56fa331da15d716c1834c46c1c` |
| Foundation log | `a35796b60632115d1e71f77f182705cd90b415116f0058c1435e03b05c860262` |
| Foundation manifest | `dafa52b71c8d87d053a1d7f9c8e76f59040fed5f6610fbb152cbfd6b1cf1dd8e` |
| Source checkpoint JSON | `86f75cdaf29fbbe624aa8e0f73bd318f8cb4b2edf373423b4e2009bb38ca7644` |

The evaluated HEAD is `ca06d579f67fac68c1ffcd1696f3d46ae40578f2`,
with a dirty worktree. No agent commit or push was performed.
All earlier slow-phase, maximal-prefix and source-count evidence is preserved.

## Robert–Sargos full window comparison — previous checkpoint

The full higher-moment window comparison in Robert–Sargos Lemma 1 is now
kernel-checked for every natural N >= 2 and p >= 1. The public consumers are
`sargos_lemma_one_upper` and `sargos_lemma_one`; the latter derives
integrability from measurability and the proved majorant. No count,
cancellation estimate, window comparison, or moment bound is assumed.

Write B for the literal number of ordered pairs of p-tuples of integers
in (N,2N] satisfying the source quadratic and quartic tolerances
1/delta and 1/lambda. Let J be the unweighted fixed-sum 2p moment on
[-Delta/2,Delta/2] x [-mu/2,mu/2]. With derivative bound K/N on the actual
source interval and parameter rectangle, set

```text
C(p,K) = 16 [3 (1 + 2 pi K) (1 + 1/log 2)]^(2p).
U <= C(p,K) delta lambda (log N)^(2p) B,
B <= 64/(Delta mu) J,
0 < Delta <= delta, 0 < mu <= lambda.
```

Here U is the genuine upper integral of the actual slow-phase prefix
maximum; arbitrary, even nonmeasurable parameter dependence is allowed.
For an AEStronglyMeasurable integrand the ordinary iterated integral is
proved to agree, and the source-normalized inequality
U / [(log N)^(2p) delta lambda] <= C(p,K) B is exposed.
The result even permits delta > 1. The finite maximum includes the empty
prefix, whose norm is zero; the estimate therefore covers all source
nonempty prefixes as well. The coefficient family is fixed in the two
parameters and has norm at most one on the actual source interval.

The dependency chain is substantive:

- The p-th power is expanded exactly over `Fin p -> (N,2N]`.
- The physical tolerance identities retain both N^2 and N^4.
- The upper sinc-kernel window bound yields 16 delta lambda times the count.
- A dual tent Gram identity bounds that count by the central integral.
  Its compact support and weight at most one are proved, and every counted
  pair contributes at least Delta mu/64; all remaining weights are nonnegative.
- Finite weighted Jensen and actual Fourier completion work for every
  positive integer power. The common prefix kernel has mass at most
  3(1+log N); each completed mode has fixed unit-modulus-twisted coefficients.
- Actual Abel removal supplies the factor (1+2 pi K)^(2p), and a proved
  log-normalization inequality recovers the literal source log.

The 13 modules are `SargosWeightedPowers`, `SargosMomentTuples`,
`SargosMomentCount`, `SargosDualTentKernel`, `SargosDualTentGram`,
`SargosDualTentWindow`, `SargosMomentCentral`, `SargosPowerRegularity`,
`SargosPowerCompletion`, `SargosMaximalWindow`, `SargosSlowPowerWindow`,
`SargosLemmaOne`, and `SargosLemmaOneMeasurable`.
All 57 public theorems are explicitly audited. The 66 new regressions
comprise 57 exact signatures and nine additional fixtures, including
N=1 count scaling, delta > 1, sixth/tenth moments, both tent-support
directions, a smooth sine phase, and an arbitrary bounded linear-phase family.

Source: [Robert–Sargos, section 4, Lemma 1](https://arxiv.org/html/2307.03554v1#S4).
The explicit derivative loss uses the correct O(K) variation over an
interval of length N, not the printed O(1/N) variation sentence.

This closes the higher-moment window-comparison subbranch of EPZAE-10.
The global sixth-moment bootstrap, real dual-scale interval handling,
quartic B/Legendre and sextic slow-error calculation, and C-process are
still open. The previous small-alpha sixth moment remains available
with its verified log^5 estimate and exact source log^6 corollary.
No aggregate task is newly marked complete.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 790 production modules, 1264 scanned Lean files,
  10122 Lake jobs, 6607 target + 6240 pinned + 5 boundary declarations
  audited (12852 total). All 57 public declarations appear exactly once
  in the explicit audit and use only permitted logical axioms.
  [Full extension log](logs/tao-trudgian-yang-build-20260922-234413-dcbd04c1.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, with 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260922_234712.log) and
  [manifest](../../logs/foundation_freeze_20260922_234712.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. The production inventory, root imports, explicit audit and
  semantic regressions were updated together.
- All 1285 source/config/tooling files were byte-identical across the
  BAT pair; the 17 normalized source/integration hashes are recorded in
  the [checkpoint JSON](logs/tao-trudgian-yang-sargos-windows-20260922-234413-dcbd04c1.json).
  Of the previous 1272 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the 13 new modules were added.

The evaluated foundation HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`
with a dirty worktree. An owner Progress Update advanced the previous
HEAD during ongoing work; no agent commit or push was performed.
All 509 protected tracked files are unchanged against this HEAD.
The permanent counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 301 nodes and 801 edges, with no missing endpoints,
duplicates or unclassified nodes. All 42 aggregate checkbox states are
unchanged (22 checked). The repaired energy branch and all nine Add-est
clauses remain intact; the whole-proof goal is still open.

Physical SHA-256 evidence:

| Artifact | SHA-256 |
| --- | --- |
| Extension log | `7957c68549ea31a49c25767ce7ef6128d3fff9ccaa96d6cfafde9546b6b96cc6` |
| Foundation log | `6c0829c28cda7b9d1b0bcf25f8c926cd263ca6899e5b8423c098080df08fa1f3` |
| Foundation manifest | `8f83c38c08dcbe2297871b260c016ceaed65e6bbbcdadf12ff6aa15b5be603b9` |
| Window-comparison checkpoint JSON | `65fc2a68de7fafaff31270d641a2259a9d73a00c092cb0c243465561a6a5ed73` |

Earlier small-alpha, slow-phase, maximal-prefix and literal-count evidence
is preserved with its historical hashes and evaluated revisions.

## Robert–Sargos sixth-moment base and strip reduction — previous checkpoint

The actual base integral `sargosSixthBaseMoment N` is defined by the
unweighted fixed sum on alpha in [0,1] and gamma in [-N^-3,N^-3].
Its kernel-checked bounds are

```text
1/64 <= I(N) <= 2 N^3                     (natural N >= 1).
```

The lower bound is derived from the literal diagonal tuple injection:
there are N^p source p-tuples, and each pair (t,t) satisfies both
nonnegative tolerances. The dual-tent count-to-central integral theorem
is then consumed. Exact complex conjugation under
(alpha,gamma) -> (-alpha,-gamma), actual integral reflection and
rectangle inclusion relate the central integral to I(N). No positive
lower bound, diagonal count or base-moment estimate is a parameter.

The same sign/window bridge consumes the previously proved small-alpha
maximal estimate and yields the fixed-sum central sixth moment on
[-1/sqrt N,1/sqrt N] x [-N^-3,N^-3] bounded by

```text
89690996736 (1+log N)^5.
```

For N >= 2, the literal source log^6 corollary has absolute constant
89690996736 (1+1/log 2)^6.

The completed Lemma 1 now has a further actual consumer:
`sargosQuartic_maximal_sixth_strip_reduction` bounds the weighted prefix
maximum on any translated unit-width alpha strip and any positive
height width lambda by

```text
128 C(3,0) (1 + lambda N^3) (log N)^6 I(N).
```

The ordinary and upper-integral slow-phase consumers replace C(3,0)
by C(3,K), for the proved derivative bound K/N. C is the explicit
constant from the preceding full-window checkpoint. The upper-integral
version allows arbitrary nonmeasurable parameter dependence; the
ordinary version derives integrability from measurability. The width
choice min(lambda,2/N^3), its positivity, physical count monotonicity,
central window inclusion and factor 1+lambda N^3 are all proved.

The six new modules are `SargosDiagonalMoment`, `SargosSymmetricWindow`,
`SargosCentralSixthMoment`, `SargosSixthBaseMoment`,
`SargosSixthStripCount`, and `SargosSixthStripTransfer`. Their 24 public
theorems are explicitly audited. The 34 new regressions comprise all
24 exact signatures and ten additional fixtures, including empty-tuple
counting, N=1 bounds, a concrete translated strip, the scale boundary,
a smooth sine phase and arbitrary bounded nonmeasurable linear phases.

These are the actual initial beta=3 estimate, nonvanishing base bound
and height-strip reduction used around
[Robert–Sargos, section 7](https://arxiv.org/html/2307.03554v1#S7).
They do not establish I(N) << N^epsilon. The exponent-improving recurrence,
quartic B/Legendre expansion, real dual-scale interval conversion and
C-process remain open. No aggregate checklist status changes.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 796 production modules, 1270 scanned Lean files,
  10128 Lake jobs, and 6640 target + 6240 pinned + 5 boundary declarations
  audited (12885 total). All 24 public theorems appear exactly once in the
  explicit audit with only permitted logical axioms.
  [Extension log](logs/tao-trudgian-yang-build-20260923-001009-8680cd0c.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260923_001404.log) and
  [manifest](../../logs/foundation_freeze_20260923_001404.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. Root imports, runner inventory, audit and regressions are
  synchronized. All 1291 source/config/tooling files were byte-identical
  across the BAT pair; ten normalized source/integration hashes and all
  physical hashes appear in the [checkpoint JSON](logs/tao-trudgian-yang-sargos-base-20260923-001009-8680cd0c.json).
  Of the preceding 1285 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the six new modules were added.

HEAD remains `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78` with a dirty worktree.
No agent commit or push was performed. All 509 protected tracked files
remain unchanged against that HEAD. The permanent counterexample retains
SHA-256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 303 nodes and 805 edges, without duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The repaired energy branch and all nine Add-est clauses
remain intact; the whole-proof goal is still open.

Physical SHA-256 evidence:

| Artifact | SHA-256 |
| --- | --- |
| Extension log | `5432ddf4896b222a11d6964ee18061e48650f74c2189f339bf29a97e2934e09c` |
| Foundation log | `59ad6985c329e0f57997d3f454e833dee2d64070a9c7a408f947c010b2db72e9` |
| Foundation manifest | `348cbd05174b9d833673312d0f1a2c10014e67743fe9a53148653fa025f8a6a5` |
| Base/strip checkpoint JSON | `424206ca443dc49edc23391e3cbf3136af26e06ff6f5dd8ef2f734d673b68f9e` |

The preceding full-window, small-alpha and energy-repair evidence remains
preserved with its historical hashes and exact evaluated scope.

## Robert–Sargos actual quartic Legendre expansion — previous checkpoint

The actual source phase g(x)=alpha*x^2+gamma*x^4 now has a kernel-checked
inverse slope on [N,2N]. Under N>0, alpha>0 and
|gamma| <= alpha/(96*N^2), its curvature lies between 3*alpha/2 and
5*alpha/2. The chosen inverse is proved to invert the real polynomial;
it is smooth on the open slope image. The signed phase
g*(y)=g(w(y))-y*w(y) has derivative -w(y).

For this actual phase, the residual v is defined by the exact identity

```text
g*(y) = -y^2/(4*alpha) + gamma*y^4/(16*alpha^4)
        - gamma^2*y^6/(16*alpha^7) + v(y).
|v(y)|  <= 10240*|gamma|^3*N^8/alpha^2.
|v'(y)| <= 16384*|gamma|^3*N^7/alpha^3.
```

Both bounds are proved by exact rational polynomial identities, not
assumed asymptotic expansions. With x=w(y), u=2*gamma*x^2/alpha,
the residual polynomials have absolute bounds 5 and 16 for |u|<=1/12.
The derivative is that of the same residual used in the phase identity.

For N>=9216, alpha>=1/sqrt(N), and |gamma|<=N^-3, the scale
hypotheses are derived, giving |v|<=10240 and |v'|<=16384/(alpha*N).
The actual slope image equals the open interval between the endpoint
slopes and is convex. Consequently the residual has the corresponding
Lipschitz bound on that image. For alpha in [Delta,2*Delta], the image
is contained in (2*Delta*N-4,8*Delta*N+32).

This is the quartic specialization of
[Robert–Sargos (6.7), with the large-scale threshold and dual interval in section 7](https://arxiv.org/html/2307.03554v1#S6).
It does not prove the generic perturbation Lemma 4 or the oscillatory
B-transform. The source display (6.2) omits a square root in the
stationary amplitude; (7.5) has the required inverse square root.
The remaining transform must use that correct amplitude, with a
proved full error bound. This discrepancy does not change any frozen
Tao–Trudgian–Yang public output.

The seven modules are `SargosQuarticPhase`, `SargosQuarticInverse`,
`SargosQuarticLegendreAlgebra`, `SargosQuarticLegendreRemainder`,
`SargosQuarticLegendreBounds`, `SargosQuarticLegendreScale`,
and `SargosQuarticDualRange`. Their 44 public theorems are explicitly
audited. The 59 regressions comprise all exact signatures and 15 fixtures,
including both signs of a nonzero quartic coefficient, the Legendre
sign, inverse endpoints, the exact quadratic residual, both polynomial
boundaries, N=9216, and a physical dyadic dual interval.

Still open: the actual oscillatory B-transform, curvature-amplitude
and residual removal from its integer sum, real dual-scale/integer-block
conversion, the parameter Jacobian and covering, the bounded N range,
the exponent-improving sixth-moment recurrence, and the C-process.
The previous base-moment and all-height strip bounds remain available.
No aggregate checklist status changes; the permanent printed-Lemma-62
counterexample, corrected powering, and all nine Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 803 production files, 1,277 scanned Lean
  files and 10,135 build jobs. The audit covers 6,731 target theorems,
  6,240 pinned-source theorems and five boundary anchors (12,976 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-004528-1a1e7f39.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_004918.log)
  and [manifest](../../logs/foundation_freeze_20260923_004918.json).
- All 1,298 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-legendre-20260923-004528-1a1e7f39.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 305 nodes and 809 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `e032bde008f3cc51156c2b742d8364ffbfef87a3c0757e980581deec276ac811` |
| Foundation log | `e2ca5018900253303648eb6d37092fd8925abdabc6731fab0227b82c25a23d2f` |
| Foundation manifest | `a3ec905f300f3eb1af8b042fba0bbe759127cfd6dce90749011a71a771f4bcaf` |
| Legendre checkpoint JSON | `f60cd00b85113fde5005428c6b0f6fbc9d4f0eb755cb3d4e3db8781c955ef645` |

All preceding base/strip, full-window, small-alpha and energy-repair evidence
is preserved with its historical hashes and exact scope.

## Robert–Sargos quartic stationary coordinate and Poisson entry — previous checkpoint

The normalized quartic phase F(u)=u^2+epsilon*u^4 now has an explicit
positive quadratic coordinate about the actual stationary point:

```text
L(epsilon,r,u) = 1 + epsilon*(u^2 + 2*u*r + 3*r^2),
z(epsilon,r,u) = (u-r)*sqrt(2*L(epsilon,r,u)).
F(u)-F(r)-F'(r)*(u-r) = z(epsilon,r,u)^2/2.
```

For |epsilon|<=1/96 and r,u in [0,3], the proved coefficient bounds are
7/16<=L<=25/16. The exact coordinate derivative is

```text
(2+4*epsilon*(u^2+u*r+r^2))/sqrt(2*L),
```

and lies in [7/16,25/4]. The coordinate is smooth wherever L>0 and
strictly increasing on the closed extended interval. Its actual chosen
inverse is proved smooth on the open image, with derivative in
[4/25,16/7]. The inverse maps zero to r, and its derivative there is
1/sqrt(2+12*epsilon*r^2).

The physical consumer uses epsilon=gamma*N^2/alpha, T=alpha*N^2,
and r=w(y)/N, where w is the already proved inverse quartic slope.
All range and coefficient hypotheses are derived from the source
curvature assumptions. It proves the exact original-variable identity

```text
g(x)-y*x = g*(y) + (T/2)*z(epsilon,r,x/N)^2.
```

The physical stationary Jacobian is also proved exactly:
(N/sqrt(T))*(inverse-coordinate)'(0)=1/sqrt(g''(w(y))).
Thus the required square-root curvature amplitude is derived from
the actual coordinate, not supplied as an input.

A separate actual-source entry constructs a smooth compact cutoff
chi with 0<=chi<=1 from the literal source lattice. For every natural
N>=1, one cutoff works for all real alpha,gamma. The theorem
`sargosQuartic_source_poisson` proves absolute summability of the
original Fourier integrals

```text
Integral chi(x/N)*e(alpha*x^2+gamma*x^4-m*x) dx
```

over all integer m, and bounds the difference between their full
Poisson series and the unweighted source sum on (N,2N] by 2.
The endpoint count, cutoff values, real/complex character convention,
Schwartz decay and Poisson equality are all derived. No
approximate-model-phase or oscillatory-transform hypothesis is used.

The four modules are `SargosQuarticMorse`,
`SargosQuarticMorseInverse`, `SargosQuarticMorsePhysical`, and
`SargosQuarticPoisson`. Their 40 public theorems are explicitly audited.
The 52 regressions comprise every exact signature and 12 fixtures,
covering both signs at the coefficient bounds, the actual inverse
and critical derivative, physical scaling/amplitude, and N=1 source
and endpoint behavior.

This supplies the actual-coordinate and Poisson-entry obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
It does not yet estimate the individual Fourier modes or prove the
B-transform. The exact lattice cutoff carries no claimed uniform derivative
budget; the quantitative step must choose controlled cutoffs and pay their
source-endpoint loss. Remaining: uniform higher inverse/weight derivatives,
actual integral substitution and cutoff transport, complete
stationary/nonstationary mode errors and lattice summation, the
curvature-amplitude/residual Abel steps, dual block conversion,
parameter Jacobian/covering, bounded N range, the sixth-moment
recurrence, and the C-process. No aggregate checklist status changes.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 807 production files, 1,281 scanned Lean
  files and 10,139 build jobs. The audit covers 6,818 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,063 total).
  All 40 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-011542-75b94f86.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_011847.log)
  and [manifest](../../logs/foundation_freeze_20260923_011847.json).
- All 1,302 physical proof/configuration/tooling hashes are identical
  before and after both runners. The four modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-20260923-011542-75b94f86.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 307 nodes and 816 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `174eea798affb9fd79577d11ee288a471cdbbd4843906dae1112b025d97d8072` |
| Foundation log | `061f078b91bc6bdb81bea84962916b0863ead16a808cc9a63abed3f43812bd2d` |
| Foundation manifest | `f2765b3bdf835cc637c40095e75f65cc306be5fdb6308423ab811409f2b50e18` |
| Stationary/Poisson checkpoint JSON | `ecb3f4a4e60b95a68f0713ab84b529cb4a0c5002a43b23dad100fadbfac94e02` |

All preceding Legendre, base/strip, full-window and energy-repair evidence
is preserved with its historical hashes and exact scope.

## Robert–Sargos uniform quartic jets and cutoff transport — previous checkpoint

The actual positive quadratic coordinate and its inverse now have
all-order derivative bounds uniform in |epsilon|<=1/96 and r in [0,3].
The coordinate bounds hold on u in (0,3); inverse bounds hold on the
actual moving open image. Constants depend only on the derivative
order, not on epsilon, r or the individual phase.

The polynomial A=2*(1+epsilon*(u^2+2*u*r+3*r^2)) has exact derivatives
A'=4*epsilon*(u+r), A''=4*epsilon and A^(j)=0 for j>=3.
Every atom in the coordinate's proved finite derivative expression
has absolute value at most 3. Explicit finite expression magnitudes
give the coordinate bounds; explicit finite sums of those bounds give
the inverse bounds. The formulas are proved against the actual
coordinate/inverse, not a model-phase surrogate.

The positive inverse Jacobian now transports both the complex
Bochner integral and integrability between (0,3) and the actual
coordinate image. The transported source cutoff is exactly

```text
W(z) = chi(inverse(z))*inverse'(z) on the actual open image,
W(z) = 0 outside that image.
W(0) = chi(r)/sqrt(2+12*epsilon*r^2).
```

For smooth chi with closed support contained in (0,3), W is globally
smooth and compactly supported, including across the moving image
boundary. Its closed support lies in the actual coordinate image of
the closed support of chi, and uniformly in [-6,6]. Every derivative
is integrable and supported in that same compact image. The whole-line
identity holds for arbitrary complex g:

```text
Integral chi(u)*g(u) du = Integral W(z)*g(inverse(z)) dz.
```

Global all-order weight estimates retain an explicit finite cutoff
jet budget M. Their constants depend only on M and the output order,
not on the phase parameters. No derivative budget uniform in a
varying cutoff family is inferred from compactness.

Eleven modules are installed: `SargosQuarticMorseCurvature`,
`SargosQuarticMorseJets`, `SargosQuarticMorseJetBounds`,
`SargosQuarticMorseInverseJets`, `SargosQuarticMorseInverseJetBounds`,
`SargosQuarticMorseChangeVariables`, `SargosQuarticMorseAmplitude`,
`SargosQuarticMorseSupport`, `SargosQuarticMorseGlobalIntegral`,
`SargosQuarticMorseWeightJets`, and `SargosQuarticMorseWeightBounds`.
All 50 public theorems have exact-signature regressions and explicit
axiom audits; 12 additional fixtures cover signed boundary coefficients,
high-order vanishing, arbitrary derivative orders, cutoff retention,
moving-image exterior behavior and global cutoff budgets.

These results discharge further actual-coordinate analytic obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
They do not yet prove a Fourier-mode remainder or the B-transform.
Remaining are the physical positive-quadratic Fourier identity and
Fresnel remainder, controlled cutoff family and source loss, complete
stationary/nonstationary mode errors and lattice sums, curvature and
Legendre-residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 818 production files, 1,292 scanned Lean
  files and 10,150 build jobs. The audit covers 6,891 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,136 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-014238-0efee296.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_014551.log)
  and [manifest](../../logs/foundation_freeze_20260923_014551.json).
- All 1,313 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-jets-20260923-014238-0efee296.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 309 nodes and 822 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `076680bd2b48f6bdec8571d669a230e4b2a96bb180043c2fcf82f64e6e4c8725` |
| Foundation log | `9a709b3169a006f05fb23efea3441df1aae2f775295db22a34b831e2979a593d` |
| Foundation manifest | `fe336155701de8908f666094ceaeb3aa9fbdfef3f33f94d821167aeca9d3a9ec` |
| Uniform-jets/cutoff checkpoint JSON | `f878fcffce69e7ca29b5eefbbb14ce2ffe572ce89b40b73a6ecfa1b945cd84ee` |

All preceding stationary/Poisson, Legendre, base/strip, full-window
and energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos physical stationary estimates and controlled source entry — previous checkpoint

The actual physical quartic Fourier integral is now proved equal to
its positive-quadratic representation. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open quartic slope image,
put epsilon=gamma*N^2/alpha, T=alpha*N^2 and r=w(y)/N. Then

```text
Integral chi(x/N)*e(g(x)-y*x) dx
  = N*e(g*(y))*Integral W(z)*e((T/2)*z^2) dz,
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

The original cutoff has closed support in (1,2), and W is its actual
smooth transported weight from the preceding checkpoint. The physical
factor N, actual stationary point, signed Legendre phase, positive
Fresnel sign and square-root curvature amplitude are all proved.
The leading coefficient is chi(r)*main(y); the cutoff is not dropped.

Exact complex conjugation transfers the already proved negative
quadratic Fresnel remainder to positive curvature. With the finite
original-cutoff derivative budget M visible, the theorem
`sargosQuarticFourierMode_stationary_bound` bounds the difference
from chi(r)*main(y) by C(M)/(alpha*N). Its constants do not depend
on N, alpha, gamma or y.

A separate varying-cutoff theorem chooses constants before both
endpoints, the width eta, and the quartic parameters. Its actual
transformed nth derivative costs at most C_n*eta^(-n), for 0<eta<=1.
This yields

```text
|physical mode - chi(r)*main(y)| <= C*eta^(-3)/(alpha*N).
```

The exponent -3 is explicitly retained. This estimate alone is not
the sharp summed B-transform error; a local plateau argument and
complete mode/lattice analysis are still required.

The source-facing controlled cutoff is now constructed explicitly:
chi(u)=bufferedCutoff((N+1)/N,2,eta)(u), for natural N>=1 and eta>0.
`sargosQuartic_buffered_poisson` proves absolute summability of the
original physical Fourier modes and

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4) - Sum_(m in Z) mode(m)|
  <= 4*N*eta+2.
```

Its endpoint count, literal source interval, source phase and
normalizations are derived. No model-phase approximation, Poisson
error certificate, or stationary-phase estimate is an input.

Seven modules are installed: `SargosQuarticMorseFourier`,
`SargosPositiveQuadraticRemainder`, `SargosQuarticMorseRemainder`,
`SargosQuarticStationaryEstimate`, `SargosQuarticBufferedJets`,
`SargosQuarticBufferedStationary`, and `SargosQuarticBufferedPoisson`.
All 17 public theorems have exact-signature regressions and explicit
axiom audits. Twelve additional fixtures test the Fresnel sign,
physical normalization and amplitude, arbitrary derivative order,
explicit width powers, and N=1,2 source support/endpoint behavior.

These are supporting steps toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
The sharp interior, near-edge, exterior and infinite-tail estimates,
their integer sums, curvature/residual Abel steps, integer dual-block
conversion, parameter Jacobian/covering, bounded N, sixth-moment
recurrence and C-process remain open. No aggregate checklist status
changes. The permanent counterexample, corrected powering and all
nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 825 production files, 1,299 scanned Lean
  files and 10,157 build jobs. The audit covers 6,930 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,175 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-020618-a3f2de7d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_020944.log)
  and [manifest](../../logs/foundation_freeze_20260923_020944.json).
- All 1,320 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-stationary-20260923-020618-a3f2de7d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 312 nodes and 833 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `790cd768231877890d12f572beca57c07148ba8f187d89532177921d619a60d9` |
| Foundation log | `248c4ed49f71e1232e627929c48cb431949f9692f7eedb1bdaec824d3bdafada` |
| Foundation manifest | `a6b08c43c938c6fde0aa138680380fe00d83ec0f925bc1a5f08538e05a853bc9` |
| Physical-stationary/buffered checkpoint JSON | `900c12923666d597929a6b8306a196c59cb49d3065c5bff50ee3f675eb41ff32` |

All preceding uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip
and energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos sharp quartic interior stationary error — previous checkpoint

The actual positive-curvature quartic Fourier mode now has a sharp
interior error with no inverse cutoff-width loss. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open slope image, write
r=w(y)/N for its actual normalized stationary point. For the controlled
cutoff chi=bufferedCutoff(l,b,eta), assume 1<=l, b<=2, eta>0, d>0,
l+2*eta+d<=r and r+d<=b-2*eta. Then

```text
|mode(y) - e(g*(y)+1/8)/sqrt(g''(w(y)))| <= C/(alpha*N*d).
```

The constant is chosen before l, b, eta, d and all physical parameters.
The cutoff coefficient is one because the actual stationary point
lies inside its proved plateau; it is not discarded by assumption.
The source mode, inverse, signed Legendre phase, positive Fresnel sign,
physical N factor and square-root amplitude are the original objects.

The proof derives an actual quadratic-coordinate window |z|<=H.
Uniform coordinate distances and slope gaps locate its inverse images.
On that window the transported cutoff's derivatives are actual inverse
derivatives, so their constants do not grow as eta tends to zero.
The local positive-quadratic remainder is bounded by C_local/(T*H).

An exact positive-Jacobian change of variables identifies the central
original-integral piece. The two omitted original-integral tails
are bounded together by 128/(7*pi*T*H), using actual slope gaps and
the proved width-independent cutoff variation. Choosing H=d/4 and
T=alpha*N^2 gives the displayed physical estimate. All hypotheses
for the window, tails, plateau and normalization are derived.

Nine modules are installed: `SargosQuarticMorseGeometry`,
`SargosQuarticMorseWindow`, `SargosPositiveQuadraticLocal`,
`SargosQuarticLocalRemainder`, `SargosQuarticCenteredPhase`,
`SargosQuarticWindowIntegral`, `SargosQuarticLocalNonstationary`,
`SargosQuarticWindowTails`, and `SargosQuarticInteriorStationary`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Twelve further fixtures check both perturbation endpoints,
the quadratic specialization and derivative, actual inverse windows,
genuine integrability, positive central transport, varying widths,
and the quarter-distance physical bound.

This completes the sharp interior component, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Near-edge, exterior and infinite-tail bounds and their integer sums
remain open, followed by curvature/residual Abel steps, integer dual
blocks, parameter Jacobian/covering, bounded N, the sixth-moment
recurrence and C-process. Aggregate checklist states do not change.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 834 production files, 1,308 scanned Lean
  files and 10,166 build jobs. The audit covers 6,960 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,205 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-023612-86705e16.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_023922.log)
  and [manifest](../../logs/foundation_freeze_20260923_023922.json).
- All 1,329 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-interior-20260923-023612-86705e16.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 314 nodes and 840 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `5ccfa2ac23b92989f7397b5efbcff12ea618bd2f249e2a7230b85be2d14b0ffa` |
| Foundation log | `bf907c43a5d791e735127993de349f34945fde616f4ec2f3cbff46034610d72a` |
| Foundation manifest | `bfa693fee02134c65a7c3199a111f1f9df0a0d80f4d393e7aeef42c85500f37d` |
| Sharp-interior checkpoint JSON | `0e7cd6385ff9b2989647462588b1f89b84eea6b84e559777a119072e55163939` |

All preceding physical-stationary/buffered, uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip
and energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos sharp quartic support-frequency core — previous checkpoint

The original quartic Fourier modes now have uniform estimates at
every real frequency, including frequencies without a stationary
point and those at moving support endpoints. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and the actual controlled cutoff
chi=bufferedCutoff(l,b,eta), with 1<=l, b<=2 and eta>0,

```text
|mode(y)| <= 4*(2/pi+2)/sqrt(alpha).
```

This follows from the actual quartic curvature and the proved cutoff
variation, by exact complex conjugation of the negative-curvature
integral theorem. No model-phase approximation is assumed. The actual
stationary main term has norm at most 1/sqrt(alpha).

Outside the support's actual slope interval, the original physical
mode has a reciprocal-gap bound 4/(pi*gap), where gap is the distance
from y to g'(N*(l+eta)) or g'(N*(b-eta)). The physical normalization
and the cutoff-empty case are proved. These are pointwise exterior
bounds; their integer sums are not yet included.

For the interior, the actual quartic curvature upper bound converts
frequency gaps to distances of the real inverse stationary point.
The preceding C/(alpha*N*d) estimate therefore becomes C'/gap.
Summing the two reciprocal edge distances gives a logarithmic error
over the literal integer interval; no stationary-image or per-mode
estimate is left as an input.

Support endpoints are rounded outwards, plateau endpoints inwards:

```text
L = floor g'(N*(l+eta)),     U = ceil g'(N*(b-eta)),
A = ceil  g'(N*(l+2*eta)),   B = floor g'(N*(b-2*eta)).
```

If l+4*eta<b, the transition complement Icc(L,U) minus Ioo(A,B)
has at most 5*alpha*N*eta+6 elements. Exactly resonant and nearest
endpoint frequencies are included. The public consumer
`sargosQuarticBufferedSupportCore_error` proves

```text
|Sum_(L<=y<=U) mode(y) - Sum_(A<y<B) main(y)|
 <= C*(1+log((B-A-1).toNat)) + (5*alpha*N*eta+6)*D/sqrt(alpha),
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

C>=1 and D>0 are chosen before all cutoff and physical parameters.
The source Fourier modes and actual signed stationary main terms are
used throughout. Empty integer interior blocks are handled explicitly.

Six modules are installed: `SargosQuarticFourierCurvature`,
`SargosQuarticExteriorModes`, `SargosQuarticInteriorFrequency`,
`SargosQuarticInteriorSum`, `SargosQuarticTransitionBands`, and
`SargosQuarticSharpCore`. All 18 public theorems have exact-signature
regressions and explicit axiom audits. Twelve further fixtures cover
all-frequency quadratic and extreme perturbation bounds, empty
cutoffs, physical stationary amplitude, both exterior gaps, exact
rounding at N=8, and the actual eleven-frequency interior block.

This is the sharp finite support-frequency core, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Exterior integer sums, quantitative infinite-tail bounds and full
source assembly remain open, followed by curvature/residual Abel
steps, integer dual blocks, parameter Jacobian/covering, bounded N,
the sixth-moment recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 840 production files, 1,314 scanned Lean
  files and 10,172 build jobs. The audit covers 7,000 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,245 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-025806-560f1b5d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_030120.log)
  and [manifest](../../logs/foundation_freeze_20260923_030120.json).
- All 1,335 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-support-core-20260923-025806-560f1b5d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 317 nodes and 849 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `394f38dd645e86e8d7518cf81ae4920b10152a162d2482f489226b0a72140635` |
| Foundation log | `3e206fc82a3a82dc258534cbf833e7d549367c7bacb8acb24aa2fd84354df3e4` |
| Foundation manifest | `b70cb7786512e340bbd9677270fe487c71b781d1476c5ac24e4c712661f9d6b0` |
| Sharp-support-core checkpoint JSON | `5c875605e813fa57803c2432d831fc427cf7747001bcfba8e196727881f89df7` |

All preceding physical-stationary/buffered, uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip
and energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos complete explicit-parameter quartic source expansion — previous checkpoint

The literal quartic source sum is now connected to its actual signed
stationary main terms through every Fourier-mode class. Exterior
integer sums, quantitative two-sided infinite tails and source
assembly are proved. The cutoff width, truncation radius and
logarithmic lengths remain explicit; the final stationary-scale
error simplification is not yet claimed.

The original normalized quartic kernel has uniform second-derivative
bound C*eta^(-2)*(1+|T|)^2. Its actual phase has first two derivative
bounds proved from |epsilon|<=1/96 on [1,2]. Exact normalization links
T=alpha*N^2, epsilon=gamma*N^2/alpha and Fourier frequency y*N to the
original physical mode. Consequently,

```text
|mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*y^2), y != 0,
|Sum_(|y|>R) mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*R).
```

The omitted series is the actual two-sided integer tail. Both signs,
absolute convergence, zero-frequency exclusion and the physical N
factor are proved. A separate source consumer chooses an explicit
positive radius achieving any requested tail tolerance.

The left and right support-exterior blocks each have norm sums bounded
by (4/pi)*harmonic(length); both together have logarithmic loss.
They are exactly reindexed, with no omitted or duplicated nearest
exterior integer. Combining them with the preceding sharp support
core gives the complete finite Fourier-window expansion.

For the literal source Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4), take
natural N>=1, alpha>0, |gamma|<=alpha/(96*N^2), 0<eta<=1,
l=(N+1)/N, and l+4*eta<2. Let L,U be the outward-rounded support
slopes and A,B the inward-rounded plateau slopes. Then
`sargosQuartic_source_stationary_expansion` proves

```text
|source - Sum_(A<y<B) e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= 4*N*eta+2
  + C*eta^(-2)*(1+alpha*N^2)^2/(N*R)
  + D*(1+log((B-A-1).toNat))
  + (5*alpha*N*eta+6)*E/sqrt(alpha)
  + (4/pi)*(2+log((L+R).toNat)+log((R-U).toNat)).
```

Here R is a positive natural number whose symmetric interval contains
[L,U], and C>=1, D>=1, E>0 are chosen before all source parameters.
The precision consumer constructs
R=ceil(C*eta^(-2)*(1+alpha*N^2)^2/(N*tolerance))+|L|+|U|+1,
proves the required interval containment, and replaces the actual
tail term by tolerance. No Poisson, stationary or tail estimate is
left as an assumption.

Six modules are installed: `SargosQuarticExteriorSum`,
`SargosQuarticKernelJets`, `SargosQuarticFourierDecay`,
`SargosQuarticFourierTail`, `SargosQuarticFourierWindow`, and
`SargosQuarticSourceExpansion`. All 17 public theorems have exact
signature regressions and explicit axiom audits. Twelve further
fixtures check extreme perturbations, the actual kernel and carrier,
physical decay/tail constants, a concrete truncation tolerance,
empty exterior blocks, rounded finite windows, and the literal N=8
source's nine-frequency stationary block.

This assembles the explicit-parameter source chain toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the linked stationary-scale cutoff choice, polynomial
radius/logarithmic budgets and the final uniform B-transform error;
then curvature/residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 846 production files, 1,320 scanned Lean
  files and 10,178 build jobs. The audit covers 7,026 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,271 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-032157-6b77f0c9.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_032511.log)
  and [manifest](../../logs/foundation_freeze_20260923_032511.json).
- All 1,341 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-expansion-20260923-032157-6b77f0c9.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 320 nodes and 860 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `e8c13a1f045f5f16ce732ee7060aee804550058305d2015ca7c2ea172852a7df` |
| Foundation log | `65e5034c6039a895965536fb4ef3f34273a7538f39f694e3d0f19e0cab235c2e` |
| Foundation manifest | `d455ad1c58361553b5a9e94a3fa06fa91469824398bb57915aab7cb17497ad61` |
| Explicit-source-expansion checkpoint JSON | `31b66ca5d02305d930456d4a6361c01c1f8c0ebb44c9c1955377377c3629889b` |

All preceding physical-stationary/buffered, uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip
and energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos large-source quartic B-transform — previous checkpoint

The literal quartic source now has a uniform B-transform into its full
closed stationary integer range. The actual cutoff choice, every
frequency logarithm, both infinite tails and the omitted endpoint
terms are consumed by one public theorem. This closes the large-source
oscillatory-transform step, not the sixth-moment recurrence.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_B_transform` proves, with one constant M>=1
chosen before N, alpha and gamma,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)
 - Sum_(g'(N)<=y<=g'(2N), y integer)
     e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= M*(1/sqrt(alpha)+1+log(2+alpha*N)).
```

Here g(x)=alpha*x^2+gamma*x^4, w is its actual inverse slope on
[N,2N], and g*(y)=g(w(y))-y*w(y). Both integer endpoint resonances
are included with full weight; their possible boundary contributions
are covered by the proved error. The positive square-root amplitude
is retained, consistently with (7.5). The earlier documented
missing square root in displayed (6.2) is not imported as an identity.

The stationary cutoff is eta=1/sqrt(alpha*N^2)=1/(N*sqrt(alpha)).
Its positivity, eta<=1 and nonempty source plateau are derived from
the original source range. Smoothing contributes 4/sqrt(alpha);
the transition term simplifies with no surviving inverse-width loss.
Every actual rounded slope has absolute integer size at most
6*alpha*N^2+1. The prescribed positive radius is at most
(C+16)*(alpha*N^2+1)^3; all three logarithmic lengths are bounded
using (C+24)*(alpha*N^2+1)^3, including zero-length cases.

The intermediate uniform consumer retains the actual buffered main
range. A separate closed-range bridge proves inverse-slope and
amplitude bounds at the endpoints, plateau containment, and the
count of omitted terms:
```text
omitted cardinality <= 5*alpha/2+10*alpha*N*eta+4.
```
At the stationary width and alpha<=1 their total norm is at most
17*(1/sqrt(alpha)+1). The final consumer restores the full closed
stationary sum and derives its logarithmic error from linked source
scales; no cutoff, stationary estimate or endpoint certificate is
assumed.

Nine modules are installed: `SargosQuarticStationaryWidth`,
`SargosQuarticRoundedBounds`, `SargosQuarticRadiusBudget`,
`SargosQuarticLogBudget`, `SargosQuarticUniformSource`,
`SargosQuarticClosedRange`, `SargosQuarticEndpointBands`,
`SargosQuarticEndpointError`, and `SargosQuarticBTransform`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen further fixtures check the stationary width,
degenerate inverse-square identity, threshold plateau, smoothing,
transition algebra, prescribed radius, full closed range, both
resonant endpoints, exterior exclusion, boundary amplitude, omitted
cardinality and the assembled source estimate.

This realizes the large-integer-source B-transform needed toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the power-scale error corollary, actual curvature and
residual Abel steps, integer dual blocks and real-scale conventions,
parameter Jacobian/covering, bounded N, the sixth-moment recurrence
and C-process. It does not assert the general C4 version of (6.2).
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 855 production files, 1,329 scanned Lean
  files and 10,187 build jobs. The audit covers 7,076 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,321 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-035345-754b20b2.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_035655.log)
  and [manifest](../../logs/foundation_freeze_20260923_035655.json).
- All 1,350 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-b-transform-20260923-035345-754b20b2.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 322 nodes and 866 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `2de4ca24a00694752a81f7b7b32826d492f77027880c21b36eacafaea574cf65` |
| Foundation log | `ab90cf56a061e656af743430a1a3f09f49610357bbd619a034b10b9cddaaa7c8` |
| Foundation manifest | `7b2a590fd2015e5a5582ab9e61c85250ece8130b8da0bf1187aed624d576f64b` |
| Large-source B-transform checkpoint JSON | `eb3a3933c7a841876b34b605efde5086ed6c977ee94ac700bf5786fa99e5e11f` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos source power error and both Abel steps — previous checkpoint

The literal quartic source is now bounded by the actual degree-six
polynomial prefix maximum. The quarter-power error and both Abel
steps are proved, including the full closed stationary range and
its resonant endpoints. Neither amplitude variation nor residual
variation is an assumed analytic input.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_le_polynomialPrefixMaximum` proves

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(alpha^(-1/2)*Pmax(N,alpha,gamma)+N^(1/4)).
```

The single constant C>=1 is chosen before N, alpha and gamma.
Pmax is the attained maximum over every prefix, including the empty
prefix, of the actual integer interval
[ceil(g'(N)), floor(g'(2N))], with phase

```text
p(y) = -y^2/(4*alpha)+gamma*y^4/(16*alpha^4)
       -gamma^2*y^6/(16*alpha^7).
```

The prefix definition uses the exact integer interval length and
works also for an empty interval. It is not a separately supplied
exponential-sum majorant. The source consumer links every parameter
to the original phase g(x)=alpha*x^2+gamma*x^4.

The preceding full B-transform now has error at most C*N^(1/4).
The proof derives alpha^(-1/2)<=N^(1/4) and
log(N+1)<=1+4*N^(1/4), then consumes the actual logarithmic error.

The actual amplitude 1/sqrt(g''(w(y))) is positive, bounded by
alpha^(-1/2), and monotone or antitone according to the sign of
gamma on the closed slope range. Its sampled finite variation is
at most alpha^(-1/2). Exact integer reindexing and Abel summation
bound the full stationary sum by twice this scale times the genuine
unweighted Legendre-prefix maximum. The unit phase e(1/8) is removed
by an exact identity and norm equality.

The literal Legendre residual v(y)=g*(y)-p(y) uses the existing
source derivative bound 16384/(alpha*N). Its character has interior
Lipschitz constant 32768*pi/(alpha*N), while the actual slope interval
has length at most 5*alpha*N/2. Interior sampled variation is therefore
at most 81920*pi. On the full closed range, the first and last possible
boundary jumps each cost at most 2 by unit modulus. This yields the
uniform finite-variation budget 5+81920*pi, without extending the
derivative theorem to an unproved endpoint domain. The residual Abel
consumer retains every endpoint and supplies the polynomial maximum
used by the final source theorem.

Eight modules are installed: `SargosQuarticPowerError`,
`SargosQuarticAmplitude`, `SargosQuarticAmplitudeVariation`,
`SargosIntegerPrefix`, `SargosQuarticAmplitudeAbel`,
`SargosQuarticResidualVariation`, `SargosQuarticResidualBoundary`,
and `SargosQuarticResidualAbel`. All 29 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures cover quarter powers, threshold source errors,
constant curvature, both monotonicity signs, inverse endpoints,
sampled amplitude variation, negative and empty integer prefixes,
the literal dual polynomial, closed residual boundary variation,
and the final source-to-polynomial bound.

This completes the power-scale and actual-weight/residual steps toward
[Robert–Sargos (7.5)–(7.8)](https://arxiv.org/html/2307.03554v1#S7).
Still open: dyadic integer block conversion and real-scale conventions,
the sign-conjugation bridge to the source parameter change, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No integral transfer or recurrence is claimed here. No aggregate
checklist status changes. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 863 production files, 1,337 scanned Lean
  files and 10,195 build jobs. The audit covers 7,128 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,373 total).
  All 29 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-042459-0f7675ca.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_042813.log)
  and [manifest](../../logs/foundation_freeze_20260923_042813.json).
- All 1,358 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-abel-20260923-042459-0f7675ca.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 324 nodes and 872 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `6aa1864d22a37ff16fe7f6d22714b34691557674e84b1ec6f7ea16b94417a4bf` |
| Foundation log | `c3ec5daf2641d715edfb14509107495b8eae61d43931eee9ee9b11859306a2d4` |
| Foundation manifest | `8941c0a14ad2ad3874cb3cdcccf1ee2b10135e87029ef2b12a09dbe9f77aae59` |
| Source power-error and Abel checkpoint JSON | `4988e3420c5a05efb23f2c900d9e3812f2e20d958414198ce828ba7f2fdfaa17` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos rounded dyadic blocks and exact conjugation — previous checkpoint

The actual closed stationary-prefix interval now reduces to two integer
dyadic blocks. Exact conjugation converts their phases to positive
quadratic phases while retaining the sextic correction.

For natural N>=9216, N^(-1/2)<=Delta<=1/2,
alpha in [Delta,2*Delta] and |gamma|<=N^(-3), let
m=floor(2*Delta*N). The source-facing theorem
`sargosQuartic_source_le_two_slow_blocks` proves, with one C>=1
chosen before every source parameter,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(Delta^(-1/2)*(Smax(m)+Smax(2*m))+N^(1/4)),
Smax(h) = max_(0<=L<=h)
 |Sum_(h<n<=h+L) e(x*n^2+y*n^4+phi(n))|,
x=1/(4*alpha), y=-gamma/(16*alpha^4),
phi(t)=gamma^2*t^6/(16*alpha^7).
```

These are the actual slow quartic maxima, not assumed majorants.
The scale is linked to the source: m>=192 and
Delta*N<=m<=2*Delta*N<m+1. The integer stationary endpoints satisfy
ceil(g'(N))>=m-4 and floor(g'(2N))<=4*m+35.
At most 40 unit-modulus terms lie outside (m,4*m].
Each retained interval is the difference of two prefixes in
(m,2*m] or (2*m,4*m]. This yields the two genuine maxima
and a bounded loss absorbed in the existing quarter-power error.

The polynomial sign reversal, character conjugation, prefix conjugation
and maximum equality are exact. In particular, the correction
gamma^2*t^6/(16*alpha^7) is retained. The natural scale m is not
silently identified with the paper's real scale 2*Delta*N.

Six production modules are installed: `SargosIntegerBlock`,
`SargosIntegerTwoBlocks`, `SargosIntegerDyadicTrim`,
`SargosQuarticRoundedScale`, `SargosQuarticPrefixBlocks`,
and `SargosQuarticDualConjugation`. All 19 public theorems have
exact-signature regressions and explicit axiom audits. Thirteen
additional fixtures cover negative and empty intervals, the exact
40-term trimming bound, integral and nonintegral rounded scales,
both extreme perturbation signs, the actual sextic polynomial,
and the source bound at N=9216.

This is a pointwise source reduction toward
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Parameter change, Jacobian, rectangle covering, integrated transfer,
the real-scale convention, bounded N, recurrence and C-process remain
open. No integral estimate or recurrence is claimed. All 42 aggregate
checkbox states are unchanged. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 869 production files, 1,343 scanned Lean
  files and 10,201 build jobs. The audit covers 7,188 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,433 total).
  All 19 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-045149-2aa62e03.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_045504.log)
  and [manifest](../../logs/foundation_freeze_20260923_045504.json).
- All 1,364 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-dyadic-conjugation-20260923-045149-2aa62e03.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 326 nodes and 874 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `f64b4c39fe9662f775f2ef61a3474174cdfb5a4819c82372acc0ca382d6be05e` |
| Foundation log | `75a229e88f646bfd60c239847d91893083c9acc9141bb9cf6b3cfc97c37879dd` |
| Foundation manifest | `3ee07df9a79c179ec5f945ec571d052541fa3c99f3a86a7fa426cf86bbc601cd` |
| Rounded dyadic blocks and conjugation checkpoint JSON | `bb898539a014c7ebcd1101d78b0fc03d54a6bd16ef037bd5735402d52d1509f1` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos actual parameter change and sextic rectangle moment — previous checkpoint

The actual source parameter substitution and the moment bound on each
admissible parameter rectangle are now proved. No Jacobian formula,
inverse map, phase-variation bound or rectangle moment is assumed.

The map
`(alpha,gamma) -> (1/(4*alpha),-gamma/(16*alpha^4))`
is its own inverse when alpha is nonzero. Its exact scalar derivatives
give the inverse Jacobian weight 1/(64*x^6). Two genuine set-integral
substitutions prove the triangular change of variables, including
the variable vertical range [-16*H*x^4,16*H*x^4]. For Delta>0 and H>=0,
this yields the fixed-rectangle bound

```text
Integral_(Delta<=alpha<=2Delta, |gamma|<=H) F(map(alpha,gamma))
 <= 4096*Delta^6 *
    Integral_(1/(8Delta)<=x<=1/(4Delta), |y|<=H/(16Delta^4)) F(x,y).
```

This statement is for nonnegative extended-real iterated integrals,
and does not require an integrand-measurability hypothesis.
`sargosQuarticDual_sixth_parameter_transfer` consumes it for the
actual source-linked slow maxima. The exact sextic identity changes
gamma^2*t^6/(16*alpha^7) into 4*y^2*t^6/x.

On a unit-width rectangle [c,c+1] by [d,d+2/M^3], with
M>=2, 0<Delta<=1/2, c>=1/(8*Delta) and
|d|<=5/(Delta*M^3), the frozen coefficients are exactly
e(4*d^2*n^6/c), of modulus one. Their residual phase is
4*(y^2/x-d^2/c)*t^6. The proved coefficient bound is
2496/M^6 and the derivative bound is 1916928/M.
The actual prefix and maximum are unchanged by this freezing.

The completed Lemma 1 consumer then proves

```text
Integral_rectangle Smax(M,x,y,4*y^2*t^6/x)^6
 <= 384*Cwindow(3,1916928)*(log M)^6*I(M).
```

Both a genuine upper-integral theorem and the ordinary nonnegative
iterated-integral theorem are installed. Measurability of the actual
sextic maximum is proved, not assumed. These are estimates for each
admissible rectangle; the finite covering has not yet been assembled.

Eight modules are installed: `SargosQuarticParameterMap`,
`SargosQuarticParameterDomain`, `SargosQuarticParameterChange`,
`SargosQuarticParameterTransfer`, `SargosQuarticSexticFreeze`,
`SargosQuarticSexticBounds`, `SargosQuarticSexticRectangle`,
and `SargosQuarticMomentTransfer`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures check reciprocal images, source-scale parameters,
the sextic identity, the extremal Jacobian bound, frozen unit modulus,
rectangle boundaries and the actual source-moment transfer.

This advances the source reduction in
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Still open: finite rectangular covering and its count, assembled
large-source sixth-moment bound, rounded/real-scale conventions,
bounded N, recurrence and C-process. The original quartic pointwise
bound uses the linked integer scales m=floor(2*Delta*N) and 2*m;
this checkpoint does not silently replace them by real scales.
All aggregate checklist states, the permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 877 production files, 1,351 scanned Lean
  files and 10,209 build jobs. The audit covers 7,254 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,499 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-051922-22d50561.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_052320.log)
  and [manifest](../../logs/foundation_freeze_20260923_052320.json).
- All 1,372 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-parameter-rectangle-20260923-051922-22d50561.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 328 nodes and 878 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `d12e53e6f0b674ec0fee1da124ccaa55055e5edd0cb3ef2a102604044ea966af` |
| Foundation log | `faf04fd0d0b2d1a8f81e97f9e59ab987ec036db1d66dd90422017dd5ded69d1b` |
| Foundation manifest | `c2ea1dbd7c7c90185273184a93b5019b29b42677461d4babfc77e8af0b482387` |
| Actual parameter and sextic rectangle moment checkpoint JSON | `5cfb3223cf789cd7964966b1700c5d6f762f3b675a880c145f98ccf4ee0e0be3` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos large-source sixth moment at rounded scales — previous checkpoint

The literal source sixth moment now satisfies the large-source
two-scale reduction. The public theorem
`sargosQuartic_large_source_sixth_moment` chooses one C>=1 before
all N and Delta, and proves for natural N>=9216 and
N^(-1/2)<=Delta<=1/4, with m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)),
R(N,Delta) =
 Integral_(Delta<=alpha<=2Delta, |gamma|<=N^(-3))
 |Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|^6.
```

R and I are the actual Bochner integrals of the literal quartic sums.
No majorant, Jacobian, covering, slow-phase estimate or moment
inequality is supplied as an analytic premise.

The closed transformed rectangle has a finite grid cover retaining
all endpoints. Its horizontal count is at most 2/Delta and its
vertical count at most 5/Delta. Every corner satisfies the already
proved sextic rectangle theorem. A finite-cover integration inequality
allows overlapping boundaries; no disjointness or boundary omission
is assumed. Summing the actual rectangle moments and applying the
proved source parameter change gives, at either admissible integer
scale M,

```text
Integral_source DualMax(M)^6
 <= 15728640*Cwindow(3,1916928)*Delta^4*(log M)^6*I(M).
```

The source-facing sixth-power consumer uses both real dual maxima
and the original pointwise source bound. It bounds the sixth power
of the quarter-power error by N^3, whose integral over the source
rectangle is exactly 2*Delta. Measurability of the actual dual maxima
and the bridge from the original Bochner integral to nonnegative
iterated integrals are proved. The linked scales satisfy
m>=2, 2*m>=2, m<=N and 2*m<=N, so both logarithms transfer to log N.
The actual lower bound I(m)>=1/64 absorbs the error, without an
extra logarithmic loss.

Eleven modules are installed: `SargosIntervalGrid`,
`SargosFiniteCoverIntegral`, `SargosQuarticCoverGeometry`,
`SargosQuarticCoverMoment`, `SargosQuarticDualMoment`,
`SargosQuarticSixthPower`, `SargosQuarticMomentIntegration`,
`SargosRectangleLinearIntegral`, `SargosQuarticSourceMoment`,
`SargosQuarticMomentScale`, and `SargosQuarticLargeSourceMoment`.
All 24 public theorems have exact-signature regressions and explicit
axiom audits. Fifteen additional fixtures cover zero/nonintegral
grid lengths, closed right endpoints, negative grid origins, actual
source grid counts at both scales, boundary corners, sixth powers,
the integrated source error, and the final threshold, nonintegral
rounding and Delta=1/4 source estimates.

This is the natural-N, rounded-scale, large-source form of the
reduction in [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
It does not identify m with the real number 2*Delta*N.
Still open: the bounded source range, the source's real-scale
convention, global recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 888 production files, 1,362 scanned Lean
  files and 10,220 build jobs. The audit covers 7338 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13583 total).
  All 24 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-054924-c8e7f79f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_055711.log)
  and [manifest](../../logs/foundation_freeze_20260923_055711.json).
- All 1,383 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-large-source-moment-20260923-054924-c8e7f79f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 330 nodes and 883 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `eb4eb3f05a853580735dfd6710b1c7ba240c42c51f57ee0669311ab8c62b56d9` |
| Foundation log | `5ee37042ec08b730c9fab03bc59f59de4b1bc6e371c77b39115a6cce55988316` |
| Foundation manifest | `d53c75179fafeabca093d8ad8904f15a43b49f33c64096927fabf5716dbf7f33` |
| Large-source sixth moment at rounded scales checkpoint JSON | `82186e22fe393eed1564b617a48a5530696c9c8e7dd557494e5f6a652d274575` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos bounded reduction and finite-scale bootstrap — previous checkpoint

The rounded two-scale reduction now covers every natural N>=16.
The theorem `sargosQuartic_sixth_moment_reduction` chooses one C>=1
before N and Delta, and proves, for N^(-1/2)<=Delta<=1/4 and
m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)).
```

The previously omitted range 16<=N<=9216 is discharged using the
actual source rectangle inclusion, I(N)<=2*N^3, I(m)>=1/64,
m>=8 and Delta>=1/96. No additional analytic premise is introduced.

The recurrence now has an actual finite-scale consumer.
For the literal full-sum moment, the near-count upper/lower bounds
and symmetry prove localization without a maximal-completion loss:

```text
I(N) <= (1024/A)*InitialMoment(N,A),       0<A<=1/2.
```

A finite dyadic split retains every interval endpoint. Its linked
scales delta_i start at N^(-1/2), satisfy delta_i<=A, cover [0,A]
together with the small-alpha interval, and obey sum(delta_i)<=2*A.
If A is below the first scale, direct integral monotonicity applies.
The integration theorem consumes the actual R(N,delta_i), not a
separately supplied surrogate integral.

`sargosSixthBaseMoment_power_bootstrap` chooses C>=1 before
beta and B. For beta,B>=0, a genuine upstream bound
I(M)<=B*M^beta for every natural M>=1 implies, for N>=16 and
0<A<=1/4,

```text
I(N) <= C*((1+log N)^5/A + B*(log N)^6*(4*A*N)^beta).
```

Both rounded moment scales are explicitly bounded by 4*A*N in this
consumer. The upstream power bound is an explicit, narrower input:
it is used at those smaller linked moments. It is not a premise
equivalent to the bootstrap conclusion.
`sargosSixthBaseMoment_cubic_bootstrap` discharges that input using
the proved trivial estimate. Separately,
`sargosSixthBaseMoment_sqrt_bound` consumes the actual small-alpha
estimate and localization to prove for natural N>=4

```text
I(N) <= (1024*44845498368)*sqrt(N)*(1+log N)^5.
```

Seven modules are installed: `SargosQuarticBoundedScale`,
`SargosQuarticBoundedMoment`, `SargosSixthLocalization`,
`SargosDyadicIntegral`, `SargosSixthDyadicBudget`,
`SargosSixthPowerBootstrap`, and `SargosSixthBootstrapInputs`.
All 18 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen additional fixtures cover threshold scales,
the bounded-range constant, empty/nonempty dyadic sums, the source
scale budget, negative/zero integration cases, localization,
small-alpha and square-root estimates, and actual source consumers.

This advances [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
The finite-scale bootstrap is proved; the epsilon-quantified exponent
improvement and its iteration are not yet proved. The exact real-scale
convention and C-process also remain open. The integer m is not
identified with 2*Delta*N. Aggregate checklist states, the permanent
counterexample, corrected powering and all nine Add-est clauses
remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 895 production files, 1,369 scanned Lean
  files and 10,227 build jobs. The audit covers 7374 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13619 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-061935-4e284490.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_062253.log)
  and [manifest](../../logs/foundation_freeze_20260923_062253.json).
- All 1,390 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-bounded-bootstrap-20260923-061935-4e284490.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 335 nodes and 894 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `92ac11ee857aa0683216b846a7516de45c737324aefe0f0839cbb27e77a9b988` |
| Foundation log | `c0c9378be0410cd8bf37f659e59c74c412625e0ed5f6043d5f539fb5558dfbcd` |
| Foundation manifest | `adbd3fe02c9c49346440b1989d84fcba33639008c5b86b12f043d8a60480bf42` |
| Bounded reduction and finite-scale bootstrap checkpoint JSON | `2acd542e50623837d5cdce6ed6232934b4d23b7f82aee9c105718b54f92daecd` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos natural-scale maximal sixth moment — previous checkpoint

The global recurrence and its iteration are now proved for the actual
natural-scale quartic moment. The public source-facing consumer
`sargosQuartic_maximal_sixth_moment` proves:

```text
For every epsilon>0 there is C>=1, chosen before N,z,lambda,c,d,
such that for every natural N>=2, |z(n)|<=1 on N<n<=2N,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(0<=H<=N)|Sum_(N<n<=N+H) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The maximum, coefficients, integer prefixes and Bochner integrals
are the actual previously defined objects. No moment estimate,
recurrence, exponent iteration or epsilon-loss bound is assumed
in this final theorem.

The finite-scale bootstrap is optimized at
A=(1/4)*N^(-beta/(1+beta)). Its admissibility is proved uniformly,
including beta=0. Exact real-power identities give the improved
exponent beta/(1+beta). The global logarithm estimate

```text
(1+log x)^6 <= (1+6/epsilon)^6*x^epsilon,    x>=1, epsilon>0
```

discharges the loss without an eventual-threshold assumption.
`SargosSixthMomentExponent beta` records the actual
epsilon-quantified estimate, with the constant chosen before N.
`sargosSixthMomentExponent_step` proves the genuine implication
from beta to beta/(1+beta), and explicitly handles all small N.

The proved trivial exponent 3 initiates the sequence
beta_n=3/(1+3*n). Its exact recurrence and arbitrarily small values
yield `sargosSixthBaseMoment_subpolynomial`:
for every epsilon>0, I(N)<=C*N^epsilon for every natural N>=1.
The final weighted maximal theorem consumes this bound and the
completed source-height strip transfer, then absorbs its logarithm.
The stronger square-root initial estimate remains available.

Six modules are installed: `SargosSixthExponentAlgebra`,
`SargosSixthLogAbsorption`, `SargosSixthOptimizedBootstrap`,
`SargosSixthMomentExponents`, `SargosSixthMomentIteration`,
and `SargosSixthMomentTheorem`. All 15 public theorems have
exact-signature regressions and explicit axiom audits.
Fourteen additional fixtures check zero-exponent parameters,
exact successive exponents, logarithmic absorption at x=1,
iteration outputs, subpolynomial bounds and the actual weighted
maximal integral at the smallest permitted natural block N=2.

This is the natural-block form of the sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not yet replace natural block endpoints by arbitrary real
scales. That real-scale bridge, the exact real-scale Lemma 5
convention, and the C-process remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 901 production files, 1,375 scanned Lean
  files and 10,233 build jobs. The audit covers 7402 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13647 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-063351-3ad01f0f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_063758.log)
  and [manifest](../../logs/foundation_freeze_20260923_063758.json).
- All 1,396 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-natural-sixth-theorem-20260923-063351-3ad01f0f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 338 nodes and 897 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `12c8251967a8d7ae8b3d48d5d9d349e72e380601ff3063542112d45dc1129e02` |
| Foundation log | `3da6d819150afd90febffb1244aeb66c43b2ddf2e3de3ac6ad5cbfc9bb939118` |
| Foundation manifest | `201372174763b8bddcb4fa29f29f18fd1c052f3bcfb96679db52330695567e48` |
| Natural-scale maximal sixth moment checkpoint JSON | `506e64278fc9ad11f481cdbcc28a9dbc7f240b167b563cd5686f890714f96659` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Robert–Sargos real-scale maximal sixth moment — previous checkpoint

The source-facing theorem `sargos_source_maximal_sixth_moment`
now proves the weighted maximal sixth-moment estimate at arbitrary
real scales, with the actual maximum over real endpoints:

```text
For every epsilon>0 there is C>=1, chosen before M,z,lambda,c,d,
such that for every real M>=2, |z(n)|<=1 on M<n<=2M,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(M<X<=2M)|Sum_(M<n<=X) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*M^(3+epsilon)+M^epsilon).
```

The endpoint maximum is the supremum of the literal integer sums
over the real interval M<X<=2M. Its equality to a finite prefix
maximum and its attainment are proved, not assumed.
The coefficient condition is stated on the physical interval
M<n<=2M. The double integral is the actual Bochner integral.
No moment estimate or endpoint bridge is a hypothesis of the
final theorem.

With m=floor(M), the real block has m or m+1 terms. The literal
prefix comparison gives Max_real<=Max_natural+1, including the
possible extra upper-endpoint term. The sixth-power bound
Max_real^6<=32*(Max_natural^6+1) is integrated over the actual
rectangle; the constant contribution is exactly lambda.
Continuity and the needed product, inner and outer integrability
are proved. Monotonicity of real powers transfers the completed
natural-scale theorem from m to M and absorbs the extra lambda.
The final uniform constant is 32*(C_natural+1).

Seven modules are installed: `SargosRealQuarticBlock`,
`SargosRealQuarticPrefix`, `SargosRealQuarticRegularity`,
`SargosRealQuarticMomentTransfer`, `SargosRealSixthMomentTheorem`,
`SargosRealQuarticEndpoints`, and `SargosSourceSixthMoment`.
All 22 public theorems have exact-signature regressions and
explicit axiom audits. Fourteen additional fixtures check
integer and noninteger scales, the strict left and closed right
endpoints, both possible block lengths, zero prefixes, attained
real maxima, translated rectangles, zero-height integration and
the source theorem at M=5/2.

This realizes the source maximal sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not claim the separate exact real-scale Lemma 5 convention,
nor Sargos's C-process. Those remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 908 production files, 1,382 scanned Lean
  files and 10,240 build jobs. The audit covers 7445 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13690 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-070029-00a8fc3c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_070350.log)
  and [manifest](../../logs/foundation_freeze_20260923_070350.json).
- All 1,403 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-sixth-theorem-20260923-070029-00a8fc3c.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 341 nodes and 901 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `ea2aa324918cad2014c571b9791800cb27b80bcd25a19bf9865af24d019da938` |
| Foundation log | `26d5ba2415b3a59901ee679aaf669bdb09a180422c49fcce16f99ef2c8d4b049` |
| Foundation manifest | `0f6883cdc0d1ea21301a15936ad6a1cf0057c347f010f9cc172c87c5fef93cba` |
| Real-scale maximal sixth moment checkpoint JSON | `469f71d28cf39c6228df994de5ca8a8e57e50df0702fce224096518d91f3efb1` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos initial-interval moments and uniform sextuple count — previous checkpoint

`sargos_initial_sextuple_count` proves the actual source count:

```text
For every epsilon>0 there is C>=1, chosen before N and c,
such that for every natural N>=1 and every real c,

 #{(n,n') in {1,...,N}^3 x {1,...,N}^3 :
     sum_i n_i^2 = sum_i n'_i^2,
     c <= sum_i n_i^4-sum_i n'_i^4 <= c+N^3}
 <= C*N^(3+epsilon).
```

Triples are literal functions from Fin 3 to the integer interval
1<=n<=N. Their square and fourth-power sums are integer sums;
ordered pairs retain all multiplicities. Both window endpoints
are closed. The theorem's constant is uniform in the real shift c.
This realizes [Sargos 2003, Lemma 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82873).

The stronger theorem `sargosInitialSextupleWindow_card_bound`
allows every positive width B and proves
card<=C*(N^3+B)*N^epsilon, uniformly in N,B,c.
No count estimate is assumed.

The initial-interval moment is also proved. The actual dyadic
decomposition separates {1,2} and the blocks (2^i,2^(i+1)].
A finite sixth-power inequality is integrated with all needed
integrability established. Literal zero-padding transfers an
arbitrary N to a power-of-two P with N<=P<=2N. The dyadic count's
sixth power is absorbed by a proved logarithmic/epsilon bound.
`sargosInitialQuartic_sixth_moment` gives, uniformly in bounded
coefficients and translated windows,

```text
Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
 |Sum_(1<=n<=N) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The shift-uniform count does not assume a translation principle.
The shifted tent-kernel Gram identity is proved with its actual
character factor. Taking the norm of the integral bounds it by
the same central unshifted moment. The actual tuple-power
expansion and source-window inclusion then give the count.

Ten modules are installed: `SargosInitialInterval`,
`SargosInitialRegularity`, `SargosInitialMomentTransfer`,
`SargosInitialDyadicMoment`, `SargosInitialTruncation`,
`SargosInitialSixthMoment`, `SargosShiftedTentGram`,
`SargosShiftedNearCount`, `SargosInitialMomentTuples`,
and `SargosInitialSextupleCount`. All 33 public theorems have
exact-signature regressions and explicit axiom audits.
Eighteen additional fixtures cover empty and non-dyadic intervals,
zero-padding at and beyond the endpoint, dyadic decomposition,
zero-height integration, exact tuple multiplicities, empty and
closed-endpoint shifted windows, arbitrary real shifts, and
the actual N=1 and N=3 moment/count consumers.

The real-scale maximal moment remains complete. Sargos's
symmetric differencing inequality, Taylor-remainder assembly,
A-bar-four inequality and C-process remain open. The separate
exact real-scale Robert–Sargos Lemma 5 convention also remains
open. No aggregate checklist item changes status. Preserve
the permanent counterexample, corrected powering and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 918 production files, 1,392 scanned Lean
  files and 10,250 build jobs. The audit covers 7506 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13751 total).
  All 33 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-072955-0a22d012.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_073326.log)
  and [manifest](../../logs/foundation_freeze_20260923_073326.json).
- All 1,413 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-initial-sextuple-20260923-072955-0a22d012.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 344 nodes and 906 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `1b87f61fb7726a5a4c85255228f736e82874602ebe2ea6f038478df36b5be506` |
| Foundation log | `2d075d38421246eb708e24d5125f79f1023e441e21884fb2dd235307b3813877` |
| Foundation manifest | `95a1652ee2e11ec32ce41b866b9eb32f7eacc2f3c0ac6129a67c470ad8d1eaad` |
| Initial-interval moments and sextuple count checkpoint JSON | `62fdc20264cc1eecfc85e6c2fe91d836fd92e4346d5e131fa9008eeb0e2cf7f5` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos finite symmetric differencing — previous checkpoint

`sargos_finite_sextuple_differencing` now proves the actual finite
polynomial estimate. For arbitrary complex coefficients a and natural
1<=H<=M, let Phi be a on the integer interval 0<=m<M and zero elsewhere.
Set S=sum Phi(m), E=sum |Phi(m)|^2 and

```text
Q = sum_(t,t' in {1,...,H}^3, s2(t)=s2(t'))
      |sum_(0<=m<M)
         product_i Phi(m+t_i)Phi(m-t_i)
         * conjugate(product_i Phi(m+t'_i)Phi(m-t'_i))|.

|S|^12 <= 1492992*(M/H)^6*E^6
           + 382205952*(M^11/H^4)*Q.
```

All tuples are literal ordered triples, their square frequencies are
integer sums, and Q retains every square-diagonal sextuple and its
multiplicity. The theorem assumes no differencing estimate, Gram identity,
moment bound or analytic certificate.

The proof starts with actual even shifts, finite Cauchy and exact
parity fibers. The square is nonconjugated at this stage. Negative
offsets pair with positive offsets, leaving the actual diagonal term.
Zero-padding support and center translation are proved. A finite maximum
selects an actual parity fiber. Cubing expands into literal triples;
Holder and the exact frequency Gram identity give the sixth-power bound.
Conjugation appears between the two triples in that Gram identity.
Finally, the parity indicators are removed by a proved termwise majorant,
so the public endpoint has no parity witness or restriction.

This is the polynomial finite input corresponding to
[Sargos 2003, Section 3.2](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The paper's one-based interval convention has not yet been bridged in
this consumer. The exact printed Lemma 1 maximum is not claimed: the
proved parity-fiber variant supplies the downstream finite inequality
directly. The source index bridge, Taylor-remainder assembly, derivative
bounds, phase/support identification, witness selection, A-bar-four
inequality and C-process remain open. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Eleven modules are installed: `SargosSymmetricAveraging`,
`SargosSymmetricFibers`, `SargosSymmetricPositive`,
`SargosSymmetricSupport`, `SargosSymmetricDifferencing`,
`SargosFiniteFrequencyGram`, `SargosGroupedSecondMoment`,
`SargosSymmetricTriples`, `SargosSymmetricSixth`,
`SargosSymmetricTwelfth` and `SargosSextupleMajorant`.
All 42 public theorems have exact-signature regressions and explicit
axiom audits. Eighteen additional fixtures cover support endpoints,
empty intervals, odd/even parity fibers, genuinely nonconjugated
squaring, Gram conjugation, empty tuple types, diagonal multiplicities
and the actual H=1 and (M,H)=(3,2) consumers.

The completed shift-uniform sextuple count and real-scale maximal
sixth moment are preserved. No aggregate checklist item changes
status. Preserve the permanent counterexample, corrected powering
and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 929 production files, 1,403 scanned Lean
  files and 10,261 build jobs. The audit covers 7596 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13841 total).
  All 42 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-080954-241e9fff.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_081351.log)
  and [manifest](../../logs/foundation_freeze_20260923_081351.json).
- All 1,424 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-symmetric-differencing-20260923-080954-241e9fff.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 346 nodes and 909 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `e089a1a107417bcf610067a108ef969f52b51fb224a9f8ef2acdb7b31add6969` |
| Foundation log | `f34cf213b58486381bb06b0c918d2bd473c8f97e8fb869682f0a302de3899e8c` |
| Foundation manifest | `9ccf0597d078ab0777b43c3dfea80f936fdb76d80b90147108b8d31576cc2c42` |
| Finite symmetric differencing checkpoint JSON | `11caee711b016f320b979f4283e6a18774499d9fd931e1ba4fcf008802e4ca44` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos source Taylor and interior reduction — previous checkpoint

`sargos_character_interior_differencing` proves a source-indexed
estimate for the actual character sum. For every epsilon>0 there is
C>=1, chosen before natural H>=1, M>=H and the real phase f, such that

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qinterior
    + C*M^11*H^epsilon.
```

Qinterior is the actual sum over all ordered pairs of triples in
{1,...,H}^3 with equal integer square sums. Each term is the norm
of the character sum over the open integer interval
(radius+1, M-radius), where radius is the maximum of all six
offsets. Its phase is exactly

```text
(s4(t)-s4(t'))/12 * f^(4)(m) + u(t,t',m),
u(t,t',m) = sum_i v(t_i,m) - sum_i v(t'_i,m).
```

The one-based source bridge is proved: sums, zero-padding, triples
and full sextuple correlations are translated exactly from the
previous zero-based finite theorem. No source-index convention
remains assumed in this consumer.

The actual symmetric residual v is defined from f(m+n)+f(m-n)
minus its constant, quadratic and quartic terms. Its degree-five
Taylor cancellation and genuine integral representation are proved:

```text
v(n,m) = (1/120) * integral_0^n
           [f^(6)(m+t)+f^(6)(m-t)]*(n-t)^5 dt.
```

Under local smoothness of the original phase on the actual segment,
the proved bound is |v(n,m)|<=B*n^6/360 when |f^(6)|<=B there.
Iterated derivatives commute with this constructed remainder.
The literal six-term residual satisfies
|u^(j)(m)|<=B*H^6/60 when the original (j+6)-th derivative is bounded
by B on the sextuple's actual maximum-offset segment. The local
radius theorem is obtained by an exact retyping of the same
coordinates; it does not enlarge the required phase domain.
A source-interior consumer uses only smoothness and original
derivative bounds inside (1,M).

The actual padded products have precisely the closed support
[radius+1,M-radius]. Their character phase, including conjugation
between the two triples and cancellation of the quadratic term,
is proved. Removing its endpoints costs at most two unit terms,
including empty, reversed and singleton intervals. The full
square-diagonal cardinality bound is proved from the earlier
width-general sextuple count, giving O_epsilon(H^(4+epsilon)).
This controls the aggregate boundary error in the displayed
interior estimate. No boundary smoothness or global remainder
extension is assumed.

These are the source-indexed polynomial differencing input and
local Taylor/phase steps for
[Sargos 2003, Sections 3.2–3.3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The global remainder extension, quartic-window witness/prefix
selection, A-bar-four theorem and C-process remain open.
The Taylor lemmas use local C-infinity hypotheses, as available
for the intended model phases; the paper's separate finite-C^k
formulation is not claimed complete. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Thirteen modules are installed: `SargosSourceDifferencing`,
`SargosSymmetricTaylor`, `SargosSymmetricTaylorJets`,
`SargosTaylorIntegral`, `SargosSymmetricTaylorIntegral`,
`SargosSextupleRemainder`, `SargosSextuplePhase`,
`SargosTupleSupport`, `SargosSourceSextuplePhase`,
`SargosSextupleRadiusJets`, `SargosSquareDiagonalCount`,
`SargosSextupleEndpoints` and `SargosInteriorDifferencing`.
All 50 public theorems have exact-signature regressions and
explicit axiom audits. Twenty additional fixtures check source
endpoints and translation, zero/constant/quartic/sextic Taylor
cases, the zero-height integral, derivative order zero, diagonal
phase cancellation, actual singleton/empty supporting intervals,
coincident/reversed endpoints, the H=1 count, and the actual
(M,H)=(3,2) interior consumer.

The earlier sixth moments, shifted sextuple count and finite
symmetric differencing are preserved. No aggregate checklist
item changes status. Preserve the permanent counterexample,
corrected powering and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 942 production files, 1,416 scanned Lean
  files and 10,274 build jobs. The audit covers 7702 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13947 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-084446-824cd661.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_084836.log)
  and [manifest](../../logs/foundation_freeze_20260923_084836.json).
- All 1,437 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-taylor-20260923-084446-824cd661.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 350 nodes and 914 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `53272997d85e155df84d754bb561c0eec4868a6756dc3cff6d84adeff25b1643` |
| Foundation log | `d47f12278a32d4789c15c74da705ca22ee58e8cb52a026ff419d20a2c731818b` |
| Foundation manifest | `e35d9cbbbb91f90dc5525e447ec6fed3697bdfcfce4c3626274d467878a8849d` |
| Source Taylor and interior reduction checkpoint JSON | `f4868e998bafb3d159d4f4c378ce4284964cbec66f4478f83027f78d6f3a9962` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos smooth remainder extension — previous checkpoint

`sargos_smooth_extended_reduction` constructs the smooth remainder
family used in the actual source-indexed finite reduction. For each
finite order Q and epsilon>0, one C>=1 is chosen before H, M, the
phase f and the original-derivative bound B. For 1<=H<=M, B>=0,
local C-infinity regularity on (1,M), and

```text
|f^(j+6)(y)| <= B/M^j   (y in (1,M), 0<=j<=Q+1),
```

the constructed physical extension U_q satisfies, for every actual
ordered sextuple q,

```text
U_q is globally C-infinity;
U_q(m) = u_q(m) at every integer radius+1 < m < M-radius;
|U_q^(j)(x)| <= C*B*H^6/(60*M^j)  (0<=x<=M, 0<=j<=Q).
```

Here u_q is the actual six-term symmetric Taylor remainder, not a
freely supplied function. The construction normalizes it as
u_q(M*x), proves the local affine derivative identity, and derives
its jets from the original phase. With l=(radius+1)/M,
r=(M-radius)/M and h=1/(8M), the actual nonempty integer support
proves l+4h<r. Every retained integer m has m/M in the agreement
plateau [l+2h,r-2h]. Both Taylor anchors lie within distance one
of the observation interval [0,1]. The existing Taylor-pasted
construction therefore gives genuine global smoothness and
uniform finite-order bounds, even as the buffer shrinks.
The zero branch is tied to an empty actual integer support.

Exact phase and sum identities replace u_q by U_q inside every
retained character sum, with all ordered sextuple multiplicities
unchanged. The assembled theorem also proves

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qextended
    + C*M^11*H^epsilon.
```

Qextended is defined using the actual interior character sums
with phase (s4(t)-s4(t'))*f^(4)(m)/12+U_q(m).
The common C controls both the extension and the boundary error.
The original phase bounds are explicit narrower analytic inputs;
no global remainder certificate, extension existence, agreement
condition or final sum estimate is assumed.

This closes the C-infinity, finite-order uniform-constant extension
consumer. It does **not** close the printed finite-C^k,
constant-one remainder statement or the A-bar-four witness theorem
in [Sargos 2003, Section 3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The construction uses original jets through Q+7. The physical
model-phase input still needs its consumer, followed by signed
quartic-window counting, witness/prefix selection, optimization
and the C-process. The separate exact real-scale Robert–Sargos
Lemma 5 convention also remains open.

Eight modules are installed: `SargosLocalAffineJets`,
`SargosRemainderLocalSmooth`, `SargosNormalizedRemainder`,
`SargosRemainderGeometry`, `SargosRemainderExtension`,
`SargosPhysicalRemainderExtension`, `SargosExtendedSextuplePhase`
and `SargosSmoothExtendedReduction`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Sixteen
additional fixtures check zero/negative affine scaling, the
M=0/1 buffer conventions, empty and singleton integer interiors,
exact agreement, zeroth derivatives, a genuinely nonzero sextic
remainder (-15120), zero original-phase bounds and an empty
actual correlation.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 950 production files, 1,424 scanned Lean
  files and 10,282 build jobs. The audit covers 7755 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14000 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-091416-0a8b1879.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_091748.log)
  and [manifest](../../logs/foundation_freeze_20260923_091748.json).
- All 1,445 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-remainder-extension-20260923-091416-0a8b1879.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 353 nodes and 920 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `6af479071b5ebdf29441e1e1e86582668b62c58ce9ab26c1bfba62e0544146e9` |
| Foundation log | `63be70d5489e8d2f273d89364de58755a1f201ca30ed649f9fad8066784e9cc1` |
| Foundation manifest | `cbdc3e6151d54449b816eba64fd50636cc63d3bd0cb112e55c068ee362bd0847` |
| Smooth remainder extension checkpoint JSON | `dd66c5003cc8003f436e6915b3148baeba5f2c785bf50fa1788b34c858b5e4b6` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos actual transformed model — previous checkpoint

The actual approximate model phase now supplies the remainder
extension's original-derivative hypotheses. The finite budget
D(sigma,Q)=1+sum_(p<Q+7) modelPhaseJetCoefficient(sigma,p)
depends only on the fixed model parameter and requested order.
For a source phase T*F((A+x)/N), N<=A and A+M<=2N imply M<=N.
Closed-interval model data through order Q+6, with delta<=1,
therefore gives

```text
|f^(j+6)(x)| <= (D(sigma,Q)*|T|/N^6)/M^j
  (1<x<M, 0<=j<=Q+1).
```

Local regularity is derived inside the physical interval; no
exterior smoothness of F is assumed. The theorem
`sargos_model_smooth_reduction` consumes this real-scale source
phase in the constructed extension and finite sum reduction.

The transformed-model branch is proved for the natural full
dyadic block, f(x)=T*F(1+x/M), M>=1. Put
D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0 and
T1=tau*T*D4/M^4. The normalized fourth derivative is defined
using **within-derivatives on the closed interval [1,2]**.
Its smoothness, derivative composition, falling-factorial identity
and exact model-error scaling are proved at both endpoints,
giving parameter sigma+4 and error delta/D4.

The actual globally smooth extension U_q is rescaled as
U_q(M*(u-1))/T1 and added to this fourth-derivative model.
`sargosTransformedModel_approximate` proves that, for each
sigma>0 and finite P, one C>=1 chosen before all physical data
gives the closed-interval model error

```text
(delta + C*H^6/(tau*M^2))/D4.
```

The source model order is P+7, the extension order is P+1,
and tau,T are positive. The correction estimate consumes the
constructed remainder's actual jets. No transformed-model
predicate or global remainder bound is assumed.

Exact physical entry is proved, not just an exponent inequality:

```text
T1*G(1+x/M) = tau*f^(4)(x)+U_q(x)  (0<x<M).
```

The source sextuple phase and its character sum are identified
with this expression at every actual interior integer.
`sargos_positive_sextuple_model` sets tau to the actual positive
quartic difference divided by 12 and returns both the approximate
model and the exact source-sum identity. A further proved
inequality gives H^6/(tau*M^2)<=eta from tau>=H^3 and
H^3/M^2<=eta.

This is the actual-model input for
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Signed quartic-window counting, the general subinterval/real-scale
transformed-model bridge, witness/prefix selection, optimization
and the C-process remain open. The natural full-block transformed
consumer is not claimed to cover arbitrary real-scale subintervals.
The printed finite-C^k constant-one A-bar-four formulation and
separate exact real-scale Robert–Sargos Lemma 5 convention
also remain open.

Eight modules are installed: `SargosModelRemainderJets`,
`SargosModelSmoothReduction`, `SargosWithinDerivativeCalculus`,
`SargosFourthDerivativeModel`, `SargosPhaseCorrection`,
`SargosTransformedModel`, `SargosTransformedSource` and
`SargosPositiveSextupleModel`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Eighteen
additional fixtures cover the fourth coefficient at sigma=0,1,2,
both closed endpoints, the exact reference primitive, derivative
order zero, zero/constant/quadratic corrections, physical time
normalization, zero frequency, a genuine square-diagonal sextuple
with quartic difference 144, the large-frequency threshold and
an actual transformed reference-model consumer.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 958 production files, 1,432 scanned Lean
  files and 10,290 build jobs. The audit covers 7821 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14066 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-094310-2a298bd0.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_095000.log)
  and [manifest](../../logs/foundation_freeze_20260923_095000.json).
- All 1,453 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-transformed-model-20260923-094310-2a298bd0.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 356 nodes and 926 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `0c65a1578f74bc26fae0e415d2d87d9ca283498f6029bad6515baba726921145` |
| Foundation log | `d80313c4c353a7145addf9f7612d9680963f3fbedd9c66ef4f77ff1c16aca894` |
| Foundation manifest | `44f7e8f9df154296a386da3404a6c363f0ade3df526ec07507d8d4536374094b` |
| Actual transformed model checkpoint JSON | `581bb8749fbd25af4dc49bbd338db9ffc7a7e71c9e255f5cdb587ee72c0ca497` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos real-scale source consumer — previous checkpoint

The transformed model now covers arbitrary admissible real scales
N>=1 and natural source windows [a,a+M] inside [N,2N].
There is no assumption that M is comparable to N. The original
physical phase is f(x)=T*F((a+x)/N), and its actual derivative
bounds retain N in every denominator.

The six-term Taylor remainder is normalized by N, extended with
the existing Taylor-pasting construction, and pulled back to a
globally smooth U_q. It agrees at every actual interior integer.
The proved jets hold on the two-sided physical observation
interval [-N,N], which is essential because N*u-a can be negative
even when u belongs to the canonical closed interval [1,2].
For each fixed model parameter and finite order, one constant
is chosen before all source scales, phases and sextuples.

With D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0,
the actual transformed time and model are

```text
T1 = tau*T*D4/N^4,
G(u) = F^(4)_within(u)/D4 + U_q(N*u-a)/T1,
model error <= (delta + C*H^6/(tau*N^2))/D4.
```

All derivatives and model bounds on [1,2] include both closed
endpoints. The original source order is P+7, and the constructed
extension uses order P+1. No regularity of F outside its source
interval is assumed.

Both signs of the actual quartic difference are handled by
swapping the two ordered triples when necessary. This preserves
the radius and exact integer support, negates the actual source
phase, and conjugates its character sum. Its norm is therefore
unchanged. The oriented frequency is exactly the absolute
integer quartic difference, and tau=abs(difference)/12.
Orientation is not used to collapse the counting set: all ordered
sextuple multiplicities remain available to subsequent estimates.

The source-entry bridges are now explicit kernel-checked identities.
The original closed natural interval sum is its one-based integer
source sum plus one endpoint character, with norm loss exactly 1.
For each nonempty actual inner support, translation by a gives
the exact natural closed interval with endpoints
a+R+2 and a+M-R-1. Its dyadic scale conditions are derived from
N<=a and a+M<=2N. Empty supports are treated as the actual empty
sum, not substituted for nonempty source objects.

The public consumer `sargos_large_frequency_exponentPair_bound`
uses an existing genuine exponent pair (k,l), sigma>0 and epsilon>0.
It chooses delta>0, source order P>=1, eta>0 and C>=1 before
all physical inputs. For the original phase model, 1<=H<=M,
N>=1, N<=a, a+M<=2N, T>0 and

```text
tau = abs(actual quartic difference)/12 >= H^3,
H^3/N^2 <= eta,
```

it proves the actual interior source-sum norm is at most

```text
C*((T1/N)^(k+epsilon)*N^(l+epsilon) + N/T1).
```

The proof derives the transformed model error, both-sign identity,
natural interval and scale conditions, then invokes the existing
all-positive-height exponent-pair theorem. None of those bridges,
nor the desired transformed-sum bound, is an assumed certificate.
This is a consumer of an upstream exponent pair, not yet a proof
of the new C-transformed exponent pair.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Remaining EPZAE-10 work is actual signed-window aggregation,
including the reciprocal-frequency term, finite C-process
assembly and optimization. The printed A-bar-four witness/prefix
selection, finite-C^k constant-one formulation and separate exact
real-scale Robert–Sargos Lemma 5 convention remain open.

Thirteen production modules are installed: `SargosScaledRemainder`,
`SargosScaledRemainderGeometry`, `SargosScaledRemainderExtension`,
`SargosScaledPhysicalRemainder`, `SargosScaledModelRemainder`,
`SargosAffinePhaseCorrection`, `SargosScaledTransformedModel`,
`SargosScaledTransformedSource`, `SargosSourceModelEntry`,
`SargosSextupleOrientation`, `SargosOrientedModelSource`,
`SargosInnerModelEntry` and `SargosLargeFrequencyModelBound`.
All 46 public theorems have exact-signature regressions and explicit
axiom audits. Twenty-two further fixtures cover non-integer scales,
negative physical arguments, correction derivatives, time scaling,
zero frequency, source singleton/endpoint behavior, an actual
positive and negative quartic difference, square-diagonal membership,
conjugation, empty and singleton inner supports, the genuine empty
extension branch and large-frequency error thresholds.

No aggregate checklist item changes status. The permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 971 production files, 1,445 scanned Lean
  files and 10,303 build jobs. The audit covers 7938 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14183 total).
  All 46 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-101936-e5b0e215.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_102331.log)
  and [manifest](../../logs/foundation_freeze_20260923_102331.json).
- All 1,466 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-scale-source-20260923-101936-e5b0e215.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 360 nodes and 935 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `09cdfd1b6cc16947c0c0097d2b57ec39da4dad46d64072f8da0634c214d7bfed` |
| Foundation log | `bea229c49570243d4abbf5d489cfe5b7f31bbc63cc1b9dda608e334230dae25d` |
| Foundation manifest | `4a2ef6b74a91d9c6bac6efb393ca82fd513d3791dc99caa97dbe3e5b93d5d0fe` |
| Real-scale source consumer checkpoint JSON | `8dd956e1199f29ee485e4a05028964bc0fdc9832b12a4039289f62612c47a2bc` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Sargos finite closed-source inequality — previous checkpoint

The actual signed-frequency aggregation and finite C-process
inequality are proved. All ordered sextuple multiplicities are
retained; orienting a phase never replaces the counting set by
its image.

The small-frequency set has absolute quartic difference at most
12*H^3. It lies in the actual signed window [-12*H^3,12*H^3],
so the proved shifted-window theorem gives cardinality at most
C_epsilon*H^(3+epsilon). Its actual inner character sum has norm
at most M, derived from the literal integer support.

For large frequencies, the absolute difference is at most 3*H^4.
Every such sextuple is covered by an actual window

```text
j*H^3 <= abs(difference) <= (j+1)*H^3,
1 <= j <= 3*H.
```

The index is the natural floor of abs(difference)/H^3.
Each absolute window is contained in two actual signed windows.
The proved finite cover inequality permits overlapping endpoints
only through nonnegative overcounting; no disjointness or omitted
multiplicity is assumed. Each window's reciprocal contribution is
controlled by its actual count and 12/(j*H^3).
The harmonic-sum estimate and an explicit logarithmic-loss bound
therefore give

```text
sum_(large ordered sextuples) 12/abs(difference)
  <= C_epsilon * H^epsilon.
```

This avoids the extra factor H produced by using only the full
diagonal count and the lower frequency threshold.

The actual all-positive-height exponent-pair consumer is summed
over this set. The quartic frequency is explicitly linked to both
terms: tau<=H^4 controls the main term, while the exact identity
N/T1=(N^5/(D4*T))*(12/abs(difference)) supplies the secondary term.
The small and large sets form a proved disjoint partition of the
original square-diagonal set.

The public theorem `sargos_finite_closed_model_process` consumes
an actual exponent pair (k,l), sigma>0 and epsilon>0. It chooses
delta>0, P>=1, eta>0 and C>=1 before all physical inputs.
For the original model F, real N>=1, T>0, N<=a, a+M<=2N,
1<=H<=M and H^3/N^2<=eta, it proves

```text
norm(exponentialSumAt F T N a (a+M))^12
 <= C * H^epsilon *
    [ N^12/H
      + N^11*(D4*T*H^4/N^5)^(k+epsilon)*N^(l+epsilon)
      + N^16/(D4*T*H^4) ],
D4 = sigma*(sigma+1)*(sigma+2)*(sigma+3).
```

This is the exact original closed natural sum, not a generic
majorant or a separately assumed transformed estimate.
The proof consumes the actual full correlation bound and
twelfth-power differencing theorem, derives M<=N, and absorbs
the single endpoint character with a proved twelfth-power bound.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The finite inequality is not yet the C-transformed exponent pair.
Actual integer-H selection, short-window and low-height branches,
epsilon bookkeeping and final exponent-pair assembly remain open.
The printed A-bar-four witness/prefix selection, finite-C^k
constant-one formulation and separate exact real-scale
Robert–Sargos Lemma 5 convention remain distinct open obligations.

Ten production modules are installed: `SargosFrequencyWindows`,
`SargosFrequencyWindowCover`, `SargosReciprocalFrequency`,
`SargosSmallFrequencyContribution`, `SargosFrequencyScaleBounds`,
`SargosLargeFrequencyContribution`, `SargosModelCorrelationBound`,
`SargosFiniteProcessAlgebra`, `SargosFiniteModelProcess` and
`SargosFiniteClosedProcess`.
All 26 public theorems have exact-signature regressions and explicit
axiom audits. Twenty additional fixtures cover zero/positive/negative
frequencies, actual large square-diagonal sextuples with quartic
difference plus or minus 2,108,304, their distinct ordered identities,
the correct width-H^3 bin and excluded adjacent bin, exact tau,
empty source support, zero weights and finite-scale arithmetic.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 981 production files, 1,455 scanned Lean
  files and 10,313 build jobs. The audit covers 7992 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14237 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-105350-e615b783.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_105812.log)
  and [manifest](../../logs/foundation_freeze_20260923_105812.json).
- All 1,476 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-finite-closed-process-20260923-105350-e615b783.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 363 nodes and 941 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `16d8526d9f8d52fdd3079b71e1c946dbefcfa44a1be75cc5037b79d5c1e72ba8` |
| Foundation log | `0b93a8830c0d75a4feba1df11004f664cc593754ad1d8998919df23c58bb4331` |
| Foundation manifest | `7bad50389130a03f97d69811cf6fa7702be83eb970b7106035a3c9b77f289079` |
| Finite closed-source inequality checkpoint JSON | `10a94678c8618d08b74bb57d65747fe3630fdddc0de3585339f8569c2f0f7688` |

All preceding explicit-source, support-core, physical-stationary/buffered,
uniform-jets/cutoff, stationary/Poisson, Legendre, base/strip and
energy-repair evidence is preserved with its historical hashes
and exact scope.

## Exact analytic C-process — previous checkpoint

EPZAE-10 is complete: the genuine analytic exponent-pair predicate is
preserved by all three exact A/B/C formulas. The new public theorem is

```text
ExponentPair.cProcess :
  ExponentPair k l ->
  ExponentPair (k/(12*(1+4*k)))
               ((11*(1+4*k)+l)/(12*(1+4*k))).
```

Its only mathematical input is the original exponent pair. It does not
assume a transformed estimate, optimized majorant or desired output pair.
The source formula is the C-process in the frozen paper's
`exp-process` lemma, citing
[Sargos 2003, Theorem 5](https://www.impan.pl/shop/publication/transaction/download/product/82873).

The proof now links every optimization variable to the original physical
parameters. With

```text
t0 = (5+15*k+5*l)/(2+3*k),
R = (T/N)^(-k/(1+4*k)) * N^((1+4*k-l)/(1+4*k)),
(Kc,Lc) = C(k,l),
```

Lean proves the exact balance identity and
`N^12/R = ((T/N)^Kc*N^Lc)^12`. In the high-height range
`N^t0 <= T`, the actual optimum satisfies
`R <= N^(2/3-1/100)` and `N^(13/3) <= T*R^3`.
A derived initial threshold makes the finite-process smallness and
secondary-term conditions hold. When `2 <= R <= M`, the proof selects
the actual natural integer `H = floor(R)`, proves `R/2 <= H <= R`,
and consumes `sargos_finite_closed_model_process` with every condition
discharged. The main and secondary terms, rounding loss and all epsilon
powers are bounded by the target twelfth power.

When `M < R` or `R < 2`, the literal closed source sum is controlled
by its actual `M+1` terms. For low heights `N <= T <= N^t0`,
three applications of the proved A-process to the genuine classical
pair `(1/2,1/2)` yield `(1/30,26/30)`; an exact threshold identity
compares its bound to the C-process target. Small N is absorbed into
a uniform constant, and reversed or singleton natural intervals are
handled with their actual source semantics.

`isExponentPairEstimateNonAsymptotic_cProcess` assembles all branches.
For every epsilon>0 and sigma>0, it chooses delta>0, derivative order
P>=1 and C>=1 before the phase, real scales and natural endpoints.
The existing non-asymptotic equivalence then gives
`ExponentPair.cProcess`. Neither a comparable-length source interval
nor a lower bound on k is imposed; k=0 remains included.

The printed A-bar-four witness/prefix-selection statement, its
constant-one finite-C^k formulation, and the separate exact real-scale
Robert–Sargos Lemma 5 convention are **not claimed as proved**.
They were previously listed as possible intermediate routes. The
implemented route instead uses the proved summed finite inequality and
the natural-rounded moment reduction. These unused stronger or
different-convention intermediates are not additional requirements of
EPZAE-10's unchanged acceptance test: the exact analytic C transformation
itself is now proved.

Fourteen production modules carry this final assembly:
`SargosCProcessParameters`, `SargosClassicalLowHeight`,
`SargosCProcessScale`, `SargosCProcessHighScale`,
`SargosCProcessLowComparison`, `SargosCProcessThresholds`,
`SargosCProcessIntegerChoice`, `SargosCProcessMainBalance`,
`SargosCProcessTrivialBranches`, `SargosCProcessMainError`,
`SargosCProcessBoundBudget`, `SargosCProcessTargetBudget`,
`SargosCProcessHighSource` and `ExponentPairCProcess`.
All 44 public theorems have exact-signature regressions and explicit
axiom audits. Another 22 fixtures check actual analytic output pairs
`(1/72,67/72)` and `(1/408,50/51)`, triangle boundaries, exact height
thresholds, zero-k scales, nonintegral rounding, empty/singleton source
intervals, zero epsilon and the low-height comparison.

Only EPZAE-10 changes aggregate status. EPZAE-11's D-process, remaining
beta-table rows, four advertised new pairs, zeta-growth/density bridges
and whole-project release remain open. These two auxiliary C-images
are not the four advertised `new-exp-pair` outputs.

Preserve the permanent counterexample, corrected two-witness powering,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 995 production files, 1,469 scanned Lean
  files and 10,327 build jobs. The audit covers 8,051 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,296 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-112323-d2b42d66.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_112654.log)
  and [manifest](../../logs/foundation_freeze_20260923_112654.json).
- All 1,490 physical proof/configuration/tooling hashes are identical
  before and after both runners. The fourteen modules and four
  integration files also have recorded normalized hashes. Full evidence
  is in the [checkpoint JSON](logs/tao-trudgian-yang-exact-c-process-20260923-112323-d2b42d66.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 365 nodes and 945 edges, with no duplicate/missing endpoints
or unclassified nodes. Of 42 aggregate checkbox states, only EPZAE-10
changes to checked (23 checked). Every other state is preserved.
The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `9f67c5e220830f06840a4f0026627a5ddb7e5bbe1ee18952aa254b181c8d26e9` |
| Foundation log | `39a559e34e419c88a375795054908f78bdf8173d74f970f4abf219d3d1a521af` |
| Foundation manifest | `f057fef758681cd21328e4083e3133dd9f7105666aead038950dc1707ad062b7` |
| Exact analytic C-process checkpoint JSON | `4b4c290adb588234c271f402eace6ba955171b1f536f5b6e6061bbbec4b636ca` |

All preceding C-process infrastructure and energy-repair evidence is
preserved with its historical hashes and exact scope.

## Native Heath-Brown exponent-pair family — previous checkpoint

The complete native Heath–Brown family is now proved for every integer
k>=3, with the exact source formula:

```text
exponentPair_heathBrown :
  3 <= k ->
  ExponentPair (2/((k-1)^2*(k+2)))
               (1-(3*k-2)/(k*(k-1)*(k+2))).
```

The input is the natural derivative order, not an assumed exponent pair,
derivative theorem or optimization certificate. The proof consumes the
already kernel-checked native kth-derivative theorem through
`isExponentSumBoundNonAsymptotic_heathBrown`.
The source is Heath–Brown,
[A new k-th derivative estimate for exponential sums via Vinogradov's mean value](https://arxiv.org/abs/1601.04493),
Theorem 2 and its proof, as frozen locally at v3. The arbitrary source
epsilon is already represented in the actual beta/exponent-pair
definitions; no fixed positive epsilon is left in the public pair.

For alpha in (0,1/2], set tau=1/alpha. The proof constructs an actual
natural j>=3 satisfying

```text
((j-1)^2+1)/j <= tau <= (j^2+1)/(j+1).
```

The construction uses the least natural index with a sufficient upper
endpoint and proves the lower endpoint from minimality. It does not
assume a cover or an order-selection oracle. Exact adjacent identities
and decreasing secant slopes prove that the selected local secant lies
below every fixed family secant. All three actual derivative-error
exponents are bounded on the selected interval. The reciprocal-scale
identity links these exponents to the native beta bound.

At alpha=0, the proved beta endpoint supplies the result. The new
`exponentPair_of_beta_bound_half` uses the already-proved exact
reflection identity and the candidate slope condition l-k>=1/2 to
supply the other half of the closed unit interval. The family satisfies
the entire exponent-pair triangle, including all boundary requirements.
The existing closed duality theorem then gives the actual analytic
exponent pair.

The separate D-transform work is deliberately narrower:
`SargosDProcessGeometry` proves denominator positivity, triangle and
slope, exact zero/half endpoint gaps, and the secondary-line comparison.
`sargosDProcess_pair_of_beta_bound` is **conditional** on its explicitly
displayed source beta estimate. It derives an exponent pair using
half-interval duality when 5*k-3*l+2>=0 and k+3*l>=2.
It is not a proof of the analytic D-process, nor of the Bourgain input
pair. In particular, the source's maximum cannot be dropped without
checking the comparison conditions. The original D-process theorem
remains EPZAE-11 OPEN. Its cited primary paper,
[Sargos 1995, Theorem 7.1](https://doi.org/10.1112/plms/s3-70.2.285),
has not yet been obtained in full; publisher pages restrict access,
and the available database statement does not supply its analytic proof.

Seven production modules are installed: `BetaHalfDuality`,
`SargosDProcessGeometry`, `HeathBrownPairParameters`,
`HeathBrownPairSecants`, `HeathBrownPairTriangle`,
`HeathBrownPairLocalBound` and `HeathBrownExponentPairs`.
All 41 public theorems have explicit axiom audits and exact-signature
regressions. Another 24 fixtures exercise actual family pairs for
k=3,4,5,6,10; genuine A/B/C images; D's exact rational formula and
negative endpoint gaps; joined interval endpoints; both directions of
global secant comparison; the actual order-selection theorem; and beta
at zero and one half. These fixtures do not assert the missing
D-process estimate.

EPZAE-10 remains complete with exact A/B/C transformations. No aggregate
checkbox changes in this checkpoint. The remaining beta rows, four
advertised new pairs, zeta-growth/density outputs and final reproduction
remain open. The new family is an analytic input, not a claim that
`new-exp-pair` has been completed.

The permanent powering counterexample, corrected two-witness theorem,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,002 production files, 1,476 scanned Lean
  files and 10,334 build jobs. The audit covers 8,108 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,353 total).
  All 41 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-114934-4d93bc9c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_115307.log)
  and [manifest](../../logs/foundation_freeze_20260923_115307.json).
- All 1,497 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-heath-brown-family-20260923-114934-4d93bc9c.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 369 nodes and 955 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(23 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `ecb3560a7df7a23e8dfdabff78887a953604e4c6ce7e547b9a702b933d399c15` |
| Foundation log | `c946c5e2a43756edf5f0958e6ee94e2d863679d9e938d4d4f6e7d221b62f88e7` |
| Foundation manifest | `b9f0e180ed02c13863cdd0cbc1e4766ba048b8bb7d569442f47379e7186a3f16` |
| Native Heath-Brown family checkpoint JSON | `56dba796833328511751e01b8b0e63dbb5ad6101b53008c0e92f612a8a815d3b` |

All preceding exact C-process and energy-repair evidence is preserved
with its historical hashes and exact scope.

## Large-value powering and subdivision — previous checkpoint

The source cardinality powering inequality is now proved by
`largeValueExponent_powering` for every natural k, including zero:

```text
1/2 <= sigma <= 1, tau >= 0
  -> LV(sigma,k*tau) <= k*LV(sigma,tau).
```

It consumes the actual cardinality witness of the corrected Lemma 62.
Neither fifth coordinate is constrained or scaled. The preserved singleton
pattern proves nonnegativity and the exact height-zero endpoint. A failed
uniform cardinality bound now yields genuine source patterns at unbounded
scales; their common compactness subsequence gives an actual energy-region
point with cardinality exponent above the failed candidate.
`isLargeValueBound_iff_region_cardinality` proves the full converse to the
existing region consumer. Infimum closure then supplies the exact
epsilon-loss boundary, not merely a strictly larger exponent.

`largeValueExponent_subdivision` proves both printed Huxley subdivision
inequalities for 0 <= tau <= tau'. Height enlargement preserves the actual
coefficients and ordinates. Subdivision sums actual localized patterns and
bounds the literal floor-bin count, with constants and radii selected
before the input pattern. Equal heights and height zero are included.
`isLargeValueBound_of_bounded_power_range` transfers a uniform bound from
the closed factor-two interval to every larger height.

`huxley_largeValueBound` and `largeValueExponent_le_huxley` now provide
the standalone uniform source bound
`LV(sigma,tau) <= max(2-2*sigma,4+tau-6*sigma)` on the full stated domain.
Their proof consumes `InCardinalityEnergyRegion.huxley_cardinality` through
the new actual-region converse. The powered Huxley estimate consumes the
corrected powering theorem. The mean-square exponent API and its short-height
and sigma=1 endpoint consequences consume the already-proved finite estimate.

Seven production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`LargeValueBoundClosure`, `LargeValueNonnegative`,
`LargeValueRegionWitness`, `LargeValuePowering`,
`LargeValueSubdivisionBounds`, `LargeValueElementaryBounds` and
`LargeValueHuxleyBound`. All 22 public theorem signatures have regressions;
16 further fixtures cover zero height/power, equal-height subdivision,
actual unchanged coefficients/ordinates, concrete mean-square/Huxley bounds
and an improved bound from the powered Huxley consumer.

EPZAE-18 remains OPEN: the random-sign/block lower bound and the resulting
exact sigma=1/2 identity still need their actual-pattern construction.
The standalone Huxley sub-obligation of EPZAE-19 is complete; the other
listed classical inputs remain open. No aggregate checkbox is changed.
The analytic D-process, remaining beta rows, four advertised new pairs,
zeta-growth/density outputs and whole-proof release obligations remain open.

The original Lemma 62 counterexample, corrected two-witness theorem,
Heath–Brown energy relation, exact optimization and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,009 production files, 1,483 scanned Lean
  files and 10,341 build jobs. The audit covers 8,145 target theorems,
  6,240 pinned-source theorems and five anchors (14,390 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-121240-f22694a3.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_121607.log) and
  [manifest](../../logs/foundation_freeze_20260923_121607.json).
- All 1,504 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-large-value-powering-20260923-121240-f22694a3.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 373 nodes and 967 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `78ce94ccf8da8c7b71ddf5a1cfab13f263b9604dadd2340afe2951aa97ae7241` |
| Foundation log | `2c0ba1844fdb0508e516a90d1cd5cd56df2dd963dd0bf4c0894c48785f3ed25d` |
| Foundation manifest | `95d1cddb04056f81d98367ae3ee003ea5596d58c1d4bd30737de5fd1cc3715b2` |
| Large-value powering checkpoint JSON | `2bcdcec509452366e80d1a952f9c17d76de290714658200582281f773bd40600` |

## Exact square-root large-value exponent — previous checkpoint

`largeValueExponent_half` now proves the exact source endpoint
`LV(1/2,tau) = tau` for every tau>=0. It constructs genuine normalized
Dirichlet polynomials and one-separated ordinate sets; neither the desired
large-value bound nor an extremal-pattern family is an assumption.

The finite sign samples are a literal recursively enumerated list.
Multiplicities are retained even when different sign choices produce the
same value. Their second moment is exactly the sum of squared block
weights times the number of samples. Their fourth moment is at most
three times the squared variance times that number. Finite Cauchy–Schwarz
gives the explicit one-twelfth lower-tail count. Double counting selects
one common sample with many large evaluations, rather than a different
coefficient sequence at every ordinate.

The input coefficient vectors are actual singleton indicators on the
closed dyadic integer interval. The proof establishes their pointwise
normalization and the actual additive evaluation map, so the selected
sample supplies one coefficient function with norm at most one at every
integer. Unit modulus of the true negative-sign Dirichlet phases gives
the exact variance. The lattice consists of natural integers between zero
and floor(T); its one-separation, interval membership and cardinality are
proved explicitly.

`exists_half_largeValuePattern` constructs, for every integer N>=2 and
every real T>0, a full source pattern with scale N, physical height T,
threshold sqrt((N+1)/2), and T<=12*card(W).
Taking N=n+2 and T=N^tau gives actual unbounded-scale patterns.
Constant-factor logarithmic sandwiches prove the value exponent 1/2 and
cardinality exponent tau. The already-proved common compactness subsequence
then yields `exists_half_largeValueEnergyRegion`, with its cardinality
coordinate exactly tau. Every uniform candidate is at least tau, and the
existing separation upper bound supplies the reverse inequality.

Twelve production modules are root-imported, explicitly audited and
included in the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`:
`FiniteSignSamples`, `FiniteSignMoments`, `FiniteMomentSelection`,
`FiniteSignLargeValues`, `FiniteSignCoefficients`,
`FiniteIncidenceSelection`, `FiniteSignEvaluationMoments`,
`FiniteSignSelection`, `FiniteRandomCoefficients`,
`LargeValueRandomLattice`, `LargeValueRandomPattern` and
`LargeValueHalfExponent`.
All 28 public theorem signatures have regressions. Sixteen additional
fixtures cover empty and repeated sign samples, concrete moment estimates,
coefficient normalization, lattice endpoint counts, the nonnegative-height
guard, a genuine N=2/T=1/2 pattern, and the exact exponent/region statements
at zero, fractional and large heights.

EPZAE-18 remains OPEN only for the remaining general lower-bound
construction: for 1/2<sigma<=1 prove
`min(2-2*sigma,tau) <= LV(sigma,tau)`.
The sigma=1 and tau=0 endpoints already follow from nonnegativity; the
remaining substantive step is the coherent finite-block construction for
1/2<sigma<1. Full subdivision, corrected cardinality powering, zero-height
and upper-bound APIs stay proved. No aggregate checkbox changes here.

The analytic D-process, remaining beta rows, advertised new pairs,
remaining classical/zeta/density interfaces and final release obligations
remain open. The original counterexample and all nine repaired Add-est
clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,021 production files, 1,495 scanned Lean
  files and 10,353 build jobs. The audit covers 8,193 target theorems,
  6,240 pinned-source theorems and five anchors (14,438 total).
  All 28 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-123925-4025ec63.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_124307.log) and
  [manifest](../../logs/foundation_freeze_20260923_124307.json).
- All 1,516 physical proof/configuration/tooling hashes are identical
  before and after both runners. The twelve modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-random-sign-half-exponent-20260923-123925-4025ec63.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 376 nodes and 973 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `70743307a6e67ce517eba10538a3400ec3967edf59448978ce93befe83dc0fd8` |
| Foundation log | `b1acc3b658adfdbaf3abf36b6db64a86f8e0a964e1e78193eb85186b85ab4164` |
| Foundation manifest | `c001a431ba6ce9debb027c3387ce894893b7a2526a8edfc826c89e73263c5539` |
| Square-root large-value endpoint checkpoint JSON | `ced7f32ec18dad2a04547143b58f714158dd8627a9acaf60a45cc07e7de82bfb` |

## Complete elementary large-value calculus — previous checkpoint

EPZAE-18 is now complete. Its original acceptance test is unchanged:
subdivision, lower/L2 bounds, obvious bounds and raising to a power all
have actual uniform source-pattern proofs with coefficient normalization.
The full source labels are `hux-sub`, `lv-lower`, `l2-mvt` and
`power-lemma`.

The remaining general lower bound is now proved by
`largeValueExponent_lower`:

```text
1/2 <= sigma <= 1, tau >= 0
  -> min(2-2*sigma,tau) <= LV(sigma,tau).
```

This includes all closed endpoints and is stronger in domain than the
printed lower-bound clause for sigma>1/2. The separate sharp endpoint
`largeValueExponent_half` remains LV(1/2,tau)=tau for every tau>=0.
No Montgomery equality is asserted beyond the proved ranges.

The new proof uses q=floor(N/L) actual disjoint natural blocks
[N+j*L,N+(j+1)*L), all contained in the closed source support [N,2N].
Each block has exactly L indices, and q*L>=N/2.
The coefficient vectors are their actual indicators, with pointwise sum of
norms at most one. The unused remainder and the right endpoint may carry
zero coefficients; the source support and its closed convention are unchanged.

`dirichletPhase_block_variation` proves the actual negative-sign phase bound
from the exact complex exponential identity and log(n/a)<=n/a-1.
For 0<=t<=N/(2L), `largeValueBlock_sum_lower` gives norm(block sum)>=L/2.
Thus the literal block-family variance is at least N*L/8.
The finite common-sign selection theorem consumes this variance and proves
one normalized coefficient sequence, shared by all selected ordinates.

`exists_block_largeValuePattern` constructs a full source pattern for
every N>=2, 1<=L<=N and T>0, with

```text
V = sqrt(N*L/16);
min(T,N/(2L)) <= 12*card(W).
```

The choice L=floor(N^(2*sigma-1)) is justified by exact real/natural
inequalities, including its positive lower bound. It gives
N^sigma/8<=V<=N^sigma and
N^min(tau,2-2*sigma)<=24*card(W) when T=N^tau.
These constants are uniform and derived before choosing the physical
pattern. Along N=n+2 the time/value logarithmic exponents converge to
tau/sigma. An actual common energy-region subsequence supplies a cardinality
coordinate rho>=min(2-2*sigma,tau). The existing uniform-bound consumer
forces every candidate B to be at least this lower bound, and the exact
least-exponent definition supplies the public statement.

The source-completion map is:

| EPZAE-18 clause | Public consumer |
| --- | --- |
| Both subdivision inequalities | `largeValueExponent_subdivision` |
| General lower bound | `largeValueExponent_lower` |
| Sharp sigma=1/2 endpoint | `largeValueExponent_half` |
| L2 mean-square upper bound | `largeValueExponent_le_meanSquare` |
| Obvious upper bound | `largeValueExponent_le_tau` |
| Every natural power, including zero | `largeValueExponent_powering` |

Powering still consumes the corrected cardinality witness, including its
actual convolution, divisor normalization and dyadic selection chain.
It does not use a scaled fifth coordinate. Subdivision still uses actual
localized patterns and its literal floor-bin count.

`LargeValueElementaryCalculus` additionally assembles the exact known
equality ranges: tau<=2-2*sigma, the mean-square range tau<=1, and the
Huxley range tau<=4*sigma-2. `largeValueExponent_one` proves
LV(1,tau)=0 for every tau>=0 by the proved bounded-range powering consumer.

Ten production modules are root-imported and included in the PowerShell
inventory behind `run_tao_trudgian_yang_build.bat`:
`DirichletBlockPhase`, `FiniteBlockCoefficients`,
`LargeValueBlockGeometry`, `LargeValueBlockCoherence`,
`LargeValueBlockVariance`, `LargeValueBlockPattern`,
`LargeValueBlockExponents`, `LargeValueLowerPatterns`,
`LargeValueLowerBound` and `LargeValueElementaryCalculus`.
All 25 public theorem signatures have explicit audits and regressions.
Twenty additional fixtures exercise zero-length empty blocks, closed
support, uncovered remainders, exact floor endpoints, phase coherence at
the height boundary, actual region witnesses, lower-bound and equality
crossovers, sigma=1 at arbitrary height, and the distinct sharp
sigma=1/2 behavior.

EPZAE-18 is the only newly checked aggregate item.
EPZAE-19 remains OPEN for its other classical inputs; the architecture
now separates that obligation from the completed elementary calculus.
The analytic D-process, remaining beta rows, advertised new pairs,
remaining zeta/density interfaces and final release obligations stay open.
The permanent counterexample and all nine repaired Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,031 production files, 1,505 scanned Lean
  files and 10,363 build jobs. The audit covers 8,245 target theorems,
  6,240 pinned-source theorems and five anchors (14,490 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-130446-48e1dea6.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_131219.log) and
  [manifest](../../logs/foundation_freeze_20260923_131219.json).
- All 1,526 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-elementary-large-values-20260923-130446-48e1dea6.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 381 nodes and 986 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. Only EPZAE-18 changes among the 42 aggregate
checkboxes (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `0783b08c67603ae94d4e540b590f2f2679707ac65e98a01b62b60e93fbf9b1e1` |
| Foundation log | `a1466ec84acc5f36691b0cf5eae504fe9b9cf878af763b09216fcab66dc13936` |
| Foundation manifest | `b97c52198cd9f545aa0ce49ef07c83f9839e368d7b9c13ba02513b8ef90ab9e8` |
| Complete elementary LV calculus checkpoint JSON | `6a2a917245cf62445b10b4a1017a2b0058be733f71adc0fcc6e4efaf1f29db0b` |

## Actual Type-I cardinality transfer — previous checkpoint

The cardinality side of `zero-from-large` now has a complete uniform
Type-I source consumer. This is a proved transfer from explicit upstream
`IsZetaLargeValueBound` hypotheses, not an unconditional zero-density
theorem. EPZAE-24 remains OPEN.

`cardinality_eq_sum_color_fibers` counts every fiber of the original finite
index type. `cardinality_le_color_count_mul` sums the corresponding bounds.
Equal ordinate values are never collapsed here. The two exact pattern
conversion theorems use proved one-separation to show that the finite
ordinate image has exactly the original index cardinality. Thus analytic
multiplicity is retained in the zero-copy domain until separation justifies
passing to an image.

`LargeValueUniformity` proves general and zeta compact-range uniformity.
A genuine finite open subcover chooses one constant and one positive
threshold window before the pattern. It includes finite-scale excursions
past both interval endpoints and lowers the actual threshold without
changing any coefficient or ordinate. The resulting bound is
`card(W) <= C*T^B*N^epsilon`.

The Type-I expanded slab [T/2,4T] is covered by three actual positive zeta
slabs. No ordinate translation or coefficient twist is used. Every color
fiber is counted, giving the literal factor 3. Actual Fourier deweighting
then supplies a bounded shifted ordinate for each original index.
The proved unit-bin occupancy estimate and parity/rank coloring separate
every shifted fiber.

The complete cardinality loss is

```text
K(d) = 3 * card(ZMod 2 x Fin(ceil(2d+2)+1))
     <= 24*(1+d).
```

It is linear in the displacement. If 0<=theta<eta and
d<=2*pi*T^theta, then eventually K(d)<=T^eta.
No energy upper bound, square/cube conversion or selection of only four
energy classes substitutes for counting all original indices.

`classicalTypeI_uniform_source_cardinality_bound` consumes the actual
sharp cutoff polynomial. Its positive threshold forces N<=6T;
the Fourier order, normalized threshold and all loss absorption are proved.
The zeta hypotheses select delta before the slightly shifted source line s
and threshold exponent D. The resulting bound is
`card(index type) <= C*T^(B+epsilon)`.

`classicalTypeI_uniform_source_class_cardinality_bound` applies this to a
literal Type-I branch/scale fiber of the shifted zero multiset. Its natural
scale is `2^r*floor(T^a)`, with the floor loss proved. Largeness and
one-separation follow from the genuine branch label and refined color.
No detached source-polynomial family or final class-count estimate is
assumed.

Nine production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`CardinalityPartition`, `ClassicalPatternCardinality`,
`LargeValueUniformity`, `ClassicalTypeICardinalityTransfer`,
`ClassicalTypeIFourierCardinality`, `ClassicalTypeICardinalityLoss`,
`ClassicalTypeICardinalityUniformity`, `ClassicalTypeISourceCardinality`
and `ClassicalTypeISourceClasses`.
All 15 public theorem signatures have regressions. Eighteen additional
fixtures cover empty/constant color fibers, analytic-copy multiplicity,
coincident-ordinate exclusion, all positive-slab boundaries, exact rounded
coloring costs and strict subpower absorption.

The source-cardinality theorem uses zeta hypotheses on [1,1/a] (or
[1,2/a] after the natural floor loss). It does not silently replace the
paper's final tau>=2 contract. Remaining: actual Type-II cardinality,
multiplicity-preserving slab/global assembly, the exact endpoint-two
reflection bridge and the sup/limsup density statement and corollaries.
No aggregate checkbox changes at this checkpoint.

EPZAE-18, the corrected cardinality/energy powering, the independent rho/k
and rho-star/k witnesses, the Heath--Brown energy relation, all nine repaired
Add-est clauses and the permanent singleton counterexample remain proved
and unchanged. Other classical, exponent-pair, zeta/density and release
obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,040 production files, 1,514 scanned Lean
  files and 10,372 build jobs. The audit covers 8,269 target theorems,
  6,240 pinned-source theorems and five anchors (14,514 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-132951-4bd2396c.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_133317.log) and
  [manifest](../../logs/foundation_freeze_20260923_133317.json).
- All 1,535 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-type-i-cardinality-20260923-132951-4bd2396c.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 386 nodes and 997 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `07669f6efa86c03672e08083ff51ae9f5755da595f54e5e331966a11a49d49be` |
| Foundation log | `c147a6f898b69e7f9e0e7d655b208cdef7646c841f1ae95ce4cf323d46af4fe1` |
| Foundation manifest | `138f30b463d9ce1b526dec023dc4cb50d539fe12f2c8716b6fe4f2fba917991e` |
| Actual Type-I cardinality checkpoint JSON | `5bf2d002a4881cba1b02b1abdab1c037e828b68f2bf8b877f38db88ec1e85f6a` |

## Actual endpoint-one cardinality-to-density transfer — previous checkpoint

`isZeroDensityBound_of_uniform_largeValue_bounds` now proves the complete
intermediate cardinality transfer:

```text
1/2 < sigma < 1, B >= 0, tau0 > 0;
LV_zeta bound B*tau for every tau >= 1;
LV bound B*tau for every tau >= tau0
  -> IsZeroDensityBound sigma (B/(1-sigma)).
```

The conclusion uses the actual multiplicity-weighted symmetric zero
rectangle and the original epsilon--delta quantifier order. The large-value
predicates are explicit, genuinely upstream inputs, not assumed zero-count
or detector-family estimates. The source statement's stronger lower zeta
endpoint 2 remains an independent obligation. EPZAE-24 is still OPEN.

`ClassicalTypeIICardinalityPatterns` packages the actual sharp mollifier,
with its divisor majorant and exact normalized threshold. It proves that the
pattern ordinate count equals the complete original zero-copy class count.
The native factory discharges the coefficient majorant. The uniform
Type-II consumer chooses its threshold window before the source real-part
line and consumes the literal dyadic cutoffs, scale label, expanded height
and one-separation.

`ClassicalSlabCardinalityClasses` extracts the genuine shifted source
branch/scale for every zero. It refines this by all parity/rank colors.
The zero count is exactly the sum of the cardinalities of these fibers;
no selected four-class energy witness replaces this partition.
The outer cardinality cost obeys `K*T^(3*theta)`, with the actual local
analytic-multiplicity cap and both logarithmic dyadic counts accounted for.

`classicalSlabZeroCount_bound_of_uniform_largeValue_bounds` assembles the
Type-I and Type-II cardinality consumers. The source cutoff exponents,
real-part shift, Fourier displacement and threshold losses are selected in
the required dependency order. Empty branch labels have empty fibers.
The conclusion is an actual positive-slab estimate for
`zeroCountRect (sigma-delta) 1 T (2*T)`.

`ZeroCardinalityRestrictions` injects indexed subfamilies into containing
weighted zero sets without discarding copy numbers. Negative ordinates are
transported through the proved zero-copy conjugation equivalence, including
equality of analytic vanishing orders. The symmetric assembly counts every
signed dyadic color, retains the terminal partially occupied slab, and
absorbs the actual finite low-height zero count. The logarithmic number of
colors is bounded by any positive height power.

The final predicate follows by splitting the arbitrary epsilon loss between
the positive-slab estimate and symmetric assembly, then choosing one global
constant and a positive real-part shift. No root of an energy estimate, zero
count oracle or unproved polynomial family is used.

Eight production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalTypeIICardinalityPatterns`, `ClassicalTypeIICardinalityTransfer`,
`ClassicalSlabCardinalityClasses`, `ClassicalSlabCardinalityLoss`,
`ClassicalSlabCardinalityTransfer`, `ZeroCardinalityRestrictions`,
`ZeroCardinalityAssembly` and `ZeroCardinalityTransfer`.
All 14 public theorem signatures have regressions. Sixteen additional
fixtures check analytic-copy counts, empty weighted sets, both signed slab
boundaries and excluded exterior points, strict subpower losses, and actual
unconditional density consequences obtained by supplying the proved obvious
large-value bounds.

Remaining within EPZAE-24: the exact sup/limsup exponent formulation,
the source's zeta endpoint-two reflection reduction, and all source
corollaries. The current endpoint-one predicate is not a substitute for
that unchanged aggregate acceptance contract. No aggregate checkbox changes.

The permanent counterexample, corrected independent cardinality/energy
powering witnesses, Heath--Brown energy relation, all nine repaired Add-est
clauses and complete EPZAE-18 elementary calculus remain intact.
Other classical, exponent-pair, zeta/density and release obligations stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,048 production files, 1,522 scanned Lean
  files and 10,380 build jobs. The audit covers 8,286 target theorems,
  6,240 pinned-source theorems and five anchors (14,531 total).
  All 14 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-134332-f1498f0d.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_134658.log) and
  [manifest](../../logs/foundation_freeze_20260923_134658.json).
- All 1,543 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-endpoint-one-density-20260923-134332-f1498f0d.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 392 nodes and 1,011 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `1a9fa1c00b696dd2275c8dd735a155b1a591d0605595f0176d1bdb60a8c94d18` |
| Foundation log | `3f2c11a35dd4372adc134f5cd61511e1156fb9d0ed439a12e1fc544e5b989a45` |
| Foundation manifest | `fe038056364cc4a4c36e536cb3bfe6463390a0a86f536ec308bf085f40c8477c` |
| Actual endpoint-one density checkpoint JSON | `916edf494f02b4e269261c692ee230aaaec26f64b5e6f4aaec34723ef0a3d5d6` |

## Endpoint-one density envelopes and sharp zeta nonexistence — previous checkpoint

The actual endpoint-one cardinality-to-density predicate now has its
supremum/limsup formulation and a bounded-range corollary using corrected
cardinality powering. The printed source's stronger zeta endpoint two
remains OPEN, so EPZAE-24 is not checked off.

For 1/2 < sigma < 1, the proved intermediate inequality is

```text
A(sigma)*(1-sigma)
  <= max(sup_{tau >= 1} LV_zeta(sigma,tau)/tau,
         limsup_{tau -> infinity} LV(sigma,tau)/tau).
```

`ZeroCardinalityExponentTransfer` consumes the actual Type-I/II
multiplicity-weighted zero-count transfer. The general-LV singleton lower
bound makes the envelope nonnegative. Each real number above it supplies
all zeta hypotheses and eventually all general hypotheses. EReal division,
infinite values and the strict real-part domain are handled explicitly.

The infimum-to-uniform zeta bound is reused from the existing
`ZetaLargeValueDiscreteness` module. `ZetaLargeValueBoundClosure` is only
a compatibility import, not a new proof. A duplicate draft definition and
duplicate audit entries were removed before this verification checkpoint.
The original canonical declarations retain their explicit audit.
Minus infinity is allowed; no false nonnegativity of zeta exponents is used.

`ZeroCardinalityBoundedRanges` reduces the necessary inputs to

```text
LV_zeta(sigma,tau) <= B*tau for 1 <= tau < tau0;
LV(sigma,tau)      <= B*tau for tau0 <= tau <= 2*tau0;
B >= 0 and tau0 > 0
  -> IsZeroDensityBound sigma (B/(1-sigma))
  -> A(sigma) <= B/(1-sigma).
```

The long general range uses the corrected cardinality-powering witness.
At and beyond tau0, the general bound also bounds zeta patterns.
The short interval is half-open; the general interval includes both
endpoints. For tau0 < 1 the short interval is empty. The disproved
s-prime/s scaling and the independent energy witness are not used here.

`ZetaSecondDerivativePatterns` proves the full sharp-interval range

```text
1/2 < sigma <= 1, 1 <= tau < 2*sigma
  -> every sufficiently large admissible zeta pattern has no ordinates
  -> LV_zeta(sigma,tau) = minus infinity.
```

It consumes the literal-polynomial bound
`2 + 200*sqrt(t) + 12*pi*N/t`. One positive parameter window retains
both strict gaps tau < 2*sigma and tau < 2; the threshold absorbs the
factor two in [T,2T]. Arbitrary real cardinality/energy bounds and
pointwise strict power saving on every sharp integer interval follow.
Earlier restricted-range results and their consumers are unchanged.

The three new analytic modules and the compatibility import are
root-imported and included in the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`. Nine new public theorem signatures
and two reused closure signatures have exact regressions. Twenty further
fixtures cover minus-infinity closure, interval boundaries, empty ranges,
endpoint nonnegativity, strict exclusions and numerical density
consequences from the native Huxley theorem. These include
`IsZeroDensityBound (3/4) (8/3)` and `A(4/5) <= 5/2`;
they are consequences, not new best-known estimates.

Remaining within EPZAE-24: actual source reflection reducing the zeta input
endpoint from one to two, and the exact source corollaries. The proved
endpoint-one results are labeled intermediates, not replacements for that
unchanged acceptance contract. No aggregate checkbox changes.

The permanent counterexample, corrected independent cardinality/energy
powering witnesses, Heath--Brown energy relation, all nine repaired Add-est
clauses and complete EPZAE-18 elementary calculus remain intact.
Other classical, exponent-pair, zeta/density and release obligations stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,052 production files, 1,526 scanned Lean
  files and 10,384 build jobs. The audit covers 8,297 target theorems,
  6,240 pinned-source theorems and five anchors (14,542 total).
  All nine new public theorems and both reused closure theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260923-141622-b8317f2e.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_142024.log) and
  [manifest](../../logs/foundation_freeze_20260923_142024.json).
- All 1,547 physical proof/configuration/tooling hashes are identical before
  and after both runners. The four module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-endpoint-one-envelope-20260923-141622-b8317f2e.json).

Owner HEAD at this checkpoint is `a8bdea22a024a84924a0c4accd6af656af969700`.
The owner advanced HEAD during development; no agent commit or push was
performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 395 nodes and 1,018 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `6120c8722485592fcc149eabc20d73962da7a0080dbdb798e5896e104dc2b0bb` |
| Foundation log | `45c823114338573974f317fe3ed8bc6371263b0326d07e89edd149812d3788c4` |
| Foundation manifest | `4bb4e5c60d3af06b89fbc972ab03a2ed7bf4416f73384e9db113cb2496ea3985` |
| Endpoint-one envelopes and sharp zeta checkpoint JSON | `456dd717abac6288c92379142ad70aacfdb9cefbbb097ded22852573fd1b474b` |

## Positive reflected source and Fourier entry — previous checkpoint

The actual interior Type-I source now produces a separated reflected family
at genuine positive ordinates, with literal coefficients, physical scales,
thresholds and cardinality loss. Its output is then explicitly consumed by
bounded coefficient-one Fourier extraction. This is proved analytic entry
work; the endpoint-two density transfer remains OPEN.

`extract_positive_ordinate_reflected_block` treats both retained Poisson
signs. For the negative sign it uses the actual isometry v -> 3*T-v.
The finite image has exactly the same cardinality and remains one-separated.
Both signs yield positive ordinates in [T/2,5T/2] and the exact loss

```text
card(W) <= 2 * (2 * (2*ceil(H)+1)) * clog(2,M) * card(U).
```

The conclusion has the literal real normalized reflected coefficients.
It does not merely supply, independently for each point, a norm-equivalent
positive ordinate without separation information.

`eventually_interior_source_positive_reflected_data` invokes the native
actual smooth-source Poisson reflection, kernel and tail bounds. It retains
the source dyadic scale Q, natural dual cutoff M, detector threshold and
normalized reflected threshold L. The selected scale is exactly 2^j < M.
The physical logarithmic scale lies between 1/(1/2+d) and the proved fixed
upper bound. Both the full source-dependent lower bound for L and
`T^g/Cref <= L` are exported, with g > 0. No detached exponent or
assumed cardinality estimate is substituted.

The coefficient identities prove, on the actual positive natural support,

```text
normalizedReflected(sigma,M,n)
  = M^(-sigma) * classicalFixedLine(M,-sigma,n).
```

The exact polynomial and norm identities retain this factor. In particular,
M^sigma times the reflected norm equals the fixed-line norm when M > 0.
The cutoff, its right endpoint and the excluded n=0 term are handled
explicitly. Nonnegative sigma is not silently dropped from the native
unit-coefficient bound.

`exists_classicalReflected_explicitBoundedOrdinate_family` applies the
proved arbitrary-order Fourier extraction at real parameter -sigma.
For reflected threshold L it uses sourceV=M^sigma*L in both the radius
and the coefficient-one threshold

```text
sourceV / (4*N^sigma*classicalTypeIFourierL1(-sigma)).
```

The Fourier step retains its input index type: the selected reflected
family. Its full perturbation-energy inequality is also exported; neither
powering nor the disproved s-prime/s scaling is used here. This does not
transfer energy from the entire original source W through the earlier
cardinality-only subset selection. That all-index energy bridge remains open.

`eventually_interior_source_positive_reflected_fourier_data` unpacks the
actual reflection factory and invokes this Fourier theorem on that same
selected block and family, for every derivative order k > 1. Thus the
factory-to-Fourier edge is a kernel-checked composition, not an inferred
relationship between compatible-looking standalone statements.

Five production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedCardinality`, `ClassicalReflectedSourceData`,
`ClassicalReflectedCoefficients`, `ClassicalReflectedFourier` and
`ClassicalReflectedSourceFourier`.
Eight exact public signatures and twelve further fixtures check literal
coefficient values, cutoff boundaries, the negative-sigma guard, exact
normalization, sign reversal, interval preservation and image cardinality.

Remaining: absorb the actual Fourier radius and threshold losses; re-separate
the shifted family; apply compact-range zeta bounds near tau=2; and connect
all source branches back to the multiplicity-weighted zero-copy partition.
The final endpoint-two cardinality/energy transfers and source corollaries
are not claimed. EPZAE-21/24/33 and all aggregate checkbox states are unchanged.

The endpoint-one density results, full second-derivative zeta nonexistence,
EPZAE-18, corrected cardinality/energy powering, Heath--Brown energy relation,
all nine repaired Add-est clauses and permanent counterexample remain intact.
Other classical, exponent-pair and release obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,057 production files, 1,531 scanned Lean
  files and 10,389 build jobs. The audit covers 8,309 target theorems,
  6,240 pinned-source theorems and five anchors (14,554 total).
  All eight new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260923-214023-ae130de3.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_214539.log) and
  [manifest](../../logs/foundation_freeze_20260923_214539.json).
- All 1,552 physical proof/configuration/tooling hashes are identical before
  and after both runners. The five module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-positive-reflection-20260923-214023-ae130de3.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
The owner advanced HEAD during development; no agent commit or push was
performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 399 nodes and 1,027 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `7ea85dbe061c5e4bda701c4bee4292dffa566ca66048d5d52bcc5d5157c1a366` |
| Foundation log | `69c9068e6408691ffee3097a86b4fad939f476586e676fc60b1c3c6e93bf873f` |
| Foundation manifest | `53799b1b2ee4b7ad2c9547470b223dae5a62adc3de89209e8c1c13128d24a106` |
| Positive reflected-source Fourier checkpoint JSON | `5fa0ae2c6944484ae51d4cdb7c78fd758f1a1bad02d1f41802df8951088f69ef` |

## All-index reflected source and uniform Fourier radius — previous checkpoint

The actual interior Type-I source now passes through reflection and
coefficient-one Fourier extraction on its original finite index type.
Every index, including coincident ordinates and multiplicity copies, is
retained. This closes the all-index displacement bridge missing from the
previous selected-subset construction; it does not yet prove the final
endpoint-two cardinality or energy transfer.

Reality of the literal normalized reflected coefficients gives exact norm
symmetry for the full wide polynomial. `exists_positive_reflected_shift`
therefore merges both native Poisson sign alternatives before any dyadic
choice. `exists_reflected_bounded_dyadic_family` chooses a bounded shift
and an actual dyadic label for every original index. It proves

```text
E_1(W) <= (4*ceil(1+4*H)+6) * E_1(W').
```

No large-cardinality subset is used to stand in for the original energy.
The source consumer uses a finite image only to obtain the native
pointwise analytic reflection and pulls the result back to every index.
It exports shifts at most T^d, positive ordinates in [T/2,5T/2],
the literal reflected coefficients and the full source-energy inequality.

`eventually_interior_source_indexed_reflected_data` also exports the
actual common threshold L, its exact source-dependent lower bound,
T^g/Cref <= L with g>0, and for each retained N=2^label:
1<N<M and logarithmic scale between 1/(1/2+d) and the fixed upper bound.
A singleton norm estimate is used only pointwise to bound L by N;
the original indexed family remains intact in the energy conclusion.

For sigma>=0, N<=M and L>=1, the factor M^sigma cancels from the
Fourier-radius base estimate. The theorem
`exists_order_eventually_classicalReflectedFourierRadius_le_rpow`
chooses one derivative order k>1 before T,M,N,L, and bounds the actual
radius by T^theta for every theta>0.

`eventually_interior_source_indexed_fourier_data` consumes the actual
indexed reflection output, derives L>=1 and N<=T, and applies
coefficient-one extraction at each actual dyadic length with that same k.
It retains the original index type and labels, the literal cutoff
Ioc(N,min(2*N,M)), the exact normalized threshold

```text
M^sigma * L / (4*N^sigma*classicalTypeIFourierL1(-sigma)),
```

and the uniform radius estimate. Its combined displacement is
D=T^d+2*pi*T^theta; its energy conclusion is for the entire original source:

```text
E_1(W) <= (4*ceil(1+4*D)+6) * E_1(W_final).
```

Six production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedRadius`, `ClassicalReflectedIndexed`,
`ClassicalReflectedIndexedSource`, `ClassicalReflectedIndexedGeometry`,
`ClassicalReflectedIndexedFourier` and
`ClassicalReflectedIndexedSourceFourier`.
Nine exact-signature regressions and twelve further fixtures cover both
signs, coincident-index energy versus set-image cardinality, empty input,
combined displacement, dyadic endpoints, the near-two scale and an
instantiated uniform-radius theorem.

Remaining: convert the exported threshold to the required N-power bound;
separate every shifted color without losing multiplicity; apply uniform
zeta bounds near tau=2; and assemble the lower-scale, near-endpoint and
terminal source branches with the actual zero-copy partition.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The endpoint-one transfers, corrected cardinality/energy powering,
Heath--Brown relation, all nine repaired Add-est clauses and the permanent
counterexample are preserved. Other whole-proof obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,063 production files, 1,537 scanned Lean
  files and 10,395 build jobs. The audit covers 8,329 target theorems,
  6,240 pinned-source theorems and five anchors (14,574 total).
  All nine new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-003630-1cb927cd.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_004011.log) and
  [manifest](../../logs/foundation_freeze_20260924_004011.json).
- All 1,558 physical proof/configuration/tooling hashes are identical before
  and after both runners. The six module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-all-index-reflection-20260924-003630-1cb927cd.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 403 nodes and 1,036 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `8605540605c3896dc7405085e9f87d2aa4c8ba172586af7e174d702cf8f53eaa` |
| Foundation log | `a97b532f4b9f8bfd15ff6af4fe56bd6e71a2370ce29f0e926faa68e53abcbdee` |
| Foundation manifest | `ed5cea25ea707a350771959ea6333263389180a262f896efb7e0d95bc3d94183` |
| All-index reflected-source checkpoint JSON | `cc0380bf558228be3c32b01fa298748c65ee383eb394c1e280a77949b5964f98` |

## Fixed-line interior reflected source bounds — previous checkpoint

The fixed-line interior smooth Type-I branch now has uniform
C*T^(B+epsilon) bounds for both its cardinality and its full indexed
additive energy. These are deductions from the intended compact zeta
large-value or zeta-energy hypotheses on [2,U], where
U=2/((sigma-1/2)/2), with 1/2<sigma<1 and B>=0.
The actual source branch has 1<tau<2, Q=2^r*Y, r>=2,
Y+1<=Q/2, 2*Q<=A, and A=floor(sharpZetaCutoff(T)).
Other branches and the global endpoint-two transfer remain OPEN.

The two source-facing consumers are:

- `classicalReflected_uniform_interior_source_cardinality_bound`;
- `classicalReflected_uniform_interior_source_energy_bound`.

For every epsilon>0 they choose a positive perturbation exponent d and
C>=1 before u, the physical scales and the indexed family. For each
0<=u<=d one height threshold then works for every actual source family.
The conclusion is respectively card(ι)<=C*T^(B+epsilon) or
E_1(W)<=C*T^(B+epsilon). All original indices are retained, and the
hypothesis is the literal smooth source-polynomial largeness condition,
not a supplied replacement family or assumed cardinality/energy estimate.

The threshold normalization keeps the full source-dependent exponent.
Its comparison with the actual upper length scale loses at most u+3*d.
The favorable M^sigma/N^sigma factor is proved to be at least one for
N<=M and sigma>=0. A uniform absorption theorem uses the exact identity
T=N^(log_N T), the upper logarithmic scale U and the explicit small-loss
condition U*(u+3*d)<=delta/2. The actual source consumer derives the
coefficient-one lower threshold N^(sigma-delta) from these facts.

Four literal positive height intervals cover [T/4,4*T], with lower
heights T/4,T/2,T,2*T. Their logarithmic heights are within the chosen
window of [2,U]. The compact zeta constants are chosen before the
physical scales and families. No height translation or coefficient twist
is used. All four cardinality fibers are counted; the energy deduction
uses the proved four-fiber energy inequality, not a cardinality-selected
subset. The corresponding explicit height costs are 4 and 2304.

The bounded perturbation of the original separated family supplies its
actual unit-bin multiplicity bound. The coloring is refined by the actual
dyadic label. Every occupied color has the required scale and threshold;
empty fibers and empty index/label types are handled explicitly.
Both resulting bounds are for the entire original indexed source family.

The physical consumer derives the large-length, near-two and positive
window conditions from the source factory. Its explicit logarithmic and
ceiling losses are then bounded: the cardinality loss is at most
Kcard*T^(2*d), and the energy loss at most Kenergy*T^(9*d).
The actual dual cutoff is proved to lie below the sharp source cutoff.
Choosing d within the threshold, scale-window and epsilon budgets
therefore yields the two stated source bounds with no residual radius,
normalization, coloring or logarithmic-loss hypothesis.

Eleven new production modules are root-imported, explicitly audited and
covered by the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`:
`ClassicalReflectedThreshold`, `ClassicalReflectedThresholdAbsorption`,
`ClassicalReflectedNormalizedSource`, `ClassicalReflectedHeightWindows`,
`ClassicalReflectedCompactTransfer`, `ClassicalReflectedColorGeometry`,
`ClassicalReflectedColorTransfer`, `ClassicalReflectedPhysicalWindows`,
`ClassicalReflectedSourceTransfer`, `ClassicalReflectedLoss` and
`ClassicalReflectedSourceBounds`.
Twenty-two exact public signatures and twenty additional fixtures check
closed height boundaries, literal color assignments, exponent-margin
endpoints, exact finite losses, empty cutoffs and uniform physical scale
conditions. Standard logical axioms are permitted; no project axiom or
admitted proof is introduced.

Remaining: match the detector's actual source-line and threshold
conventions to this fixed-line branch; handle the lower-scale,
near-endpoint and terminal source cases; and assemble every source and
zero-copy color with actual analytic multiplicities. The exact endpoint-two
cardinality/energy transfers and final corollaries are not claimed.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.

The endpoint-one transfers, corrected two-witness powering, Heath--Brown
relation, all nine repaired Add-est clauses and the permanent singleton
counterexample remain intact. The full EPZAE-00--41 goal is still open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,074 production files, 1,548 scanned Lean
  files and 10,406 build jobs. The audit covers 8,374 target theorems,
  6,240 pinned-source theorems and five anchors (14,619 total).
  All 22 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-014058-1fb323df.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_014526.log) and
  [manifest](../../logs/foundation_freeze_20260924_014526.json).
- All 1,569 physical proof/configuration/tooling hashes are identical before
  and after both runners. The eleven module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-interior-source-20260924-014058-1fb323df.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 409 nodes and 1,051 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `cf6b64439782d9f2f2d40d168a8fa6e263be3c978c7d92639eb6f3bdf2290566` |
| Foundation log | `1fd0d0cc878c54d6142a9eb6587569d99f0a125878ca7c502ef78ed70c88c98e` |
| Foundation manifest | `860d8506c01055e7f4613a83ea4c424b18c5013bcae5769f831620035c751bd8` |
| Fixed-line interior-source checkpoint JSON | `1353a4c481f1a336cea62d8de775197b3a811cb640ed0e98cc5850b698687a40` |


## Global detector entry and shifted-line interior bounds — previous checkpoint

Seven production modules add thirteen audited public theorems and twenty
semantic regressions (thirteen exact signatures and seven boundary/empty
or multiplicity fixtures).

The actual Type-I detector's full long-tail assertion now supplies global
smooth labels on every original multiplicity-copy index. These are the
global `Y,A` blocks, not the local two-block smoothing of one sharp
polynomial. The exact cardinality partition and four-fiber energy
inequality are retained; no cardinality-selected subfamily replaces the
energy source.

`classicalReflected_uniform_shifted_line_source_cardinality_bound` and
`classicalReflected_uniform_shifted_line_source_energy_bound` choose one
line window, displacement exponent and constant before the source line
and threshold loss. They use genuine upstream zeta large-value bounds on
`[2, 8/(sigma-1/2)]`. The two
`classicalTypeI_global_interior_source_*_bounds` theorems consume the
actual detector classes and bound every legal interior fiber with
`1 < tau < 2` by `C*T^(B+epsilon)`.

Terminal blocks are impossible pointwise, hence their entire index types
are empty. `eventually_classicalTypeI_global_source_classification`
additionally proves that every occupied global label is either one of the
two bottom blocks or an interior block with actual physical `tau > 1`.
The source-line parameter order is non-circular: the common window and
loss budget precede the later Type-II-dependent choice of shifted line.

Still open: estimates for the bottom blocks and direct interior
`tau >= 2`, their joint loss budget and full multiplicity-copy slab
assembly, and the printed endpoint-two density/energy corollaries.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The endpoint-one results, corrected two-witness powering, Heath--Brown
relation, all nine repaired Add-est clauses and singleton counterexample
are preserved. The whole-proof goal remains open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,081 production files, 1,555 scanned Lean
  files and 10,413 build jobs. The audit covers 8,405 target theorems,
  6,240 pinned-source theorems and five anchors (14,650 total).
  All 13 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-021500-212125e6.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_021842.log) and
  [manifest](../../logs/foundation_freeze_20260924_021842.json).
- All 1,576 physical proof/configuration/tooling hashes are identical before
  and after both runners. The seven module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-global-source-20260924-021500-212125e6.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 414 nodes and 1,067 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `1e28e03092f37b27556a48cb544f7fc7fdd8c5d8eb06a2c5ea40be9c2e5cb054` |
| Foundation log | `97d0cc66dabb405e80f2903b54afbacf1b6e43536e06fdcaae3370705ce52003` |
| Foundation manifest | `3ca6d8c4df084e59cde6c668f366175e86ebdd40564d227aed94f5c6c3e14159` |
| Global detector-source checkpoint JSON | `b8fc50cbfd3623ff72e0853611d3a4e3e59fc1023492d01fd3d22579606b6acd` |


## Direct interior source bounds and detector consumers — previous checkpoint

Thirteen production modules add thirty public theorems and forty-six
semantic regressions (thirty exact signatures and sixteen boundary
fixtures). The new source branch is conditional only on the displayed
upstream coefficient-one zeta large-value/cardinality or energy bounds.

The actual global interior block is restricted to its literal annulus
`(Q/2,2Q]`, with `Q=2^r*floor(T^a)`. Fourier inversion uses one fixed
Schwartz profile and gives exactly the two coefficient-one dyadic lengths
`Q/2` and `Q`. The arbitrary-order tail, bounded ordinate shift and
full-index energy perturbation are proved without selecting a
cardinality-only subfamily. One derivative order precedes the source line;
profile constants affect only the eventual height threshold.

The physical floor cutoff proves `N >= T^a` for both lengths. If the
original source has `tau >= 2`, both actual logarithmic scales lie in
`[2,1/a]`. The global smooth-label loss, Fourier mass, source threshold,
height windows and every separation color are discharged and their
finite losses absorbed.

`classicalDirect_uniform_shifted_line_source_cardinality_bound` and
`classicalDirect_uniform_shifted_line_source_energy_bound` give
`C*T^(B+epsilon)` with a common line window, displacement exponent and
constant chosen before the source line and threshold loss. The two
`classicalTypeI_global_direct_source_*_bounds` theorems consume the
actual detector's global-label fibers, retaining the exact original
cardinality partition and four-fiber energy decomposition.

Both interior ranges now have actual detector consumers: reflected
`1 < tau < 2` and direct `tau >= 2`. Still open are the two bottom
source blocks and the common-parameter, single-labeling full slab
assembly with Type II and analytic multiplicities, followed by the
printed endpoint-two density/energy corollaries. Separate existential
label choices from the two branch consumers must not be spliced together.
EPZAE-21/24/33 and all aggregate checkbox states remain unchanged.
The repaired powering, Heath--Brown relation, nine Add-est clauses and
permanent singleton counterexample remain intact.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,094 production files, 1,568 scanned Lean
  files and 10,426 build jobs. The audit covers 8,466 target theorems,
  6,240 pinned-source theorems and five anchors (14,711 total).
  All 30 new public theorems occur
  exactly once in the explicit audit, with only permitted standard logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-025840-866df8ea.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_030835.log) and
  [manifest](../../logs/foundation_freeze_20260924_030835.json).
- All 1,589 physical proof/configuration/tooling hashes are identical before
  and after both runners. The thirteen module files and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-direct-source-20260924-025840-866df8ea.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are byte-identical to current
HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 419 nodes and 1,080 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `b5cbc3fc57f8783d761d4f8aede972a8a23aa94597032b92d668ca3b51846af2` |
| Foundation log | `0c6c7fcfd8255c9204582e488dddcea397e2bc8447f53abafc030525f19da7ab` |
| Foundation manifest | `bdb0778c4a3dd8530b9c87f620dee8e48ae457cf316ebc2f8c7d4490ce69729a` |
| Direct interior-source checkpoint JSON | `74cb17c4f12452ea548a76684c5139be67777d430a26237c9a9429c82eefbef3` |


## Endpoint-two density and energy transfers — previous checkpoint

Thirteen production modules add forty public theorems and sixty-two
semantic regressions (forty exact signatures and twenty-two boundary
fixtures). EPZAE-24 and EPZAE-33 now reach their source conclusions.

The two bottom global blocks use the actual normalized source coefficients
on every original index. Their literal support and floor cutoff prove
`T^(a/2) <= N <= T^(2a)`, and both logarithmic counts are absorbed.
The general large-value estimates, reflected interior estimates and direct
interior estimates share constants chosen before the shifted source line.

One global labeling is then selected once from the actual Type-I detector.
The same fibers feed every branch; exact cardinalities and all four
energy-color classes retain every analytic multiplicity copy. The common
cutoff and Type-I window precede the Type-II tolerance, and the source
line is chosen only after both. All outer losses are absorbed.

The audited source-facing outputs are:

- `zeroDensityExponent_le_sup_limsup_endpoint_two`: printed
  `zero-from-large`, with zeta supremum over `tau >= 2`.
- `zeroDensityExponent_le_endpointTwo_bounded_suprema`: exact
  `zero-large-cor-0`, with zeta `[2,tau0)` and general
  `[tau0,2*tau0]`.
- `zeroDensityExponent_le_two_thirds_suprema`,
  `zeroDensityExponent_le_three_div_of_largeValue_bounds`, and
  `zeroDensityExponent_le_three_div_of_montgomery_range`: the other
  three printed density corollaries. Powers two and three cover the
  two-thirds interval; the Montgomery variant uses proved subdivision.
  Its small-cutoff case uses the independently proved Ingham bridge.
- `zeroDensityEnergyExponent_le_endpointTwo_bounded_suprema`: exact
  `zeroe-large-cor-0`. The original endpoint-one `zeroe-from-large`
  remains intact; an additional endpoint-two energy sup/limsup theorem
  is proved as a strengthening, not mislabeled as the printed lemma.

The short zeta supremum is literally `bottom = -infinity` when
`tau0 <= 2`, including equality. Compact-range powering consumes the
independent corrected cardinality or energy witness. No relation between
the fifth coordinates is reintroduced.

The singleton counterexample, corrected two-witness powering,
Heath--Brown relation and all nine Add-est clauses are preserved.
The whole-proof goal remains open: the D-process analytic input,
remaining beta/exponent-pair and zeta-growth work, improved density
outputs and final release assembly are separate obligations.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,107 production files, 1,581 scanned Lean
  files and 10,439 build jobs. The audit covers 8,541 target theorems,
  6,240 pinned-source theorems and five anchors (14,786 total).
  All 40 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-034939-53b58c9d.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_035654.log) and
  [manifest](../../logs/foundation_freeze_20260924_035654.json).
- All 1,602 physical proof/configuration/tooling hashes are identical before
  and after both runners. The thirteen modules and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-endpoint-two-20260924-034939-53b58c9d.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 428 nodes and 1,108 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
26 are checked; only EPZAE-24 and EPZAE-33 changed at this checkpoint.
The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `f7b1c99ae43aae95ae63f6228ca821e429a202e7e1ceaee4b231a822fc1b0ad3` |
| Foundation log | `1c07ed2d8406641b8ff822bb1f8ea4fc99219f6d81cf6043deef078ccd71e6f1` |
| Foundation manifest | `3bcf4a34fe768bd2aee20ce88c839e35c5c19a2be32be405941ff9c58903e4dc` |
| Endpoint-two checkpoint JSON | `08da5b8cb051c9e42f1ec81af4a9d7cc136a78ff15eca5167a9ca3796e5157bc` |


## Improved Bourgain density — previous checkpoint

Four production modules add twenty-four public theorems and forty semantic
regressions (twenty-four exact signatures and sixteen boundary fixtures).

EPZAE-27 reaches the unchanged source output:
`zeroDensityExponent_le_bourgain_improved` proves
`A(sigma) <= max(2/(9*sigma-6),9/(8*(2*sigma-1)))`
for the full closed interval `17/22 <= sigma <= 4/5`.
The `_lower` and `_upper` public theorems prove the two closed subranges,
including their common endpoint `38/49`.
`bourgain_improved_isZeroDensityBound` also gives the uniform shifted,
multiplicity-weighted zero-count estimate itself.

The proof uses the original cutoff
`min(9*(3*sigma-2)/2,8*(2*sigma-1)/3)` and the paper's two auxiliary
parameter choices. Exact certificates bound all five Bourgain terms and
derive nonnegative auxiliary parameters, cardinality side conditions and
the physical margin `tau-chi>1`. The existing actual-region consumer and
the failure-of-uniformity equivalence then yield the genuine uniform LV
bound. The proved twelfth moment supplies the zeta range, and the completed
endpoint-two source transfer concludes the density estimate.

One documented proof change is necessary: use the already-proved Jutila
theorem with `k=4`, rather than the printed argument's insufficient
`k=3` comparison. At `sigma=38/49, tau=6/5`, both displayed k=3/Bourgain
estimates exceed the desired `11/20`; a kernel-checked regression records
this gap. The k=4 bound closes it, and exact overlap certificates cover the
entire interval. This is not a counterexample to the advertised density
theorem, whose statement is unchanged.

The standalone unrestricted Bourgain LV input (EPZAE-19) remains open;
this proof derives every condition for the sufficient existing source range.
The permanent Lemma-62 singleton counterexample, corrected independent
powering witnesses, Heath--Brown relation, all nine Add-est clauses, and
completed EPZAE-24/33 transfer contracts are preserved.

Kernel integrity and source completeness are separate verdicts: both pass
for EPZAE-27. The D-process, remaining beta/new-pair/zeta-growth work, other
advertised density outputs, reproduction and whole-proof release remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,111 production files, 1,585 scanned Lean
  files and 10,443 build jobs. The audit covers 8,582 target theorems,
  6,240 pinned-source theorems and five anchors (14,827 total).
  All 24 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-041416-2d614f2b.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_041829.log) and
  [manifest](../../logs/foundation_freeze_20260924_041829.json).
- All 1,606 physical proof/configuration/tooling hashes are identical before
  and after both runners. The four modules and four integration files
  also have normalized hashes in the [checkpoint evidence](logs/tao-trudgian-yang-bourgain-density-20260924-041416-2d614f2b.json).

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 432 nodes and 1,119 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
27 are checked; only EPZAE-27 changed from the preceding checkpoint.
The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `c09dd3425f3539175bf604a8a669afb740c1a9f0bb2e1e15acf9c81412fc40d2` |
| Foundation log | `582ce49dff4f50087d87edb124ce1fa7f34e5d0287c10b1dda54552241ebace5` |
| Foundation manifest | `361f71fdee139ddcfc7dbeb8e838412b1d96f63c58432925689f7bacec7ee4c3` |
| Improved Bourgain checkpoint JSON | `155f4ee056bb95085e1fe09ab0bf4ff1f3973d0977baa583d0f9dae72470131b` |


## Exponent-pair zeta growth — previous checkpoint

Seven production modules add twenty-six public theorems and forty-two
semantic regressions (twenty-six exact signatures and sixteen fixtures).

The exact source lemma `exp-pair-mu` is proved by
`ExponentPair.isZetaGrowthBound` and
`ExponentPair.zetaGrowthExponent_le`:
an actual analytic exponent pair `(k,l)` gives `mu(l-k) <= k`.
The growth predicate has every epsilon quantifier and a uniform threshold,
uses the actual Riemann zeta function and both signs of the ordinate.
Its extended-real infimum is proved equivalent to these epsilon-loss
upper bounds; no finiteness or conjectural lower bound is assumed.

The consumer derives the logarithmic model phase with its exact
`t/(2*pi)` normalization, conjugates the phase sign, applies finite Abel
summation to the actual weighted Dirichlet sums, and cancels the dyadic
scale at `sigma=l-k`. The sharp cutoff is partitioned exactly, including
its last partial block. Its logarithmic count is absorbed by epsilon loss.
The genuine sharp Poisson/Euler truncation is used at arbitrary strip
points, with no zeta-zero hypothesis. Its three remainder terms total at
most 150. This covers both strip endpoints and negative ordinates.

Actual pair consumers in the regression suite prove the classical
`mu(0)<=1/2`, `mu(1)<=0`, `mu(1/2)<=1/6` and `mu(5/7)<=1/14`
bounds. The `mu(7/10)<=3/40` fixture deliberately retains the unproved
specific pair as an explicit premise; it is not an unconditional result.
EPZAE-15 remains open until that named corollary is proved.

The permanent Lemma-62 singleton counterexample, corrected independent
powering witnesses, Heath--Brown energy relation, all nine Add-est clauses,
and completed EPZAE-24/27/33 contracts are unchanged. Preserve the
Bourgain-density k=3 proof-gap regression and its proved k=4 replacement.

Kernel integrity and source completeness are separate verdicts: the
generic exponent-pair-to-mu source lemma is complete, but EPZAE-15 and
the whole-proof release are not. The remaining D-process, beta/new-pair
outputs, other advertised density outputs and reproduction stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,118 production files, 1,592 scanned Lean
  files and 10,450 build jobs. The audit covers 8,628 target theorems,
  6,240 pinned-source theorems and five anchors (14,873 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-060220-bc031597.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260924_060604.log) and
  [manifest](../../logs/foundation_freeze_20260924_060604.json).
- All 1,613 physical proof/configuration/tooling hashes are identical before
  and after both runners. The seven modules and four integration files
  also match after normalizing line endings.

Owner HEAD at this checkpoint is `a0cacfc338fdbcd6fcc58b155c00a66ddae363ec`.
No agent commit or push was performed. All 509 protected tracked files are
byte-identical to current HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 439 nodes and 1,131 edges, with no duplicate/missing endpoints,
class conflicts or unclassified nodes. Of 42 aggregate checklist items,
27 are checked; no aggregate completion status changed in this checkpoint.
The whole-proof goal remains open.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `4fa07a91d597face0afab1b24def6eb5b3d0915a990fda98836f1765007514e5` |
| Foundation log | `d4a6831a6f9984059d1e66ffe7978b1dbdc16216d4d5365b5199438b517df65b` |
| Foundation manifest | `5c3b54c206915fac0bfec12be2521a5494b4dc7681c0851a699c002f52564975` |

## Low-height obstruction and corrected pair transfer — previous checkpoint

The printed unrestricted `add-bound(i)` is false. This is a second, separate
source obstruction; the permanent printed-Lemma-62 powering counterexample
and its authorized repair remain unchanged.

For every integer n >= 2, the new genuine coefficient-one interval patterns
have N=n^4, T=n/4, V=n^3/2 and W={n/4}. Their actual Dirichlet sums have norm
at least V. The unbounded family proves
`zetaLargeValueExponent (3/4) (1/4) ≠ ⊥`.
The already proved classical pair gives mu(1/2)<=1/6, so
1/2+(1/4)mu(1/2)<=13/24<3/4. Thus the printed implication cannot hold
for all positive tau. The public theorem
`zetaGrowth_unrestricted_largeValue_transfer_counterexample`
assembles the actual family and growth bound; this is not a numerical
sample or an assumed asymptotic witness.

A corrected pair-based theorem is independently kernel-checked:
for an actual `ExponentPair k l`, tau>=0,
sigma>k*tau+l-k and sigma>1-tau imply LV_zeta(sigma,tau)=-infinity.
`ExponentPair.zetaLargeValueExponent_eq_bot` retains the genuine
2*pi*N/t residual in the all-height logarithmic-sum estimate, proves a
common positive margin, and consumes the actual coefficient-one interval
of each zeta pattern. The second strict condition is automatic when
tau>=1 and sigma>=1/2. The classical (1/6,2/3) pair therefore gives
nonexistence when tau>=1 and sigma>tau/6+1/2.

Source crosswalk: frozen TeX `add-bound(i)` at lines 770–789 and
`lvz-340` at lines 864–866; the latter's unrestricted height domain
must not be inferred from the corrected theorem. The current
[ANTEDB zeta large-values chapter](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html)
also juxtaposes unrestricted transfer statements with a low-height
coherent-pattern lower bound. The local proof, not the blueprint's prose,
is the proof evidence.

Five new production modules:
`ZetaCoherentPattern`, `ZetaLowHeightFamily`,
`ZetaLowHeightObstruction`, `ZetaPairNonexistenceMargin` and
`ZetaPairNonexistence`. Their 15 public theorems have explicit audits;
the regression adds 15 exact-interface checks and 14 fixtures, including
actual n=2/n=4 patterns, the obstruction, both strict margins and
high-height applications. The root imports and principal runner inventory
include all five modules.

EPZAE-21 remains OPEN. The generic arbitrary-mu corrected transfer,
remaining source zeta interfaces and full advertised outputs are not
claimed. Source-contract correction authorization is pending; the false
printed statement is not silently replaced. This does not obstruct work
on independently proved corrected results or other proof branches.
EPZAE-15 still needs the specific old-pair/growth input. EPZAE-24/27/33,
all nine repaired Add-est clauses, their multiplicity conventions and
their public outputs are preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,123 production files, 1,597 scanned Lean
  files and 10,455 build jobs. Audit: 8,676 target,
  6,240 pinned-source and five anchor theorems (14,921 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  using only permitted logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-063123-ea95cd5a.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_063511.log) and
  [manifest](../../logs/foundation_freeze_20260924_063511.json).
- All 1,618 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates; all nine new/changed module and
  integration files also match after line-ending normalization.
  All 509 protected tracked files remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 443 nodes and 1,139 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. A clean dependency audit
does not close the remaining source-semantic obligations.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `2dd748f6cc47e8ddd5f38f8a3fb40f0685423433136e025ec79f2bf385b63644` |
| Foundation log | `a915857ac00d1e4bb0f4d8c40b026c4dc161dcb6e1920f6b378470d27dc586e2` |
| Foundation manifest | `7c0c1891f1813066fb473d80b683bfa19d527dfd41a077b07be4ca5185961e9f` |

## Sharp low-height zeta exponent — previous checkpoint

The low-height obstruction is now sharpened to the exact value:
for sigma>=0 and 0<=tau<1,
LV_zeta(sigma,tau)=tau when sigma+tau<=1, and equals -infinity
when sigma+tau>1. The public consumer is
`zetaLargeValueExponent_lowHeight`.
The boundary is included in the nonempty branch:
in particular, LV_zeta(3/4,1/4)=1/4, not merely a value different
from -infinity. Both earlier counterexamples remain unchanged.

The proof constructs coefficient-one intervals of length
floor(N^sigma), samples the actual Dirichlet sum on a translated
one-separated lattice in [T,2T], and uses T=N^tau/8 and
V=floor(N^sigma)/2. The family has at least T ordinates and
N^sigma/4<=V<=N^sigma/2. Logarithmic limits and the genuine
uniform-bound definition give the lower exponent. The opposite
branch uses the actual first-derivative estimate O(N/t), retaining
closed interval endpoints, phase normalization and strict margins.
No exponent-pair, growth or moment estimate is assumed.

Four production modules:
`ZetaCoherentLattice`, `ZetaCoherentScale`,
`ZetaLowHeightExact`, `ZetaLowHeightVanishing`.
There are eight new public theorems, eight exact-interface regression
checks and 18 fixtures. These include equality at sigma+tau=1,
tau=0, values approaching tau=1, the genuine finite lattice patterns,
and contradictions to both unrestricted `lvz-340` and a falsely
nonstrict vanishing boundary. All four modules are imported by the
root, inventoried by the BAT runner and explicitly audited.

This proves the low-height formula corresponding to
[ANTEDB Lemma 8.10](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html),
and independently pinpoints the failure of frozen-source
`add-bound(i)` and `lvz-340` below height N. It does not prove the
generic arbitrary-mu corrected transfer, the remaining reflection
interface, or the missing old exponent pair. EPZAE-15/19/21 and the
whole-proof release remain OPEN; no aggregate checklist item closes.
Source-contract correction authorization remains pending, while
independent valid proof branches continue.

The corrected pair transfer from the preceding checkpoint still
requires sigma>k*tau+l-k and sigma>1-tau; the latter is automatic
for tau>=1 and sigma>=1/2. The permanent printed-Lemma-62
counterexample, authorized two-witness powering repair, Heath–Brown
energy relation, optimization and all nine Add-est clauses are preserved.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,127 production files, 1,601 scanned Lean
  files and 10,459 build jobs. Audit: 8,696 target,
  6,240 pinned-source and five anchor theorems (14,941 total).
  All eight new public theorems occur exactly once in the explicit audit,
  using only permitted logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-064709-bc64d0ee.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_065116.log) and
  [manifest](../../logs/foundation_freeze_20260924_065116.json).
- All 1,622 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates; all eight new/changed module and
  integration files also match after line-ending normalization.
  All 509 protected tracked files remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 446 nodes and 1,145 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. A clean dependency audit
does not close the remaining source-semantic obligations.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `5ff02c813cc66302cac3d13fc82e36591963e4e695a35c830bee218d41950e20` |
| Foundation log | `f4d94f6e69c02350b4a2ba5fd67c41389798f7be6ce093c7b72eb4e28003cfe8` |
| Foundation manifest | `3de594ef8d0e1ca8938a226459203139e69b0690dfd3d9dac3950ef81188bd19` |

## Exact Heath–Brown large values — previous checkpoint

The printed `hb-opt` result is now proved on the full source strip
`1/2 ≤ σ ≤ 1, τ ≥ 0`:

`LV(σ,τ) ≤ max(2−2σ, 10+τ−13σ)`.

`heathBrown_largeValueBound` supplies the uniform epsilon–delta
statement. `largeValueExponent_le_heathBrown` and
`zetaLargeValueExponent_le_heathBrown` expose its general and
coefficient-one exponent consequences. This is an independent Lean
derivation of the exact displayed source result, not an assumed import
of the unavailable 1979 page.

Thirteen new production modules contain 31 public theorems, one private
helper theorem and the actual integral definition `zetaGlobalConvolution`.
The proof keeps the original coefficient-one interval, finite ordinate
sets, one-separation, and all Perron residues and tails:

- Actual interval probes give the short-height estimate and the
  sixth-order Perron convolution estimate.
- The proved zeta twelfth moment extends to `[0,3T]). Weighted Hölder
  and the separated kernel bound control the common-window convolution.
- Sharp Gram duality is split at `N^(7/5)). The near row retains its
  diagonal and harmonic term; the far row uses both signed difference
  sets and their actual twelfth moment.
- The resulting finite dichotomy gives
  `LV ≤ max(2−2σ,18+2τ−24σ)` for `σ ≥ 7/8, τ ≥ 3/2`.
  Subdivision at `τ₀=11σ−8` gives the exact `hb-opt` maximum.
  One-separation and Jutila `k=2` cover the lower strip.

The principal BAT inventory, root imports, explicit axiom audit, and
semantic regression suite include all 13 modules. The 44 added checks
comprise all 31 exact public signatures and 13 endpoint, branch,
normalization and preserved-counterexample fixtures.

EPZAE-19 remains OPEN for the unrestricted Bourgain theorem and its
remaining source-facing assembly. EPZAE-26 is not closed: the specific
old exponent pair and the full improved-density consumer are separate
obligations. The exact low-height zeta formula, both source
counterexamples, corrected two-witness powering and all nine Add-est
clauses remain intact. No supporting source statement was silently
changed. Recovery-record maintenance remains permanently optional and
skipped.

Source-facing Lean statement: [HeathBrownLargeValues.lean](Extension/TaoTrudgianYang2025/HeathBrownLargeValues.lean).
The frozen source remains [Tao_Trudgian_Yang_v2.tex](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex), label `hb-opt`.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,140 production files, 1,614 scanned Lean
  files and 10,472 build jobs. Audit: 8,739 target, 6,240 pinned-source
  and five anchor theorems (14,984 total). All 31 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-073452-c7fdbca1.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_073845.log) and
  [manifest](../../logs/foundation_freeze_20260924_073845.json).
- All 1,635 physical proof/configuration/tooling hashes are unchanged
  across the two successful gates. All 509 protected tracked files
  remain byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 450 nodes and 1,156 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 27 of 42 checklist items. The failed preliminary
endpoint-regression run is superseded by the successful logs linked
above; no failed run is release evidence.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `cf3b26009f4df4681c86abe2143261db3d73c13c984c14efcb7a8869e3af43c6` |
| Foundation log | `c5de6c66b62796d253bb9ab9b30c0e7630c388b608715a4ddc89ada27bee7591` |
| Foundation manifest | `8a2aefe82fc65e7311b5da5c6a8252c335be577d83a58432501ac0fa52db613e` |

## Full Bourgain source theorem — previous checkpoint

Both printed parts of `bourgain-lvt` are now proved on their complete
source range. `bourgain_large_values` uses the actual
`ρ=(largeValueExponent σ τ).toReal`, nonnegative `α₁,α₂`,
`1/2<σ<1` and `τ>0`. Its second part retains exactly the printed
cap `ρ≤min(1,4−2τ)`. The supporting dichotomy and uniform-bound APIs
also include the closed sigma and height endpoints.

The earlier physical restrictions were discharged, not made into
new theorem assumptions. If `τ−α₂≤1`, mean square gives the small
branch. If `σ≤3/4`, either mean square again gives that branch or
the explicit witness `s=4σ+ρ` satisfies the auxiliary inequality.
The proved physical Bourgain argument covers every remaining case.

`exists_energyRegion_at_largeValueExponent` realizes the exact
infimum exponent using actual patterns on unbounded scales. Failure of
each slightly smaller bound, simultaneous compactness of the three
logarithmic coordinates, and the genuine uniform upper bound identify
the cardinality limit. Thus the final theorem has no assumed region
membership, dichotomy, moment bound, or realization hypothesis.

EPZAE-19 is now DONE: Huxley, all positive-integer Jutila bounds,
Heath–Brown `hb-opt`, the genuine twelfth moment and the unrestricted
Bourgain source theorem are all supplied.

The same continuation proves `hb-density2` unconditionally for
`7/10<σ≤19/22`, and separately at `σ=1`.
`ExponentPair.heathBrown_density_of_old_pair` gives the exact full
`7/10<σ≤1` consumer when supplied the actual analytic pair
`(3/40,31/40)`; that pair is still unproved. EPZAE-26 remains OPEN.
The corrected high-height pair-to-zeta theorem is used; the false
unrestricted growth-transfer statement is not used or silently replaced.

Four new modules contain 12 public theorems and one five-term
exponent definition. All are registered in the root package and
principal BAT; 24 regressions cover all 12 exact signatures plus
12 endpoint, branch, attainment, density and counterexample fixtures.
The original powering counterexample, the later low-height obstruction,
the sharp low-height formula and all nine repaired Add-est clauses
remain unchanged. Recovery-record maintenance is skipped.

Source-facing modules:
[BourgainLargeValues.lean](Extension/TaoTrudgianYang2025/BourgainLargeValues.lean),
[LargeValueExponentAttainment.lean](Extension/TaoTrudgianYang2025/LargeValueExponentAttainment.lean),
[HeathBrownDensityRange.lean](Extension/TaoTrudgianYang2025/HeathBrownDensityRange.lean).

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,144 production files, 1,618 scanned Lean
  files and 10,476 build jobs. Audit: 8,757 target, 6,240 pinned-source
  and five anchor theorems (15,002 total). All 12 new public declarations
  occur exactly once in the explicit audit, using only permitted logical
  axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-074939-b6807e10.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regression modules, 7,636 explicit
  and 14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_075340.log) and
  [manifest](../../logs/foundation_freeze_20260924_075340.json).
- All 1,639 physical proof/configuration/tooling hashes are unchanged
  across the successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original powering counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 454 nodes and 1,168 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion is now 28 of 42 checklist items; EPZAE-19 is the sole newly
checked item. The whole-proof goal remains active and incomplete.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `539e9350d0a7f99b18b3a9b910d7e70dfbceb5d4ee38a7d984de63c8a55604b8` |
| Foundation log | `cfc937a09dd4d1fb4782a3762b95aef24b6d1d420083b49de4d73109bf6ffaa3` |
| Foundation manifest | `64ee1f2688864010cf9944776f77da64565d8553a0e278db8f05bdabef500a9b` |

## General real zeta moment transfer — previous checkpoint

Printed `add-bound(ii)` is proved with its full closed-strip parameters:
`1/2≤c≤1`, `1/2≤σ≤1`, every real `A≥1`, every real `M`, and
`τ≥2`. The actual dyadic moment
`∫[H,2H] |ζ(c+it)|^A ≤ Cη H^(M+η)` implies the uniform bound
`IsZetaLargeValueBound σ τ (τM−A(σ−c))` and the corresponding
inequality for the actual extended-real infimum `LV_ζ`.
The moment input is exactly the source hypothesis, not an assumed
Perron estimate, large-value conclusion, or energy-region witness.

For `c<1`, the exact arbitrary-line Mellin identity retains the
moving pole. Uniform cutoff bounds control both its residue and the
far integral `O_c(N^(c+3)/T²)`. The physical source windows derive
the Perron entry, with the approximation tolerance explicitly
depending on `1−c`. Weighted Hölder is proved for real orders,
including `A=1`; separation gives only logarithmic loss.
Three actual dyadic intervals normalize the source window, and the
two-sided height window handles either sign of `M+η`.

The endpoint `c=1` uses a separate proved argument. Euler–Maclaurin
with fixed cutoff `ceil(H²)`, the literal constant term, and the
integrated oscillatory prefix give
`∫[H,2H] |ζ(1+it)| ≥ H/2` eventually. Real-order Hölder then forces
`M≥1` from the source moment itself. The elementary ordinate count
closes the endpoint. No contour integrability through the pole and
no extra hypothesis `M≥1` are assumed.

Twelve new modules contain 49 public theorems and seven definitions.
All modules are in the default root and principal BAT inventory.
The 63 new regressions comprise 49 exact signatures and 14 fixtures:
fractional orders, the order-one and pole-line endpoints, negative
height exponents, the genuine twelfth-moment specialization, the
literal unwrapped source statement, and both counterexamples.

Source-facing declarations are
`zetaRealMoment_largeValueBound_closed_strip` and
`zetaLargeValueExponent_le_of_realMoment_closed_strip` in
[ZetaRealMomentEndpoint.lean](Extension/TaoTrudgianYang2025/ZetaRealMomentEndpoint.lean).
The endpoint lower bound is in
[ZetaOneLineLowerMean.lean](Extension/TaoTrudgianYang2025/ZetaOneLineLowerMean.lean);
the arbitrary-line transfer is in
[ZetaRealMomentLargeValues.lean](Extension/TaoTrudgianYang2025/ZetaRealMomentLargeValues.lean).
The unchanged [frozen source](Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex)
is label `add-bound(ii)`, not the false unrestricted part (i).

EPZAE-21 remains OPEN for the general growth/nonexistence and exact
reflection-supremum obligations. EPZAE-19 remains complete; the
specific old pair and full EPZAE-26 density range remain open.
The original printed-powering counterexample, the low-height growth
counterexample, the sharp low-height formula, corrected two-witness
powering and all nine Add-est clauses are preserved. No false
supporting statement is silently replaced. Recovery records are
untouched and their maintenance is permanently skipped.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,156 production files, 1,630 scanned
  Lean files and 10,488 build jobs. Audit: 8,847 target, 6,240 pinned
  and five anchor theorems (15,092 total). All 49 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-083213-8b579737.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_083711.log) and
  [manifest](../../logs/foundation_freeze_20260924_083711.json).
- All 1,651 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The architecture has 459 nodes and 1,179 edges, with no duplicate or
missing endpoints, class conflicts or unclassified nodes. Aggregate
completion remains 28 of 42; no whole checklist item is newly
crossed out. The whole-proof goal remains active and incomplete.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `dfb59a5aac207acc08bf112835120efb65bc7041bfc144114dc4598ecd936607` |
| Foundation log | `ef8c603633319825ed6693aa3a4f12ec6d9cdc71803709beac86fccdff88191d` |
| Foundation manifest | `815484db2236146049ac2b3e9354ad3b221aa6efddf0431e3a0783c3a344c777` |

## General high-height zeta growth transfer — previous checkpoint

General growth, not just an exponent-pair specialization, now gives
zeta-pattern nonexistence throughout `τ≥2`. For
`1/2≤c,σ≤1`, the proved source-style condition is
`c+τ·μ(c)<σ`, with `μ(c)` the actual extended-real infimum.
`zetaHighHeight_exponent_eq_bot_of_mu` concludes
`LV_ζ(σ,τ)=−∞` without assuming that the infimum is finite or attained.

The proof integrates the actual pointwise growth bound to supply every
real-order dyadic moment, with exponent `1+A·m`. Either sign of
`m` is allowed. Choosing a sufficiently large real `A≥1` in the
completed moment transfer makes the cardinality exponent negative.
The proved discreteness theorem then excludes every ordinate in one
uniform physical parameter window. A separate consumer gives strict
power saving for every literal sharp integer interval in `[N,2N]`.
The actual pole-line first moment also proves that any growth
candidate at `c=1` is nonnegative.

Two modules contain ten new public theorems, all root-imported,
registered in the principal BAT inventory and explicitly audited.
Eighteen regressions cover all ten exact signatures plus eight
actual-Weyl, infimum, fractional-moment, Lindelof-conditional,
negative-exponent, pole-line and preserved-counterexample fixtures.
See [ZetaGrowthRealMoments.lean](Extension/TaoTrudgianYang2025/ZetaGrowthRealMoments.lean)
and [ZetaGrowthHighHeight.lean](Extension/TaoTrudgianYang2025/ZetaGrowthHighHeight.lean).

This does not assert or silently repair the false unrestricted
`add-bound(i)`. The height restriction is explicit. Corrected
intermediate-height growth transfer and the exact reflection supremum
remain open under EPZAE-21. Full `add-bound(ii)`, EPZAE-19, both
counterexamples, corrected two-witness powering and all nine Add-est
clauses remain intact. Aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,158 production files, 1,632 scanned
  Lean files and 10,490 build jobs. Audit: 8,864 target, 6,240 pinned
  and five anchor theorems (15,109 total). All ten new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-084907-ccf72179.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_085748.log) and
  [manifest](../../logs/foundation_freeze_20260924_085748.json).
- All 1,653 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 461 nodes and 1,184 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `5b4a581970acbb267aafdeb712c98f77a8f4af6cfae708964bcd064981bd918c` |
| Foundation log | `6998437ac002940e4b1124384ebea99526a800c1c1817e039da61812a0d96268` |
| Foundation manifest | `996845966ae0a7f40a589ca1e0316327858cefc0a57874621d35920575f96892` |

## Corrected general zeta growth transfer — previous checkpoint

The independent corrected growth theorem is proved across all height
cases. On `1/2≤c,σ≤1`,
`zetaCorrected_exponent_eq_bot_of_mu` consumes the actual EReal
inequality `c+τ·μ(c)<σ` together with the explicit necessary
low-height condition `σ>1−τ`, and concludes `LV_ζ(σ,τ)=−∞`.
It assumes neither a finite nor an attained growth infimum.
The same theorem chain supplies one uniform empty-pattern window
and strict power saving for every literal sharp interval in `[N,2N]`.

The proof now covers `1<τ<2` as well as higher heights. Actual
cutoff order `j+3` gives the far error
`D(j,c) N^(c+j+2)/T^(j+1)`. For each `τ>1`, a fixed integer
order makes this bounded on the physical height window. The retained
pole error is also bounded and both are absorbed against the actual
large value. Consequently the real-order moment transfer is strengthened
to every `τ>1`, all real `A≥1`, arbitrary real `M`, and the
full closed line/sigma strip, using only the source moment hypothesis.

At `τ=1`, the actual classical pair gives nonexistence for `σ>1/2`.
The native Dirichlet mean-square identity, with its diagonal retained,
proves that no genuine closed-strip growth candidate is negative.
This also proves `μ(c)≥0` for the actual EReal infimum, so the strict
growth gap reaches that height-one boundary. Below height one, the
already proved sharp low-height formula supplies the corrected result.

Seven new modules contain 27 public theorems and one definition.
They are root-imported, included in the principal BAT inventory and
explicitly audited. The 41 added regressions comprise all 27 exact
signatures and 14 fixtures, including translated intervals, actual Weyl
growth at `τ=3/2`, the pole endpoint, a Lindelof-conditional consumer,
the essential strict residual boundary and both counterexamples.
See [corrected transfer](Extension/TaoTrudgianYang2025/ZetaGrowthCorrectedTransfer.lean),
[above-one moment transfer](Extension/TaoTrudgianYang2025/ZetaRealMomentAboveOne.lean)
and [growth nonnegativity](Extension/TaoTrudgianYang2025/ZetaGrowthNonnegative.lean).

This does not rename or replace the false unrestricted printed
`add-bound(i)`. Its counterexample remains permanent, as does the
printed Lemma 62 counterexample. Corrected two-witness powering and
all nine Add-est clauses are preserved. EPZAE-21 remains OPEN for the
exact reflection supremum and unresolved source-contract correction;
aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,165 production files, 1,639 scanned
  Lean files and 10,497 build jobs. Audit: 8,924 target, 6,240 pinned
  and five anchor theorems (15,169 total). All 27 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-091728-00db0d90.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_092155.log) and
  [manifest](../../logs/foundation_freeze_20260924_092155.json).
- All 1,660 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 468 nodes and 1,201 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

| Evidence | SHA-256 |
| --- | --- |
| Extension log | `7409f9a29fe60b8bab6337e1fc04d518724d9377f530b58e9f3fb3305975c25a` |
| Foundation log | `9b0aa60cf5adad9ca6cd5f80be0ace6ce2407f52f2be3cf63ed781ca66187bbe` |
| Foundation manifest | `f76c0f0dc510dde58e00b0f9f7cbdc3e64eb39e111367f4d8116a7cc0d9978b3` |

## Sharp logarithmic reflection source — previous checkpoint

The reflection source entry now starts from an actual zeta pattern.
For every positive epsilon one constant is fixed before the pattern.
If its physical height satisfies `T≥2π`, the source interval is
retained and every actual ordinate `t` has a literal positive
natural-number interval `J_t` contained in
`(t/(4πN), t/(2πN))`. With `λ=t/(2π)`, the proved estimate is

`V ≤ sqrt(λ) |Σ[n∈J_t] n^(-1) n^(-it)| + Cε (N/sqrt(λ)+λ^ε).`

`zetaPattern_sharp_log_reflection_entry` supplies the actual
interval property, exact dual-scale bounds and this full-error
estimate together. No functional-equation, reflection estimate,
moving-interval large-value bound or coefficient-one conclusion
is assumed. Both source endpoints and the empty/short branch are paid
by the existing sharp B-process comparison.

The new proof specializes the genuine logarithmic phase: inverse
slope `1/v`, curvature `v²`, physical amplitude `sqrt(λ)/q`
and an explicit common phase of norm one. It identifies every
retained stationary term and reindexes the actual positive consecutive
integer frequencies without changing the reciprocal weights.

Five new modules contain 23 public theorems and two definitions.
All are root-imported, included in the principal BAT inventory and
explicitly audited. The 31 regressions comprise all 23 exact signatures
and eight concrete rational-stationary, empty-interval and preserved
counterexample fixtures. See
[actual pattern entry](Extension/TaoTrudgianYang2025/ZetaSharpReflectionEntry.lean),
[sharp source comparison](Extension/TaoTrudgianYang2025/ZetaSharpLogReflection.lean)
and [literal dual interval](Extension/TaoTrudgianYang2025/ZetaLogDualInterval.lean).

This is the source entry, not the full reflection supremum.
The moving reciprocal-weighted intervals must still be completed to
one common coefficient-one convolution, with uniform kernel/tail
bounds, separated extraction and the exact supremum consumer.
The independent corrected general growth transfer and above-one
real-moment transfer remain proved. Both permanent counterexamples,
corrected two-witness powering and all nine Add-est clauses remain
intact. EPZAE-21 remains OPEN; aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,170 production files, 1,644 scanned
  Lean files and 10,502 build jobs. Audit: 8,968 target, 6,240 pinned
  and five anchor theorems (15,213 total). All 23 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-094315-eff1f4b8.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_094943.log) and
  [manifest](../../logs/foundation_freeze_20260924_094943.json).
- All 1,665 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 473 nodes and 1,209 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

Build-log SHA-256: `3eebc45f7056e341cb531718430c5c2ff3a40c699b45689405a36546a7f72edd`.
Foundation-log SHA-256: `df5f149dece0290595988f3fac0061ff04558513ea24bfbeabc0681919784eaa`.
Foundation-manifest SHA-256: `7ca7e4f3b6825ea95a958ced643d0a5735bee4f124938f29ba35227fbb4b8581`.

## Uniform common reflection convolution — previous checkpoint

The moving reciprocal-weighted reflection sum is now completed exactly
to one common coefficient-one polynomial. Set
`M=T/(4πN)` and
`S=Icc (floor(M)+1) (ceil(T/(πN)))`.
This actual positive integer interval is fixed before the ordinate.
Mellin inversion on `Re(s)=-1` cancels the reciprocal coefficients,
with integrability and every finite sum/integral interchange proved.

Define the actual localized convolution

`B(S,T,t) = ∫[T/2-t,3T-t] |Σ[n∈S] n^(-i(t+u))|/(1+|u|) du.`

For every positive epsilon one source constant is fixed before the
pattern. Whenever `T≥2π` and `M≥1`,
`zetaPattern_uniform_localized_reflection` proves, for every actual
ordinate and every natural derivative parameter `j`, with `λ=t/(2π)`,

`V ≤ sqrt(λ) [4 D1 B(S,T,t)/M + K_j/(4πN)^(j+1)] + Cε [N/sqrt(λ)+λ^ε].`

Here `D1=zetaCutoffDerivativeMass 1` and
`K_j=12·5^j·2^(j+1)·zetaCutoffDerivativeMass(j+2)/(j+1)`.
These are fixed transition constants, not hypotheses about a desired
large-value bound. All moving endpoints have disappeared from the
estimate. The empty dual interval is handled explicitly.

The first derivative controls the negative-line Mellin kernel at every
frequency, including zero. Higher derivatives provide arbitrary-order
tails away from zero. The common interval has cardinality at most
`6M`; actual endpoint geometry supplies uniform bounds. The near
window keeps every shifted ordinate in `[T/2,3T]`, and the discarded
integral is fully paid by the displayed tail.

Nine modules contain 33 public theorems and three definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 45 regressions contain all 33 exact signatures and 12
fixtures: zero frequency, literal common intervals, empty intervals,
a computed reciprocal sum, kernel constants and both counterexamples.
See [uniform actual-pattern entry](Extension/TaoTrudgianYang2025/ZetaReflectionUniformEntry.lean),
[exact finite completion](Extension/TaoTrudgianYang2025/ZetaReciprocalCompletion.lean)
and [localized convolution](Extension/TaoTrudgianYang2025/ZetaReflectionLocalizedCompletion.lean).

The exact reflection supremum is still OPEN. The next steps are
physical-window error absorption, separated extraction from this
common convolution, fixed-factor interval/height normalization and
the exact EReal supremum consumer. The corrected general growth
transfer, full real-moment transfer, corrected two-witness powering,
all nine Add-est clauses and both permanent counterexamples remain
intact. EPZAE-21 stays OPEN; aggregate completion remains 28/42.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,179 production files, 1,653 scanned
  Lean files and 10,511 build jobs. Audit: 9,047 target, 6,240 pinned
  and five anchor theorems (15,292 total). All 33 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-101527-45061ad5.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_101937.log) and
  [manifest](../../logs/foundation_freeze_20260924_101937.json).
- All 1,674 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 478 nodes and 1,215 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

Build-log SHA-256: `671e3e7fe88b9300b34b8bf578881b257bf1c84bc86e7b1767d08d80f2188d08`.
Foundation-log SHA-256: `4cccabb3da31f74338ea5552a193c1b133b18395c0b300e5e9a75d1a421e2c18`.
Foundation-manifest SHA-256: `0236368779ae2d725337e69e68dc02b60dc40a31dc0ee7d5a9beae3df0933bc0`.

## Error-free reflection convolution entry — previous checkpoint

All sharp-source and Mellin-tail errors are now absorbed uniformly on
the actual physical exponent window. For every fixed `τ>1`,
`exists_zetaReflectionConvolution_uniform_entry` chooses a positive
radius and a threshold before the pattern. For every `σ≥1/2`,
an actual pattern with `N^(τ−δ)≤T≤N^(τ+δ)` and
`N^(σ−δ)≤V` satisfies, at every actual ordinate,

`V·sqrt(T)/N ≤ K·B(S,T,t).`

The constant `K=1+32π·zetaCutoffDerivativeMass 1` is fixed and
positive. The common coefficient-one interval and the actual localized
convolution are unchanged from the preceding proof. No reflection,
convolution or large-value estimate is assumed.

The proof chooses a fixed derivative order and
`δ=min(1/8,(τ−1)/16)`. Physical powers imply both required
source conditions `T≥2π` and `T/(4πN)≥1`. The three retained
errors have a common strict power gap, and one threshold bounds
their sum by `V/2`. The final theorem needs no upper value bound
and no restriction `σ≤1`, which is useful for reflected coordinates.

Finite dyadic selection is also proved separately. A positive finite
mass above the low floor selects an actual nonempty value band with
the required amplitude-times-cardinality lower bound. Translating the
selected subset by one common shift preserves both cardinality and
one-separation exactly. This finite result does not yet choose the
analytic common shift from the convolution.

Five modules contain 17 public theorems and two definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 29 regressions contain all 17 exact signatures and 12
fixtures: actual height and remainder bounds, the `τ=3/2, σ=1/2`
consumer, concrete value bands, common-shift separation, positive
selected mass and both counterexamples.
See [uniform error-free entry](Extension/TaoTrudgianYang2025/ZetaReflectionConvolutionEntry.lean),
[physical threshold](Extension/TaoTrudgianYang2025/ZetaReflectionErrorThreshold.lean)
and [finite value bands](Extension/TaoTrudgianYang2025/ZetaReflectionValueBands.lean).

Next: select one common shift using the weighted integral mean, apply
the finite amplitude selection to actual shifted values, construct
the normalized target zeta pattern and prove the exact EReal reflection
supremum. The affine value loss must be retained; the informal
pointwise reflection identity is not a replacement for the source
supremum statement. EPZAE-21 remains OPEN; completion remains 28/42.
Both counterexamples, corrected powering and all nine Add-est clauses
remain intact.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,184 production files, 1,658 scanned
  Lean files and 10,516 build jobs. Audit: 9,081 target, 6,240 pinned
  and five anchor theorems (15,326 total). All 17 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-103643-8f5e545b.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_104037.log) and
  [manifest](../../logs/foundation_freeze_20260924_104037.json).
- All 1,679 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 482 nodes and 1,220 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.

Build-log SHA-256: `5357bfe8b861d9742f7af6ec8c97536393615e6aca04c2273bdfdabe62513312`.
Foundation-log SHA-256: `dd1eebeb8c8739b444500591c101f71bb2a41fc457bf95e3da6517ce3952042e`.
Foundation-manifest SHA-256: `986788b6f3b3473bc3655b21adfa6dee7817156b4a8b45162cb3d8c078a9e281`.

## Actual common-shift reflected family — current checkpoint

The analytic common shift and actual separated value-family extraction
are proved. `exists_zetaReflection_value_family` starts from an
actual nonempty zeta pattern in the uniform physical window, for every
`τ>1` and `σ≥1/2`. It supplies one common shift
`u∈[-2T,2T]` and a literal nonempty subset of the translated
original ordinates. The selected set is exactly one-separated and
lies in `[T/2,3T]`.

Let `K=zetaReflectionConvolutionConstant`,
`L=zetaMomentLogLoss T`, `S=zetaReflectionCommonInterval T N`,
`a=V sqrt(T)/(8 K N L)`, and
`J=clog_2(ceil(|S|/a))+1`. The actual selected values satisfy
`q≤|Σ[n∈S] n^(-iv)|<2q`, with `q=a·2^j` and `j<J`, and

`q·|U| ≥ |W| V sqrt(T)/(8 K N L J).`

Every frequency coefficient is literally one. The proof retains the
amplitude-cardinality loss needed by the source's affine supremum;
it does not assert cardinality conservation at one fixed threshold.

An exact identity first turns the finite sum of localized convolutions
into one weighted common-shift integral, including the actual shifted
height indicators. Its support is `[-2T,2T]`; its positive kernel has
logarithmic mass. A weighted mean selects one shift, and the previously
proved finite dyadic lemma selects a nonempty band. The final theorem
discharges the convolution input using the actual error-free source
entry. No desired LV bound, reflection estimate or selected-pattern
existence is assumed.

Five modules contain 16 public theorems and three definitions. All are
root-imported, listed in the principal BAT inventory and explicitly
audited. The 28 regressions contain all 16 exact signatures and 12
fixtures: empty inputs, actual positive and excluded shifted heights,
literal band counts, the exact common integral, positive floors and
both counterexamples.
See [actual-pattern extraction](Extension/TaoTrudgianYang2025/ZetaReflectionSourceFamily.lean),
[common-shift mean](Extension/TaoTrudgianYang2025/ZetaReflectionShiftMean.lean)
and [actual selected value family](Extension/TaoTrudgianYang2025/ZetaReflectionValueFamily.lean).

The selected family is not yet packaged as a normalized zeta pattern:
its fixed common frequency annulus and positive height range still
need finite dyadic subdivision and scale normalization. Those steps,
the logarithmic loss bounds and the exact EReal supremum equality
remain OPEN. The informal pointwise reflection identity is not the
target. EPZAE-21 stays OPEN; aggregate completion remains 28/42.
Both counterexamples, corrected powering and all nine Add-est clauses
remain intact.

Verification:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,189 production files, 1,663 scanned
  Lean files and 10,521 build jobs. Audit: 9,115 target, 6,240 pinned
  and five anchor theorems (15,360 total). All 16 new public theorems
  occur exactly once in the explicit audit and use only permitted
  logical axioms. The [extension log](logs/tao-trudgian-yang-build-20260924-105438-e7ef1b7e.log)
  has zero errors, warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass with zero diagnostics and 8,857 build jobs;
  301 root modules, two retained regressions, 7,636 explicit and
  14,290 discovered theorem audits. See the
  [foundation log](../../logs/foundation_freeze_20260924_110150.log) and
  [manifest](../../logs/foundation_freeze_20260924_110150.json).
- All 1,684 physical proof/configuration/tooling hashes are unchanged
  across both successful gates. All 509 protected tracked files remain
  byte-identical to owner HEAD
  `35bcc49b2086c6403b95f42ace4f97bffa399f68`. No agent commit or push.
  The original counterexample SHA-256 remains
  `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

The synchronized architecture has 485 nodes and 1,223 edges, with no
duplicate or missing endpoints, class conflicts or unclassified nodes.
The whole-proof goal remains active and incomplete. Recovery-record
maintenance remains permanently skipped; no such file was changed.
