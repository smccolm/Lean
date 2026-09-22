# Tao--Trudgian--Yang 2025 reproduction manifest

Current analytic progress: [Width-independent curvature and the bounded inner core](#width-independent-curvature-and-the-bounded-inner-core--current-checkpoint).
The actual Fourier modes now obey a cutoff-width-independent C_sigma*N/sqrt(T) bound. The genuine endpoint slopes determine the exact stationary integer interval; the complete inner-core nonstationary complement has a derived N/sqrt(T) plus logarithmic bound. The original source expansion contains only actual cutoff-weighted stationary main terms, with every remaining error explicit. Sharp stationary/source error balance, canonical dual-chart assembly and full beta reflection remain open. The counterexample and all nine repaired Add-est clauses are preserved; the full goal remains unfinished.

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

## Width-independent curvature and the bounded inner core — current checkpoint

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
