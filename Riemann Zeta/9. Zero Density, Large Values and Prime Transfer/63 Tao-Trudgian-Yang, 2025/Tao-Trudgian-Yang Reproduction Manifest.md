# Tao--Trudgian--Yang 2025 reproduction manifest

## Manifest status

**Verified implementation baseline, 19 September 2026.** A unified Lean
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

The latest installed-scope verification ran on 19 September 2026 with
`run_tao_trudgian_yang_build.bat --no-pause`, exited `0`, and wrote
`logs/tao-trudgian-yang-build-20260919-220935-26fb4b92.log` (SHA-256
`a005b958eb19973809b271f4bfb22b5cec494a65901a30e723b41ced0559e7ec`).
It scanned 42 Lean files and audited 610 nonprivate target theorems plus five
imported boundary declarations and reported no warnings.

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
