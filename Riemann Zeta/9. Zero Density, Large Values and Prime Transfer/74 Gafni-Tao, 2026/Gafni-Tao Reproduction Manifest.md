# Gafni-Tao reproduction manifest

This manifest records the isolated release inputs. It does not claim external
review, publication, canonicality, or new mathematics.

## Frozen inputs

- Frozen Guth-Maynard tag: `gm-foundation-freeze-v1.0.1`
- Frozen Guth-Maynard commit: `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`
- Frozen source archive SHA-256:
  `5149F19EA6A94DF7DA920A47EE2EDD970D06073CA2411426941B11BDDA6FAB5E`
- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- PrimeNumberTheoremAnd source revision:
  `4ecb950126c4290293c5662dfe0e884123171df5`
- Warning-free local PNT+ closure: 83 transitive source files, with 82 retained
  byte-for-byte and one audited unreachable block removed from `Wiener.lean`
- Gafni-Tao source: arXiv `2505.24017v1`
- Guth-Maynard source: arXiv `2405.20552v2`
- ANTEDB/expdb source snapshot:
  `2b1aea3de263996c4da3042c115126bff601c618`

The complete downloaded-artifact byte manifest is
[`Sources/SHA256SUMS.txt`](Sources/SHA256SUMS.txt). The resolved Lake dependency
graph is pinned in `Extension/lake-manifest.json`; no moving revision is used.
The local PNT+ closure has a two-column upstream/retained byte manifest at
[`Dependencies/PrimeNumberTheoremAndClean/SOURCE_SHA256SUMS.txt`](Dependencies/PrimeNumberTheoremAndClean/SOURCE_SHA256SUMS.txt).

## Frozen-boundary check

At preparation time, this command produced no changed path:

```powershell
git diff --name-status 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be -- RiemannZeta RiemannZeta.lean lakefile.toml lean-toolchain
```

The isolated package compiles the copied foundation under
`Extension/FrozenFoundation/`. Its archived bytes are checked by the principal
runner before compilation.

## Reproduction command

From `9. Zero Density, Large Values and Prime Transfer/74 Gafni-Tao, 2026` run:

```powershell
cmd /c run_gafni_tao_build.bat --no-pause
```

The two Lake workspaces set `packagesDir` to dedicated locations under the
repository-root `.lake/` directory. The formalization and its local PNT+ source
remain in this Node 74 directory, while the shorter generated-dependency paths
keep deeply nested Mathlib artifacts below the legacy Windows path limit.

Latest recorded verification: **PASS**, 2026-09-07 09:23:16 -07:00.
The root build completed all 10,344 jobs, the central audit exited successfully,
the warning-free PNT+ build completed its full dependency closure, and the source-hash and
forbidden-token gates passed. Neither build emitted a Lean warning, linter
suggestion, or tactic diagnostic. Raw logs are transient ignored evidence;
rerun the principal command to reproduce them for the current checkout.

The runner:

1. checks every downloaded source hash and the frozen-foundation archive;
2. verifies the exact 83-file local PNT+ closure and its sole recorded edit;
3. builds that PNT+ closure and the isolated `GafniTao` root;
4. rejects every warning, linter suggestion, or tactic diagnostic;
5. executes `Extension/GafniTao/Audit.lean`;
6. scans the Gafni-Tao and local PNT+ Lean sources for forbidden shortcuts; and
7. writes a timestamped, unsuppressed log under `logs/`.

## Warning-free PNT+ dependency boundary

The exact upstream PNT+ revision contains two unrelated admitted declarations
in `PrimeNumberTheoremAnd/Wiener.lean`. They and the two local declarations
used only by them form an unreachable four-declaration block: no retained
theorem, including `WeakPNT` and `chebyshev_asymptotic`, refers to the block.
The isolated package therefore vendors exactly the 83-file transitive import
closure used jointly by the frozen foundation and Gafni-Tao, deleting only
that block. The other 82 files are byte-identical to source revision
`4ecb950126c4290293c5662dfe0e884123171df5`.

This is a minimal source derivative, not a claim that the original upstream
repository is warning-free. The runner verifies every retained hash, the sole
allowed divergence, the exact file count, absence of the removed declarations,
and zero diagnostics. The central audit includes the Chebyshev consumer and
the public Gafni-Tao endpoints; their reported dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Release claim boundary

The release target is the exact general Theorems 1.1-1.3 and the two displayed
Section 3 sample inequalities. It does not claim the optional complete
best-known numerical curve, the optimized constants in Ford's older density
theorem, or a full formalization of every result in the cited papers.
