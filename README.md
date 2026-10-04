# Lean Mathematics Monorepo

This repository is a workspace for independent Lean 4 mathematics projects,
research-source archives, and a small visualization utility. Each Lean project
owns its own toolchain, Lake manifest, build instructions, and claim boundary;
the repository root is documentation and coordination space, not a Lake
package.

Author: **S. McColm**

## Start here

| Area | Role | Entry point |
|---|---|---|
| [`Riemann Zeta/`](Riemann%20Zeta/) | RH-map research tree, frozen Guth--Maynard foundation, and isolated follow-on projects | [`Riemann Zeta/README.md`](Riemann%20Zeta/README.md) |
| [`EllipsePerimeter/`](EllipsePerimeter/) | Canonical complete ellipse-perimeter formalization, paper, and archived development history | [`EllipsePerimeter/README.md`](EllipsePerimeter/README.md) |
| [`Compacted Graphs/`](Compacted%20Graphs/) | Early-stage compactified-graph and cylindrical-topology formalization | [`Compacted Graphs/README.md`](Compacted%20Graphs/README.md) |
| [`visualizer/`](visualizer/) | Standalone Python/WebGL mathematical visualizations | [`visualizer/README.md`](visualizer/README.md) |

The human-readable numbered directory names under `Riemann Zeta/` intentionally
mirror the research map and are stable navigation labels. Lean module names and
package roots are documented inside the relevant projects.

## Principal formal projects

### Guth--Maynard foundation

The frozen foundation source and its colocated control documents are under
[`71 Guth-Maynard, 2026/`](Riemann%20Zeta/9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/71%20Guth-Maynard,%202026/).
The repository records an internally kernel-checked release boundary without
claiming independent semantic review, publication, or canonical status.

From `Riemann Zeta/`:

```powershell
cmd /c run_lake_build.bat --no-pause
```

### Gafni--Tao follow-on

The isolated project under
[`74 Gafni-Tao, 2026/`](Riemann%20Zeta/9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao,%202026/)
has its own frozen dependency, source ledger, documentation controls, audit, and
human-facing runner.

From that directory:

```powershell
cmd /c run_gafni_tao_build.bat --no-pause
```

### Tao--Trudgian--Yang 2025

The isolated [node 63 project](Riemann%20Zeta/9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang,%202025/README.md)
records all 42 acceptance gates complete under the owner-authorized supporting
repairs. The four exponent pairs, density outputs, nine additive-energy bounds,
and unchanged density table are proved; the disputed closed Pintz endpoints
are original research strengthenings, not reproductions of Pintz's strict-cell
source theorem. Frozen statements and counterexamples remain preserved.

From that directory:

```powershell
cmd /c run_tao_trudgian_yang_build.bat --no-pause
```

Its [reproduction manifest](Riemann%20Zeta/9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/63%20Tao-Trudgian-Yang,%202025/Tao-Trudgian-Yang%20Reproduction%20Manifest.md)
records the separate paper and foundation verification gates. A recorded PASS
is evidence for its recorded source snapshot, not a fresh build of any checkout.

### Tao 2026

The isolated [node 73 project](Riemann%20Zeta/9.%20Zero%20Density,%20Large%20Values%20and%20Prime%20Transfer/73%20Tao,%202026/README.md)
records a verified four-theorem release: Theorems 1.7--1.10, with the documented
owner-approved endpoint-equivalent PNT and sieve substitutions. This does not
claim every stronger auxiliary statement in the paper.

From that directory:

```powershell
cmd /c run_tao_build.bat --no-pause
```

### Prime Shell investigation

[`Riemann Zeta/Investigations/PrimeShell/`](Riemann%20Zeta/Investigations/PrimeShell/)
is an isolated route-analysis project. Its documented endpoint is route-specific
and is not a new theorem about zeta zeros.

From `Riemann Zeta/Investigations/PrimeShell/Extension/`:

```powershell
lake update
lake build
lake env lean PrimeShell/Audit.lean
```

### Ellipse perimeter

`EllipsePerimeter/` is the sole production package for the ellipse theorem. The
former EllipseLab proof has been consolidated into it; historical iterations
are inert records under `EllipsePerimeter/archive/`, and the associated article
files are under `EllipsePerimeter/paper/`.

From `EllipsePerimeter/`:

```powershell
lake build
```

### Compacted Graphs

From `Compacted Graphs/`:

```powershell
lake build
```

## Verification policy

Formal builds are intentionally local. Heavyweight GitHub Actions workflows
were removed because they duplicated project-owned verifiers without providing
reliable evidence. Use each project's pinned local command and consult its audit
and reproduction documents for the exact verification scope.

`push_to_github.bat` is an owner-operated synchronization helper. It is not a
build command and is not invoked by project verification.

## Sources, archives, and generated files

Pinned papers, TeX/source archives, database snapshots, and upstream source
captures are intentional research artifacts. Their provenance and hashes live
beside the projects that consume them. Temporary extraction tools, caches,
logs, backups, and generated page images are excluded from version control.

[`directory_tree.txt`](directory_tree.txt) is a historical, repository-relative
snapshot predating the node-63 formalization, not the current module inventory.
Use the project READMEs and each runner's coverage inventory for current scope,
or `git ls-files` for tracked files. Its original regeneration command is below;
review local scratch/dependency inclusions before replacing the snapshot:

```powershell
python list_files.py
```

## License and third-party material

Original repository material is offered under
[MIT No Attribution (MIT-0)](LICENSE). Vendored or captured third-party material
retains its original copyright and license; see
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) and the project-local source
ledgers.
