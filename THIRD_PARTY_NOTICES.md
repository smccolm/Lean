# Third-Party Notices

The root `LICENSE` applies only to original repository material for which the
repository owner holds the relevant rights. It does not relicense third-party
source code, papers, books, scans, TeX archives, datasets, database snapshots,
or other captured research artifacts.

## PrimeNumberTheoremAnd (PNT+)

The Guth--Maynard and Gafni--Tao projects contain adapted or source-derived
files from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
distributed upstream under the Apache License 2.0. Copyright remains with the
upstream contributors. Detailed revision, adaptation, and path information is
recorded in
[`Riemann Zeta/THIRD_PARTY_NOTICES.md`](Riemann%20Zeta/THIRD_PARTY_NOTICES.md)
and the Gafni--Tao reproduction manifest.

## Lean and Mathlib dependencies

Project Lake manifests pin Lean ecosystem dependencies, including Mathlib.
Downloaded package caches are not repository source and retain their upstream
licenses. Source-derived files that are intentionally included in this
repository retain their upstream notices and SPDX identifiers where present.

## Zeta23 / formal-math

The Prime Shell extension pins the Zeta23 package from Anthropic's
`formal-math` repository. The dependency is fetched by Lake rather than
vendored as project-owned source. Its exact commit and reproduction caveats are
recorded in
[`Prime Shell Sources.md`](Riemann%20Zeta/Investigations/PrimeShell/Prime%20Shell%20Sources.md).
Use and redistribution remain subject to the upstream project's terms.

## Research papers, source archives, and datasets

The `Sources/` directories and related research ledgers contain intentional
copies of papers, author manuscripts, scans, arXiv source archives, and
database/repository snapshots. These materials are included for research
reproducibility and retain their authors', publishers', or upstream projects'
rights. No license is granted by the root MIT-0 file for those artifacts.

The authoritative artifact identities and provenance are recorded in the
project-local `PINS.md`, `SHA256SUMS.txt`, source ledgers, crosswalks, and
reproduction manifests. Those records should be consulted before any
redistribution.
