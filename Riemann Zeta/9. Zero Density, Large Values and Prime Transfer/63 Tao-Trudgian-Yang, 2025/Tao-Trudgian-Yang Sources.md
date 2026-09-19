# Tao--Trudgian--Yang 2025 sources and repository survey

Research checked on 19 September 2026.

## Primary paper

Terence Tao, Tim Trudgian, and Andrew Yang,
*New exponent pairs, zero density estimates, and zero additive energy
estimates: a systematic approach*, arXiv `2501.16779v1`, submitted
28 January 2025, 44 pages.

- [arXiv abstract](https://arxiv.org/abs/2501.16779)
- [experimental HTML](https://arxiv.org/html/2501.16779v1)
- [Tao's launch post](https://terrytao.wordpress.com/2025/01/28/new-exponent-pairs-zero-density-estimates-and-zero-additive-energy-estimates-a-systematic-approach/)

ArXiv currently lists only v1. The official source archive internally names
its main file `Tao_Trudgian_Yang_v2.tex`; the archive version, not that internal
filename, is the citation authority.

## ANTEDB / expdb

- [GitHub repository](https://github.com/teorth/expdb)
- [web blueprint](https://teorth.github.io/expdb/blueprint/)
- [dependency graph](https://teorth.github.io/expdb/blueprint/dep_graph_document.html)
- [single-file blueprint PDF](https://teorth.github.io/expdb/blueprint.pdf)

Two pins serve different purposes:

| Purpose | Commit | Date/evidence |
|---|---|---|
| paper-time computation | `9953003a48f46fe8075ccf9534321f98f656032e` | last commit before the arXiv v1 submission timestamp |
| current Lean reuse survey | `088040634e8300f87e80f431d8bdc38c42cc8e11` | repository HEAD inspected 19 September 2026; commit dated 4 September 2026 |

The paper-time tree uses Lean `v4.16.0-rc2` and contains only a placeholder
Lean example. The current tree uses Lean `v4.32.0` and contains 18 substantive
Lean modules. A source scan found no `sorry`, `admit`, project axiom, unsafe
proof bypass, or `native_decide` in those modules.

### Current ANTEDB Lean coverage

Available modules cover:

- variable objects, boundedness, infinitesimals, underspill, and automatic
  uniformity;
- power asymptotics;
- model phase functions and the logarithmic phase;
- fixed and asymptotic exponential sums;
- non-asymptotic equivalence for the exponent-sum growth function;
- trivial bounds, scale transfer, continuity/upper semicontinuity;
- Euler--Maclaurin and iterated derivatives; and
- smooth bump functions and an L2 exponential-sum integral estimate.

No current Lean file defines exponent pairs, large-value exponents,
zero-density exponents, or additive-energy exponents. These are target work,
not existing proofs.

## Existing local formalization assets

1. `../71 Guth-Maynard, 2026/` is the canonical local Lean formalization of
   Guth--Maynard large values and zero density. Its publication contracts
   include the exact large-values theorem, Ingham, Huxley, and the
   Guth--Maynard density theorem. Reuse requires target-specific bridges.
2. `../74 Gafni-Tao, 2026/` contains already downloaded copies of the
   Tao--Trudgian--Yang paper, Guth--Maynard v2, Heath--Brown's kth-derivative
   paper, the twelfth
   moment paper, Ivić material, Pintz 2023, and an older ANTEDB snapshot.
3. `../73 Tao, 2026/` demonstrates the desired source pinning, frozen
   dependency, build, audit, crosswalk, and reproduction-document pattern. Its
   multi-gigabyte dependency tree should not be copied into this folder.
4. The root `Riemann Zeta` package is pinned to Lean `v4.30.0`, mathlib commit
   `c5ea00351c28e24afc9f0f84379aa41082b1188f`, and
   `PrimeNumberTheoremAnd` commit
   `4ecb950126c4290293c5662dfe0e884123171df5`.

## Core upstream analytic sources

### Direct arXiv inputs

- Timothy S. Trudgian and Andrew Yang,
  [*Toward optimal exponent pairs*](https://arxiv.org/abs/2306.05599), v3,
  15 July 2024. Supplies the pre-ANTEDB exponent-pair hull and beta tables.
- D. R. Heath-Brown,
  [*A New kth Derivative Estimate for Exponential Sums via Vinogradov's Mean Value*](https://arxiv.org/abs/1601.04493),
  v3. Supplies `heath-brown-2017`.
- Larry Guth and James Maynard,
  [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
  v2. The v1 PDF and gzip-compressed TeX actually cited by the 2025 paper are
  pinned here; v2 is also retained because the local formalization freezes and
  documents its chosen publication contract separately.
- Kaisa Matomäki and Joni Teräväinen,
  [*A note on zero density results implying large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2403.13157),
  v1. Supplies `zero-dens_implies-large`.

### Classical results consumed directly

The primary TeX bibliography is the authority for editions and page/theorem
references. The highest-priority formalization inputs are:

- Bourgain (1995), *Remarks on Halász--Montgomery Type Inequalities*,
  especially Proposition 3 (`bourgain-zd`);
- Bourgain (2000), *On large values estimates for Dirichlet polynomials and
  the density hypothesis for the Riemann zeta function* (`bourgain-lvt`);
- Heath--Brown (1978), the twelfth moment of zeta;
- Heath--Brown (1979), the large-values estimate and the zero-density/additive-
  energy relation;
- Huxley (1972, 1996), zero density and exponent-pair tables;
- Ingham (1940), `A(sigma) <= 3/(2-sigma)`;
- Ivić (1980; 2003 reprint), exponent pairs, zeta growth, and density tables;
- Jutila (1977), zero-density/large-values estimates;
- Montgomery (1971), *Topics in Multiplicative Number Theory*;
- Pintz (2023), density near `Re s = 1`;
- Sargos (1995, 2003), the D- and C-process inputs;
- Titchmarsh (1986), zeta and Euler--Maclaurin background; and
- Watt (1989), exponential sums and zeta.

Lower-priority references used for definitions or background include
Iwaniec--Kowalski, Tao--Vu, Tao's cheap nonstandard-analysis post, and
Cladek--Tao on additive energy.

## Complete bibliography triage

This table covers every item in the primary paper's embedded bibliography.
“Formalize” means that an exact theorem surface is consumed by the planned
dependency graph; “reference” means background or an alternative route unless
the crosswalk later promotes it.

| Key | Source | Planned use | Acquisition/status |
|---|---|---|---|
| Bou91 | Bourgain, *Remarks on Montgomery's conjectures on Dirichlet sums* | large-value background | citation/reference |
| Bou95 | Bourgain, *Remarks on Halász--Montgomery Type Inequalities* | Proposition 3, pair-to-density theorem | formalize EPZAE-28; obtain authoritative scan |
| Bou00 | Bourgain, *On large values estimates for Dirichlet polynomials...* | `bourgain-lvt`, density-hypothesis optimization | formalize consumed form EPZAE-19 |
| Bou02 | Bourgain, *On the distribution of Dirichlet sums II* | density-table input | reference then exact EPZAE-30 bridge if retained |
| Bou17 | Bourgain, *Decoupling, exponential sums and the Riemann zeta function* | exponent pair `(13/84,55/84)` | formalize/import exact pair input |
| CDV24 | Chen--Debruyne--Vindas, density for cusp-form L-functions | best-known zeta-density table entry cited by paper | validate scope before EPZAE-30 |
| CT21 | Cladek--Tao, additive energy of regular measures | alternate proof of a basic energy inequality | reference |
| GM24 | Guth--Maynard, *New large value estimates...* | `guth-maynard-lvt`, density input | local completed formalization; exact bridge EPZAE-20/25 |
| HT69 | Halász--Turán, distribution of zeta roots | Lindelöf-implies-density theorem | supporting/reference |
| HB78 | Heath--Brown, twelfth moment | `twelfth-bound` | PDF pinned; formalize/import EPZAE-21 |
| HB79a | Heath--Brown, differences between consecutive primes II | optimized large-value inequality `hb-opt` | formalize consumed form EPZAE-19 |
| HB79b | Heath--Brown, large values for Dirichlet polynomials | classical LV input | formalize consumed form EPZAE-19 |
| HB79c | Heath--Brown, zero density and Dirichlet L-functions | `hb-density2` precursor and energy relation `hbt` | formalize EPZAE-35 and cited LV steps |
| HB17 | Heath--Brown, kth derivative estimate | beta formula | PDF/source pinned; formalize EPZAE-12 |
| Hux72 | Huxley, consecutive primes | Huxley density bound | local theorem; bridge EPZAE-25 |
| Hux96 | Huxley, *Area, Lattice Points, and Exponential Sums* | beta tables, A/B process references | book/citation; exact used rows need source verification |
| Ing40 | Ingham, estimation of `N(sigma,t)` | classical density bound | local theorem; bridge EPZAE-25 |
| Ivi80 | Ivić, exponent pairs and zeta | density-table pieces | local scan available; formalize exact EPZAE-30 inputs |
| Ivi03 | Ivić, *The Riemann Zeta-Function* | exponent-pair processes and density theorems | local scan available; citation/page crosswalk required |
| IK04 | Iwaniec--Kowalski, *Analytic Number Theory* | L2 mean value and van der Corput background | reference; prefer Mathlib/local proofs |
| Jut77 | Jutila, zero-density estimates for L-functions | `jutila-lvt` | formalize exact consumed form EPZAE-19 |
| MT24 | Matomäki--Teräväinen, zero density implies large values | reverse implication used in the database | PDF/source pinned; supporting theorem |
| Mon71 | Montgomery, *Topics in Multiplicative Number Theory* | conjectures and classical LV machinery | reference/source theorem as needed |
| Pin23 | Pintz, density near `Re s=1` | final best-known table | local PDF available; bridge only for EPZAE-30 |
| Sar95 | Sargos, integer points/short trigonometric sums/exponent pairs | D-process | formalize exact theorem EPZAE-11 |
| Sar03 | Sargos, analog of van der Corput A4 process | C-process | formalize exact theorem EPZAE-10 |
| Tao | Tao, *A cheap version of nonstandard analysis* | asymptotic methodology | reference; ANTEDB Lean API is implementation authority |
| Tit86 | Titchmarsh, *Theory of the Riemann Zeta-Function* | zeta/Euler--Maclaurin background | reference |
| TV10 | Tao--Vu, *Additive Combinatorics* | additive-energy background | reference |
| TY23 | Trudgian--Yang, *Toward optimal exponent pairs* | old hull and beta table | v3 PDF/source pinned |
| Wat89 | Watt, exponential sums and zeta II | zeta growth/LV input | reference unless a target certificate consumes it |

## Repository search verdict

The only authoritative public repository found that directly combines the
paper's formulas with Lean is ANTEDB itself. General web/GitHub searches did
not locate a separate Lean implementation of the four new exponent pairs,
the paper's zero-density table, or `Add-est`. Unrelated repositories making
Riemann-hypothesis claims were not treated as sources.

Accordingly, the implementation should collaborate with or track ANTEDB where
practical, while keeping this repository's stricter no-placeholder and
exhaustive-audit contract.

## Acquisition policy

- Prefer arXiv source archives and author/journal pages.
- Record citation-only status for copyrighted books or inaccessible journal
  scans; do not redistribute material without a clear basis.
- Reuse adjacent local source files only after recording their hash and origin.
- Never replace a pinned paper-time artifact with a moving ANTEDB `main`
  download.
- Treat the live blueprint as a useful expansion, not as the immutable 2025
  theorem statement.
