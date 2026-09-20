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

## License and redistribution record

License here means the license displayed by the authoritative source, not a
claim that every local research copy may be republished under an open license.

| Frozen material | Authoritative URL | Recorded license/status |
|---|---|---|
| Tao--Trudgian--Yang `2501.16779v1` PDF/source | `https://arxiv.org/abs/2501.16779` | arXiv non-exclusive distribution license 1.0 |
| Trudgian--Yang `2306.05599v3` PDF/source | `https://arxiv.org/abs/2306.05599` | arXiv non-exclusive distribution license 1.0 |
| Matomäki--Teräväinen `2403.13157v1` PDF/source | `https://arxiv.org/abs/2403.13157` | arXiv non-exclusive distribution license 1.0 |
| Heath--Brown `1601.04493v3` PDF/source | `https://arxiv.org/abs/1601.04493` | arXiv non-exclusive distribution license 1.0 |
| Guth--Maynard `2405.20552v1/v2` PDF/source | `https://arxiv.org/abs/2405.20552` | Creative Commons Attribution 4.0 |
| ANTEDB snapshots and frozen Lean subset | `https://github.com/teorth/expdb` | Apache License 2.0; preserved as `Dependencies/ANTEDBFrozen/LICENSE` |
| Heath--Brown 1978 twelfth-moment PDF | journal scan cited in the primary bibliography | no open redistribution license identified; retained as a pinned research/reference copy |

The arXiv non-exclusive license grants distribution rights to arXiv and is not
an open-source license. Citation-only books and journal articles are not copied
into this target. `Sources/SHA256SUMS.txt` and the principal runner bind the
installed artifact bytes independently of their license status.

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
| GM24 | Guth--Maynard, *New large value estimates...* | `guth-maynard-lvt`, density input | local completed formalization; exact kernel-checked bridges EPZAE-20/25 |
| HT69 | Halász--Turán, distribution of zeta roots | Lindelöf-implies-density theorem | supporting/reference |
| HB78 | Heath--Brown, twelfth moment | `twelfth-bound` | PDF pinned; formalize/import EPZAE-21 |
| HB79a | Heath--Brown, differences between consecutive primes II | optimized large-value inequality `hb-opt` | formalize consumed form EPZAE-19 |
| HB79b | Heath--Brown, large values for Dirichlet polynomials | classical LV input | formalize consumed form EPZAE-19 |
| HB79c | Heath--Brown, zero density and Dirichlet L-functions | `hb-density2` precursor and energy relation `hbt` | formalize EPZAE-35 and cited LV steps |
| HB17 | Heath--Brown, kth derivative estimate | beta formula | PDF/source pinned; formalize EPZAE-12 |
| Hux72 | Huxley, consecutive primes | Huxley density bound | local theorem and EPZAE-25 bridge kernel-checked |
| Hux96 | Huxley, *Area, Lattice Points, and Exponential Sums* | beta tables, A/B process references | book/citation; exact used rows need source verification |
| Ing40 | Ingham, estimation of `N(sigma,t)` | classical density bound | local theorem and EPZAE-25 bridge kernel-checked |
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

### Twelfth-moment route checked on 20 September 2026

The live author-maintained [zeta-moment chapter](https://teorth.github.io/expdb/blueprint/zeta-moment-chapter.html)
and [zeta large-values chapter](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html)
were inspected for Theorem 9.7 and Lemmas 8.4/8.11. Theorem 9.7's displayed
minimum does not match Lemma 8.11's maximum; the crosswalk records the
proved discreteness-based maximum reduction. These moving pages are
research references, not changed source pins or proof dependencies.

The already-present adjacent file
`../74 Gafni-Tao, 2026/Sources/ivic-zeta-book-scan.pdf` was read in place;
it was not copied into this project's source archive. Its SHA-256 is
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`,
and its local capture is recorded by that folder's `Sources/PINS.md`.
Its title pages identify Ivić's *Topics in Recent Zeta Function Theory*,
Orsay report 83.06; the filename is not a bibliographic identification.
Printed pages 107--115 and 127--133 contain the local mean-square
Theorem 6.2 and the large-values/twelfth-moment Theorem 7.1 and Corollary
7.2. This is a different text from the book edition referenced by ANTEDB;
its theorem numbers must not be identified with that edition's numbers.
The inspected nearby Lean modules provide conditional statements and
genuine partial analytic steps, not a proved twelfth-moment instance.
No dependency pin or archived source was changed.

### One-sided contour adaptation, 20 September 2026

Two adjacent source files were adapted into this target rather than
importing the incompatible separate package:

| Adjacent file under `../74 Gafni-Tao, 2026/Extension/GafniTao/` | SHA-256 at adaptation | Target module |
|---|---|---|
| `HeathBrownOneSidedZetaSquareContour.lean` | `9880bb13ed4d0cf80fd16a38d151a06a69430056e4d94efbd9c59a8c4e63a201` | `ZetaSquareContour` |
| `HeathBrownOneSidedZetaSquareAFE.lean` | `0a1c6c6ec8f4386994b4340c21a4a8638410a2bce070a86a4a65842cd4a10291` | `ZetaSquareContourShift` |

Changes replace imports/namespaces with the canonical Lean 4.30 native
foundation and target namespace; the unused adjacent AFE import is
removed. The target additionally proves the exact pole normalization
and lower bound. Neither adjacent file was edited. Four new target
modules prove the right-kernel majorant, complete ordinary-divisor
series with absolute integral summability, actual squared-zeta
normalization, and local sum--integral exchange. They do not import a
twelfth-moment instance or assert the uniform Theorem 6.2 estimate.
The archived paper and dependency pins are unchanged.

### Gaussian averaging continuation, 20 September 2026

The same pinned Orsay scan was inspected on printed pages 107--115
(PDF pages 112--120). Equation (6.27)'s first Gaussian majorization
is now implemented on the literal `T ± G L` window. The complete
actual-zeta Gaussian tail is proved uniformly on `L=log T`.
Equations (6.32)--(6.33) motivate the separate quadratic kernel with
coefficient `G^(-2)+i/(2T)`. Its exact integral uses
`fourierIntegral_gaussian` and `integrable_cexp_quadratic` from the
already-pinned Mathlib `Gaussian/FourierTransform.lean`, not numerical
quadrature. The actual unit-phase substitution is proved in the next
continuation; the amplitude/complete reflected-source remainder is proved
in the later continuation below.
The later shortened divisor sum, Voronoi terms, stationary
phase, and source error estimates remain open. No archived source,
package pin, or adjacent project was changed.

### Actual digamma/Gamma phase continuation, 20 September 2026

The leading logarithmic term was checked against the primary NIST
[DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2), alongside
[DLMF 5.9](https://dlmf.nist.gov/5.9). The formal proof does not import
an asymptotic expansion or assume its error. `ZetaDigammaLog` derives
`‖psi(z)-log(z)‖≤4/|Im z|` from the already-pinned
`Complex.hasSum_digamma_of_re_pos`, harmonic-number limit, elementary
unit-interval integration, and a telescoping reciprocal-square bound.
The estimate includes both height signs throughout the right half-plane.

The GammaR derivative proof (now public as `hasDerivAt_gammaReal`)
is adapted from the canonical
`71 Guth-Maynard, 2026/GuthMaynard/HughesYoungGammaRatioJets.lean`
(`hasDerivAt_GammaR_eq_mul_logDeriv_of_re_pos`, SHA-256
`41f6beb58aee0e927bbb1546d0c4c78d0be3e2a37f3ca0cb96f2fc5a344e47e6`).
Conjugation follows from Mathlib's actual Gamma conjugation and
`deriv_conj_conj`; no unfinished dependency module is imported.
The source phase is the literal reflected Gamma quotient, with an
actual zeta functional-equation consumer and exact factorization of
the existing contour normalization.

The quadratic expansion uses the pinned
`Real.abs_log_sub_add_sum_range_le` and a real-interval mean-value
inequality. The whole-line consumer uses Mathlib's actual Gaussian
integral, both physical tails, and the previously proved quadratic
frequency damping. This proves the phase component of the Orsay
scan's (6.28)--(6.33) route. The amplitude is controlled in the continuation
below; divisor truncation, Voronoi/stationary phase, and Theorem 6.2
remain open.
No paper archive, dependency pin, or adjacent source file was changed.

### Uniform amplitude/source continuation, 20 September 2026

The new shift estimate does not assume a Stirling ratio expansion.
It uses the proved actual digamma/log estimate, a principal-log path
entirely in the lower half-plane, and the pinned Mathlib
`norm_le_gronwallBound_of_norm_deriv_right_le`. The actual GammaR
derivative is the audited adaptation recorded above.

The far bound uses Mathlib's `Complex.Gamma_mul_Gamma_one_sub`
(`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`),
`Complex.two_sin`, and the native
`norm_Gamma_le_realGamma_re` in `HughesYoungContourShift.lean`.
Its linear exponential in height is derived explicitly, not taken
from the coarser native quadratic-exponential bound. The normalized
source's auxiliary Gaussian absorbs that exponential on `|u|≥t/4`.

The elementary sine-exponential calculation was adapted from the opening
of `norm_complex_sin_le_two_mul_exp_sq_im` in native
`HughesYoungCentralBounds.lean` (SHA-256
`7cbaa4755da8c373d295ac49c4a438fe3d28e70881350f29ca7b0c31af261ba9`),
then proved with the sharper linear-exponential conclusion needed here.
The imported `HughesYoungContourShift.lean` has SHA-256
`f23953d14892b53c8acbf11fbec31e9d4028e9dfce712abc58ba1143f3afcce4`.
Both are canonical native sources; neither file was edited.

The kernel and complete-series consumers use the already proved
`zetaSquareRightKernel`, actual pole/Gamma normalizations, and the
ordinary divisor terms on `Re(s+w)=3/2`. Absolute integrated-norm
summability justifies all complete-series operations. This proves
a uniform reflected-source remainder, not Ivić's shortened sum,
Voronoi/stationary reduction or sharp Theorem 6.2. No paper archive,
dependency pin, adjacent source, or preserved counterexample changed.

### Source handling

- Prefer arXiv source archives and author/journal pages.
- Record citation-only status for copyrighted books or inaccessible journal
  scans; do not redistribute material without a clear basis.
- Reuse adjacent local source files only after recording their hash and origin.
- Never replace a pinned paper-time artifact with a moving ANTEDB `main`
  download.
- Treat the live blueprint as a useful expansion, not as the immutable 2025
  theorem statement.
