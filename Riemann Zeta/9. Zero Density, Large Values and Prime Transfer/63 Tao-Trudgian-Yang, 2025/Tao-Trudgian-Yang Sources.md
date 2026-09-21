# Tao--Trudgian--Yang 2025 sources and repository survey

Current analytic progress: [Jutila physical-scale smoothing and uniform pattern bounds](#jutila-physical-scale-smoothing-and-uniform-pattern-bounds--current-checkpoint).
The moments and full-domain clauses (i)--(ii) are proved; clauses (iii)--(ix) and the full goal remain open.
Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


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

### Actual divisor weights and Gaussian-source continuation, 20 September 2026

The nine new weight/freezing/source modules use the same pinned
ordinary-divisor contour and the already recorded Orsay Theorem 6.2
route. No new source download, copied adjacent module, toolchain
change or dependency-pin change is involved.

The weight residue/reflection proof adapts the already local
`ZetaSquareContour` and `ZetaSquareContourShift` rectangle and
infinite-line arguments. The actual exponential kernel is integrated
on `Re w=1`; its reflection gives `W(q)+W(-q)=1`.
The source argument's imaginary part is `pi/2`, so the weight
is not silently replaced by a real cutoff.

Height variation uses a real mean-value bound on that actual kernel,
dominated by its integrable Gaussian envelope. The square-root mass
uses the pinned Mathlib real-power identities and the native absolutely
convergent ordinary-divisor L-series at real part greater than one.
No pointwise divisor asymptotic is a theorem hypothesis.

The conjugation bridge uses the pinned `Complex.cpow_conj`,
`Complex.conj_tsum`, Bochner `integral_conj` and change of variable
`integral_neg_eq_self`, together with the proved `gammaReal_conj`.
The actual source factor two is proved before the real zeta window is
compared with the quadratic series.
Gaussian exchange uses `hasSum_integral_of_summable_integral_norm`;
continuity of the frozen series uses `continuous_tsum` with the
proved summable coefficient majorant. The consumer
`exists_abs_zetaSquareGaussianWindow_sub_quadratic_le` composes
these real-source, tail and actual-phase results.

This closes the complete quadratic source comparison only. The
source-scale shortening corresponding to the scan's (6.34)--(6.35),
Voronoi/Bessel and stationary-phase reduction, Theorem 6.2 and the
dyadic twelfth moment remain open. The original Lemma 62 counterexample
and the authorized two-witness repair are unchanged.

### Source-scale shortening and native Voronoi boundary, 20 September 2026

The six-module continuation proves the actual finite frequency band,
its Gaussian shortening tail, uniform logarithmic scales and the
local-second-moment entry with error `Cδ G log T`.
The physical band is proved from exponentiating its exact log-frequency
condition, not from assuming a paper truncation interval. The ordinary
divisor coefficient and full complex weight are retained in
`zetaShortDivisorTestFunction`.

The proof uses the existing exact Gaussian transform and source
consumers, pinned Mathlib finite/complement infinite-sum identities,
real log/exp monotonicity, the real exponential remainder bound and
`isLittleO_log_rpow_rpow_atTop`. All six modules are new native
proofs in this package; no adjacent file was copied or edited.

The next available native theorem was inspected directly:
`DFIVoronoiTestFunction.dfiProposition1_native` in
`71 Guth-Maynard, 2026/GuthMaynard/DFIProposition1Native.lean`,
SHA-256 `006e2405784c73f037b3527fa68e7eb15d00cc61436320428e46c9bb44bcab79`.
Its actual input is `DFIVoronoiTestFunction g`, defined in
`GuthMaynard/DFIProposition1.lean`,
SHA-256 `841c8ea474b358be0d5b88be0c629087bfd7f1efb946c5b761e804c1c68c1670`.
That structure requires `ContDiff ℝ ∞ g` and support in a proved
compact positive interval. The theorem returns the main term and
both canonical Mellin--Barnes divisor transforms with their additive
characters; the ordinary-divisor use requires its modulus-one
specialization and exact transform normalization.

The hard finite band is not a smooth test-function structure. The next
continuation constructs its actual smooth replacement, pays the error,
and applies the native theorem and literal Bessel bridges as recorded
below. Uniform Bessel/stationary estimates and the sharp Ivić/Atkinson
inequality remain open source obligations. Existing adjacent
Atkinson/Gram modules do not by themselves supply those estimates or
the genuine twelfth moment.
No archive, dependency pin, adjacent source, counterexample or
corrected powering theorem changed.

### Actual smooth-source Voronoi/Bessel consumer, 20 September 2026

The eight-module continuation constructs the literal contour weight's
complex derivative with Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
Its locally uniform bound is proved from the installed Gaussian
envelope; `Differentiable.contDiff` and restriction of scalars supply
real smoothness. A fixed affine smooth-transition profile on the
exponentiated inner/outer frequency bands gives the actual positive
compact support. The change from the hard finite source is bounded
by the existing off-band Gaussian estimate.

`ordinaryDivisorVoronoi_native` specializes the already-inspected
native theorem to modulus one. The constructed test is consumed by
`zetaSmoothDivisorSum_eq_voronoi`; no native test-interface premise is
left in that theorem. The literal Bessel identifications use these
existing canonical files, inspected directly and left unchanged:

- `GuthMaynard/DFIBesselKernel.lean`: real integral definitions of
  `dfiBesselY0`, `dfiBesselK0` and their transforms;
  SHA-256 `f64faaf8ac5a810cda871cc6ef46011015636ee92182efe570a52b2c20ddb7a2`.
- `GuthMaynard/DFIBesselTransformBridge.lean`:
  `dfiVoronoiPlusTransform_mellin_eq_bessel`;
  SHA-256 `d1dc9be9fffa1e85e65f730bf7e548de0824960bb70ad1614e3457112b95c5d7`.
- `GuthMaynard/DFIEquation29.lean`:
  `DFIVoronoiTestFunction.dfiEquation29InitialMinusTransform_eq_bessel`,
  including its required contour displacement;
  SHA-256 `7d6cbe7d7c5257d6c2b2b6276e709a252485c9453ab2384831054f399708af4e`.

All paths are under the local `71 Guth-Maynard, 2026` package. No
frozen adjacent Gafni–Tao package was imported or copied.
`exists_zetaSquareLocalMean_le_bessel` and its actual physical
Gaussian companion close this source-entry edge with uniform
`Cδ G log T` error for `0<G≤T^(1/2-δ)`.
They preserve the logarithmic main term and both literal Bessel
branches with factors `-2pi` and `4`, including the zero-index
coefficient convention.

The existence of these bridges does not supply the sharp oscillatory
estimate. The following continuations discharge K0, then transfer it
to the source-aligned lattice phase. Uniform main estimates, the Y0
stationary reduction and the sharp Ivić/Atkinson inequality remain open. The known native
quarter-power Bessel bounds alone are not a substitute for that
oscillatory source analysis or the genuine twelfth moment.


### Source handling

- Prefer arXiv source archives and author/journal pages.
- Record citation-only status for copyrighted books or inaccessible journal
  scans; do not redistribute material without a clear basis.
- Reuse adjacent local source files only after recording their hash and origin.
- Never replace a pinned paper-time artifact with a moving ANTEDB `main`
  download.
- Treat the live blueprint as a useful expansion, not as the immutable 2025
  theorem statement.

### Complete modified-Bessel source estimate, 20 September 2026

The new native `ZetaBesselK0Decay` proof starts from the literal
`dfiBesselK0` real integral, not a claimed special-function asymptotic.
It uses `Real.one_le_cosh`,
`integrableOn_dfiBesselK0_integrand`,
`abs_dfiBesselK0_le_two_div_sqrt`, and Mathlib's exact
`Real.pow_div_factorial_le_exp` to obtain exponential and arbitrary
even-power decay. The canonical `DFIBesselKernel.lean` source and
its recorded hash are unchanged.

`ZetaSmoothDivisorSupport` proves the exponentiated outer-band
endpoints and hence the full smooth support in `[T/16,T]` when
`8L≤G`. This condition is derived from `G≥T^δ` at `L=log T`.
`ZetaSmoothDivisorMass` consumes the actual complex weight and
Gaussian transform. `ZetaBesselK0Integral` proves actual
measurability and absolute integrability before estimation.
The complete divisor series is summed using
`summable_divisorDirichletTerm` at `s=2`, with its literal
coefficient norm and zero-index convention; no pointwise divisor
asymptotic or moment input is assumed.

`exists_zetaDivisorBesselPlus_powerSaving` and
`exists_zetaSquareLocalMean_le_main_minus` consume the whole
source chain. The explicit lower width `G≥T^δ` belongs to the
Ivić source range; the earlier wider Voronoi entry for arbitrary
positive sub-square-root `G` remains intact. Both the power-saving
threshold and the final source-error constant precede the choice of
width.

The following continuation corrects the continuous source phase before
the main-term estimate and sharp Neumann-kernel reduction. The present coarse
absolute mass bound is used only for the exponentially decaying K0
branch, not as a substitute for that cancellation. No source archive,
native dependency file, toolchain pin, counterexample or corrected
powering theorem was changed.

### Lattice-phase convention and carrier saddle, 20 September 2026

The same pinned local `ivic-zeta-book-scan.pdf` was reread in place:
PDF pages 115--117, printed pages 110--112. Its SHA-256 remains
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`.
Equation (6.36) inserts `exp(2pi i n)=1` before Voronoi;
(6.38) uses the corresponding continuous test and (6.47) records
the resulting saddle equation. Our actual source carries
`x^(-1/2+iT)`, the opposite sign, so `ZetaDivisorLatticePhase`
uses `exp(-2pi i x)`. This is an exact convention bridge on every
natural index, not a claim that the phase is one for real x.

`ZetaAtkinsonVoronoi` constructs and consumes the new smooth
native test. `ZetaAtkinsonK0` transfers the actual norm majorant,
proves the new integrability and complete divisor summation, and
obtains arbitrary power saving. `ZetaAtkinsonReducedSource`
applies that result to the genuine physical Gaussian/local moment.
No equality of old and new continuous Bessel integrals is asserted.

`ZetaAtkinsonPhase` factors the actual test while retaining its
complex amplitudes, and differentiates the real carrier
`T log x - 2pi x + 4pi b sqrt(x)`. `ZetaAtkinsonSaddle`
proves that its unique positive saddle is
`((b+sqrt(b²+4T/(2pi)))/2)²` and that the second derivative
there is strictly negative, for all real b and T>0. Thus both
prospective Bessel signs and the zero-index main carrier are covered.
Mathlib's exact logarithm/square-root derivative and positive-axis
complex-power identities are used; no stationary-phase theorem is
postulated. The literal Y0 expansion is proved below; uniform stationary
source estimates and the sharp Ivić inequality remain open.

All six modules, 40 named public audits and 22 regressions are
covered by the root and batch-runner inventory. No scan was copied,
source/dependency pin changed, adjacent package edited, or original
counterexample altered.

### Actual logarithmic main-term estimate, 20 September 2026

The canonical native `GuthMaynard/LargeValuesReflection.lean`
was inspected in place. SHA-256:
`91b34cff0e5f72a6dbbd844e03f4c98ae06344d5d5e6b767869e8418d7177534`.
`norm_gmReflectionIntegral_le_ten_div_sqrt` proves the uniform
`10/sqrt(tau)` bound for the literal `x^(-1)` logarithmic
reflection kernel on every positive interval, for `tau≥1`.
`norm_weighted_gmReflectionIntegral_le` inserts a complex C1
amplitude with its actual endpoint norm and derivative-norm integral.
The carrier is exactly `tau log x - 2pi x`, matching the
phase-adjusted main source. No new black-box stationary theorem
or special-function asymptotic is assumed.

`IntervalAmplitudeBounds` records and composes literal C1
supremum/variation bounds. The source constructs all instances.
`ZetaMainElementaryWeights` uses Mathlib's monotone smooth
transition and exact positive square-root/logarithm derivatives.
`ZetaMainMellinProfile` uses the already proved holomorphy of
the actual contour weight on a fixed positive compact interval.
Its source argument after `x/T` rescaling is proved equal to
the profile, including the imaginary `pi/2` component.

`ZetaQuadraticGaussianDerivative` differentiates the exact
complex Gaussian transform. `ZetaLogGaussianVariation` and
`ZetaQuadraticLogGaussianVariation` retain the Gaussian damping
and prove uniform variation `4 sqrt(pi) G` for the actual
logarithmic transform. `ZetaAtkinsonMainWeight` combines every
factor; `ZetaAtkinsonMainIntegral` proves absolute integrability,
the support/reflection identity and `norm(V0_A)≤C G log T`.
`ZetaAtkinsonMinusSource` applies the bound to the actual physical
Gaussian and local zeta mean. The complete Y0 sum and its `-2pi`
normalization remain. Nine modules, 38 named audits, 20 regressions.

This closes the main-integral estimate only. The literal Y0
expansion is proved below; uniform oscillatory stationary reduction,
sharp Atkinson inequality and genuine twelfth moment remain open.
The native source file was imported, not copied or edited. No
source scan, dependency pin, adjacent package or counterexample
was changed.

### Y0 asymptotic research: references, not an imported proof

Checked online on 20 September 2026: [DLMF 10.17.1--4](https://dlmf.nist.gov/10.17#i)
and its [real-argument remainder bounds](https://dlmf.nist.gov/10.17#iii).
Specializing to order zero gives the candidate two-term expansion

```text
Y0(z) = sqrt(2/(pi z)) * (sin(z-pi/4) - cos(z-pi/4)/(8z)) + R(z),
|R(z)| ≤ sqrt(2/(pi z)) * (9/(128z²) + 75/(1024z³)), z>0.
```

This specialization uses one term of each even/odd series. It gives
`R(z)=O(z^(-5/2))` for `z≥1`. The proposed application, now
proved below with a different explicit bound, is that at
`z=4pi sqrt(nx)` the remainder has a summable
`n^(-5/4)` divisor weight, whereas a one-term absolute remainder
would only give `n^(-3/4)`. The bridge to the literal native
`dfiBesselY0` and the complete arithmetic replacement are proved
below; stationary-phase evaluation is still required. No DLMF statement is used as
a Lean premise or a kernel oracle.

The current [Mathlib Bessel documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Bessel.html)
provides first-kind `Complex.besselJ`; its TODO lists second-kind
functions and integral representations. The local pinned Mathlib
search found no Bessel-named source file. This is a limited reuse
check, not a claim that no external Lean development exists. The
dependency pin is unchanged; the actual native kernel is the
object estimated by the following proof.

### Literal Neumann ray and complete source replacement, 20 September 2026

[DLMF 10.9.5](https://dlmf.nist.gov/10.9.E5) gives the order-zero
Schläfli normalization used for comparison with the native definition;
[DLMF 10.17.1--4](https://dlmf.nist.gov/10.17#i) fixes the signs
of the two oscillatory coefficients. These are reference checks, not
formal imports. No source theorem, asymptotic or remainder is assumed.

The local proof starts with the literal `dfiBesselY0Osc` and
`dfiBesselY0Tail`. Cauchy's rectangle identity for
`exp(ixz)(1-z)^(-1/2)(1+z)^(-1/2)` is passed to two infinite
vertical rays. The positive angular endpoint is approached only
after proving continuity of the integrable ray through one.
The ray through zero equals the native tail, which cancels exactly.
Thus `dfiBesselY0_eq_neumannLaplaceIntegral` identifies the actual
kernel with an exponentially decaying integral, not a substitute.

The elementary inverse-square-root remainder
`|(1+iu)^(-1/2)-1+iu/2|≤3u²/8` is proved algebraically using
the principal square root and `Re sqrt(1+iu)≥1`. Mathlib's actual
Gamma integral evaluates the moments. The resulting theorem
`abs_dfiBesselY0_sub_neumannTwoTerm_le` proves, for every x>0,

```text
P(x)=sqrt(pi)/pi*((sin x-cos x)x^(-1/2)-(sin x+cos x)x^(-3/2)/8),
|dfiBesselY0(x)-P(x)| ≤ ((2/pi)(9/128)sqrt(pi)) x^(-5/2).
```

The retained terms match the expanded sine/cosine normalization;
the displayed explicit remainder is the local proved bound, not a
claim that the earlier DLMF bound was imported verbatim.

`GuthMaynard/DFIEquation24.lean` was inspected and imported in place.
SHA-256:
`2011e38c332aeda0ada42c73a44014f31711c75dfd25ac55047f8aafd7245474`.
Its `summable_norm_dfiVoronoiDualTerm` supplies summability of the
original complete minus branch; the actual smooth test and literal
Bessel bridge identify the terms before it is used. The ordinary
divisor Dirichlet series at `5/4` sums the proved remainder.
All original, remainder and new two-term series are genuinely
summable. Zero-index coefficients and all `-2pi` factors are retained.

`exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le` gives the
complete uniform error `C G` on `T≥16`, `G>0`, `G²≤2T`,
`L>0`, `8L≤G`. The actual physical Gaussian and local-mean
consumers in `ZetaAtkinsonTwoTermSource` then give `Cδ G log T`
on `T^δ≤G≤T^(1/2-δ)` beyond one uniform threshold. Their
signatures contain no analytic theorem parameter. Thirteen modules,
71 public audits and 25 regressions are covered by the root and
exact batch-runner inventory.

Uniform stationary evaluation of the actual two-term series, the sharp
Ivić/Atkinson inequality, genuine twelfth moment and unconditional
Add-est outputs remain open. No dependency pin, native source,
source scan or preserved counterexample was changed.

### Signed-carrier integral source audit, 20 September 2026

The new cancellation proof uses the pinned native theorem
`ZetaAppendix.nonstationary_phase_integral_bound`, imported through
`GuthMaynardExternal.PNT.ZetaAppendix`. The native file is
`../71 Guth-Maynard, 2026/GuthMaynardExternal/PNT/ZetaAppendix.lean`;
SHA-256:
`9fad94d5a7026d86882df61147b1082b103caf555ac803f0b1b52efd8bc28d9f`.
It was inspected and imported in place, not copied or edited.
The local Mathlib search did not find the required complete
stationary-value theorem; no such theorem is presumed available.

The native estimate requires a nonzero derivative and continuous
monotone absolute reciprocal slope. `AtkinsonFirstDerivative`
constructs these hypotheses from the actual C2 phase and slope.
Its negative-slope bound is `1/(lam*pi)`; the positive-slope
version follows by the proved reflection `x↦-x`, with the
integral orientation and `2pi` normalization retained.
`AtkinsonRootPhase` proves the square-substituted phase and
derivatives, including `q''=-T/(pi*y²)-2`.
The exact saddle factorization puts the left and right tails in
the native estimate's domain. `AtkinsonRootIntegral` combines
them with a central length bound to give the uniform bound four.

Mathlib's interval substitution and integration-by-parts theorems
then apply to actual derivatives and actual positive support.
`IntervalC1Bound.comp_sq` proves preservation of the derivative
mass; `IntervalC1Bound.atkinsonRoot` proves the weighted bound
`8M`. `AtkinsonPowerWeight` constructs the needed amplitude
bound from the fixed power/Mellin profile, cutoff, unit Gamma
factor and damped Gaussian. `AtkinsonPowerIntegral` proves the
exact source Jacobian and the uniform bound `Cα G T^(-α)`.

The carrier algebra is derived from the already proved literal
Neumann two-term expansion, not from a new assumed asymptotic.
Actual integrability precedes linearity; complete summability
comes from the actual convergent two-term source. The leading
and correction estimates give powers `n^(-1/4)` and
`n^(-3/4)`; these are not used as summable majorants.
The actual physical Gaussian and local-mean consumers retain
the whole series and the uniform source error.

The canonical
[Ivić Orsay scan](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf)
was located again; browser retrieval exceeded the 10 MiB limit.
No new page content from that attempt is used as evidence.
The previously recorded local scan and source conventions remain
unchanged. No package or external theorem was installed.

Ten modules, 43 public audits and 24 regressions cover this scope.
Uniform stationary main values and sharper arithmetic tails,
the sharp Atkinson inequality, genuine twelfth moment and all
unconditional Add-est outputs remain open. No native source,
dependency pin or preserved counterexample changed.

### Actual frequency tails and complete correction removal

The next proof reuses the same pinned native reciprocal-slope
theorem, without importing a stationary-value assertion.
On `sqrt(T/16)≤y≤sqrt(T)`, the exact actual slope satisfies
`q'(T,b,y)≥b` and `q'(T,-b,y)≤-b` when
`b≥8sqrt(T)`. Its monotonicity was already proved.
The weighted primitive lemma now retains a variable primitive
bound B, giving `2 B M` for the actual C1 amplitude.
Consequently `exists_norm_atkinsonPowerIntegral_far_le`
proves `Cα G T^(-α)/b` for both signs, including the
threshold equality, on the original physical support.

The correction argument is a local proved estimate, not an
assumed literature input. Below the threshold it uses
`T^(-3/4)sqrt(T)≤1` for T≥1; above the threshold it
uses the proved reciprocal-frequency gain. This yields
`C G/sqrt(n)` for the actual correction pair, n>0.
The exact `n^(-3/4)` coefficient turns the result into
`C G |divisorDirichletTerm(5/4,n)|`; n=0 is handled
by its genuine zero divisor coefficient.

The ordinary-divisor Dirichlet theorem already imported from
the native project proves absolute summability.
`GuthMaynard/HughesYoungAFE.lean` defines the actual
`LSeries.term` and proves `summable_divisorDirichletTerm`
for `1<Re(s)`, consumed here at `s=5/4`. It was inspected
in place; SHA-256:
`8b500bf307d4faa135cbff55f52e827216840bc1d0ffa8bd84e46f858ed0a1cb`.
No native source was copied or edited. The complete
correction has norm at most `C G`; exact subtraction from
the genuinely convergent two-term source proves summability
of the full leading series. Both physical zeta theorems then
consume the bound with unchanged factors and width ranges.
Four modules plus one generalized helper, 19 new public audits
and 16 regressions cover this continuation.

The remaining leading stationary main values, sharper leading
arithmetic tails and genuine twelfth moment are not supplied
by that convergence argument. All unconditional Add-est outputs
remain open. The native file/hash, all dependency and source
pins, archived texts and preserved counterexample are unchanged.

### Constructed C2 bounds and exact Fourier-tail source

The pinned native `GuthMaynard/DFIParametricMellin.lean` was inspected
and imported in place. SHA-256:
`d07da5016fb76403dabaa23c377ca137ddf78c78767a03b9ac5303a92d9e4b42`.
Its `one_add_abs_fourier_decay_of_support_of_bounds_order` at order two
consumes actual smoothness, compact support and global derivative bounds.
It derives from Mathlib Fourier integration by parts; it is not a
stationary-value theorem. Mathlib's
`Real.fourier_real_eq_integral_exp_smul` fixes the signed frequency
-2b sqrt(T), and its interval scaling theorem supplies the exact Jacobian.

The cutoff's exponential edges, Gaussian Q'', fixed logarithmic profile
and nonlinear phase all have constructed derivative bounds. Extension
by zero retains only the positive root; the actual band supplies smoothness
at zero. The resulting bound for the true leading term is
C G T^(5/4) |divisorDirichletTerm(5/4,n)|. The same native
`summable_divisorDirichletTerm` recorded above is used at 9/8 to bound
the tail by C G T^(5/4) N^(-1/8), not an assumed arithmetic estimate.
N≥T^10 gives C G and is consumed in both physical zeta source theorems.

This local coarse truncation is not attributed to Ivić as his sharp
conclusion. Evaluated stationary mains and source-scale localization
are proved by the later local deductions below; the summed stationary
error, sharp Atkinson assembly, twelfth moment and unconditional Add-est
outputs remain open. Fifteen modules,
59 named public audits and 20 regressions cover this continuation.
No native source, dependency pin, source archive or counterexample changed.

### Paired saddles and actual finite stationary reduction

Rechecked the primary [Ivić Orsay scan](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf).
The online reader again rejected the PDF above its size limit; the
already pinned local scan was read instead, printed pages 107–115,
including Theorem 6.2, (6.22), and (6.47)–(6.51). SHA-256 unchanged:
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`.
Its title is *Topics in Recent Zeta Function Theory*, Orsay 83.06,
not the ANTEDB-cited book edition. No source was silently replaced.

The phase definition was also checked against the adjacent
`GafniTao/HeathBrownAtkinsonPhase.lean`, inspected in place, SHA-256
`a42e7b9e7dbad92a9c7fd1f8a2859207d8d29241503eea259429386656cb7fa9`.
Its source comment cites Heath–Brown (1978), (11). No adjacent package
or conditional twelfth-moment proposition was imported.
Our symmetric source retains both saddles; the lower-side truncation
in Ivić's derivation does not authorize discarding one here.

The exact logarithm/arsinh bridge, both alternating phases, actual
paired complex Gaussian, natural derivative scale and cubic log error
are locally proved using pinned Mathlib calculus/logarithm bounds.
The outer integrals consume the existing native reciprocal-slope test.
`exists_atkinsonPowerIntegral_small_n_pair_approximation` is a
locally derived finite-quadratic reduction, not an attribution of
Ivić's sharp conclusion: it uses 10000n≤T and H≤sqrt(T)/12 and
retains the actual finite quadratic integral and both physical amplitudes.

Twelve modules, 71 public audits and 22 regressions cover this continuation.
Fresnel evaluation is now proved below. Sharp source-scale localization/
error summation and the genuine twelfth moment remain open. Native files, source pins,
archives and preserved counterexample are unchanged. Keep the exact
batch runner and backing inventory synchronized.

## Fresnel normalization and locally proved stationary power saving

Primary normalization checked online: [NIST DLMF §7.2(iii)](https://dlmf.nist.gov/7.2.iii),
equations 7.2.7–7.2.9, defines the cosine/sine Fresnel integrals with
phase pi t²/2 and gives their positive-infinity limits as 1/2.
With t=2sqrt(c)z and the negative complex phase, our symmetric
normalization is (1-i)/(2sqrt(c))=exp(-i pi/4)/sqrt(2c).
This comparison checks the sign and scale; it is not a proof oracle.

The local proof uses pinned Mathlib's
`integrable_cexp_neg_mul_sq`, `integral_gaussian_complex_Ioi`,
`continuousAt_cpow_const` and `Complex.sq_cpow_two_inv`, with
actual integrable positive damping, a locally proved damping-uniform
tail and a finite-interval Abel limit. It proves the explicit remainder
2/(c H pi) and the principal branch, with no whole-line zero-damping
Lebesgue-integrability claim.

The evaluated stationary consumer and choice H=T^η/12 are local
deductions from the already constructed carrier amplitude and tails.
The source-width bound uses η=min(δ/3,1/10), retains both physical
signs and their separate profiles, and applies only to 10000n≤T.
It is not attributed to Ivić as a complete sharp Atkinson formula.
Sharp localization and summed errors remain missing.

Nine modules, 35 public audits and 16 regressions are in the exact
batch-runner inventory. No dependency pin, source archive, native file
or preserved counterexample changed; both principal runners remain
mandatory. The full goal, twelfth moment and unconditional Add-est remain open.

## Source-scale tail: local deductions from the pinned source

No additional paper, dependency or external theorem was imported.
The original cutoff has edges (T/(2pi)) exp(±2L/G).
Combining these actual edges with the already proved saddle logarithm
gives |b|≤3sqrt(T)L/G. The actual root-band restriction is proved by
support and the square change of variables, not by assuming localization.

The quantitative reciprocal-slope second derivative, both integrations
by parts, vanishing actual endpoints and band length are locally proved.
The resulting bound Cα G² T^(-α) L/(sqrt(T)n), n≥36T(L/G)², is
summed using the already pinned ordinary-divisor Dirichlet series at 5/4.
Both physical zeta consumers retain the actual leading integral sum and
Cδ G log T error, with the new source-scale cutoff. Ceiling rounding and
the retained-index stationary range are proved, including 10000N≤T
eventually on the lower power-width range.

This is not an attribution of the complete sharp Atkinson formula to
the new local estimate: summed stationary errors and final main assembly
remain missing. Eleven modules, 53 named audits and 22 regressions
cover the continuation. Source pins, native files, archives and the
counterexample are unchanged. The exact batch runner and both evaluation
scopes remain mandatory; the full goal and unconditional Add-est remain open.

## Symmetric summation and a renewed width-range check

The [Ivić Orsay scan](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf)
was rechecked locally at printed pages 107–109 and 127–130.
The web reader again exceeded its PDF size limit. Text extraction and
visual inspection of printed page 130 confirm that (7.20) links
B G (log T)²=V² and that the proof uses G≤T^(1/3); an estimate only
for G≥T^(1/3) would not supply the missing range.
The existing adjacent PDF remains SHA256
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`.
A PDF reader installed under ignored workspace `.tmp` was used only
for inspection, not as a Lean dependency or proof oracle.

The new local proof uses the actual logarithmic quartic remainder,
a kernel-checked complex exponential remainder, C2 amplitude control,
and exact odd cancellation. Its radius T^(1/4)/(12sqrt(G)) is derived
for G≥T^(1/4). The actual quarter-weighted divisor prefix is controlled
through absolute convergence at 1+ε, and the ceiling cutoff gives a
summed Oε(T^(1/4+ε)) retained error. Both physical zeta consumers use
the complete evaluated series, retaining both coefficients and profiles.

Their error is Cδ,ε (G log T+T^(1/4+ε)), or Cδ,κ G log T above
T^(1/4+κ), within the original power-width range. This is not attributed
to Ivić as a proof of his full-width Theorem 6.2. Smaller widths, any
necessary lower-value-range reduction, final main assembly and the
genuine twelfth moment remain open. Ten modules, 43 audits and 24
regressions cover the continuation. All source pins, archives and
native files, and the preserved counterexample, are unchanged.

## Source fidelity of the normalized main and Abel step

The renewed [Ivić source check](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf)
used the existing scan's printed pages 107–109: Theorem 6.2,
the dyadic phase-sum bound and the weighted sum preceding partial
summation. No source pin or file changed. This is the Orsay text,
not a substituted edition of the book cited in the paper's blueprint.

The five new modules derive their normalization from local identities,
including the exact saddle-curvature product and original Bessel constants.
Finite partial summation consumes Mathlib's `Finset.sum_range_by_parts`
in `Mathlib/Algebra/BigOperators/Module.lean` at the existing pin.
There is no new external proof dependency.

The actual weights remain separate: only the raw phase sums are conjugate.
Their pointwise fourth-root/Gaussian bound and the literal finite-difference
Abel consumer are proved. The continuation below supplies the uniform
damped variation estimate and an actual source-block consumer. Four physical consumers retain the preceding explicit
fourth-root-width restrictions and error terms. These results are not
attributed to Ivić as a completed proof of his full Theorem 6.2.
The smaller-width route, dyadic/Gram argument, genuine twelfth moment and
unconditional Add-est remain open. All 30 public theorems are audited,
and 24 regression examples retain exact source objects and endpoints.

## Source fidelity of damped variation and actual block bounds

The existing [Ivić Orsay scan](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/86/6d/866d1cf0-a942-4f8a-9d30-7cb3b03e1b1c/i_ivic-66.pdf)
was rechecked at printed page 108, equations (6.24)–(6.25), using
the local PDF after the web reader again exceeded its size limit.
The retained PDF is unchanged, SHA256
`fafac152db87abe132858fa97d8fe501c61cd261e20732ef701396fba27b61aa`.
The source uses dyadic phase sums and an endpoint-plus-integral bound
after partial summation. The new finite maximum of raw partial sums is
a locally proved block majorant, not an asserted identity with that
source expression or a completed Gram estimate.

The new analytic input from the existing Mathlib pin is
`norm_sub_le_integral_of_norm_deriv_le_of_le` in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean`.
It bounds actual complex Gaussian increments by the integral of their
already proved derivative majorant. The explicit real Gaussian primitive
and finite telescoping produce damping with no block-length loss.
Ordered saddle samples and the already constructed compact C2 Mellin
bound give uniform variation of the actual residual profiles; both
original cutoff transitions and both signed weights are retained.

`exists_finiteVariationBound_atkinsonMainWeights` and
`exists_atkinsonSourceCutoff_block_bound` are local deductions with
all constants before the physical parameters. The latter consumes the
actual stationary terms and derives the small-frequency range from the
same source ceiling cutoff. Its range is the original power-width
range, but it does not extend the older stationary-error estimate below
G=T^(1/4).

Six modules, 36 named audits and 24 regressions cover this continuation.
No dependency pin, native file, archive, preserved counterexample,
production exclusion or diagnostic gate changed. Maintain the exact
`run_tao_trudgian_yang_build.bat` inventory and run both principal
scopes. Global dyadic assembly, the source-shaped phase-sum/Gram argument,
smaller-width errors or a proved lower-value reduction, the genuine
twelfth moment and unconditional Add-est remain open; the full goal
is unchanged.

## Exact truncated dyadic assembly: source and API fidelity

The new partition is a local proof, not an imported paper theorem.
At the existing Mathlib pin it uses `Nat.clog`,
`Nat.pow_lt_of_lt_clog` and `Nat.le_pow_clog` from
`Mathlib/Data/Nat/Log.lean`, together with the finite range-splitting
identity `Finset.sum_range_add`. A direct induction proves the
partition, including the shortened final block and exact powers of two.

The actual stationary zero coefficient and finite-support theorem then
supply the complete source identity. The previously proved block bound
is applied only before the exact source ceiling. The monotonicity proof
for raw phase-prefix maxima may enlarge the last phase block to a full
one, but never asserts that stationary geometry holds beyond the cutoff.

The four physical consumers bound actual Gaussian/local zeta means by
the resulting full-block phase majorant plus the existing error.
The Gaussian conclusion is an upper bound, not a signed approximation.
The fourth-root-width restrictions of the earlier stationary error are
unchanged. The source's maximal phase/Gram estimate and any necessary
comparison with Ivić's endpoint-plus-integral expression remain separate
obligations; none is silently assumed or attributed to the source.

Three modules, 20 named public audits and 24 regressions cover the
continuation. No new dependency, source pin, archive, native file,
warning gate or production exclusion changed. The original counterexample
and repaired powering/Heath–Brown chain are unchanged.
The exact batch interface and both principal evaluations remain required.
Smaller-width estimates or a proved low-value reduction, the genuine
twelfth moment and unconditional Add-est remain open.

The adjacent Gafni–Tao `HeathBrownAtkinsonPrefixGram` and
`HeathBrownAtkinsonGramBound` modules were inspected read-only.
The former proves Bombieri–Halász for a common integer prefix j at
every height on (K,2K]; the latter bounds exact full-block Gram entries
using the actual two-height phase. Neither statement alone supplies
the present height-dependent prefix maximum on [M,2M).
The continuation below proves variable-prefix finite duality directly.
A faithful reuse of the adjacent analytic estimates still requires an
endpoint/general-prefix bridge and uniform truncated Gram bounds. No adjacent module or conditional
twelfth-moment statement was added as a dependency.

## Height-dependent prefixes: local finite proof and native arithmetic

The native `GuthMaynard.ClassicalLargeValues` module supplies finite
phase alignment, coefficient Cauchy–Schwarz and the Gram expansion.
`FinitePrefixGram` combines those exact results into a norm-sum
inequality for arbitrary height-dependent vectors.
`AtkinsonPrefixVectors` specializes to the actual divisor coefficient
and source phase, using `unitaryPhase` from native
`GuthMaynard.VanDerCorput`. That convention is exp(iθ), with θ in
radians; the equality with the source's exp(θi) is proved.

The maximum is attained using Mathlib's
`Finset.exists_mem_eq_sup'` in `Data/Finset/Lattice/Fold.lean`.
Masking proves the actual pairwise minimum-prefix identity before
finite duality is applied. This is a new local derivation on [M,M+j),
not an imported common-prefix theorem on (K,2K].

Native `GuthMaynard.DFIErrorTerms.exists_norm_divisorWeight_le_rpow`
at ε/2 proves the actual block coefficient energy bound Cε M^(1+ε).
The inspected adjacent `HeathBrownDivisorSquare` and its stronger
logarithmic arithmetic estimate are not dependencies of this proof.
No sharp divisor-square logarithmic asymptotic is claimed.

The adjacent Gafni–Tao full/prefix Gram and explicit B-process /
first-derivative modules were inspected read-only for the next analytic
stage. Their results are not treated as numerical estimates for the
present height-dependent truncated Gram entries without an endpoint
and general-prefix bridge. The finite result does not prove those
analytic bounds or their separated-height sum.

The actual stationary and local-excess consumers derive the cutoff
ceil(72H(log(2H)/G)²) and preserve the original source errors and width
restrictions. Gaussian damping is removed by a proved upper bound;
the final finite budget retains literal coefficient energy.
Eight modules, 41 named public audits and 24 regressions cover this
checkpoint. No new dependency, source pin, archive, native file,
production exclusion or diagnostic gate was introduced.

ZMG records finite maximal-prefix assembly and actual consumers;
The continuation below proves uniform truncated phase-difference bounds;
ZGB retains separated-height summation and scale optimization as open. The source-form bridge, smaller-width error
or a proved low-value reduction, genuine twelfth moment and
unconditional Add-est remain open under the unchanged full goal.
The original counterexample and corrected powering/Heath–Brown chain
are unchanged. Maintain `run_tao_trudgian_yang_build.bat`, its exact
backing inventory and both principal evaluation scopes.

## Truncated cancellation: adapted real-index proofs and native entry

The six adjacent Gafni–Tao real-index modules were read completely and
adapted locally to the target's already connected
`atkinsonSourcePhase`. They are not imported as a new package.
The inspected source paths, relative to
`74 Gafni-Tao, 2026/Extension/GafniTao`, and SHA256 hashes are:

- `HeathBrownAtkinsonRealPhase.lean`:
  `ba83fc0edbc619c7650c741bcd9d1d0d8c4e619d0df3b74f1b0bd7bb09c120f5`.
- `HeathBrownAtkinsonRealCurvature.lean`:
  `36530f4ebf575c8f930ddc2885c6c0a0e0d90f2c9205050d46db15869f2d7af2`.
- `HeathBrownAtkinsonCurvatureHeight.lean`:
  `a269da4c7d923297a2a95908102935a273157c8ce8c02e891527d44e373cde25`.
- `HeathBrownAtkinsonCurvatureScale.lean`:
  `0b5587c001377b53dca695e67dedbd18ad5d7eec0e2f629cfe003c38f5684cbc`.
- `HeathBrownAtkinsonBProcess.lean`:
  `51851547d1eeee799726a4bf594371538ed3a8bc1d028ce3d279a0698363615d`.
- `HeathBrownAtkinsonFirstDerivative.lean`:
  `d4d38fe39c2b2237b6edb8697ca97a84f65040775689b116d9cd8a0796978780`.

The literal phase agrees at natural indices by its definition, including
the radian convention and -π/4 term. Exact real-index derivatives,
height derivatives and uniform curvature bounds are proved, not assumed.
The target uses current `GuthMaynard.SecondOrderMeanValue`,
`vanDerCorput_B_process` in `GuthMaynard.SecondDerivative`, and
`kusminLandau_one_period_decreasing` in `GuthMaynard.VanDerCorput`.
Their actual signatures were inspected before use.

The new prefix application is local: fixed ambient derivative parameters
are restricted to every shorter prefix [M,M+j), including zero.
No (K,2K] terminal estimate is silently reused for an unknown prefix.
The previously inspected adjacent `HeathBrownAtkinsonSeparatedGram`
was also checked: it is a diagonal/off-diagonal ledger, not a completed
spacing estimate. Its title is not treated as proof of separated-height
summation.

The actual cutoff at 2H now supplies every block's mean-value endpoints,
and actual physical consumers use the numerical gap bounds.
The ordinary-divisor epsilon-energy theorem is now genuinely consumed,
giving the dyadic weight M^(1/2+η). This is not a claim of the sharper
logarithmic divisor-square asymptotic. All physical local-source errors
and fourth-root-width restrictions are retained.

Thirteen modules, 79 named audits and 30 regressions cover the
continuation. ZPC records uniform truncated cancellation and the actual
numerical consumers; ZGB retains separated-height summation and scale
optimization as open. The source-form bridge, smaller-width error or a
proved low-value reduction, genuine twelfth moment and unconditional
Add-est remain open under the unchanged full goal.

No new dependency, source pin, archive, native file, production exclusion
or diagnostic gate changed. The original counterexample and corrected
independent powering/Heath–Brown chain are unchanged. Maintain
`run_tao_trudgian_yang_build.bat`, its exact backing inventory and both
principal evaluation scopes.

At the preceding checkpoint, native `separated_annulus_card_le_two`
and `sum_inv_distance_near_le_harmonic` in
`GuthMaynard.ClassicalLargeValues` were inspected, together with
`GuthMaynard.ScaledSeparated` and the target's existing
`sum_zetaMomentKernel_le_harmonic`. They were then available inputs.
The subsequent near-height checkpoint consumed the native reciprocal-gap
estimate after proving physical rescaling; the current checkpoint below
also proves the far-height estimate.

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

### Point-value entry source rechecked, 21 September 2026

[Huxley–Ivić, arXiv:math/0611809v3, Section 2, equation (2.1)](https://arxiv.org/pdf/math/0611809v3)
states
`|zeta(1/2+iT)|^2 << log(T)*(1+integral_(T-log(T)^2)^(T+log(T)^2)|zeta(1/2+it)|^2 dt)`.
Its explanation invokes a contour integral of squared zeta times Gamma
and the functional equation. Its references are Ivić's 1991 TIFR
Lecture Notes 82, Theorem 1.2, and the 2003 Dover zeta book,
Lemma 7.1—not the theorem numbering of the adjacent Orsay scan.

This is a research input to prove, not an imported Lean theorem.
No archived source or pin was changed. The original larger Orsay PDF
exceeded the web fetch limit, and local PDF extraction packages were
unavailable; the smaller primary arXiv paper was successfully read.
The missing entry must account for the additive term and window
radius. Separately, our remaining counting argument must preserve
cluster occupancy when passing from unit-separated point values to
G-separated local-mean windows; selecting one point per window alone
does not justify the desired pointwise count.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions and linter
failures. The target audited 2,847 declarations (2,842 discovered
target theorems plus five imported contracts); all 27 new regressions
passed. Exact commands, logs, hashes and coverage are in the current
Reproduction Manifest. This verifies local-integral superlevel counting,
not pointwise zeta large values, the twelfth moment or Add-est.

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

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions or linter
failures. The target audited 2,890 declarations (2,885 discovered
target theorems plus five imported contracts); all 46 new regressions
passed. The foundation audit covered 14,290 declarations and its
manifest reports PASS with no failed stages. Exact logs and hashes
are in the current Reproduction Manifest. This verifies the Gamma
and overlap components, not the still-open pointwise zeta entry,
twelfth moment or unconditional Add-est.

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

Verification (2026-09-21): both principal scripts were polled to terminal
exit 0. The target reports `LEAN VERIFICATION PASS`, covering all 299
package files and 3,104 audited declarations (3,099 discovered target
theorems plus five imported contracts). All 129 new named audits and
136 new regressions pass. The foundation reports `PASS`, with 14,290
discovered theorems audited and all six stages passed. Neither final
evaluation has a Lean error, warning, tactic suggestion or linter failure.
Exact logs, hashes and the repaired intermediate comment-scan failure are
recorded in the current Reproduction Manifest. The counterexample hash is
unchanged. This verifies Lemma 3 and the finite point-entry consumer;
occupancy-aware counting, the genuine twelfth moment, unconditional Add-est
and the full goal remain open.

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

### Source and API verification for the unweighted input

Local inspection confirms that `TypeIIZeros.twistedZetaMomentIntegrand`
contains the short Möbius polynomial, and the native
`twistedZetaFourthMoment_native` bounds that mollified object.
It does not yield the required unweighted fourth moment by deleting
the factor. The current route instead composes the target's proved
`ZetaSquareRealSource`, `ZetaSquareDivisorSeries`, Gamma-amplitude
bounds and Mathlib contour/integration APIs. This is a local proof
construction, not a claim that an external Lean theorem was found.

The primary [Radziwiłł paper](https://arxiv.org/abs/1106.4806)
records the classical fourth-moment result as background; its
higher 4.36-moment result is conditional on RH and is not used here.
The [author-hosted text](https://math.mcgill.ca/radziwill/moment.pdf)
was also located. Searches did not supply a verified external Lean
unweighted-fourth-moment implementation for this checkout; this is
not an exhaustive claim of global absence. No new downloaded source,
archive, toolchain pin or dependency is installed.

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

### Exact reused APIs for the current moment proof

The source was checked against the installed, unchanged pins and the
frozen nine-clause table, not against numerical optimization output.
The ordinary-divisor prefix uses the native
`integral_norm_sq_dirichletTime_le`, `endpointTwist`,
`norm_endpointTwist` and `divisorCountBound_native`.
The actual entry is `zetaSquareNorm_eq_two_re_fourthRightPiece` and the
mixed-line contour identities already recorded in the preceding source
checkpoint. The exact generic analytic inputs are Mathlib's monotone
sum/integral comparison, improper real-power integral, Gaussian integral,
Bochner product integrability/Fubini and real-power monotonicity.
The unweighted moment is derived here from these inputs; it is not
inferred by deleting the mollifier from `twistedZetaFourthMoment_native`.

The separate Ivić/Atkinson sharp source-form statement remains open.
The moment result above therefore does not retroactively mark that
different source contract proved. The printed Add-est (i) interval and
maximum agree exactly with the frozen Crosswalk and pinned source.

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

Source check: the frozen paper TeX's `Add-est` item (ii) supplies the
literal maximum and closed interval. The detailed frozen ANTEDB blueprint
`zero_density_energy.tex`, label `imp-energy-bound2`, supplies the
general-energy optimization route. The local proof independently supplies
the short-zeta range, avoiding reliance on the still-open endpoint-two
corollary. No external numeric search or solver output is proof evidence.
The paper archive, frozen blueprint and dependency pins are unchanged.

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

### Exact local inputs for this checkpoint

The pinned foundation supplies `finitePowCoeff_bound_uniform`,
`wideDirichletPoly_finitePoweredLineCoeffs`,
`heathBrownWeightedMeanSquare_native`,
`gmReflectionDirichletPoly_eq_one_add_wide`,
`heathBrownTracePolynomial_reflection_with_length`,
`exists_norm_gmTraceNonzeroTailAt_le_sqrt_near`,
`gmTraceZeroMode_separated_bound`, and
`heathBrownFixedReflectionLength`. Their exact signatures were inspected.
Mathlib's `ConvexOn.map_set_average_le` supplies normalized interval
Jensen. No new external download, source pin, or paper statement was
substituted for these proved inputs.

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

## Jutila physical-scale smoothing and uniform pattern bounds — current checkpoint

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

### Exact inputs consumed in the smoothing chain

The previously recorded Ivić §§9.5–9.6 and pinned Tao–Trudgian–Yang paper
remain the source references. This step consumes the native
`heathBrownFixedReflectionLength_bounds_real`,
`heathBrownReflectionBinError_fixed_le_sharp_uniform`,
`heathBrownSmoothingHeight`, `heathBrownReflectionDerivativeOrder`,
`one_div_heathBrownSmoothingHeight_pow_order_le`,
`heathBrownSharpUniformReflectionError_smoothing_le`,
`heathBrown_displacement_bin_count_le_log`,
`heathBrown_natCast_clog_two_le_one_add_log`, and
`heathBrown_eventually_log_le_rpow`.
Their actual signatures and admissibility conditions were inspected.
Mathlib's real-power monotonicity and exact natural/real power identities
perform the loss accounting. No new source download or pin change was
needed; the final Jutila exponent is still a proof obligation.
