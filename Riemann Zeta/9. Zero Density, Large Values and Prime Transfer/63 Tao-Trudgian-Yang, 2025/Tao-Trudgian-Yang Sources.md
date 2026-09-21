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
A faithful reuse requires a proved variable-prefix/endpoint bridge and
uniform truncated Gram bounds. No adjacent module or conditional
twelfth-moment statement was added as a dependency.
