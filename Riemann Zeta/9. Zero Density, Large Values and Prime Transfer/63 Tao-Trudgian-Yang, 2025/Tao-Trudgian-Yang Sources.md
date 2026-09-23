# Tao--Trudgian--Yang 2025 sources and repository survey

Current analytic progress: [Robert–Sargos small-alpha sixth moment](#robertsargos-small-alpha-sixth-moment--current-checkpoint).
The actual unweighted maximal sixth moment on the small-alpha window is proved with explicit bound 44845498368 (1+log N)^5 and a literal source (log N)^6 corollary. Higher-moment window transfer and the global bootstrap/C-process remain open. The permanent counterexample and all nine repaired Add-est clauses are preserved.

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

### Source comparison at this checkpoint

The frozen v1 TeX, lines 648--673, states `jutila-lvt` for every
positive integer k, 1/2 ≤ σ ≤ 1 and τ ≥ 0, with exactly the maximum
above and the same optimized local exponent. The new source-facing
theorems match these quantifiers and all three terms. The preceding
physical proof chain remains tied to the inspected Ivić source
discussion (printed pages 175--179, §§9.5--9.6) and the frozen source
ledger. No new external download, dependency pin, or publication
statement was substituted in this checkpoint. Paper-time ANTEDB
optimization remains discovery/certificate-generation material, not
proof evidence.

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

### Frozen-source comparison

The public rate and closed interval are literal Add-est (iii) in
`Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex`.
The paper-time ANTEDB blueprint's `imp-energy-bound9`, from the
unchanged `antedb-expdb-paper-time-9953003.zip`, supplies the k=13
branch layout. The implementation derives every numerical comparison
in Lean and consumes actual analytic region witnesses.

The source proof mentions a bound on the powered fifth coordinate;
that bound is unnecessary here and is not asserted. The authorized
two-witness repair is used instead. The implementation also supplies
the whole short-zeta range explicitly, so the open endpoint-two source
corollary is not a hidden premise. The preserved archive is not edited.
No new source download, pin, external solver or proof oracle is used.

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

### Frozen-source comparison and next-clause discovery

The public statement matches Add-est (iv) in the frozen v1 TeX and
`imp-energy-bound10` in the paper-time ANTEDB energy chapter.
The full k=12 maximum, sigma split 409/541, companion cardinality cap
and both energy-power choices are realized by actual Lean consumers.

The blueprint occasionally writes an unstarred ρ in prose where its
advertised A* theorem and surrounding energy argument require ρ*.
The implementation proves the energy conclusion, not the weaker
cardinality statement. Its unused printed fifth-coordinate restrictions
are replaced by the authorized independent-witness theorem; the archive
itself is preserved. The short-zeta range is supplied explicitly.

For the next clause, the unchanged archive's
`expdb-9953003/blueprint/src/python/derived.py`,
`prove_zero_density_energy_10()`, names Jutila k=11, Guth--Maynard,
Heath--Brown energy-region 2a and τ₀=2. This is a discovery reference,
not an imported proof or proof oracle. No new external download,
dependency pin or frozen-source edit occurred in this checkpoint.

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

### Frozen-source comparison and next-clause discovery

The theorem matches Add-est (v) in the frozen v1 TeX and
`imp-energy-bound11` in the paper-time energy chapter.
That blueprint entry has no handwritten proof; the adjacent
`prove_zero_density_energy_10()` identifies the k=11 inputs.
The new witness switch and all branch certificates are derived and
kernel-checked locally, not imported from numerical optimization.

For Add-est (vi), the reread blueprint `imp-energy-bound4` supplies
a handwritten proof on the larger [664/877,31/40] interval.
Its code reference is `prove_zero_density_energy_4()`, with Jutila
k=10, Guth--Maynard and Heath--Brown at τ₀=2; the prose also uses L2.
Its printed s-scaling assertions must again be replaced by separate
corrected cardinality/energy witnesses. The archived text is preserved.

No new external download, dependency pin or frozen-source edit occurred.

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

### Frozen-source comparison

The public result matches Add-est (vi) in the frozen v1 TeX.
The supporting blueprint `imp-energy-bound4` is also proved on
its entire [664/877,31/40] interval, including its literal A*
normalization; the paper interval is then restricted explicitly.

The corrected proof uses a Jutila companion cardinality cap where
the blueprint uses its L2 form, and balances the high-sigma energy
witnesses at (14σ+1)/10. These are proved deductions from actual
upstream objects, not supplied optimization constraints.
The unchanged archive's false s-scaling assertions are not used.

The complete handwritten proof of next `imp-energy-bound6` was
reread: Jutila k=6, sigma split 97/127, and companion cardinality
caps are its main inputs. No new download, pin change or frozen-source
edit occurred.

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

### Frozen source and proof comparison

The two public conclusions match clauses (vii) and (viii) in the
frozen v1 TeX. Their full blueprint counterparts `imp-energy-bound6`
and `imp-energy-bound7`, including both literal A* normalizations,
are also proved. Both handwritten proofs were reread from the pinned
paper-time archive.

The clause-(viii) proof uses the already proved independent q−1 energy
witness for the low-height interval and τ₀=2, instead of the blueprint's
varying τ₀. Every replacement range and analytic input is derived;
the paper and blueprint conclusions have not been weakened.

The next theorem `imp-energy-bound8` has no handwritten proof in its
frozen block. Its `prove_zero_density_energy_7()` implementation was
located and read in
`expdb-9953003/blueprint/src/python/derived.py`. It names Bourgain's
optimized large values, Jutila k=5, zeta large values and Heath--Brown
energy-region 2a, with powers 2--5 and τ₀=8σ−4. This remains a source
map for the open clause (ix), not a proof or a substitute for the
missing analytic bridges. No download, source edit or pin change occurred.

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

### Source comparison and explicit typographical distinctions

The frozen paper-time archive's `additive_energy.tex` supplies
`hb-double`, `cauchy-schwarz`, `bourgain-lvt`, `borg-lv-simp`
and the final row of `optimised_bourgain_lve`. The online
[authors' energy chapter](https://teorth.github.io/expdb/blueprint/energy-chapter.html)
was checked as a supplementary reference; it does not replace the frozen pin.
Bourgain's paper metadata is confirmed by the
[publisher](https://academic.oup.com/imrn/article-abstract/2000/3/133/663303).

The frozen mixed-sum display omits u from the polynomial although its
own proof uses t−u. The new finite theorem proves that latter formula,
not the displayed u-independent assertion. Also, the simplification's
prose writes τ where its displayed mixed term and convex combination
require τ/2. The Lean algebra uses the displayed τ/2 expression.
Neither archive was edited. These distinctions do not change any public
Add-est conclusion or authorize reinstating the false Lemma 62 scaling.

The optimized row's α₁ agrees with the table; the alternative α₂ above
is certified directly. No numerical optimizer is trusted. The Bourgain
dichotomy itself is not yet proved for actual large-value patterns.

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

### Original Bourgain paper and exact source scope

Jean Bourgain, *On large values estimates for Dirichlet polynomials and
the density hypothesis for the Riemann zeta function*, IMRN 2000(3),
133–146, DOI [10.1155/S107379280000009X](https://doi.org/10.1155/S107379280000009X).
[Crossref metadata](https://api.crossref.org/works/10.1155/S107379280000009X)
confirms the bibliographic record. The publisher PDF endpoint returned
an access challenge; it was not downloaded or treated as inspected.

The original paper text was inspected through its publicly readable
[14-page reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function),
using the paper's title, pagination and equation numbers. The platform's
generated questions/summary are not mathematical sources. OCR formulae
were checked against the frozen blueprint and independently derived
Lean statements; OCR alone is not proof evidence. No frozen archive
or source-pin ledger was modified.

The new counting definition matches (4.6), and the sharp square-count
bound matches (4.21). Positive-mass dyadic selection implements the
finite content of (4.27)–(4.28), with log₂|W|+1 visible rather than
hidden in a small-power loss. The integer-window bridge implements
an endpoint-safe (4.19), enlarging H to H+1. The actual weighted
fourth-moment theorem proves the reduction underlying (4.22) with
explicit window and height losses. It does not claim (4.7), the
complete Bourgain dichotomy, or the final optimized large-value row.

The missing source chain still includes the retained-zeta Mellin entry
(4.7)/(4.17)–(4.20), zeta superlevels and common shift (4.30)–(4.47),
the polynomial local mean (4.48)–(4.53), and final actual-pattern
assembly (4.54)–(4.57). The mixed upper bound itself is already proved.

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

### Source and reformulation ledger

The relevant classical source remains Bourgain (2000),
*On large values estimates for Dirichlet polynomials and the density
hypothesis for the Riemann zeta-function*, DOI
`10.1155/S107379280000009X`, specifically the (4.14)--(4.19) route to
(4.7). The preceding source checkpoint records the inspected public
reproduction and the publisher-access limitation.

This increment uses a fixed compact plateau instead of asserting the
source's exponential smoothing formula. The replacement's actual
coefficients, finite support, Mellin identity, residue, tails and full
self-moment entry are proved. Its application to the full reflected
prefix is still required, so it is not reported as source-(4.7)
completion. Native `DFIVoronoiTestFunction` Mellin/dilation APIs and
`heathBrownDifferenceMoment_le_of_norm_le`, the existing zeta contour
shift, and Mathlib's integrable inverse-power weight are consumed in
the proof terms. No source archive, dependency pin, public theorem
statement, or license record was changed.

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

### Source-range check for this increment

Bourgain's original paper was rechecked on 21 September 2026 through the
previously recorded [public reproduction of the original article](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
Only the original article text, not the platform's generated summaries,
is used. Lemma 4.1 assumes N<T and height-separated large values; its
displayed conclusion (4.7) does not impose our numerical high-value
absorption condition. The new consumer is therefore labeled as a
high-value result, not completion of that full source lemma.

The Lean route uses the actual native unweighted reflection prefix.
The conversion to critical weighted moments and the compensating
displacement-scale factors are proved. The compact smooth Mellin
replacement and the unit-window enlargement remain as documented in the
previous checkpoint. No source archive, dependency pin or public output
statement was changed; no blocked publisher download was bypassed.

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

### Source correspondence checked for this increment

The original article's equations (4.24)--(4.28) were rechecked on
21 September 2026 through its [previously recorded public reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
The new theorem proves their small-mass/heavy-difference-level mechanism
for actual power-window patterns with sigma>3/4 and N<=T. Its small
branch has the three source powers; its other branch supplies the actual
dyadic difference level and explicit logarithmic loss.

The notation alpha is the exponent parameter corresponding to a
small-mass factor N^(-alpha); it is not the subdivision index used later
in the article. The Lean theorem allows every real alpha, while the
source application can restrict it to positive alpha. The radius is an
explicit small power of N, obtained from the physical T radius using the
fixed height exponent. Later zeta superlevels, common shift and mixed
lower bound are not asserted. No source archive or dependency pin changed.

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

### Source correspondence checked for this increment

On 21 September 2026 the original article's equations (4.29)--(4.37)
were rechecked through the [previously recorded public reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
Only the reproduced original article, not the platform's generated
summary, is used. The local theorem implements actual band selection,
fourth-moment control and occupancy normalization with explicit finite
losses.

Lean uses the traced spatial radius T+h+1 and left-closed/right-open
amplitude bands. Its low floor is chosen from the actual local mass,
and its finite ceiling-logarithmic count is retained. These are
documented finite formulations; the source's suppressed small-power
losses have not yet been recovered uniformly. A single-band shift and
a general weighted-family common-shift theorem are proved, but the
source's common-parameter subdivision and mixed local-mean lower bound
are still open. No source archive or dependency pin changed.

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

### Source correspondence checked for this increment

The original article's subdivision and common-parameter discussion,
equations (4.38)--(4.47), was rechecked on 21 September 2026 through the
[recorded public reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
Only the original article, not the platform's generated summaries,
is used.

This increment proves actual localized-pattern construction and a common
amplitude grid with explicit finite/logarithmic losses. It additionally
proves the inverse-reflection bridge needed to form one original-source
union. It does not assert that the component amplitude indices, relative
difference levels or correlations have already been made common, nor
that the mixed local-mean lower estimate follows. The local-height
exponent and its distinction from the original height remain explicit.
No source archive, dependency or toolchain pin changed.

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

### Source correspondence for the common-component checkpoint

The original Bourgain article's (4.40)--(4.43) motivates the component
partition and common parameters; (4.31)--(4.37) motivates the product
comparison. The finite constants and explicit grid losses above are the
local formalization's proved accounting, not a claim that the complete
printed asymptotic argument is finished. The original article text was
rechecked in its [public reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function);
platform-generated summaries are not proof sources. No source pin changed.

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

### Source correspondence for the common-correlation checkpoint

The original Bourgain article's (4.34)--(4.37) and (4.43) guide the
correlation normalization and shared selection; (4.45)--(4.47) remain the
next source comparison. The displayed finite floors and constants are
proved local accounting, not quotations of the printed asymptotic
notation. The [original article's public reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function)
was rechecked; platform-generated summaries are not proof inputs.
No pinned source or upstream dependency changed.

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

### Source comparison for this step

Bourgain, IMRN 2000(3), 133--146, DOI 10.1155/S107379280000009X:
the original article's equations (4.43)--(4.63) were rechecked in the
[public article reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
Use the reproduced article, not the hosting platform's generated FAQ.
The selected-family comparison and mixed lower estimate are now realized
with explicit finite costs. Instead of claiming the printed log-window
local lemma, the implementation proves a small-power-window estimate
directly from the existing native finite-exponential-sum Fourier theorem.
This is a documented alternate supporting route, not a changed Add-est
contract. The mixed upper assembly and final source dichotomy remain open.
No frozen source or dependency pin changed.

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

### Source comparison for this checkpoint

Bourgain, IMRN 2000(3), 133--146, DOI 10.1155/S107379280000009X,
equations (4.53)--(4.63), were rechecked in the
[original article reproduction](https://www.scribd.com/document/816345203/On-large-values-estimates-for-Dirichlet-polynomials-and-the-density-hypothesis-for-the-Riemann-zeta-function).
The implementation now performs the actual mixed comparison and parameter
elimination, retaining the full three-term native Heath--Brown bound and
explicit finite losses. The article's final simplified estimate and the
frozen logarithmic large-values dichotomy are not yet claimed.
The native local code supplies the analytic upper bound; no new external
analytic hypothesis, source download or dependency pin is introduced.

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

## Actual inverse and Legendre phases — historical checkpoint

Primary research reference checked on 21 September 2026:
[J. Vandehey, Error term improvements for van der Corput transforms,
arXiv:1205.0090v1](https://arxiv.org/html/1205.0090), introduction and
Theorem 1.1. The source writes the transformed exponent at the critical
point satisfying f'(x_r)=r, with a curvature-dependent amplitude.
Its endpoint conventions, curvature orientation and uniform errors
must be bridged explicitly before using it for the closed ANTEDB sum.

This reference is research-only, not a Lean dependency or a newly frozen
archive. The new code proves the actual inverse, dual-phase calculus,
first-order model comparison and original physical stationary-point
identities; it does not claim Theorem 1.1 or beta reflection.

Mathlib APIs used at the unchanged pin include
`HasStrictDerivAt.to_local_left_inverse`,
`ContDiffAt.to_localInverse`, strict antitonicity from a negative
derivative, the intermediate-value theorem and convex mean-value bounds.
Their hypotheses are discharged from the genuine frozen approximate-model
definition in `Expdb/ExponentialSums/PhaseFunctions.lean`.

The live [ANTEDB exponential-sums directory](https://github.com/teorth/expdb/tree/main/Expdb/ExponentialSums)
was checked for an existing B-process implementation; none was visible in
that directory at the time of review. This is a scoped search result,
not a claim that no Lean formalization exists anywhere.
No dependency pin, frozen source, counterexample or energy theorem changed.
Higher-order dual model control and the actual sum transformation remain
open; the full goal is unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions. Target log:
`logs/tao-trudgian-yang-build-20260921-211419-4caca476.log`;
foundation log: `Riemann Zeta/logs/foundation_freeze_20260921_211419.log`.
The target covers 553 package files and audits 4929 declarations.
All 37 new public audits and 42 new regression examples pass.
Both BATs and the counterexample are unchanged. Exact hashes and
foundation stage evidence are in the latest Reproduction Manifest section.

## Uniform all-order Legendre model control — historical checkpoint

The local frozen TeX's `phase-def`, equation `fpu` and example
`phase-ex` are the source contract for this step:
`Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex`.
The model condition concerns every fixed derivative order, uniformly
in the phase variable; the Legendre closure assertion also requires a
faithful canonical-domain bridge.

The new all-order recurrence and sensitivity proofs are implemented
locally, using the unchanged Mathlib chain/product/reciprocal rules,
iterated derivatives, finite sums and convex mean-value estimates.
The exact logarithmic/power primitive is proved to satisfy the original
frozen approximate-model definition at every order, including endpoints.
The actual inverse formulas, Pochhammer estimates and original phase
errors are then consumed by the compact-uniformity theorem.

No external formula is treated as a proof oracle, and no phase derivative
estimate is imported as an axiom. Smooth extension/normalization to [1,2]
and the actual transformed-sum theorem remain open. The available
`ContDiffBump` smoothness, support and plateau APIs were located for the
next extension step; locating them is not a proof of that extension.

No dependency pin, archive, original source, counterexample or energy
theorem changed. The full goal remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-215130-00a61f53.log)
and [final foundation log](../../logs/foundation_freeze_20260921_215409.log).
The target covers 561 package files and audits 5026 declarations.
All 44 new public audits and 52 new regression examples pass.
All 220 checkpoint source/integration/runner hashes are stable across
both final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Canonical Legendre extension and finite model families — historical checkpoint

The frozen TeX `phase-def`, `fpu` and `phase-ex` remain the source
contract. The extension now satisfies the original closed [1,2]
approximate-model definition and the original
`IsModelPhaseFunctionWith`/`IsModelPhaseFunction` predicates.
The latter are read directly from the pinned ANTEDB
`Expdb/ExponentialSums/PhaseFunctions.lean`.

Local Mathlib APIs used include real `ContDiffBump` plateaus and support,
`IsCompact.exists_bound_of_continuousOn`, the iterated-derivative product
and multiplicative composition formulas, finite open subcovers, and
eventual finite conjunctions. The reference homogeneity, actual
Legendre correction bounds and source consumers are proved locally.

The source `beta-reflect` formula is still not proved. Specialized native
logarithmic reflection and Atkinson stationary estimates have not been
silently generalized to arbitrary model phases. No source archive,
dependency pin or existing energy theorem changed.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-222922-4233a5f3.log)
and [final foundation log](../../logs/foundation_freeze_20260921_222922.log).
The target covers 569 package files and audits 5058 declarations.
All 27 new public audits and 35 new regression examples pass.
All 228 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Exact Poisson source entry and physical dual sums — historical checkpoint

The frozen `phase-def`, `fpu`, `phase-ex` and `beta-reflect`
contracts remain unchanged. The literal `exponentialSumAt` and model
predicates come from the pinned ANTEDB sources. Integer and natural
interval conventions are bridged in Lean.

The pinned Mathlib Poisson theorem is
`SchwartzMap.tsum_eq_tsum_fourier` in
`Mathlib/Analysis/Fourier/PoissonSummation.lean`.
The actual weighted model kernel is proved Schwartz before use.
Fourier integrals use Mathlib's real character with its negative sign;
`Measure.integral_comp_div` supplies the exact x=N*u substitution.
Schwartz polynomial decay and integer rpow summability prove absolute
convergence. Constructed smooth interval cutoffs provide the original
source entry; no smoothing assumption replaces the source sum.

These local pinned sources were inspected directly. No source archive
or dependency pin changed. General uniform stationary-phase asymptotics
and the full `beta-reflect` formula remain open; specialized native
logarithmic/Atkinson results are not generalized without proof.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-231301-8d992207.log)
and [final foundation log](../../logs/foundation_freeze_20260921_231301.log).
The target covers 575 package files and audits 5124 declarations.
All 32 new public audits and 40 new regression examples pass.
All 234 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Stationary amplitudes, source beta consumers and quadratic coordinates — historical checkpoint

The frozen `phase-def`, `fpu`, `phase-ex` and `beta-reflect`
contracts are unchanged. The original order-two ANTEDB model condition
supplies the third-derivative bounds used for amplitude monotonicity;
the source beta predicate is consumed directly at the linked dual
physical scales. No general reflection theorem is imported from the
specialized logarithmic/Atkinson branch.

The pinned local Mathlib APIs inspected and used here include:

- `Mathlib/Analysis/SpecialFunctions/Sqrt.lean` for smooth/derivative
  square-root rules at positive curvature;
- `Mathlib/Analysis/Calculus/Taylor.lean`,
  `taylor_mean_remainder_lagrange_iteratedDeriv` for the two-sided
  stationary deficit, and `Real.taylor_tendsto` for its critical limit;
- `Mathlib/Analysis/Calculus/Deriv/Slope.lean`,
  `hasDerivAt_iff_tendsto_slope` for the actual coordinate derivative;
- the local `FiniteWeightVariation` and native finite summation-by-parts
  identity, applied to the actual physical amplitude samples.

These are direct inspections of pinned local sources, not a new online
source refresh. No archive, dependency pin or source theorem changed.
The exact quadratic phase is proved; uniform inverse/transformed-weight
control and general stationary-phase error estimates remain open.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-000055-22681e8e.log)
and [final foundation log](../../logs/foundation_freeze_20260922_000107.log).
The target covers 583 package files and audits 5203 declarations.
All 46 new public audits and 54 new regression examples pass.
All 242 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Smooth quadratic inverse and original-mode remainder — historical checkpoint

The frozen `phase-def`, `fpu`, `phase-ex` and `beta-reflect`
contracts remain unchanged. The new proofs consume the original
order-one model condition and actual source Poisson cutoff, not an
assumed stationary-phase approximation or a specialized log-phase proxy.

Pinned local Mathlib sources inspected and used include:

- `Analysis/Calculus/ParametricIntegral.lean`:
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with compact
  jet bounds derived locally for the actual segment integrand.
- `Analysis/Calculus/ContDiff/Deriv.lean`: derivative induction for
  all-order smoothness of the Taylor averages.
- `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`:
  `integral_eq_sub_of_hasDerivAt` for the exact second-order identity.
- `Analysis/Calculus/InverseFunctionTheorem/Deriv.lean` and
  `InverseFunctionTheorem/ContDiff.lean`: actual local inverse
  derivatives and smoothness, identified with the constructed inverse.
- `MeasureTheory/Function/JacobianOneDim.lean`:
  `integral_image_eq_integral_abs_deriv_smul` and
  `integrableOn_image_iff_integrableOn_abs_deriv_smul`.
- `Analysis/Calculus/MeanValue.lean`: the original curvature bound
  supplies the upper slope-gap bound used in uniform first derivatives.

These are inspections of pinned local primary sources, not a new
online source refresh. No source archive or dependency pin changed.
The exact quadratic transform and remainder normalization are proved;
uniform remainder estimates, higher-derivative bounds and moving-band
control still require proof. No Fresnel evaluation is claimed here.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-010958-9aae1d59.log)
and [final foundation log](../../logs/foundation_freeze_20260922_010947.log).
The target covers 594 package files and audits 5272 declarations.
All 54 new public audits and 63 new regression examples pass.
All 253 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Uniform smooth weights and stationary remainder bounds — historical checkpoint

The frozen `phase-def`, `fpu`, `phase-ex` and `beta-reflect`
contracts are unchanged. The new estimates consume the actual original
model phase and cutoff; no specialized logarithmic stationary-phase
hypothesis is promoted to arbitrary F.

Pinned local primary sources and proved inputs inspected and used:

- Mathlib `Topology/Algebra/Support.lean` and
  `Topology/Compactness/Compact.lean`: compact continuous images,
  support closure and local vanishing.
- Mathlib `Analysis/Calculus/Deriv/Support.lean`: derivative support
  containment, including all iterated derivatives of the zero-extension.
- Mathlib `Analysis/Calculus/IteratedDeriv/Defs.lean` and
  `IteratedDeriv/Lemmas.lean`: actual derivative iteration and local
  equality transport.
- Mathlib `MeasureTheory/Integral/Bochner/Basic.lean` and `Set.lean`:
  bounded-integrand estimates, indicator integrability and set integrals.
- Mathlib `Analysis/Fourier/FourierTransformDeriv.lean`:
  `Real.hasDerivAt_fourierChar`, checked in the e(x)=exp(2*pi*i*x) convention.
- Mathlib `MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`:
  `integral_mul_deriv_eq_deriv_mul`, with both endpoint terms retained.
- Existing `BetaInverseExpressions`: finite-expression magnitude calculus,
  reinterpreted with proved derivative rules for the actual Morse objects.
- Existing `FresnelEvaluation`: the GENERIC Gaussian/Fresnel phase and
  finite-window tail, applied to the exact quadratic character. The
  Atkinson-specific source transformation is not used as a theorem for F.

The frozen TeX `beta-reflect` statement was reread. These are pinned
local-source inspections, not a new online source refresh. No archive,
dependency pin or source theorem changed. The new C*N/T stationary-mode
error is fixed-cutoff uniform; varying-cutoff, nonstationary and moving-band
estimates are still required for the full B process.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-021704-cf554732.log)
and [final foundation log](../../logs/foundation_freeze_20260922_021704.log).
The target covers 610 package files and audits 5402 declarations.
All 75 new public audits and 85 new regression examples pass.
All 269 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Controlled cutoff families and weighted Fourier bounds — historical checkpoint

This checkpoint uses the existing pinned local Lean and paper sources;
it is not a new online literature refresh. No archive, source statement,
toolchain or dependency pin changed.

- Mathlib's fixed `Real.smoothTransition`, its smoothness and endpoint
  rules, together with the existing local affine derivative formula,
  supply the actual two-transition cutoff.
- `iteratedDeriv_fun_mul` and `Nat.sum_range_choose` give exact
  Leibniz/binomial width budgets. Compactness bounds only the fixed
  transition's finite jets, not a different cutoff for each lattice.
- Mathlib finite integer intervals and natural ceilings support the
  original endpoint-band count and the explicit 4*N*eta+2 source loss.
- Existing actual Morse jets and the checked generic quadratic remainder
  supply the stationary estimate; the new weighted-expression degree
  argument tracks cutoff derivative order and proves the sharp eta^(-n).
- `AtkinsonResidualVariation` supplies only its GENERIC two-transition
  finite-variation result; `AtkinsonAmplitudeIntegral` supplies the
  amplitude interface. The carrier FTC/integration-by-parts theorem is
  proved for an arbitrary continuous carrier on an open set.
- `AtkinsonFirstDerivative` supplies GENERIC positive/negative reciprocal-
  slope integral estimates. Their Fourier normalization and actual
  original-model slope hypotheses are proved in the new consumers.
  No Atkinson-specific phase transformation is asserted for F.
- The frozen TeX `beta-reflect` source statement and the existing
  physical dual-scale interfaces remain the target. The source beta
  predicate used in the weighted-main theorem is upstream and unweighted;
  neither full reflection nor the weighted conclusion is assumed.

Quantitative far tails, summed error balance and moving boundary bands
remain requirements of the original source theorem. None is imported
from informal prose or inferred from absolute summability.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-085137-4fb8b007.log)
and [final foundation log](../../logs/foundation_freeze_20260922_085138.log).
The target covers 625 package files and audits 5516 declarations.
All 50 new explicit public audits and 66 new regression examples pass.
All 284 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Quantitative Fourier tails and the actual core expansion — historical checkpoint

This checkpoint uses the pinned local source tree, not a new online
literature refresh. The frozen TeX `beta-reflect` statement was reread;
no archive, dependency pin or original source theorem changed.

- Mathlib's `Real.fourier_iteratedDeriv` and its integrability/normalization
  requirements were inspected. The existing foundation theorem
  `one_add_abs_fourier_decay_of_support_of_bounds_order` is applied
  only in its GENERIC compact-support form, with the actual kernel's
  uniform derivative bounds derived in the new consumer.
- The existing generic complex exponential and second-order chain/product
  rules provide carrier derivatives. The original phase's first two jet
  bounds supply the constants; no Atkinson-specific root phase is substituted.
- `tsum_nat_rpow_tail_le` supplies the checked real integral comparison.
  Mathlib's integer positive/negative sum decomposition and indicator
  summability are used to prove the two-sided inverse-square tail.
- Mathlib finite integer intervals, floor/ceiling inequalities, harmonic
  numbers and `harmonic_le_one_add_log` supply the actual signed window
  partition and the logarithmic exterior cost.
- The previous actual stationary Fourier-mode theorem is applied to the
  core filtered by the ORIGINAL slope image. Its cardinality is derived
  from the original model envelope, independently of the tail radius.

The final consumer begins at the original exponential sum and retains
the unevaluated inner-core nonstationary contribution. The source's
full B-process/reflection conclusion still needs that contribution and
the required power-saving error balance; neither is an imported premise.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-094603-f91c6946.log)
and [final foundation log](../../logs/foundation_freeze_20260922_094604.log).
The target covers 635 package files and audits 5587 declarations.
All 29 new explicit public audits and 41 new regression examples pass.
All 294 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Width-independent curvature and the bounded inner core — historical checkpoint

No external source or dependency pin changed at this checkpoint. The
primary statement was reread in frozen
`Sources/TaoTrudgianYang-v1-source/Tao_Trudgian_Yang_v2.tex`,
lines 297--307, especially `beta-reflect`. Its whole-interval beta
symmetry remains unproved; the new modules supply original-object
analytic inputs toward that statement.

Mathlib was searched before proving the integral bound. The pinned
`Analysis/Calculus/Deriv/MeanValue.lean` supplies the quantitative
secant inequality, `Topology/Order/IntermediateValue.lean` supplies
actual slope thresholds, and the interval-integral/continuous-derivative
APIs supply additivity, trivial length bounds and one-sided endpoint
continuity. The existing locally audited first-derivative oscillatory
integral theorem and actual cutoff variation theorem are consumed.

The second-derivative integral bound, uniform original-mode consumer,
closed-slope image, exact integer partition and actual inner-core estimate
are new Lean deductions here, not imported from a newly discovered repo
or certified by an external solver. No browser/search result is claimed
as evidence for this checkpoint.

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

No frozen paper, ANTEDB source, dependency pin or source contract changed.
The refinement uses the existing local inverse-coordinate, Fresnel,
original cutoff variation and first/second-derivative lemmas, plus pinned
Mathlib integration by substitution and harmonic sums. The source beta
reflection formula is still an uncompleted downstream acceptance result.

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

### Next-input source check (not a completion claim)

The frozen target cites Sargos, *Acta Arith.* 110 (2003), Theorem 5,
for C. Its publisher-hosted [primary paper](https://www.impan.pl/shop/publication/transaction/download/product/82873)
was checked: the proof uses a twelfth-power symmetric-correlation
inequality, sixth-order Taylor control and a separate near-diophantine
counting input. Those are not supplied merely by the new A-process.
The cited Robert--Sargos 2000 mean-value paper is also available as
[arXiv:2307.03554v1](https://arxiv.org/abs/2307.03554v1).
These references guide the remaining EPZAE-10 work, not an imported
Lean assumption or an already completed C theorem.

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

### Primary sources for this checkpoint and continuation

The exact three-term input is [Heath--Brown, Theorem 1](https://arxiv.org/abs/1601.04493v3).
The local native proof supplies its Vinogradov mean-value input. The
source-to-beta formula and first two table rows are matched to the frozen
Tao--Trudgian--Yang v1 TeX, lines 406--445.

For the still-open C-process, [Robert--Sargos (2000), author-uploaded version](https://arxiv.org/abs/2307.03554v1)
provides the sixth-moment estimate and equivalent square/quartic near-solution
count. Its proof uses Fourier window comparison, a fourth-moment count,
a quantitative quadratic/quartic B-transform and a decreasing-exponent
iteration. These remain references, not imported Lean proofs. The
[Sargos (1995) publisher record](https://doi.org/10.1112/plms/s3-70.2.285)
identifies the D-process paper; the attempted full-PDF retrieval did not
succeed. This does not obstruct the available independent implementation work.

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

## Robert–Sargos small-alpha sixth moment — current checkpoint

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
