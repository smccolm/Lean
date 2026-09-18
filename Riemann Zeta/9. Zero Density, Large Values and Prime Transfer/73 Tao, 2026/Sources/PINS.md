# Tao 2026 source pins

## Primary paper

- Author: Terence Tao
- Title: *Products of consecutive integers with unusual anatomy*
- arXiv: `2603.27990v2`
- Version date: 22 April 2026
- Abstract record: <https://arxiv.org/abs/2603.27990v2>
- PDF origin: <https://arxiv.org/pdf/2603.27990v2>
- TeX source origin: <https://arxiv.org/e-print/2603.27990v2>
- Retrieved for this scaffold: 7 September 2026

## Baker--Harman--Pintz prime-interval input

- Authors: R. C. Baker, G. Harman, and J. Pintz
- Title: *The Difference Between Consecutive Primes, II*
- Journal: *Proceedings of the London Mathematical Society* 83 (2001),
  532--562
- DOI: <https://doi.org/10.1112/plms/83.3.532>
- Publisher record: <https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/plms/83.3.532>
- Archived PDF origin:
  <https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf>
- Retrieved: 8 September 2026
- Local artifact: `baker-harman-pintz-2001.pdf`
- Source locator: Theorem 1, journal page 532 (PDF page 1), states the
  sufficiently-large backward interval result with exponent `0.525 = 21/40`.
  The quantitative lower bound completing the proof is on journal page 561
  (PDF page 30). Section 2, beginning on journal page 535 (PDF page 4), invokes
  Watt's mean-value theorem; Lemma 2 is on journal page 536 (PDF page 5).

The publisher and ResearchGate endpoints rejected non-browser retrieval. The
local artifact is therefore the byte-identical identity recorded here from the
accessible University of Maryland archival mirror; the DOI above remains the
bibliographic authority.

## Burgess prime-modulus precursor

- Author: D. A. Burgess
- Title: *On character sums and primitive roots*
- Original journal: *Proceedings of the London Mathematical Society*, Series
  3, 12 (1962), 179--192
- MathNet archival record: <https://www.mathnet.ru/eng/mat267>
- Archived PDF origin:
  <https://www.mathnet.ru/php/getFT.phtml?jrnid=mat&option_lang=eng&paperid=267&what=fullt>
- Archived edition: Russian translation by O. M. Fomenko, *Matematika* 7:4
  (1963), 3--16
- Retrieved: 14 September 2026
- Local artifact: `burgess-character-sums-primitive-roots-1962.pdf`
- Source locators: Theorem 1 is on original/archived PDF page 1 and gives the
  prime-modulus character-sum estimate for arbitrary positive integer `r`.
  Lemma 2, beginning on archived PDF page 5, proves the complete `2r`-th
  moment estimate; Lemma 3 begins on archived PDF page 7 and selects disjoint
  intervals; Lemma 4 begins on archived PDF page 8 and supplies the
  amplification lower bound. The proof combines Lemmas 2 and 4.

This is the first paper in Tao's three-item Burgess citation bundle and
records the original prime-modulus proof architecture. It is not the 1963
composite cube-free theorem that supplies Tao's required all-`r`, `r = 7`
case. The latter remains an unpinned analytic source and an unformalized
boundary; this artifact is source evidence, not a Lean dependency.

## Modern explicit cube-free Burgess proof architecture

- Authors: Elchin Hasanalizade, Hua Lin, Greg Martin, Andradis Luna Martínez,
  and Enrique Treviño
- Title: *Explicit Burgess inequalities for cubefree moduli*
- arXiv: `2511.17778v2`
- Version date: 29 August 2026
- Abstract record: <https://arxiv.org/abs/2511.17778v2>
- PDF origin: <https://arxiv.org/pdf/2511.17778v2>
- TeX source origin: <https://arxiv.org/e-print/2511.17778v2>
- License: [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
- Retrieved: 14 September 2026
- Local artifacts: `explicit-burgess-cubefree-2511.17778v2.pdf` and
  `explicit-burgess-cubefree-2511.17778v2.tar`
- Source locators: Theorem 1.1 gives the explicit cube-free Burgess bound;
  Theorem 1.3, labeled `weil` in
  `Explicit_Burgess_for_composite_moduli_HLLMT.tex`, gives the exact shifted
  `2r`-th moment; Lemma 2.1, labeled `burgess weil`, isolates Burgess's
  composite-modulus complete rational-function character sum; Lemmas 2.3 and
  2.4 bound the resulting gcd tuple sum; the proof immediately following
  them expands the moment and separates tuples with at least `r+1` distinct
  shifts from the diagonal tuples.

This modern paper is pinned as an accessible, explicit proof architecture for
formalization. It is not silently substituted for Tao's cited theorem, and
none of its analytic results is asserted as a Lean theorem. In particular,
its Lemma 2.1 still cites Burgess's 1962 Lemma 7 and 1963 Lemma 8; the latter
original source remains locally unavailable. The intended formal reduction
is to kernel-check the finite moment expansion and gcd combinatorics, leaving
that complete Weil-type character sum as the sharply identified analytic
boundary.

## Granville smooth-number input

- Author: Andrew Granville
- Title: *Smooth numbers: computational number theory and beyond*
- In: *Algorithmic Number Theory*, MSRI Publications 44 (2008), 267--323
- Author-hosted PDF origin:
  <https://dms.umontreal.ca/~andrew/PDF/msrire.pdf>
- Publisher record:
  <https://www.cambridge.org/core/books/algorithmic-number-theory/4C4A9C117A30E1AC72814695F223B656>
- Local artifact: `granville-smooth-numbers-2008.pdf`
- Source locators: equations (1.14) and (1.15), journal page 270 (PDF page
  4), give the polylogarithmic and subexponential smooth-number scales cited
  in Tao's Proposition 2.1. The elementary lattice-count lower bound is
  equation (3.3), journal page 282 (PDF page 16). The polylogarithmic upper
  estimate and its combination with (3.3) occur on journal page 291 (PDF page
  25). The Perron representation is equation (3.22), journal page 292 (PDF
  page 25); the saddle calculation on the central segment
  `|t| <= 1/log y` and its resulting asymptotic are equation (3.23), journal
  page 293 (PDF page 26). Tao additionally cites equation (3.24) for
  multiplicative stability.

This pin records the exact cited survey and proof locators. The PDF is source
evidence, not a Lean dependency or a substitute for formalizing the stated
finite lattice-count and asymptotic arguments.

## Canfield--Erdős--Pomerance critical smooth-number input

- Authors: E. Rodney Canfield, Paul Erdős, and Carl Pomerance
- Title: *On a problem of Oppenheim concerning “Factorisatio Numerorum”*
- Journal: *Journal of Number Theory* 17 (1983), 1--28
- DOI: <https://doi.org/10.1016/0022-314X(83)90002-1>
- Author-hosted PDF origin:
  <https://math.dartmouth.edu/~carlp/PDF/paper39.pdf>
- Retrieved: 8 September 2026
- Local artifact: `canfield-erdos-pomerance-1983.pdf`
- Source locator: Theorem 3.1, journal/PDF pages 10--15, gives the
  unconditional explicit lower bound for `Psi(x,x^(1/u))` for `x>=1` and
  `u>=3`. Its finite multiscale product decomposition is equation (3.5), the
  recursive `D(v)` insertion is (3.10), the reciprocal-prime packet lower
  bound is (3.11), and their assembled iteration is (3.15).

This is the primary proof behind Granville (1.12). The scanned PDF has no text
layer; the page and equation locators above are therefore part of the pin.
As with every analytic source here, the paper is evidence to formalize, not a
Lean dependency or an admitted theorem.

## Matomäki--Radziwiłł--Shao--Tao--Teräväinen prime-equidistribution input

- Authors: Kaisa Matomäki, Maksym Radziwiłł, Xuancheng Shao, Terence Tao, and
  Joni Teräväinen
- Title: *Singmaster's conjecture in the interior of Pascal's triangle*
- arXiv: `2106.03335v1` (the sole arXiv version)
- Version date: 7 June 2021
- Journal: *The Quarterly Journal of Mathematics* 73 (2022), 1137--1177
- DOI: <https://doi.org/10.1093/qmath/haac006>
- Abstract record: <https://arxiv.org/abs/2106.03335v1>
- PDF origin: <https://arxiv.org/pdf/2106.03335v1>
- TeX source origin: <https://arxiv.org/e-print/2106.03335v1>
- Retrieved: 8 September 2026
- Local artifacts: `singmaster-2106.03335v1.pdf` and
  `singmaster-2106.03335v1.tar`
- Source locator: Proposition 1.12(i)--(ii) in `main.tex`. Part (i) gives the
  prime exponential-sum estimate for the phase `N/p + M/p^j`; part (ii)
  obtains the smooth two-periodic weight estimate by Fourier expansion. Tao's
  Theorem 2.5 restates part (ii), and the later argument only consumes its
  specialization `M=N`, `j=2`.
- Proof locator: the proof of Proposition 1.12 in `main.tex` reduces the
  periodic-weight statement to the exponential-sum statement, treats small
  frequencies by the prime number theorem, and treats the remaining
  frequencies through Vaughan's identity, the paper's Vinogradov derivative
  estimate, and its Type I/II bounds.

This pin establishes the exact cited source and statement. It does not import
the paper as a Lean dependency or claim that Proposition 1.12 has already been
formalized.

## Public Sylvester--Schur Lean proof reference

- Repository: `AllenGrahamHart/FormalConjectures-Bench`
- Commit: `482dacc4d9335240f26218cdc62032da3100392b`
- Path: `formalizations/erdos699/Erdos699Formalization.lean`
- Raw-file SHA-256: `ab0987fe6012fb421138af86ea6509979fcf885aa54744f06b2215fbb7f7e7b4`
- Raw-file size: `365225` bytes
- Target: `Erdos699Formalization.sylvester_schur`, the standard statement
  represented locally by `Tao2026.BinomialSylvesterSchurConclusion`.
- Upstream environment: Lean `v4.27.0`; this project uses Lean `v4.30.0`.

This is a provenance-only reference. The proof file has no license header, the
pinned repository root has no license file, and that repository's pinned
`manifest/licence_review.csv` has no Erdős 699 entry. Consequently the source
has not been copied or vendored here. The local binomial-to-interval bridge was
proved independently and is kernel-checked in this repository.

## Erdős--Selfridge factorial-fiber input

- Authors: P. Erdős and J. L. Selfridge
- Title: *The Product of Consecutive Integers Is Never a Power*
- Journal: *Illinois Journal of Mathematics* 19 (1975), 292--301
- MR: `MR51 #12692`
- Archived PDF origin: <https://combinatorica.hu/~p_erdos/1975-46.pdf>
- Bibliographic authority: <https://renyi.hu/en/node/4094>
- Retrieved: 8 September 2026
- Local artifact: `erdos-selfridge-1975.pdf`
- Source locator: Theorem 1 is the full assertion that
  `(n+1)⋯(n+k)=x^l` has no solutions for `n≥0`, `k≥2`, and `l≥2`.
  Tao uses its square case after Theorem 1.10 to show that, for fixed
  `(a₂,a₃)`, at most two values of `a₁` share the required factorial
  squarefree component.

No completed Lean proof was located. The Google DeepMind
`formal-conjectures` entry for the corresponding consecutive-integer theorem
contains a `sorry` body and is research metadata only; it is not a permissible
dependency for this project.

The local filenames and SHA-256 values are authoritative in
`SHA256SUMS.txt`. These third-party artifacts retain their original rights and
are not covered by the repository's MIT-0 grant.

Release 4.12 records the precise formal status of Granville's equations
(3.22)–(3.23): the survey states that the contour outside the central segment
is a small error but does not provide the high-frequency proof there. The
local development now identifies that missing assertion exactly as decay of
`smoothSaddlePostTerminalPerronTail`; no source theorem has been silently
imported for it.

Release 4.13 further records that the local CEP/PNT shell implementation has
a proved absolute physical-height ceiling whenever its terminal prime scale
survives. This is an internal limitation theorem, not a claim extracted from
Granville's survey.

Release 4.14 uses the corrected author-hosted Hildebrand--Tenenbaum 1986
paper as a proof locator: Lemma 8(ii), equation (3.16), supplies the global
minor-arc exponent, while Lemmas 9–10 supply the smoothed short-interval and
finite Perron-truncation steps. These results are being reproduced locally;
they are not imported as axioms.

Release 4.15 reproduces the algebraic corollary immediately following HT
Lemma 6: subtract the transforms at `0` and `t` and take real parts. The
uniform complex transform estimate itself remains to be proved locally.

Release 4.16 pins the complete statement of HT Lemma 6 to equation (3.10):
the ceiling is `Y(epsilon)=exp((log y)^(3/2-epsilon))` and the error is the
source's `beta^(-1)` majorant multiplied by an `O_epsilon` constant. The
epsilon-dependent implied constant, the error shape, and the implied cosine
corollary are represented explicitly in local definitions and theorems; the
cited contour argument is not imported as an axiom.

Release 4.17 follows the proof of HT Lemma 8(ii) on page 276: the Mangoldt
cosine sum is divided by `log y`, its prime part is compared with the Euler
product loss, and the higher-prime-power part is isolated. The local bridge
is proved exactly; the paper's preceding Lemma 5 remains the provenance for
the required sharp remainder estimate.

Release 4.18 reproduces the required `sigma>=1/2` specialization of HT
Lemma 5 locally. Mathlib's exact prime-power decomposition is combined with
the elementary estimate
`(p^k)^(-sigma) <= p^(-1) 2^(-(k-2)/2)`, a geometric series, and the
previously audited Chebyshev bound. No analytic estimate is imported as an
axiom; the resulting explicit `O(log y)` bound is stronger than the needed
specialization of the source remainder estimate.

Release 4.19 reproduces the elementary main-term estimate in the proof of HT
Lemma 8(ii). The local proof uses only the exact equation-(3.10) Cartesian
main term, `sin^2+cos^2=1`, and algebra; no source inequality is imported as
an axiom. The resulting bound is combined locally with the proved Lemma 5
specialization.

Release 4.20 reproduces the saddle-coefficient comparison used in HT Lemma
8(ii) from local finite Abel summation and the exact saddle equation. The
explicit comparison constant is deliberately coarse; no asymptotic prime
sum or source assertion is imported as an axiom. Its cutoff is not expected
in the critical regime, so the theorem is retained only as a conditional
intermediate result.

Release 4.21 replaces that route by the finite theta-Abel argument implicit
in the same HT Lemma 8(ii) prime-sum step. Chebyshev's explicit theta bound
and the existing finite power-sum inequality prove the uniform main-scale
estimate locally. No asymptotic prime theorem or HT conclusion is imported;
the only remaining source input in this chain is the analytic Lemma 6
transform estimate, still represented by a named proposition.

Release 4.22 follows the literal notation of HT Lemma 6: `s=1-beta+i*t`,
the truncated series `sum Lambda(n)n^(-s)`, and the main term
`y^(1-s)/(1-s)`. Their equality with the local transform notation is proved,
not assumed. The author-hosted paper explicitly omits the usual contour
details, so the equivalent shifted-Perron proposition remains a transparent
analytic obligation rather than a source axiom.

Release 4.23 proves the standard initial Perron-line expansion locally from
the frozen von Mangoldt `LSeries` theorem and dominated convergence. The
finite cutoff and source-coordinate specialization are also proved, not
imported from Hildebrand--Tenenbaum. Consistently with the paper's omission,
the contour displacement and zero-free-region estimates remain explicit
formalization obligations.

Release 4.24 formalizes the omitted contour displacement as an exact local
residue theorem rather than importing it from the paper. The surrogate
presentation, pole location, residue, and four-edge orientation are all
proved in Lean. Only the stated rectangle zero-freeness and quantitative
edge bounds remain to be supplied from the frozen analytic machinery.

Release 4.25 supplies the zero-free part from the frozen, locally proved
Ford/Vinogradov--Korobov theorem. The coordinate translation and rectangle
membership argument are proved in this node; no additional zero-free source
claim is assumed. Quantitative parameter selection and edge bounds remain.

Release 4.26 makes the standard omitted contour choices locally and proves
their algebra rather than importing it: the shift gives exactly the source
exponential decay, the initial line gives exactly a constant power cost, and
twice the source frequency ceiling encloses every requested frequency. The
combined contour/Perron error identity is also proved in Lean. Only the
quantitative bounds on its explicit terms and the native VK-width
asymptotic remain; no HT Lemma 6 conclusion is assumed.

Release 4.27 proves that remaining VK-width asymptotic locally. The exact
source ceiling converts the denominator to explicit powers of `log y` and
`log log y`; Mathlib's log-versus-power theorem and the frozen VK
factor-three comparison then give the required uniform width. The native
Ford theorem is instantiated directly, with no new zero-free assumption.
The source Lemma 6 conclusion is still not assumed: its explicit edge and
truncation estimates and small-beta branch remain.

Release 4.28 proves the standard finite-height Perron truncation reduction
locally from the frozen sharp-kernel inequalities. The beta-dependent source
weight is cancelled algebraically, all cutoff cases are explicit, and the
infinite upper tail is justified by an actual summability proof. No
big-O truncation claim from the source is imported; its remaining explicit
majorant sum must still be estimated in Lean.

Release 4.29 estimates that majorant locally. The only source-independent
input is the frozen, already proved bound for the positive von Mangoldt
Dirichlet series. The reciprocal-distance comparison, integral endpoint
separation, optimized-power simplification, summation, and specialization
to the HT contour height are all proved in this node. No asymptotic Perron
error from the paper is imported; absorption into Tao's target allowance
remains a separate formal obligation.

Release 4.30 proves the sharp arithmetic summation locally rather than
importing the paper's omitted Perron-error calculation. The near/far split,
half-integral harmonic comparison, factor-two far estimate, explicit
summation, and source-height specialization are all checked in Lean. The
only reused analytic input is the frozen positive von Mangoldt series bound.
Eventual absorption into the equation-(3.10) scale is not yet claimed.

Release 4.31 proves that absorption locally. No asymptotic truncation estimate
is imported: the source exponent inequality, fixed-logarithm absorption,
three-component budget, restoration of the `y^(beta-1)` factor, and comparison
with the exact Lemma-6 allowance are all formal Lean arguments. The remaining
source analytic work in this chain is confined to the three displaced edges
and the elementary small-beta case.

Release 4.32 introduces no new analytic source. It proves the contour
length-times-sup reduction directly from Mathlib's interval-integral norm
inequality, computes the literal HT edge lengths, and combines the three
normalized edges. The only remaining large-beta source input is pointwise
control of the translated zeta logarithmic derivative on those boundaries.

Release 4.33 likewise imports no omitted contour estimate. The reciprocal
Perron denominator is integrated locally, its logarithmic envelope is proved
from the fundamental theorem of calculus, and the zeta-Perron integrand norm
is factored exactly in Lean. This removes the artificial full-height loss
from the vertical sup reduction. The remaining source-facing analytic input
is precisely a translated zero-free-strip logarithmic-derivative bound.

Release 4.34 proves that logarithmic-derivative input locally from the pinned
native VK theorem and frozen Landau machinery. The spare-width separation,
individual and summed zero-term estimates, exclusion from the larger zero
disk, partial-fraction instantiation, and physical-coordinate transport are
all checked in Lean. No selected-height logarithmic-derivative estimate or
omitted contour bound from the paper is imported.

Release 4.35 adds no source assumption. The negative-height estimate is
proved from the pinned conjugation identity, the absolute-height wrapper is
an exact reparameterization of release 4.34, and the logarithmic form uses
only the frozen proved zero-mass and elementary logarithm bounds.

Release 4.36 proves the low-height input locally. It uses the pinned native
VK theorem to exclude surrogate zeros on a fixed compact rectangle, standard
compactness for the resulting continuous logarithmic derivative, and the
already proved exact surrogate/zeta identity for the pole term. No omitted
low-height estimate is imported.

Release 4.37 also imports no contour estimate. The nine-frequency comparison,
horizontal ordinate geometry, real-strip bounds, and vertical high/low case
split are local Lean arguments using only the already pinned VK and Landau
results.

Release 4.38 imports no new analytic estimate. Surrogate-to-zeta
nonvanishing, the exact shifted-integrand factorization, horizontal
reciprocal-height geometry, vertical denominator retention, and weighted
integration are all local consequences of the pinned results already listed.

Release 4.39 adds no source input. The factor-two shift correction uses the
same pinned VK region and a stronger local asymptotic comparison. Every
logarithmic envelope and stretched-exponential absorption is proved locally
from the explicit release-4.38 majorant.

Release 4.42 adds no source assumption. It combines the already pinned
native VK zero-free rectangle, frozen Euler-product right-line lower bound,
frozen Pintz zeta-window estimate, and frozen disk logarithmic-derivative
theorem. The variable-disk geometry, empty-zero-set reduction, native-width
specialization, `loglog` estimates, HT scale absorption, and low/high-height
assembly are all proved locally in Lean.
