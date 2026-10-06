# Sources and repository survey — 5 October 2026

This is a fresh primary-source survey, not a copied node-77 literature list. The research cutoff is 5 October 2026; exact API observations are in `Tools/upstream_snapshot.json` and archived under `Sources/observations/`. Search result crawl dates do not establish publication dates. The primary submission was 1 September, not October. The goal was subsequently activated on 5 October; source review and Lean implementation are underway.

## Primary paper, author pages and companion programs

| Resource | Observed state and significance |
|---|---|
| [arXiv record](https://arxiv.org/abs/2609.00537) / [v1 PDF](https://arxiv.org/pdf/2609.00537v1) / [TeX archive](https://arxiv.org/src/2609.00537v1) / [HTML](https://arxiv.org/html/2609.00537v1) | One listed revision, v1, submitted 2026-09-01 01:21:11 UTC; 37 PDF pages. Theorem 8 weighted Poisson, Theorem 9 AFE1, Theorem 10 AFE2, Corollaries 0.1–0.5 and 8.1. No journal-reference/DOI field for a journal publication observed. arXiv DOI is a preprint identifier. |
| [Kadiri's research homepage](https://sites.google.com/view/habibakadiri/home) | Lists the paper as current research with Dhiman and Quesada-Herrera and identifies the 2025 explicit B-process/AFE student project. Primary author context, not independent verification. |
| [Quesada-Herrera's research page](https://sites.google.com/view/quesada-herrera/research) | Lists the paper under 2026 preprints, not the published-paper list. No separate correction or code repository linked for it in the inspected page. |
| [AFE1.sage](https://arxiv.org/src/2609.00537v1/anc/AFE1.sage) | Author's SageMath 9.5 script for Corollary 0.3. Symbolic derivatives, interval comparisons and floating-point constants. Archived within the original source extraction; inspected, not replayed. |
| [AFE2.py](https://arxiv.org/src/2609.00537v1/anc/AFE2.py) | Author's NumPy/SciPy/Decimal script for AFE2 constants. Archived unchanged and replayed. Detailed limitations are in Computation Review and E08. This is the actual companion code found, even though no dedicated GitHub repo was found. |
| [2026 Meeting of the Minds abstract book](https://www.ulgsa.org/_files/ugd/2fb501_1e6d0c6b0e5948628a79fea23094f7a4.pdf) | Conference abstract “Approximation of Zeta Function on the critical line” by the same three authors, p.36. Contextual earlier presentation, not an alternate theorem edition. |

The arXiv archive contains seven files: processing metadata, TeX, compiled bibliography, two EPS figures, and the two ancillary programs. It references `AFE2026ago31.bib`, but that `.bib` is not present; the supplied `.bbl` contains the bibliography. Do not fabricate a recovered original bibliography or assume a clean LaTeX rebuild without recording this detail.

## Direct analytic references and editions

The 15-entry source bibliography is preserved verbatim in the archived `.bbl`. The table below covers every entry and separates actual supporting inputs from historical/comparative references.

| Source bibliography | Verified resource / edition | Role in this project |
|---|---|---|
| [1] Abramowitz–Stegun, 1965 | Source bibliography; related modern [NIST DLMF gamma relations](https://dlmf.nist.gov/5.5) and [gamma asymptotics](https://dlmf.nist.gov/5.11) inspected | Digamma recurrence/duplication and asymptotic checks. DLMF is a companion reference, not a substituted source edition or a Lean proof. |
| [2] Arias de Reyna, *High precision computation… Riemann–Siegel formula, I*, Math. Comp. 80 (2011), 995–1009 | Bibliographic details from original `.bbl`; relevant Theorems 4.1–4.2 identified in DKQH | Comparative symmetric AFE2 constants through Simonič. Full paper not independently archived/reviewed in this setup. |
| [3] Arias de Reyna, *On the approximation of the zeta function by Dirichlet polynomials* | [arXiv:2406.16667v1](https://arxiv.org/abs/2406.16667v1), submitted 24 June 2024; six-page PDF archived | Lemma 2 stationary/nonstationary integral input; Lemmas 4–5 comparison Poisson bounds; Theorem 6 sharp truncation comparison. |
| [4] Brent, *Algorithms for minimization without derivatives*, 1973, chapter 4 | Original bibliography; [SciPy's primary implementation documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.minimize_scalar.html) inspected | Numerical search method. SciPy explicitly describes local minimization; no global or certified upper bound follows solely from optimizer success. |
| [5] Hardy–Littlewood, 1921, Math. Z. 10, 283–317 | Original bibliography and DKQH's explicit Lemma 15 / Lemma 2 citations | Historical log-loss AFE/first-kind argument. No claim to have digitized or rechecked every original page. |
| [6] Hardy–Littlewood, 1923, Proc. LMS s2-21, 39–74 | Original bibliography and Theorem A citation | Historical log-free AFE. It is a different route and does not remove DKQH's stated log factors automatically. |
| [7] Iwaniec–Kowalski, *Analytic Number Theory*, 2004 | [Author-hosted exponential-sums excerpt](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf), reused byte-identically from node 77 with its origin retained | Section 8.3/Proposition 8.7 comparison and classical Poisson/stationary analysis; available locally before writing new infrastructure. |
| [8] Kadiri, *A zero density result for the Riemann zeta function*, Acta Arith. 160 (2013), 185–200 | [Publisher](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/160/2/83310/a-zero-density-result-for-the-riemann-zeta-function); [author PDF](https://www.cs.uleth.ca/~kadiri/articles/explicit-bound-NsigmaT-ActaArith-July-2013.pdf) archived; [2014 arXiv record](https://arxiv.org/abs/1401.4781) | Corollary 1.3 earlier AFE1 constant. The later arXiv upload date is not the journal year. |
| [9] Karatsuba–Korolev, 2007 | [Journal PDF](https://www.mathnet.ru/links/88ad61a777d3e9924c1423613b66a/im1136_eng.pdf), DOI [10.1070/IM2007v071n02ABEH002359](https://doi.org/10.1070/IM2007v071n02ABEH002359) | Explicit shorter-sum transformation. Russian pp.123–150 versus English pp.341–370 are translations, not conflicting papers. Web text was accessible; direct archive download returned HTTP 403, so no local PDF is claimed. |
| [10] Dhir Patel, Ohio State PhD thesis, 2021 | [OhioLINK thesis](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1626742085346834&disposition=inline), accession `osu1626742085346834`, PDF archived | Lemma 2.26 and explicit derivative/B-process context. |
| [11] Patel–Yang, *An explicit sub-Weyl bound for ζ(1/2+it)*, JNT 262 (2024), 301–334 | [arXiv:2302.13444v1](https://arxiv.org/abs/2302.13444v1), submitted 27 February 2023, PDF archived; publication metadata preserved from DKQH | Lemmas 2.1/2.3 and equation (2.2), used in the explicit stationary/B-process comparison. Proposed improvement of their final subconvexity constant is not proved in DKQH. |
| [12] Platt–Trudgian, RH true to 3·10^12, BLMS 53 (2021), 792–797 | Original bibliography | Explains a chosen numerical threshold. Not a premise that RH holds above it, and not required to prove an AFE bound for that value of t₀. |
| [13] Revol–Rouillier, MPFI, Reliable Computing 11 (2005), 275–290 | Original bibliography; [Sage MPFI interval documentation](https://doc.sagemath.org/html/en/reference/rings_numerical/sage/rings/real_mpfi.html) inspected | AFE1 interval-arithmetic context. External interval arithmetic is still separate from kernel-checked certification. |
| [14] Simonič, *Explicit zero density estimate… near the critical line*, JMAA 491 (2020), 124303 | [arXiv:1910.08274v2](https://arxiv.org/abs/1910.08274v2), revised 29 November 2019; PDF archived | Proposition 1 χ bound, Corollary 2 AFE1 comparison, Theorems 4/6 and Tables 2–4 AFE2 comparison. Preprint is 35 pages; DKQH cites a 41-page journal article. Compare numbering before importing a quoted result. |
| [15] Titchmarsh, *The theory of the Riemann zeta-function*, second edition 1986 | Original bibliography; exact cited lemma/theorem/equation numbers retained in TeX | Lemmas 4.7/4.10; equations 4.12.3; Theorems 4.11/4.13/4.15. Standard historical foundations; use existing formal APIs where their precise statements fit. |

## Repositories observed live

| Repository | Observed immutable HEAD | Toolchain / decision |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `9194f400a4ef67d0c14c98e0cf300cc9f289048e`, 2026-10-05 07:59:20 UTC | `v4.35.0-rc3`. Discovery only. This checkout uses Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` / Lean 4.30; preserve it. |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `c39a751132c88b6e8080b74c74023fd95b3d8be0`, 2026-10-01 03:31:57 UTC | `v4.34.0`. Installed pin is `4ecb950126c4290293c5662dfe0e884123171df5`, with usable digamma series and analytic infrastructure already present. No upgrade installed. |
| [ANTEDB / expdb](https://github.com/teorth/expdb) | `c8eda5e4f1f51024b6cbf70c7bef6c33da74c691`, 2026-09-26 19:01:00 UTC | `v4.32.0`; complete API tree contained 18 `.lean` files, no truncation. Asymptotics, exponential-sum language, Fourier bumps and Euler–Maclaurin are visible. No DKQH-specific file found in that tree. Node 63 already has a much larger local completed extension; do not confuse current external ANTEDB with its local proof coverage. |

The exact toolchain files and API responses are archived. These observations do not certify every theorem at upstream HEAD. No new repository is installed and no third-party theorem is imported during setup.

Broad indexed AFE/Lean searches also found [Littlewood_Proof](https://github.com/JohnNDvorak/Littlewood_Proof) and [RH_DH_experiment_2026](https://github.com/captaldebuch/RH_DH_experiment_2026). Their publicly surfaced documentation describes incomplete/conditional work. Neither is a dedicated DKQH implementation; neither was selected, copied or axiom-audited. An apparent proof claim or project name is not dependency evidence. Prefer the audited local library and pinned Mathlib/PNT+ sources.

## Search ledger and limits

Executed exact-title/author/arXiv searches; title plus `code repository`; arXiv ID plus `site:github.com`; author trio plus `erratum`; general `approximate functional equation Lean github`; direct author-page checks; current public GitHub repository searches `2609.00537` and `Dhiman Kadiri`; and current upstream commit/toolchain/tree checks. Both GitHub repository queries returned `total_count=0`, with raw JSON archived. No authenticated global GitHub code search or exhaustive private-repository survey is claimed.

Outcome: no dedicated public DKQH Lean formalization, separately linked GitHub companion repo, later primary revision or author erratum was found. **Two actual author programs are available on arXiv.** Negative searches do not exclude private, unindexed or differently named work. This dated evidence should be refreshed when the goal is activated; the primary paper and source code remain the mathematical references rather than search summaries.

## Additional Kershner investigation — 5 October 2026

Rogers’s author-hosted [Real and p-Adic Oscillatory Integrals thesis](https://web.maths.unsw.edu.au/~michaelc/Students/rogers.pdf), printed page 13 and bibliography, attributes the sharp second-derivative constant to Kershner’s 1935 and 1938 papers. The extracted formula needs visual verification before reuse; the browser PDF screenshot failed. The older [2003 preprint](https://arxiv.org/abs/math/0311013) has different historical wording and is not a kernel certificate for 1.343. The [published Rogers paper](https://doi.org/10.1090/S0002-9939-05-07918-9) and its AMS PDF were unavailable through the browsing tool during this check. No inaccessible proof was treated as read.

The new FresnelSharp proof instead uses the pinned Mathlib rectangle form of Cauchy–Goursat and the already proved local Fresnel limit. These research observations neither change the 25 frozen source pins nor supply the still-missing general Kershner bound.
