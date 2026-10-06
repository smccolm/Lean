# Dubon 2026 — research survey as of 6 October 2026

**GOAL ACTIVE — 0/20 proof gates complete.** Research snapshot, source hashes and negative-search evidence are retained locally. Live web facts below are dated observations, not permanent claims.

## Primary paper and author

Eric Dubon, [*Zero-Density Concentration for Dirichlet Polynomials*](https://arxiv.org/abs/2609.17875), arXiv:2609.17875v1, submitted 15 September 2026 at 22:04:33 UTC, 28 pages. The live history showed only v1 on the research date. The PDF, HTML, abstract/history page, complete source tarball and both extracted members are frozen under Sources. The TeX contains **139 labels and 25 inline bibliography entries**, indexed in [source_labels.json](Tools/source_labels.json). It has no ancillary program.

The [University of Alicante author profile](https://cvnet.cpd.ua.es/curriculum-breve/es/dubon-eric-vincent/19872) provides primary institutional context. Exact-title/arXiv/author searches and that page yielded no identified later revision, published erratum or dedicated companion repository. This statement is limited to the recorded survey. The arXiv deposit's distribution permission is not a license to reuse arbitrary source code.

## Primary supporting sources actually retrieved

| Resource | Why it matters | Inspection / limitation |
|---|---|---|
| Jessen–Tornehave, [*Mean motions and zeros of almost periodic functions*](https://archive.ymsc.tsinghua.edu.cn/pacm_paperurl/20170108203121071731656), Acta Math. 77 (1945), 137–279; DOI 10.1007/BF02392225 | Actual vertical logarithmic mean, convexity and zero frequencies | Full 143-page PDF retained. Theorems 5, 7, 31 and §116 located; Theorem 31's printed p.275 visually confirms the all-open-strip one-sided formula. These classical results still need Lean proofs/bridges. |
| Barnet-Lamb–Gee–Geraghty, [*The Sato–Tate conjecture for Hilbert modular forms*](https://arxiv.org/abs/0912.1054), v2; JAMS 24 (2011), 411–469 | Source [2], Corollary 7.1.7 | Full PDF retained; exact corollary inspected. It concerns non-CM automorphic representations and normalized Hecke eigenvalues. Classical newform specialization and rescaling remain explicit proof obligations. |
| Viktor Andersson, [*The Littlewood–Paley formula and mean counting function for vertical limits of Dirichlet series*](https://arxiv.org/abs/2606.20293), v2, 2 July 2026 | New 2026 context cited by Dubon | Full 31-page PDF retained. Its infinite-series/vertical-limit setting is not a drop-in statement of Dubon's finite-polynomial theorem. |
| Eric Dubon, [*A note on the density of zeros of partial sums of the Dirichlet lambda, beta and eta functions*](https://doi.org/10.1007/s40879-025-00821-0), European J. Math. 11 (2025), article 29 | Earlier work by the same author | Primary University of Alicante repository PDF retained; title and abstract inspected. Density of real parts must not be conflated with normalized vertical-frequency concentration. |

## Repository survey

The public GitHub repository API returned zero repositories for `2609.17875`, `"Zero-Density Concentration"` and `Dubon Dirichlet`; the exact JSON responses are archived. Web queries also covered the exact title, arXiv identifier, errata, Jessen/Bohr Lean formalization, Sato–Tate Lean and Bessel J₀ Lean. This was not authenticated global code search and cannot exclude private, differently named or unindexed work.

| Repository | Observed commit / toolchain | Relevance and selection |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `331d5244f0d3aad530d9ab00ded135b4c7691502`, 6 Oct; Lean 4.35.0-rc3 | Full tree and Bessel source archived. New `Complex.besselJ` definitions/analyticity, with integral formulas still TODO. Selected local Mathlib remains the existing 4.30.0 pin. |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `c39a751132c88b6e8080b74c74023fd95b3d8be0`, 1 Oct; Lean 4.34.0 | Full tree archived. Existing pinned PNT already has actual prime-counting asymptotics; use those first. Newer complex-analysis files are research leads, not automatically audited dependencies. |
| [ANTEDB / expdb](https://github.com/teorth/expdb) | `c8eda5e4f1f51024b6cbf70c7bef6c33da74c691`, 26 Sep | Full tree archived; analytic-number-theory reference database, not a Lean proof of this concentration theorem. |
| [LeanBridge](https://github.com/cbirkbeck/LeanBridge) | README snapshot 6 Oct | LMFDB-to-Lean definitions/blueprint resource, not evidence that Sato–Tate has been proved. No dependency selected. |
| [Ramanujan tau misses primes](https://github.com/AxiomMath/ramanujan-tau-misses-primes) | README snapshot 6 Oct; advertised Lean 4.34.0-rc2 | ABC-conditional prime-value problem, not the general non-CM Sato–Tate/Rankin–Selberg theorem required here. No dependency selected. |

Exact commit dates, tree completeness, queries and scope limits are in [upstream_snapshot.json](Tools/upstream_snapshot.json); retrieval URLs, sizes and SHA-256 values are in [download_receipts.json](Tools/download_receipts.json). Branch README snapshots are dated byte captures, not immutable commit pins. No external repository was installed or executed.

## Complete bibliography coverage

All 25 entries below are transcribed/indexed from the frozen source bibliography. “Reference” means recorded for later consultation, not that every page or proof was reviewed. Primary theorem sources and the full frozen bibliography remain available even where a book or publisher PDF was not downloaded.

| Source number | Reference / stable identifier | Role |
|---|---|---|
| 1 | Andersson 2026, arXiv:2606.20293 | Current vertical-limit context; retrieved |
| 2 | Barnet-Lamb–Gee–Geraghty 2011, DOI 10.1090/S0894-0347-2010-00689-3 | Sato–Tate; retrieved preprint |
| 3 | Boyd 1998, DOI 10.1080/10586458.1998.10504357 | Mahler-measure context |
| 4 | Borwein–Fee–Ferguson–van der Waall 2007, DOI 10.1080/10586458.2007.10128981 | Earlier zeta partial-sum zeros |
| 5 | Conway, *Functions of One Complex Variable I*, 2nd ed., 1978 | Complex analysis/Jensen |
| 6 | Deligne, *La conjecture de Weil I*, 1974, DOI 10.1007/BF02684373 | Ramanujan–Petersson bound input |
| 7 | Dubon 2025, DOI 10.1007/s40879-025-00821-0 | Earlier density work; retrieved |
| 8 | Folland, *Real Analysis*, 2nd ed., 1999 | Stieltjes measures/integration |
| 9 | Gonek–Ledoan 2010, DOI 10.1093/imrn/rnp186 | Zeros of zeta partial sums |
| 10 | Haviland–Wintner 1934, DOI 10.2307/2370908 | Kronecker–Weyl input |
| 11 | Iwaniec, *Topics in Classical Automorphic Forms*, 1997, §§6.6–6.8 | Actual newforms and coefficient conventions |
| 12 | Jessen–Tornehave 1945, DOI 10.1007/BF02392225 | Central mean/zero-frequency theory; retrieved |
| 13 | Kahane, *Some Random Series of Functions*, 2nd ed., 1985 | Random-circle-series context |
| 14 | Kerr–Klurman–Thorner 2026, DOI 10.1007/s00208-026-03542-1 | L-function zeros / partial sums context |
| 15 | Ledoan–Roy–Zaharescu 2014, DOI 10.1016/j.jnt.2013.09.003 | Dedekind partial-sum zeros |
| 16 | Li–Roy–Zaharescu 2016, DOI 10.1007/s11139-016-9791-3 | Symmetrized Hecke approximations |
| 17 | Montgomery, *Zeros of approximations to the zeta function*, 1983 | Earlier asymptotic geometry |
| 18 | Mora 2013, DOI 10.1016/j.jmaa.2013.02.006 | Partial-sum zero geometry |
| 19 | Rankin 1939, DOI 10.1017/S0305004100021101 | Mean-square Fourier coefficients |
| 20 | Rockafellar, *Convex Analysis*, 1970, Theorems 10.8 and 24.1 | Convex local uniform limits and one-sided slopes |
| 21 | Roy–Vatwani 2019, DOI 10.1016/j.aim.2019.02.009 | Zeros of Dirichlet polynomials |
| 22 | Roy–Vatwani 2021, DOI 10.1090/tran/8261 | Further zero-distribution context |
| 23 | Rudin, *Fourier Analysis on Groups*, 1962, §1.5.2 | L¹ characteristic function to bounded density |
| 24 | Selberg 1940, Arch. Math. Naturvid. 43, 47–50 | Rankin–Selberg coefficient input |
| 25 | Watson, *Bessel Functions*, 2nd ed., 1944, §§2.11, 2.2, 7.21 | J₀ series, circle integral and asymptotic |

The formalization should first use audited local APIs and then fill exact missing bridges. No table entry converts a classical reference into a proved Lean dependency.
