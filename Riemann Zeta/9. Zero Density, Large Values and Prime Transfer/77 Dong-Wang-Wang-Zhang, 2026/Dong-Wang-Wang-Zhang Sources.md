# Sources and repository survey — 4 October 2026

This is a dated research snapshot, not a claim to have searched every private/unindexed repository. Primary-paper statements were read in full; cited analytic inputs and candidate Lean interfaces were inspected selectively. No source is treated as a Lean proof merely because it is published or present in a database.

## Primary paper and publication status

Zikang Dong, Ruihua Wang, Weijia Wang, Hao Zhang: *Large zeta sums and zeros of the Riemann zeta function*. [arXiv record](https://arxiv.org/abs/2608.31060), [versioned HTML](https://arxiv.org/html/2608.31060v1), [PDF](https://arxiv.org/pdf/2608.31060v1), [TeX archive](https://arxiv.org/src/2608.31060v1). The observed history has **v1 only**, submitted **31 August 2026, 16:38:47 UTC**, 19 pages. DOI `10.48550/arXiv.2608.31060` is an arXiv DOI, not evidence of journal acceptance.

The [first author's current publication list](https://zikangdong.github.io/) lists this as preprint [25], distinct from the three-author *Large zeta sums* published in 2025. No later primary revision, author-issued erratum, journal version, or dedicated implementation was identified in this survey. Search-engine crawl dates are not publication dates.

The primary v1 PDF, raw source archive, `main.tex` and arXiv processing metadata are archived locally. The abstract is not sufficient to recover the exact disk radius or quantifier order; those come from the full Theorems 1.1/1.2 and their proofs. See [Source Contract](Dong-Wang-Wang-Zhang%20Source%20Contract.md).

Activation recheck, 4 October 2026: the live arXiv submission history still lists only v1. All nine archived artifact hashes pass. Node-73 interface survey scope and its negative reuse outcome for the initial obligation are now recorded in Crosswalk; no source revision or dependency upgrade was selected.

## Essential analytic references

| Source | Exact role | Access and local record |
|---|---|---|
| Granville–Soundararajan, *Decay of Mean Values of Multiplicative Functions*, Canadian J. Math. 55 (2003), 1191–1230, DOI `10.4153/CJM-2003-047-0` | Theorems 2b/4, Lemma 7.1: hybrid mean-value, Lipschitz and twist-comparison inputs of Lemma 2.1. | [Publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/9BE47DD2587F7A1078B1D9219B5B3F82/S0008414X00031552a.pdf/decay-of-mean-values-of-multiplicative-functions.pdf) archived; [1999 preprint](https://arxiv.org/abs/math/9911246) also archived, but not an interchangeable edition. Relevant journal statements and comparison proof inspected. |
| Granville–Soundararajan, *Large character sums: Burgess's theorem and zeros of L-functions*, JEMS 20 (2018), 1–14, DOI `10.4171/JEMS/757` | Section 2 restatement; Lemmas 3.1–3.3; Proposition 3.4; Theorem 1.3. Direct architectural ancestor of this paper. | [Journal PDF](https://ems.press/content/serial-article-files/32264), [arXiv v2](https://arxiv.org/abs/1501.01804v2), both archived. ArXiv's corresponding proposition is numbered 3.1; the journal citation is correct. |
| Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004), Chapter 8, especially §§8.3–8.4 | Classical exponent pair `(1/6,2/3)` and first-derivative technology for Lemma 5.1. | [Author-hosted exponential-sums excerpt](https://people.math.ethz.ch/~kowalski/ik-ant-exp-sums.pdf) accessible and archived (61 pages). This is an excerpt, not a downloaded complete book. |
| Guth–Maynard, *New large value estimates for Dirichlet polynomials*, Annals 203 (2026), 623–675 | Supplementary Remark 1.3; also local analytic/counting infrastructure. Not a premise of T1. | [arXiv](https://arxiv.org/abs/2405.20552); primary source already held by node 63 and foundation contracts already local. No duplicate archive needed here. |

The adaptation must keep the translated spectral height and the zeta pole. The character-sum theorem cannot simply be instantiated with `n^(it)` as a Dirichlet character. Likewise its modulus parameter is not automatically the zeta height. Those are the substantive mathematical changes to trace through Sections 2–4.

## Other references and current surrounding work

These identify the context and alternative techniques; none supplies a discovered ready-made Lean proof of T1/T2.

| Paper/reference | Verified resource | Relevance / limitation |
|---|---|---|
| Dong–Wang–Zhang, *Large zeta sums*, Period. Math. Hung. 91 (2025), 388–398; primary bibliography [1] | [arXiv:2310.13383](https://arxiv.org/abs/2310.13383), first author's publication list | Prior asymptotics and large-value constructions; not the four-author inverse theorem. |
| Fréchette–Gerbelli-Gauthier–Hamieh–Tanabe, *Large Sums of Fourier Coefficients of Cusp Forms*, JTNB 37 (2025), 171–188; [2] | [Journal](https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.1318/), [arXiv:2308.06311](https://arxiv.org/abs/2308.06311) | Related local-zero criterion for cusp-form sums, not a zeta specialization. |
| Peng Gao, *Upper bounds for moments of zeta sums*, J. Number Theory 278 (2026), 47–63; [3] | [Publisher](https://www.sciencedirect.com/science/article/pii/S0022314X25001416), [arXiv:2405.12506](https://arxiv.org/abs/2405.12506) | RH-dependent moment upper bounds; may not be imported as unconditional pointwise input. |
| Gonek–Graham–Lee, *The Lindelöf hypothesis for primes is equivalent to the Riemann hypothesis*, Proc. AMS 148 (2020), 2863–2875; [7] | Bibliographic entry and displayed formulation read in primary paper; [AMS meeting abstract](https://jointmathematicsmeetings.org/amsmtgs/2217_abstracts/1145-11-1074.pdf) located | Context only; full journal proof not independently inspected in this setup. |
| Adam Harper, *The typical size of character and zeta sums is o(sqrt(x))*; [8] | [arXiv:2301.04390](https://arxiv.org/abs/2301.04390) | Averaged/typical behavior, not pointwise zero forcing. |
| Youness Lamzouri, *Large sums of Hecke eigenvalues of holomorphic cusp forms*, Forum Math. 31 (2019), 403–417; [10] | [arXiv:1703.10582](https://arxiv.org/abs/1703.10582) | Automorphic analogue; separate objects and hypotheses. |
| **Daodao** Yang, *Extreme values of derivatives of zeta and L-functions*, BLMS 56 (2024), 79–95; [11] | [Publisher](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/blms.12915), [arXiv:2204.13826](https://arxiv.org/abs/2204.13826) | The primary paper cites Theorem 5 for an RH smooth-number approximation; not Andrew Yang and not an unconditional replacement. |
| Dong–Wang–Zhang, *Lower bounds for high moments of zeta sums* | [arXiv:2506.09334](https://arxiv.org/abs/2506.09334) | Related unconditional lower moments, not a missing inverse-theorem proof. |
| Harper, *Lower bounds for low moments of character sums, I: Short sums with general multiplicative weights* (July 2026) | [arXiv:2607.01184](https://arxiv.org/abs/2607.01184) | Current related work also discussing zeta-sum moments; distinguish this newer context from dependencies actually cited in v1. |

The eleven references of the primary paper are accounted for above: [4] Guth–Maynard, [5] GS 2003, [6] GS 2018 and [9] Iwaniec–Kowalski appear in the essential-input table. Only the core inputs were archived; context papers remain linked.

## Live repositories observed on 4 October 2026

Commit IDs and toolchain files were read directly from public GitHub APIs/raw files, with untruncated recursive file inventories. These are observations, **not dependency upgrades**. [Machine-readable snapshot](Tools/upstream_snapshot.json).

| Repository | Observed default-branch commit / commit date UTC | Observed Lean toolchain | Scope relevant here |
|---|---|---|---|
| [teorth/expdb (ANTEDB)](https://github.com/teorth/expdb) | [`c8eda5e4f1f51024b6cbf70c7bef6c33da74c691`](https://github.com/teorth/expdb/commit/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691), 26 Sep 19:01 | `v4.32.0` | 18 Lean files in whole tree; includes log phase, finite/nonasymptotic exponential sums, scale transfer, oscillatory bounds and Euler–Maclaurin. Python/blueprint entries are not kernel proofs. |
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | [`dd56d02cb7a58fa066c4a2c7fddec3cbb59ae8df`](https://github.com/leanprover-community/mathlib4/commit/dd56d02cb7a58fa066c4a2c7fddec3cbb59ae8df), 4 Oct 17:07:32 | `v4.35.0-rc3` | 9,188 Lean files in whole tree; current zeta/log-derivative, Gaussian Fourier, Mellin and complex-analysis infrastructure. No target-paper implementation located. |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | [`c39a751132c88b6e8080b74c74023fd95b3d8be0`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/commit/c39a751132c88b6e8080b74c74023fd95b3d8be0), 1 Oct 03:31:57 | `v4.34.0` | 236 Lean files in whole tree; xi/Hadamard, zeta continuation, log derivative, Mertens, Euler–Maclaurin and Mellin candidates. Full dependency audits not performed here. |

The installed foundation instead uses Lean `v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, and PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`. Node 63's ANTEDB subset came from `088040634e8300f87e80f431d8bdc38c42cc8e11`; it is **not** current upstream HEAD. Prefer audited compatible local interfaces before introducing an upgrade. Do not mix these toolchains in one Lake graph.

## Search ledger and meaning of negative results

All searches below were run on 4 October 2026.

- Web: exact title; `"Dong" "Wang" "Wang" "Zhang" zeta arxiv`; `"2608.31060" github Lean`; exact title excluding arXiv; ID with `erratum OR correction OR formalization`; ID with `Lean OR Coq OR Isabelle OR GitLab`. Results identified the paper, author listing and secondary summaries, but no dedicated verified implementation or correction.
- GitHub repository search: `2608.31060`, `large zeta sums`, `Halasz lean` each returned an empty repository list. GitHub code search for `2608.31060` returned no matches. This is a bounded indexed search, not proof of nonexistence.
- GitHub scoped code search for `Halasz` and `pretentious` in Mathlib, ANTEDB and PNT+ found ANTEDB bibliography/blueprint/Python mentions, not a located Lean mean-value/Lipschitz implementation. Name searches can miss equivalent differently named results; future implementation must inspect exact interfaces.
- Local search covered node 63's production and frozen dependencies, foundation modules, node 74's cleaned PNT+ tree, and installed Mathlib. Actual useful declarations and caveats are in the Crosswalk. Halász–Montgomery occurrences in the large-values foundation are not the required multiplicative mean-value theorem.
- Primary source retrieval initially failed under restricted shell networking; the authorized public downloads then succeeded. No missing credential or inaccessible essential source remains for planning. No authors were contacted and no issues/messages were posted.

No exhaustive public-proof absence, whole-internet completeness, independent correctness review, or future reproducibility of moving URLs is asserted. The paper and essential input bytes are pinned locally; upgrades and additional discovery require explicit comparison, not silent replacement.
