# Dubon source acceptance review — 6 October 2026

This review records the source-contract work for DUB-01. It does not certify any downstream mathematical gate or the whole paper. The original PDF, TeX, source archive, all 139 labels and all 25 bibliography entries remain unchanged. No author-issued erratum or false printed theorem is asserted.

The complete TeX, including proofs and bibliography, was read against the frozen source ledger. The PDF has 28 pages; its full text was extracted, and complete displayed source statements were visually compared on pages 3–6, 9, 12, 21 and 26. The primary contracts agree. In particular, Corollary 8.2 explicitly says **cusp eigenform**. The independent level-one construction therefore consumes the paper’s actual class of objects.

The companion `Tools/source_acceptance_20261006.json` lists each label and bibliography entry individually, with original line and assigned semantic contract. The frozen `Tools/source_labels.json` remains unchanged.

## Reviewed source blocks

| TeX lines | Labels | Owning gates | Contract |
|---|---:|---|---|
| 1–290 | 33 | DUB-02/11–18 | Actual source objects and all main-result hypotheses; height tends to infinity for each fixed truncation before the truncation limit. |
| 291–343 | 5 | DUB-03 | Prime factorization, injective exponent vectors, trivial integer resonance lattice and actual vertical flow. |
| 344–541 | 8 | DUB-04/05 | Nonzero multivariate logarithmic integrability; continuous equidistribution alone is insufficient for the logarithm; actual uniform truncation transfer required. |
| 542–590 | 4 | DUB-06 | Every open strip uses analytic multiplicity, symmetric height normalization and (J′(b−)−J′(a+))/(2π), including atom-carrying boundary lines. |
| 591–720 | 4 | DUB-04/07 | Actual energy, iterated Jensen, affine asymptotes, total mass log M; probability normalization requires M>1. |
| 721–967 | 29 | DUB-08/09 | Positive K-comparable weights; one constant before every m≥5 and every complex translation; three Fourier regions with the exact planar inversion factor. |
| 968–1110 | 6 | DUB-10 | Literal isolated-prime decomposition, phase rotations and the genuine conditional product Haar integral. |
| 1111–1283 | 9 | DUB-11/12 | Pointwise H1, compact-uniform H2, eventual supported maximum and local uniform potential convergence; tightness upgrades to weak probability convergence. |
| 1284–1394 | 11 | DUB-13 | Inclusive dyadic PNT and all real energy regimes; Corollary 6.1 keeps the boundary-frequency convention and the nested limit order. |
| 1395–1533 | 10 | DUB-14 | Every fixed positive modulus, including principal and imprimitive characters; exact totient coefficient, σ=1/2 and actual support maximum. |
| 1534–1615 | 8 | DUB-15/16 | Genuine normalized cusp coefficients; Rankin–Selberg and c_f>0 remain explicit proof obligations. Weighted asymptotics must include σ=0,3/10,1/2. |
| 1616–1687 | 10 | DUB-15/17 | Actual Deligne bound and non-CM Sato–Tate remain proof obligations; semicircle/angle normalization, η/2 dyadic density, ramified-prime removal and compact comparability are retained. |
| 1688–1718 | 2 | DUB-18 | Actual classical shift by (k−1)/2; Corollary 8.2 explicitly quantifies over cusp eigenforms. The level-one primitive/non-CM bridge has an independent Fricke/depletion proof. |

## Source-review decisions

- **E01 resolved as a convention/obligation:** N=1 and M_N=1 are excluded from literal probability normalization. The declared early Dirac convention is eventually replaced by the actual normalized measure, with support growth derived from H2. No division-by-zero probability claim is accepted.
- **E02 resolved as a proof obligation:** logarithms at zeros require actual nullity, integrability and uniform negative-log control. Haar integrability or dense flow alone is insufficient. The finite-jet/sublevel proof and actual vertical/Haar identity address the obligation without modifying the source.
- **E03 resolved without repair:** the PDF and TeX agree on open strips and the signs b−, a+. The retained Jessen–Tornehave Theorem 31 supports this convention. The λ example is read with positive frequency λ>0, as in the source contract. General boundary atoms are handled by the actual local proof, not by discarding endpoints. Corollary 6.1’s printed boundary convention is preserved; the local all-radius result is a strengthening.
- **E04 resolved without changing the threshold:** the operative statement is Lemma 4.1, m≥5. Informal introductory prose does not drop this hypothesis. One constant depends only on K; it precedes dimension, coefficient vector, probability space and translation. Negative-sign 2π Fourier APIs require the proved normalization bridge.
- **E05 resolved as exact quantifiers:** H1 is pointwise on all real abscissae; H2 is locally uniform left of α. The conclusion is locally uniform on all ℝ, including α. Height tends to infinity first for every fixed N. No coupled limit is introduced.
- **E06 resolved without restricting characters:** q>0, including q=1 and principal/imprimitive characters. The actual maximum supported index is used, and the totient factor is retained. No prime-number theorem in progressions is required.
- **E07 resolved as a retained downstream obligation:** the source’s modular hypotheses and true Rankin–Selberg, Deligne and Sato–Tate inputs are preserved. Actual primitive objects, eigenvalue scaling, coefficient reality and level-one non-CM are implemented; the classical-to-automorphic bridge and deep inputs remain OPEN. A bibliographic citation is never treated as a Lean proof. This is a resolution of the source scope, not completion of DUB-15–18.
- **E08 resolved as the exact topology:** the endpoint is weak convergence of probability measures, including bounded continuous tests and tightness, not merely vague/distributional convergence. The early-index convention does not affect this eventual statement.

## Bibliography roles

Every original entry was reviewed for its role in this paper. This checks source identity, applicability and the dependency contract; it does not claim a new full-text audit of every cited monograph or article.

| Key | Role |
|---|---|
| `Andersson2026` | Context: vertical limits of infinite Dirichlet series; not substituted for finite-truncation limits. |
| `BLGG2011` | Required deep input: Corollary 7.1.7 and its classical-to-automorphic normalization. Not yet a Lean theorem. |
| `Boyd1998` | Logarithmic Mahler measure background; actual finite-dimensional logarithmic integrability is proved locally. |
| `BorweinEtAl2007` | Historical/numerical context on finite zeta zeros; no numerical proof dependency. |
| `Conway1978` | Jensen and elementary complex analysis; imported analytic APIs and local exact adapters replace citation-only reasoning. |
| `Deligne1974` | Required deep arithmetic bound for actual cusp eigenvalues; still an open formalization input. |
| `Dubon2025` | Predecessor/support context; not the concentration theorem or a Lean dependency. |
| `Folland1999` | Positive Stieltjes measures and measure theory; actual one-sided derivative measure construction is implemented. |
| `GonekLedoan2010` | Different finite-height regime; no coupled limit imported into the target. |
| `HavilandWintner1934` | Continuous Kronecker–Weyl context; actual prime flow equidistribution and density proved locally. |
| `IwaniecTopics` | Classical newform/eigenvalue normalization; genuine old/newspace and Hecke objects implemented, automorphic bridge still separate. |
| `JessenTornehave1945` | Theorems 5,7,31; retained printed p.275 fixes the open-strip convention. Finite-polynomial proof obligations are implemented locally. |
| `Kahane1985` | Definition/background for independent uniform-circle variables; actual probability law and independence consumed in Lean. |
| `KerrKlurmanThorner2026` | Context about zeros of infinite L-functions; not a theorem about finite-polynomial zeros. |
| `LedoanRoyZaharescu2014` | Context: Dedekind-zeta partial sums; not part of the required application scope. |
| `LiRoyZaharescu2016` | Context: symmetrized approximations with a dual term; not the raw truncation in this project. |
| `Montgomery1983` | Context: extreme zeros of fixed finite approximations; distinct from normalized vertical mass. |
| `Mora2013` | Context: broad support is compatible with concentration of vertical mass. |
| `Rankin1939` | Required genuine mean-square asymptotic input, including a positive leading constant; still open. |
| `Rockafellar1970` | Convex slopes and compact-uniform convergence; actual convexity and derivative inequalities are proved/consumed locally. |
| `RoyVatwani2019` | Context: zero-free regions and counts for partial L-functions. |
| `RoyVatwani2021` | Context: existence and support of Dirichlet-polynomial zeros. |
| `Rudin1962` | Finite-measure Fourier inversion; exact Gaussian identification supplies the actual measure/density bridge locally. |
| `Selberg1940` | Required Rankin–Selberg input; remains open rather than being assumed as completed. |
| `Watson1944` | J₀ series, circle integral and large-argument bound; actual needed bounds proved locally with pinned dependencies. |

## Acceptance boundary

DUB-01 is a source-review gate. Its acceptance does not mean that any source theorem is proved simply because its statement is faithfully registered. Each mathematical gate still requires its actual source consumer, transitive audit, exact semantic review and required sequential verification. The unchanged checklist remains the authority. In particular, no arithmetic hypothesis is silently added to an unconditional application, and no modular branch is abandoned.
