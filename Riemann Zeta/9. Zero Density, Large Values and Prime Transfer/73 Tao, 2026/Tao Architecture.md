flowchart TD
    MAP["RH Map node 73<br/>Tao, 2026"] --> PAPER["Tao: Products of consecutive integers<br/>with unusual anatomy"]
    PAPER --> SOURCE["arXiv 2603.27990v2<br/>PDF and TeX pinned + SHA-256 verified"]
    SOURCE --> PLAN["Whole-proof contract researched<br/>Theorems 1.7--1.10 fixed as release scope"]
    PLAN --> CROSSWALK["Tao Crosswalk<br/>principal objects and endpoints mapped;<br/>Section 2--6 ledger still expanding"]

    subgraph FOUNDATION["Immutable foundation boundary"]
        direction TB
        MATHLIB["Mathlib c5ea0035...<br/>factorization, squarefree, smooth numbers,<br/>Dirichlet-character infrastructure inspected"]
        PNT["PNT+ 4ecb9501...<br/>83 reachable modules frozen"]
        GM["Node 71 Guth--Maynard<br/>frozen commit 2ace9e7c..."]
        GT["Node 74 Gafni--Tao<br/>2/15 almost-all short-interval PNT available"]
        E137["scottdhughes/erdos137<br/>commit 3027d9a...; partial elementary reuse candidate"]
        FREEZE["Exact GafniTao.Theorem11 closure<br/>1,226 Lean sources frozen + SHA-256 verified"]
        MATHLIB --> FREEZE
        PNT --> FREEZE
        GM --> GT
        GT --> FREEZE
        E137 --> FREEZE
    end

    CROSSWALK --> CONTRACTS["Exact Lean conclusion contracts<br/>Theorems 1.7--1.10 compile"]
    FREEZE --> CONTRACTS

    subgraph OBJECTS["Source objects and asymptotic language"]
        direction TB
        ASYM["Precise O, o(1), x^o(1), and ~ APIs<br/>initial quantified definitions compile"]
        ANATOMY["PROVED anatomy interfaces<br/>largest prime, squarefree component,<br/>unique powerful a²b³ decomposition"]
        INTERVALS["PROVED interval interfaces<br/>H≥1 enforced + factorial product identity"]
        SETS["PROVED literal B, VB, F3 interfaces<br/>one-term subsets + exact count splits"]
        FACTEQ["PROVED factorial bridge<br/>ordered triples, root uniqueness,<br/>exact F3 endpoint image + count inequality"]
        F31["PROVED F3 one-term bridge<br/>square-multiple characterization<br/>and floor(sqrt x)-1 lower family"]
        F3LOWER["PROVED square-root lower asymptotics<br/>reverse-big-O for F3 and triples"]
        FIBERRED["PROVED factorial-fiber + Lemma 4.1<br/>F3: H&lt;N, prime-free, a≪H log N<br/>residual ES core 3≤H&lt;N<br/>ES + subpoly gap + T1.9 ⇒ T1.10"]
        ASYM --> SETS
        ANATOMY --> INTERVALS
        INTERVALS --> SETS
        ANATOMY --> FACTEQ
        FACTEQ --> F31
        F31 --> F3LOWER
        FACTEQ --> FIBERRED
    end

    CONTRACTS --> ASYM
    CONTRACTS --> ANATOMY

    subgraph SECTION2["Section 2 common inputs"]
        direction TB
        SMOOTH["Proposition 2.1 quantified forms PROVED<br/>Euler product + Rankin + Abel/Chebyshev/Bernoulli upper route PROVED;<br/>critical z^(-1/alpha+epsilon) and polylog x^(-1/A+epsilon) upper bounds PROVED;<br/>polylog x^(1-1/A-epsilon) lower bound PROVED;<br/>exact largest-prime + Chebyshev-Hildebrand + source CEP packet infrastructure PROVED;<br/>coarse fixed-dyadic CEP packet PROVED;<br/>reciprocal mass 1/(16 log 2 log u), multiplicity floor(u-2u/log u), cofactor depth <=10u/log u;<br/>secondary loss <=60u log log u;<br/>critical z^(-1/alpha-epsilon) lower bound PROVED;<br/>thin-band CEP retained as optional source-faithful route;<br/>downstream multiplicative instantiation belongs to Lemma 1.6"]
        ONETERMID["PROVED: exact B1 identity<br/>unique p²m representation + finite Psi sum"]
        ONETERM["Lemma 1.6(i) PROVED<br/>lower z<p<3z packet + upper finite exponent grid;<br/>Lemma 1.6(ii) exact floor(cX) target + regime preservation + monotone halves PROVED;<br/>exact saddle + phase + curvature + complete Gaussian main-term dilation ratio c PROVED;<br/>uniform Granville asymptotic absent"]
        VBONETERM["PROVED: exact VB1 identity<br/>unique a²b³ + finite squarefree-cube sum"]
        VBLOWER["PROVED VB square-family lower bounds<br/>reverse-big-O square-root scale"]
        VBONESCALE["PROVED complete VB1 square-root scale<br/>convergent b^-3/2 majorant + lower family"]
        VBONEZETA["PROVED exact VB1 asymptotic<br/>dominated limit + zeta(3/2)/zeta(3) identity"]
        PRIMEI["PROVED: Proposition 2.3(i)<br/>exact Bertrand endpoints"]
        PRIMEII["Proposition 2.3(ii)<br/>exact interface compiled and consumed;<br/>BHP proof absent"]
        PRIMEIII["PROVED: Proposition 2.3(iii)<br/>global prime-free measure power saving"]
        GTPOWER["Compiled quantitative bridge<br/>uniform dyadic discrepancy power xi < 1"]
        DYADICFREE["Compiled dyadic prime-free bridge<br/>prime-power tail retained and absorbed"]
        PREFIX["Compiled constant-length endpoint measure<br/>finite dyadic assembly + full theta range"]
        VINO["Theorem 2.5 partial<br/>j=1 absorption + phase/character variation + low-frequency complex Abel/PNT-discrepancy reduction + qualitative-PNT uniform dyadic and fixed-bounded-frequency o(P) consequences + finite Fourier assembly with automatic integrability, exact retained-box count, uniform-approximation transfer, finite ℓ¹ truncation, summable cubic ℤ² envelope, vanishing square-box tails, open-quotient torus descent, character compatibility, conditional uniform reconstruction of W, complete smooth-periodic radial C³ Fourier decay + source-oriented product-restricted Vaughan with exact 1/log-P coefficient envelopes and supports + exact outer/double coefficient blocks + canonical (log₂B+1)^102 short family with coverage, exact weighted Type I/II decomposition, and literal real-log relative-width support + prime-power + Abel + Type I + product-restricted Type II + all-support distance-kernel bound with necessary +1 and endpoint-free pure off-diagonal bound through exact double blocks and source-facing block lengths + high-frequency log absorption + normalized parameter bounds + critical deletion + arbitrary-depth finite van der Corput majorant with exact source four-step specialization, positive-ray exact-interval finite-difference FTC bridge with arbitrary lag-product upper and critical-regular lower estimates, IVT sign separation, terminal derivative windows from the next two source derivatives, critical-regular nonlinear Kusmin--Landau terminal bound, exact `rH`/`H^r` admissible-lag control, uniform arbitrary-depth and literal four-round regular-interval closure, exact lag-sensitive Weyl tree, inverse-product/truncation leaf profile, harmonic leaf summation, closed all-depth scalar lag envelope with generalized harmonic factors ≤ H, source four-round sixteenth-root estimate, coarse scale recurrence with exact `(QH)^15/scale` sixteenth power, four explicit diagonal terms with exact powered denominator bounds, source five-term root/rpow majorant without hidden recurrence, a canonical floor-rounded range that automatically satisfies upper-smallness, exact expanded-critical-start deletion plus global long/short regular-component assembly, optimized fixed-power global closure, arbitrary-subinterval low-frequency two-term width `(F/X^5+1/F)^(1/1024)`, and equal-parameter Type II distance-kernel propagation through arbitrary positive blocks and the exact canonical dyadic Vaughan double family, with uniform scale/effective-error majorants and quadratic geometry discharge, plus affine nearest-integer endpoint<br/>quantitative arbitrary-log-saving PNT, source split `(log Bcap)^d≤F`, large-band bound `10F≤K^4(log Bcap)^100`, exact equation-(18), sharp critical root/source-decay ledger, explicit native p-adic coefficient `C(p^(B₀+1)κ)^ε`, uniform absolute-coefficient positive Ford benchmark at moment `4R²` for `R≥10000` (quantitatively below the source decay), and finite absorption of every native critical coefficient for `40≤R<1000`; uniform rooted control for `R≥1000` and the remaining high-scale Vinogradov-Weyl cancellation are open; the inner singleton branch is closed diagonally"]
        SCALEMONO["PROVED quadratic short-block source bridge<br/>near/far split + pairwise F'=K^4 dispatch + intrinsic low error (1/K)^(1/1024) + exact high-pair Vinogradov consumer + diagonal singleton closure"]
        SCALEMONO --> VINO
        UNCERT["PROVED finite Lemma 2.6<br/>native DFT Parseval + arbitrary tensor uncertainty<br/>additive CRT character and energy reindexing"]
        LSIEVE["Corollaries 2.8--2.9 PROVED FINITELY<br/>loss-free Fejér + separated 8L + CRT cross-denominator separation + global finite Corollary 2.8;<br/>elementary-symmetric denominator + literal factorial Corollary 2.9 fixed-fiber bound"]
        PELL["PROVED Lemma 2.10<br/>signed square relations x^o(1)<br/>uniform polynomial parameters"]
        POWERREL["PROVED Corollary 2.11<br/>signed powerful relations x^(2/5+o(1))<br/>uniform linear parameters"]
        SMOOTH --> ONETERM
        ONETERMID --> ONETERM
        GTPOWER --> DYADICFREE
        DYADICFREE --> PREFIX
        PREFIX --> PRIMEIII
        UNCERT --> LSIEVE
        PELL --> POWERREL
    end

    ASYM --> SMOOTH
    ANATOMY --> SMOOTH
    SETS --> ONETERMID
    GT --> GTPOWER
    ANATOMY --> PELL
    ANATOMY --> VBONETERM
    VBONETERM --> VBLOWER
    VBLOWER --> VBONESCALE
    VBONESCALE --> VBONEZETA

    subgraph SECTION3["Section 3: very bad intervals"]
        direction TB
        VBSHORT["CONDITIONAL FULL Lemma 3.1 contract<br/>(N,H)=(0,1) is the unique H&lt;N exception + obstruction/cutoff/T2.5 upper + both substitutions + periodic slice + unit-cell insertion + unconditional eventual PNT/binomial scale and measure lower bound + fixed-constant contradiction;<br/>open: analytic Theorem 2.5 only"]
        VBEXTRACT["PROVED Lemma 3.2<br/>polynomial coefficients + powerful relation"]
        VBCOVER["PROVED finite Lemma 3.2 encoding<br/>injective interval codes + subpolynomial budgets"]
        T18["CONDITIONAL FULL Theorem 1.8<br/>nontrivial x^(2/5+o(1)) count + zeta-ratio asymptotic<br/>open: analytic Theorem 2.5 only"]
        VBSHORT --> VBEXTRACT
        VBSHORT --> VBCOVER
        VBEXTRACT --> T18
        VBCOVER --> T18
    end

    VINO --> VBSHORT
    POWERREL --> T18
    VBONETERM --> T18
    VBLOWER --> T18
    VBONEZETA --> T18
    SETS --> T18

    subgraph SECTION4["Section 4: type F3 and factorial equation"]
        direction TB
        FBOUNDS["PROVED Lemma 4.1 + conditional full Lemma 4.2<br/>both low/high cutoffs, geometric lower bounds, and contradictions<br/>explicit x^o(1) Theorem 1.10 gap budget; analytic BHP remains"]
        FEXTRACT["PROVED Lemma 4.3<br/>canonical square decomposition + exact product envelope<br/>two-half selection + bounded smooth square relation"]
        FCASES["PROVED conditional source case split<br/>easy cases + hard residue/fiber/PNT weights + finite Corollaries 2.8--2.9;<br/>maximal-k closure + F3 one-term upper bound; consumes Lemma 4.2"]
        T19["PUBLIC: Theorem 1.9<br/>nontrivial F3 bound + x^(1/2+o(1))"]
        T110["PUBLIC: Theorem 1.10<br/>factorial solutions x^(1/2+o(1))"]
        FBOUNDS --> FEXTRACT
        FEXTRACT --> FCASES
        FCASES --> T19
        T19 --> T110
        FBOUNDS --> T110
    end

    PRIMEII --> FBOUNDS
    PRIMEIII --> FBOUNDS
    VINO --> FBOUNDS
    PELL --> FCASES
    LSIEVE --> FCASES
    SETS --> T19
    FACTEQ --> T110

    subgraph SECTION5["Section 5: character and sieve machinery"]
        direction TB
        DIRICHLET["Normalized prime character sums PROVED<br/>exact Z^(-1/125) threshold + Z^-8 unexceptional moment;<br/>principal split + exact primitive-conductor regrouping PROVED;<br/>exceptional 1000th moment reduced to Lemma 5.1 square"]
        BURGESS["Lemma 5.2 PARTIAL<br/>source-shaped cubefree target + exact sieve-prefix interface PROVED;<br/>saving 0.0163, cutoff, q<=H^3.1 encoded;<br/>analytic Burgess proof open"]
        BHM["Lemma 5.3 PROVED<br/>finite weighted Bombieri--Halasz--Montgomery;<br/>Hermitian row reduction + prime-indicator specialization"]
        FUND["Lemma 5.4 PARTIAL<br/>generic finite algebra + O(R) floor error PROVED;<br/>real Selberg alternative with nonnegativity + 2/log R main mass PROVED;<br/>source {-1,0,1} Rosser construction open"]
        EXCHAR["Lemma 5.1 CONDITIONAL<br/>Selberg diagonal + divisor expansion + normalized BHM assembly PROVED;<br/>heterogeneous q1*q2 family, squarefree lcm, Z^3.09 bound, pair-character identity PROVED;<br/>R=floor(Z^0.0001), cutoff/range/band side conditions PROVED;<br/>exact band cardinality + strict off-diagonal absorption PROVED;<br/>self-improving J bound + bounded moment + lambda tail PROVED conditional on Burgess;<br/>maximal admissible conductor universe + all-selector Section 6 insertion PROVED;<br/>analytic Burgess open"]
        DIRICHLET --> EXCHAR
        BURGESS --> EXCHAR
        BHM --> EXCHAR
        FUND --> EXCHAR
    end

    MATHLIB --> DIRICHLET
    PNT --> FUND

    subgraph SECTION6["Section 6: bad intervals and anti-sieve"]
        direction TB
        NORMALIZE["Lemmas 6.1--6.2 arithmetic/normalization core PROVED<br/>H≤N + prime-free + exact dyadic bounds + p0²m witness;<br/>contained power-of-two endpoint child with H/4<H'≤H;<br/>finite weak-(1,1) maximal transfer PROVED<br/>#admissible≤30#normalized"]
        TYPICAL["Definitions 6.3--6.4 PROVED<br/>exact cutoff-parametrized typicality;<br/>ordered 1000-prime anatomy + smooth remainder;<br/>>=1000 multiplicity-counted large factors construct anatomy PROVED"]
        ATYPICAL["Proposition 6.5 PROVED<br/>condition-(ii) actual union weak bound;<br/>condition-(i) cofactor sieve + corrected full k>=2 z^-4 saddle + summed long moderate union <=x/z^3;<br/>large-p0 union <=x^(199/200) and large-H fixed power saving;<br/>small-p0, moving low/high smooth bands, and moving deficient band;<br/>fixed-row eight-branch bound <=x/z^(2+1/(128d^2));<br/>countable diagonal with exact floor/ceiling cutoffs both z^(1+o(1));<br/>selected actual union <=x/z^2"]
        RANDOM["Proposition 6.6 partial<br/>literal 1001-coordinate finite product probability space PROVED;<br/>exact uniform prime-band laws + mutual independence PROVED;<br/>exceptional p|l event empty with probability zero PROVED;<br/>small-prime cutoff + ordered 50th-moment expansion + primitive lcm-residue CRT PROVED;<br/>all-character expansion + exact 2^50/lcm insertion PROVED;<br/>coordinate reordering + factor-1000 pigeonhole PROVED;<br/>primitive-conductor divisor reduction inserted into full moment PROVED;<br/>complete support/equality-pattern Mertens sum + H^50 shift reduction PROVED;<br/>rounded selector range + exceptional and totient absorption into principal majorant PROVED conditional on Burgess;<br/>large-prime exact mean/variance/covariance expansion + same-prime cancellation PROVED;<br/>analytic Burgess, distinct-prime covariance bounds, and final normalization open"]
        MOMENTS["Propositions 6.7--6.8 partial<br/>finite mean/variance algebra and diagonal reduction PROVED;<br/>single-p and joint-pp' primitive character fibers PROVED;<br/>principal split + exact one/two-prime collision loss PROVED;<br/>prime-modulus nonprincipal Z^-8 error PROVED;<br/>product-modulus conductor reduction + change-level collision removal PROVED;<br/>literal improved probability + distinct-prime covariance error PROVED;<br/>finite exceptional mean/covariance partition + variance insertion PROVED;<br/>bad product pairs covered by exceptional endpoints/partner union PROVED;<br/>dyadic first-moment PNT/main/error/cardinality block PROVED;<br/>exact two-band covariance error/cardinality block PROVED;<br/>exceptional pair cardinality reduced to exact three-family count PROVED;<br/>source aggregate + one/joint/covariance error envelopes PROVED;<br/>direct R^-1.001 and ordered R^-1.001 S^-1 power errors PROVED;<br/>adaptive Burgess endpoint O(R^0.02) + partner O(S^0.02) counts PROVED;<br/>adaptive character-moment and one/joint/covariance error consumers PROVED;<br/>mixed R-for-p, S-for-p'/pp' pair partition + joint/covariance powers PROVED;<br/>adaptive one-/two-band aggregation + pair-cardinality reduction PROVED;<br/>Burgess cardinalities + improved errors inserted into both blocks PROVED;<br/>fixed-threshold exceptional p and uniformly-in-p exceptional p' counts PROVED;<br/>exact residue fiber + uniform finite tuple-count law PROVED;<br/>one-coordinate collision-closed crude bounds PROVED;<br/>source two-/three-coordinate crude fibers with multiplicities 2/6 PROVED;<br/>normalized crude shapes 16L²/p and 96L³/(pp') PROVED;<br/>uniform PNT scale gives 256log²(z)/p and 6144log³(z)/(pp') PROVED;<br/>whole-band crude specialization + automatic conductor/partner geometry PROVED;<br/>p|m' zero branches + complete source blocks PROVED;<br/>final dyadic sums open"]
        T17["PUBLIC: Theorem 1.7<br/>nontrivial B saving + x/z^(2+o(1))"]
        NORMALIZE --> TYPICAL
        TYPICAL --> ATYPICAL
        TYPICAL --> RANDOM
        RANDOM --> MOMENTS
        ATYPICAL --> T17
        MOMENTS --> T17
    end

    ONETERM --> NORMALIZE
    PRIMEIII --> ATYPICAL
    SMOOTH --> ATYPICAL
    LSIEVE --> ATYPICAL
    EXCHAR --> MOMENTS
    SETS --> T17
    ONETERM --> T17

    T17 --> PUBLIC["Tao2026/PublicTheorems.lean<br/>all four exact endpoints"]
    T18 --> PUBLIC
    T19 --> PUBLIC
    T110 --> PUBLIC
    PUBLIC --> AUDIT["Tao2026/Audit.lean<br/>transitive #print axioms coverage"]
    AUDIT --> RUNNER["run_tao_build.bat<br/>hash/file-set/pin/shortcut/audit/build PASS"]
    RUNNER --> RELEASE["Tao 2026 formal proof release<br/>not achieved"]

    DOCS["Goal Prompt complete<br/>Checklist / Crosswalk / Manifest continuously updated"] --> CROSSWALK
    SHELL["Extension/Tao2026<br/>active pinned Mathlib package builds"] --> CONTRACTS
    MILESTONE["Proposition 2.3(i),(iii), Proposition 2.1 quantified forms,<br/>Lemma 1.6(i), exact one-term sums,<br/>VB1 zeta asymptotic + factorial lower-asymptotic verifier PASS"] --> SHELL
    HULL["PROVED expanded critical hull assembly<br/>same additive deletion bound;<br/>at most two cuts per order"] --> VINO

    LEGEND["Status: green = verified groundwork<br/>blue = inspected candidate/ready shell<br/>yellow = specified but unproved<br/>red = major unformalized input or endpoint"]

    classDef complete fill:#d9f7df,stroke:#238636,color:#111
    classDef ready fill:#dbeafe,stroke:#2563eb,color:#111
    classDef pending fill:#fff4cc,stroke:#b7791f,color:#111
    classDef absent fill:#f8d7da,stroke:#b42318,color:#111
    classDef note fill:#f3f4f6,stroke:#6b7280,color:#111

    class MAP,PAPER,SOURCE,PLAN,DOCS,MILESTONE,FREEZE,GTPOWER,DYADICFREE,PREFIX,PRIMEI,PRIMEIII,SMOOTH,ONETERMID,VBONETERM,VBLOWER,VBONESCALE,VBONEZETA,ANATOMY,INTERVALS,FACTEQ,F31,F3LOWER,FIBERRED,HULL,SCALEMONO,VBCOVER,FEXTRACT,AUDIT,RUNNER complete
    class MATHLIB,PNT,GM,GT,E137,SHELL,ASYM,SETS,CONTRACTS ready
    class CROSSWALK,ONETERM,VINO,UNCERT,LSIEVE,POWERREL,VBSHORT,VBEXTRACT,T18,FBOUNDS,FCASES,DIRICHLET,BHM,EXCHAR,TYPICAL,ATYPICAL,RANDOM,MOMENTS pending
    class NORMALIZE complete
    class PRIMEII,PELL,BURGESS,FUND,T17,T19,T110,PUBLIC,RELEASE absent
    class LEGEND note
