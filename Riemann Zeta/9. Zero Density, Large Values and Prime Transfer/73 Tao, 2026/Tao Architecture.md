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
        ONETERM["Lemma 1.6(i) PROVED<br/>lower z<p<3z packet + upper finite exponent grid;<br/>Lemma 1.6(ii) from sharp critical dilation via power-of-two bracketing PROVED;<br/>exact saddle + phase + curvature + complete Gaussian main-term dilation ratio c PROVED;<br/>uniform Granville asymptotic absent"]
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
        VINO["Theorem 2.5 partial<br/>j=1 absorption + phase/character variation + low-frequency complex Abel/PNT-discrepancy reduction + qualitative-PNT uniform dyadic and fixed-bounded-frequency o(P) consequences + finite Fourier assembly with automatic integrability, exact retained-box count, uniform-approximation transfer, finite ℓ¹ truncation, summable cubic ℤ² envelope, vanishing square-box tails, open-quotient torus descent, character compatibility, conditional uniform reconstruction of W, complete smooth-periodic radial C³ Fourier decay + source-oriented product-restricted Vaughan with exact 1/log-P coefficient envelopes and supports + exact outer/double coefficient blocks + canonical (log₂B+1)^102 short family with coverage, exact weighted Type I/II decomposition, and literal real-log relative-width support + prime-power + Abel + Type I + product-restricted Type II + all-support distance-kernel bound with necessary +1 and endpoint-free pure off-diagonal bound through exact double blocks and source-facing block lengths + high-frequency log absorption + normalized parameter bounds + critical deletion + arbitrary-depth finite van der Corput majorant with exact source four-step specialization, positive-ray exact-interval finite-difference FTC bridge with arbitrary lag-product upper and critical-regular lower estimates, IVT sign separation, terminal derivative windows from the next two source derivatives, critical-regular nonlinear Kusmin--Landau terminal bound, exact `rH`/`H^r` admissible-lag control, uniform arbitrary-depth and literal four-round regular-interval closure, exact lag-sensitive Weyl tree, inverse-product/truncation leaf profile, harmonic leaf summation, closed all-depth scalar lag envelope with generalized harmonic factors ≤ H, source four-round sixteenth-root estimate, coarse scale recurrence with exact `(QH)^15/scale` sixteenth power, four explicit diagonal terms with exact powered denominator bounds, source five-term root/rpow majorant without hidden recurrence, a canonical floor-rounded range that automatically satisfies upper-smallness, exact expanded-critical-start deletion plus global long/short regular-component assembly, optimized fixed-power global closure, arbitrary-subinterval low-frequency two-term width `(F/X^5+1/F)^(1/1024)`, and equal-parameter Type II distance-kernel propagation through arbitrary positive blocks and the exact canonical dyadic Vaughan double family, exact outer-sum/Cauchy--Schwarz insertion into the literal source Type II convolution blocks, source beta/gamma envelopes, exact tail-cutoff annihilation of both small-band regimes, full-family conditional summation, exact `(log₂ B+1)^204` uniform loss, and full-convolution square-root reassembly, with uniform scale/effective-error majorants and quadratic geometry discharge, plus affine nearest-integer endpoint<br/>quantitative arbitrary-log-saving PNT, source split `(log Bcap)^d≤F`, large-band bound `10F≤K^4(log Bcap)^100`, exact equation-(18), sharp critical root/source-decay ledger, explicit native p-adic coefficient `C(p^(B₀+1)κ)^ε`, uniform absolute-coefficient positive Ford benchmark at moment `4R²` for `R≥10000` (quantitatively below the source decay), and finite absorption of every native critical coefficient for `40≤R<1000`; uniform rooted control for `R≥1000` and the remaining high-scale Vinogradov-Weyl cancellation are open; the inner singleton branch is closed diagonally"]
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
        ES2["CONDITIONAL SOURCE: Erdos--Selfridge Theorem 2<br/>prime valuation not divisible by exponent"]
        T110["CONDITIONAL FULL: Theorem 1.10<br/>factorial solutions x^(1/2+o(1));<br/>source-Theorem-2 translation PROVED"]
        FBOUNDS --> FEXTRACT
        FEXTRACT --> FCASES
        FCASES --> T19
        T19 --> T110
        FBOUNDS --> T110
        ES2 --> T110
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
        BURGESS["Lemma 5.2 PARTIAL<br/>literal cubefree r=7 target + exact sieve-prefix interface PROVED;<br/>epsilon'=1/2000000 exponent bridge to saving 0.0163 PROVED;<br/>exact Möbius primitive-to-all-character reduction PROVED;<br/>periodicity + trivial-bound reduction to q^(2/7+7epsilon')&lt;H&lt;q PROVED;<br/>exact 2r-moment expansion + quotient correlations PROVED;<br/>degenerate count ≤r^(2r)B^r + standard moment split PROVED;<br/>literal A_j product + nondegenerate A_j≠0 PROVED;<br/>gcd weight + composite Weil interface + literal r=7 production predicate PROVED;<br/>gcd-weight tuple sum ≤2rB(2B tau(q))^(2r-1) PROVED;<br/>r=7 losses absorbed: moment ≤7^14 B^7 q+C_epsilon B^14 q^(1/2+epsilon) PROVED conditional on Weil;<br/>exact coprime CRT correlation/factor/gcd multiplicativity + common-witness assembly PROVED;<br/>primitivity descends to both canonical CRT factors PROVED;<br/>fixed-Fin 7 strong cube-free iteration to p and p^2 local bounds PROVED;<br/>p-divides-A_j branches at p and p^2 PROVED trivially;<br/>p^2 first-order fiber phase + nonstationary cancellation + stationary root count ≤2r + local 4rp bound PROVED;<br/>fixed-r=7 prime quotient and source bridge PROVED;<br/>prime quotient converted exactly to a split non-order-power polynomial with ≤2r roots PROVED;<br/>one-root cancellation + two-root Jacobi-sum bound PROVED;<br/>inactive-root deletion + correction absorption PROVED;<br/>exact degree divisibility + three-active-root Möbius/Jacobi reduction PROVED;<br/>small-characteristic p≤4D^2 cases PROVED trivially;<br/>exact four-active-root Möbius/hypergeometric normalization PROVED;<br/>exact five-active-root Möbius/four-point normalization PROVED;<br/>exact six-active-root Möbius/five-point normalization PROVED;<br/>exact seven-active-root Möbius/six-point normalization PROVED;<br/>exact eight-active-root Möbius/seven-point normalization PROVED;<br/>exact nine-active-root Möbius/eight-point normalization PROVED;<br/>exact ten-active-root Möbius/nine-point normalization PROVED;<br/>exact eleven-active-root Möbius/ten-point normalization PROVED;<br/>exact twelve-active-root Möbius/eleven-point normalization PROVED;<br/>exact thirteen-active-root Möbius/twelve-point normalization PROVED;<br/>exact fourteen-active-root Möbius/thirteen-point normalization PROVED;<br/>generic higher-root residual restricted to exact cleared Burgess polynomials PROVED;<br/>fixed-r=7 source-cardinality residual eliminated using the structural card≤14 cap PROVED;<br/>four-root input restricted to p&gt;64, one ambient character, finite exponent range, and one Legendre parameter PROVED;<br/>five-root input restricted to p&gt;64, one ambient character, finite exponent range, and two Legendre parameters PROVED;<br/>six-root input restricted to p&gt;64, one ambient character, finite exponent range, and three Legendre parameters PROVED;<br/>seven-root input restricted to p&gt;64, one ambient character, finite exponent range, and four Legendre parameters PROVED;<br/>eight-root input restricted to p&gt;64, one ambient character, finite exponent range, and five Legendre parameters PROVED;<br/>nine-root input restricted to p&gt;64, one ambient character, finite exponent range, and six Legendre parameters PROVED;<br/>ten-root input restricted to p&gt;64, one ambient character, finite exponent range, and seven Legendre parameters PROVED;<br/>eleven-root input restricted to p&gt;64, one ambient character, finite exponent range, and eight Legendre parameters PROVED;<br/>twelve-root input restricted to p&gt;64, one ambient character, finite exponent range, and nine Legendre parameters PROVED;<br/>thirteen-root input restricted to p&gt;64, one ambient character, finite exponent range, and ten Legendre parameters PROVED;<br/>fourteen-root input restricted to p&gt;64, one ambient character, finite exponent range, and eleven Legendre parameters PROVED;<br/>sharp Kummer (t-1)sqrt(p) contract + scalar-power exclusion bridge PROVED;<br/>open: reduced one- through eleven-parameter trace endpoints"]
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
        ATYPICAL["Proposition 6.5 PROVED<br/>condition-(ii) actual union weak bound;<br/>condition-(i) cofactor sieve + corrected full k>=2 z^-4 saddle + summed long moderate union <=x/z^3;<br/>large-p0 union <=x^(199/200) and large-H fixed power saving;<br/>small-p0, moving low/high smooth bands, and moving deficient band;<br/>fixed-row eight-branch bound <=x/z^(2+1/(128d^2));<br/>countable diagonal with exact floor/ceiling cutoffs both z^(1+o(1));<br/>selected union <=B1(x)/log(x)^(1-o(1))"]
RANDOM["Proposition 6.6 conditional closure<br/>literal 1001-coordinate finite product probability space PROVED;<br/>exact uniform prime-band laws + mutual independence PROVED;<br/>forward and reflected v-l small-prime 50th moments PROVED conditional on Burgess;<br/>forward and reflected large-prime source mean/variance bounds PROVED conditional on Burgess;<br/>exact Markov/Chebyshev normalization + both typical-event inclusions PROVED conditional on Burgess;<br/>one B simultaneous for every admissible H,m' in both orientations PROVED conditional on Burgess;<br/>exact probability/support-cardinality identities + uniform tuple-count bounds PROVED;<br/>fixed-prime-scale smooth-remainder sums + dyadic geometric cost 2 PROVED;<br/>moving grid + all ordered prime-scale choices PROVED;<br/>enlarged-band global image + fiber ≤1000^1000 PROVED;<br/>PNT band comparison + unweighted assembly factor →0 PROVED conditional on Burgess;<br/>length-weighted all-scale assembly has explicit log saving PROVED conditional on Burgess;<br/>canonical left- and right-endpoint actual-union injections PROVED;<br/>typical/non-typical recombination + factor-30 maximal transfer PROVED;<br/>eventual start-uniform Sylvester--Schur + scale-local large-prime transfer PROVED;<br/>conditional local dyadic-window log saving + exact finite global dyadic cover PROVED;<br/>adjacent-ratio geometric summation + exact conditional T1.7 contract PROVED;<br/>slow central-packet concentration + B1 half-ratio + adjacent ratio + Lemma 1.6(ii) from sharp smooth dilation PROVED;<br/>Sylvester--Schur all-start large-length tail + finite-rectangle reduction + all H&lt;49 PROVED independently;<br/>open for T1.7: critical smooth saddle asymptotic + analytic Burgess"]
        MOMENTS["Propositions 6.7--6.8 conditional closure<br/>finite mean/variance algebra and diagonal reduction PROVED;<br/>single-p and joint-pp' primitive character fibers PROVED;<br/>principal split + exact one/two-prime collision loss PROVED;<br/>prime-modulus nonprincipal Z^-8 error PROVED;<br/>product-modulus conductor reduction + change-level collision removal PROVED;<br/>literal improved probability + distinct-prime covariance error PROVED;<br/>finite exceptional mean/covariance partition + variance insertion PROVED;<br/>bad product pairs covered by exceptional endpoints/partner union PROVED;<br/>dyadic first-moment PNT/main/error/cardinality block PROVED;<br/>exact two-band covariance error/cardinality block PROVED;<br/>exceptional pair cardinality reduced to exact three-family count PROVED;<br/>source aggregate + one/joint/covariance error envelopes PROVED;<br/>direct R^-1.001 and ordered R^-1.001 S^-1 power errors PROVED;<br/>adaptive Burgess endpoint O(R^0.02) + partner O(S^0.02) counts PROVED;<br/>adaptive character-moment and one/joint/covariance error consumers PROVED;<br/>mixed R-for-p, S-for-p'/pp' pair partition + joint/covariance powers PROVED;<br/>adaptive one-/two-band aggregation + pair-cardinality reduction PROVED;<br/>Burgess cardinalities + improved errors inserted into both blocks PROVED;<br/>fixed-threshold exceptional p and uniformly-in-p exceptional p' counts PROVED;<br/>exact residue fiber + uniform finite tuple-count law PROVED;<br/>one-coordinate collision-closed crude bounds PROVED;<br/>source two-/three-coordinate crude fibers with multiplicities 2/6 PROVED;<br/>normalized crude shapes 16L²/p and 96L³/(pp') PROVED;<br/>uniform PNT scale gives 256log²(z)/p and 6144log³(z)/(pp') PROVED;<br/>whole-band crude specialization + automatic conductor/partner geometry PROVED;<br/>p|m' zero branches + complete source blocks PROVED;<br/>exact disjoint dyadic grid + uniform scale constants PROVED;<br/>literal mean ≤2000000H + covariance ≤H + variance ≤2000001H PROVED conditional on Burgess;<br/>analytic Burgess open"]
        T17["CONDITIONAL FULL: Theorem 1.7<br/>nontrivial B saving + x/z^(2+o(1));<br/>open inputs: critical smooth saddle asymptotic,<br/>analytic Burgess"]
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
    class CROSSWALK,ONETERM,VINO,UNCERT,LSIEVE,POWERREL,VBSHORT,VBEXTRACT,T18,FBOUNDS,FCASES,DIRICHLET,BHM,EXCHAR,TYPICAL,ATYPICAL,RANDOM,MOMENTS,BURGESS pending
    class NORMALIZE complete
    class PRIMEII,PELL,FUND,T17,T19,T110,PUBLIC,RELEASE absent
    class LEGEND note

    %% Release 2.57: BurgessAmplification supplies the exact edge from a
    %% character prefix through affine shifted intervals to burgessShiftSum.
    %% Exact multiplier aggregation by residue is complete. The multiplicity
    %% collision bound, Holder, and parameter optimization remain pending.
    %% Release 2.58: the second moment equals an ordered collision cardinality;
    %% unit cancellation gives the source cross-multiplied congruence, and the
    %% exact three-factor Holder estimate is complete. The arithmetic upper
    %% bound on fixed-multiplier collision fibers remains pending.
    %% Release 2.59: determinant no-wrap and reduced-multiplier spacing prove
    %% the local collision-fiber bound. Exact global fiber decomposition gives
    %% the finite max/gcd sum; its elementary divisor estimate remains pending.
    %% Release 2.60: divisor incidence and exact multiple counting sum the
    %% max/gcd majorant. The collision count now has a diagonal term plus
    %% 2*H*A*harmonic(A); Burgess recursion and optimization remain pending.
    %% Release 2.61: the exact pre-Holder averaging recursion now has main term
    %% sum_x v_A(x)|W_B(x)| and arbitrary shorter-interval error 2*sum E(ab).
    %% Specializing and summing E, then r=7 optimization, remain pending.
    %% Release 2.62: monotonicity and endpoint summation specialize E to every
    %% nonnegative power majorant. Division by #A*B exposes M/(#A*B) plus the
    %% normalized boundary 2*C*(A*B)^alpha*Q; root extraction remains pending.
    %% Release 2.63: the powered Holder bound is rooted and its collision and
    %% complete fourteenth-moment factors are replaced by their compiled
    %% majorants. Only coprime-count and A,B scalar optimization remain here.
    %% Release 2.64: exact Mobius inversion gives the short multiplier count
    %% at totient density with a tau(q) discrepancy, and a half-density lower
    %% bound once that explicit error is dominated. Since q/phi(q)<=tau(q),
    %% the natural criterion 2*tau(q)^2<=A suffices. A,B optimization remains.
    %% Release 2.65: divisor epsilon bounds make that criterion eventual for
    %% the actual rounded A. With B=floor(q^(1/14)) and A=H/(K*B), compiled
    %% geometry proves shortening and no-wrap from explicit scalar ranges.
    %% The rooted recurrence is cardinality-free and its collision bracket is
    %% 3*H*A*harmonic(A). Epsilon algebra and boundary absorption remain.
    %% Release 2.66: harmonic and reciprocal-totient losses are explicit
    %% q^delta powers. The complete moment contributes q^(3/28+epsilon/14)
    %% after rooting, and exact root algebra exposes A^(13/14)H^(13/14).
    %% Rounded A,B substitution and strict boundary contraction remain.
    %% Release 2.67: exact rounded quotient/floor algebra contributes
    %% q^(-13/196) and H^(6/7), so the normalized main exponent is now
    %% q^(2/49+epsilon/14+delta/14). Totient loss and boundary contraction
    %% remain the next scalar closure.
    %% Release 2.68: totient insertion and a single epsilon allocation give
    %% q^(2/49+eta). Exact K*A*B<=H makes the power boundary contractive;
    %% K=128 leaves at most half. Recurrence assembly and complete Weil remain.
    %% Release 2.69: recurrence assembly and strong induction are complete.
    %% Every affine child is strictly shorter; below-core children are trivial.
    %% The primitive bound holds on the eventual quadratic no-wrap range.
    %% Polya-Vinogradov and the prime finite-field Weil residual remain.
    %% Release 2.70: finite Fourier inversion, the exact primitive Gauss norm,
    %% the harmonic L1 kernel bound, and the large-length exponent transfer
    %% are complete. Medium and large ranges now give every-prefix Burgess,
    %% conditional only on the prime finite-field complete-Weil residual.
    %% Release 2.71: the prime residual is consolidated into the sharp Kummer
    %% theorem. Tagged multiplicity excludes every nonzero scalar order-power;
    %% the (t-1)*sqrt(p) estimate alone now feeds the full composite chain.
    %% Release 2.73: the large-length tail plus fixed-length thresholds yield
    %% one uniform start cutoff. Admissible starts escape this cutoff with the
    %% dyadic scale, removing unrestricted Sylvester--Schur from Theorem 1.7.
    %% Release 2.75: character orthogonality and the Jacobi-sum theorem prove
    %% the sharp Kummer trace bound for one and two roots. The exact remaining
    %% prime-Weil input is restricted to at least three distinct roots.
    %% Release 2.76: the sharp three-root bound is also proved when character
    %% order divides degree. The exact generic residual is four-or-more roots
    %% or three roots with degree nondivisible by the character order.
    %% Release 2.77: nondivisible three-active-root traces are exactly the
    %% existing three-point hypergeometric endpoint. Under that theorem, the
    %% remaining Kummer residual is purely four-or-more distinct roots.
    %% Release 2.78: under the same three-point theorem, degree-divisible
    %% four-root traces satisfy the sharp 3*sqrt(p) bound. The exact generic
    %% residual is five-or-more roots or nondivisible-degree four roots.
    %% Release 2.79: nondivisible-degree four-active-root traces translate
    %% exactly to a four-point hypergeometric endpoint. With the three- and
    %% four-point endpoints, the remaining Kummer residual is purely five or
    %% more distinct roots, with every inactive-root deletion accounted for.
    %% Release 2.80: degree-divisible five-root traces Möbius-reduce to the
    %% four-point endpoint plus one deleted value and satisfy the sharp
    %% 4*sqrt(p) bound. The exact cleared Burgess residual now begins at six
    %% active roots; the generic residual also retains nondivisible five roots.
    %% Release 2.81: on the exact Burgess path the four-point input is now
    %% restricted to powers of one character, reduced exponents, p > 64, and
    %% the two-parameter Legendre form 0,1,t,u.
    %% Release 2.82: the six-active-root case Möbius-reduces to a reduced
    %% five-point power endpoint in the three-parameter form 0,1,t,u,v. The
    %% exact source residual now begins at seven active roots.
    %% Release 2.83: the complete-Weil consumer, local prime-power CRT
    %% induction, prime quotient, and exact source residual are all separately
    %% specialized to the sole production order r=7.
    %% Release 2.84: the seven-active-root case Möbius-reduces to a reduced
    %% six-point power endpoint in the four-parameter form 0,1,t,u,v,w. The
    %% exact fixed-order source residual now begins at eight active roots.
    %% Release 2.85: the 2r root bound specializes the fixed-order residual to
    %% the exact finite active-root window 8 through 14.
    %% Release 2.86: the eight-active-root case Möbius-reduces to a reduced
    %% seven-point power endpoint in the five-parameter form 0,1,t,u,v,w,z.
    %% The exact fixed-order residual window is now 9 through 14.
    %% Release 2.87: the nine-active-root case Möbius-reduces to a reduced
    %% eight-point power endpoint in the six-parameter form 0,1,t,u,v,w,z,r₀.
    %% The exact fixed-order residual window is now 10 through 14.
    %% Release 2.88: the ten-active-root case Möbius-reduces to a reduced
    %% nine-point power endpoint in the seven-parameter form
    %% 0,1,t,u,v,w,z,r₀,s₀. The exact fixed-order residual is now 11 through 14.
    %% Release 2.89: the eleven-active-root case Möbius-reduces to a reduced
    %% ten-point power endpoint in the eight-parameter form
    %% 0,1,t,u,v,w,z,r₀,s₀,a₀. The exact fixed-order residual is now 12 through 14.
    %% Release 2.90: the twelve-active-root case Möbius-reduces to a reduced
    %% eleven-point power endpoint in the nine-parameter form
    %% 0,1,t,u,v,w,z,r₀,s₀,a₀,b₀. The exact fixed-order residual is now 13 through 14.
    %% Release 2.91: the thirteen-active-root case Möbius-reduces to a reduced
    %% twelve-point power endpoint in the ten-parameter form
    %% 0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀. The exact fixed-order residual is now only 14.
    %% Release 2.92: the fourteen-active-root case Möbius-reduces to a reduced
    %% thirteen-point power endpoint in the eleven-parameter form
    %% 0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀. The fixed-order source residual is closed.
    %% Release 2.93: the stronger Erdos--Selfridge Theorem 2 is transcribed
    %% exactly. Interval conversion, least-prime/endpoint bounds, and the
    %% exponent-two valuation contradiction feed the public T1.10 consumer.
    %% The prime-multiplicity theorem itself remains the source input.
    %% Release 2.94: source equation (3) is compiled. Factorization remainders
    %% modulo l give m=a*x^l with v_p(a)<l; exact uniqueness for H<=p makes
    %% every counterexample coefficient H-smooth.
    %% Release 2.95: source equations (2) and (4), the sharp rational-power
    %% gap, and full coefficient-product Lemma 1 are compiled. Lemma 2 and
    %% the remaining deletion/counting cases are the next source boundary.
    %% Release 2.96: maximal-valuation deletion, exact pi(H-1) padding,
    %% equation (9), and the square-case equation (21) are compiled. The
    %% large-length square inequality and finite residual cases remain.
    %% Release 2.97: exact interval counts for multiples of 4, 9, and 36
    %% prove that every 36-term block contains at most 24 squarefree values.
    %% The product lower bound (22), equation (23), and finite cases remain.
    %% Release 2.98: cumulative squarefree density, the exact first-64 base,
    %% ordered-finset minimality, and maximum deletion prove equation (22)
    %% for the canonical counterexample coefficients. Equation (23) remains.
    %% Release 2.99: the exact 2- and 3-adic cancellation ledger for equation
    %% (21), and its strict combination with equation (22), are compiled.
    %% The four numerical valuation bounds and displayed equation (23) remain.
    %% Release 3.00: binary/ternary digit-sum bounds, exact odd-valuation
    %% interval recurrences, all four source valuation estimates, and the
    %% factorial-cancelled logarithmic real-power form are compiled. The
    %% numerical simplification to 14/3 and the primorial contradiction remain.
    %% Release 3.01: exact rpow/logb evaluation and a slack root-factor bound
    %% prove displayed equation (23) with constant 14/3. The explicit
    %% primorial contradiction and finite residual square cases remain.
    %% Release 3.02: the frozen PNT bounds the prime product by 3^H
    %% eventually; exact rational root bounds make the equation-(23) base
    %% strictly larger than 3, so polynomial-versus-exponential growth rules
    %% out all sufficiently large square-case failures. The explicit cutoff
    %% and finite residual square cases remain.
    %% Release 3.03: a finite coefficient-candidate embedding and exact
    %% divisor-cardinality computations close H=3 and H=5. Exhaustion of
    %% {1,2,3,6}, equation (3), and the four-consecutive difference-of-squares
    %% identity close H=4. The finite residual now begins at H=6.
    %% Release 3.04: an exact modulo-five split closes H=6. Five nonexceptional
    %% positions collide among four {2,3}-supported coefficients; in the
    %% exceptional class the middle four exhaust them and force a forbidden
    %% square four-term subproduct. The finite residual now begins at H=7.
    %% Release 3.05: exact enumeration modulo five shows that at least five of
    %% seven positions have {2,3}-supported coefficients, contradicting the
    %% four available values. The finite residual now begins at H=8.
    %% Release 3.06: reduction modulo 35 gives the H=8 five-coefficient count
    %% except in the exact source class 7|(N+1), 5|(N+2); there the middle four
    %% coefficients force the same forbidden square subproduct. Residual H=9.
    %% Release 3.07: exact periodic counts modulo 35 and 385, persisted across
    %% prime-stable ranges, close H=9 through H=13 by five-to-four coefficient
    %% pigeonhole. The finite residual now begins at H=14.
    %% Release 3.08: a reusable union bound for interval multiples of
    %% 5,7,11,13 closes H=14 through H=17 without large residue enumeration.
    %% The finite residual now begins at H=18.
    %% Release 3.09: sharp finite-prime union bounds and a generic coprime
    %% coefficient transfer close H=18 through H=20. Residual H=21.
    %% Release 3.10: nine coefficients supported on 2,3,5 contradict the eight
    %% divisors of 30 for every H=21 through H=70. Section 3.2 is complete.
    %% Release 3.11: actual prime-product certificates close H=71 through 296;
    %% a 31335/10000 base bound gives equation-(23) growth from H=297. The sole
    %% remaining square input is the elementary all-H prime product <= 3^H.
    %% Release 3.12: Hanson's Sylvester factorial coefficient and a fixed
    %% 2,3,7,43 multinomial prove that prime-product bound for every H. The
    %% square branch now depends only on unrestricted Sylvester--Schur.
    %% Release 3.13: an independent ascending-factorial argument replaces the
    %% H^H start cutoff by H!*2^pi(H)+1 (and the classical H!*2^(H-1)+1
    %% corollary). Only the resulting finite H>=49 rectangle remains.
    %% Release 3.14: kernel-checked 3H baselines and bounded witnesses close
    %% every length 49 through 100. The finite rectangle now starts at H=101.
    %% Release 3.15: split choose(n,H) at sqrt(n); high valuations are at most
    %% one and central support contracts to n/3. Hanson gives the explicit
    %% envelope n^sqrt(n)*3^(n/3+1), leaving its uniform numerical gap.
    %% Release 3.16: exact integral inductions discharge that gap for every
    %% H>=34134 and H<N<=2H. Noncentral starts and 101<=H<34134 remain.
    %% Release 3.17: explicit Chebyshev growth at 1024H plus the near envelope
    %% closes every start for H>=4^101. The residual is the concrete rectangle
    %% 101<=H<4^101 below the exact prime-count factorial start cutoff.
    %% Release 3.18: tighter certified margins move the common transition to
    %% 64H and the all-start cutoff to H>=250000. The residual is now exactly
    %% 101<=H<250000 below the same prime-count factorial start cutoff.
    %% Release 3.19: retaining pi(sqrt n) in the low-prime envelope and
    %% proving pi(m)<=m/4 from m=120 moves the all-start cutoff to H>=10000.
    %% The exact residual is 101<=H<10000 below the factorial start cutoff.
    %% Release 3.20: the finite bound 6*pi(m)<=m+84 for 100<=m<800 closes
    %% the bridge 6000<=H<10000. The exact residual is now 101<=H<6000.
    %% Release 3.21: adaptive transitions 16H and 20H plus the finite bound
    %% 4*pi(m)<=m+12 close every start from H>=2200. Residual: 101<=H<2200.
    %% Release 3.22: transitions 5H, 6H, and 5H plus exact finite prime-count
    %% certificates close every start from H>=512. Residual: 101<=H<512.
    %% Release 3.23: the exact central baseline at 2H, with five rows bridged
    %% at upper indices 281 and 403, closes H>=121. Residual: 101<=H<121.
    %% Release 3.24: a common baseline at 243 plus one finite certificate
    %% closes the final twenty rows. Sylvester--Schur and square ES are complete.
    %% Release 3.25: the conditional mixed Weyl--Vinogradov squared-inner-sum
    %% estimate is connected to the literal source Type II Vaughan double
    %% block, including source coefficients and full convolution reassembly.
    %% Release 3.26: both source tail cutoffs annihilate small dyadic bands;
    %% the explicit large--large majorants are summed over the full family,
    %% with exact uniform block-family loss (log_2 B+1)^204.
    %% Release 3.27: U=V=floor(B^(1/3)) now eventually dominates the exact
    %% subdivision budget and 2*B^(1/4); empty product blocks vanish, and one
    %% global phase inequality supplies every surviving block-scale premise.
    %% Release 3.28: the order family is fixed to {5,6}; canonical short-block
    %% lengths, cardinalities, and component logarithms are bounded uniformly,
    %% giving the first geometric compression of the exact Type II majorant.
    %% Release 3.29: separate dyadic widths preserve product geometry; exact
    %% expansion gives log exponents 298,197,297, and the inner cutoff gives
    %% the diagonal power saving D^2 E <= B^2/B^(1/4).
    %% Release 3.30: the global phase lower bound and outer quarter-power
    %% endpoint remove all block dependence; nested powers flatten to
    %% B^(7/4), log(B)^(-d/1024), and B^(-1/4096), and the exact double family
    %% is evaluated and bounded by (3 log B)^204 times one square root.
    %% Release 3.31: fixed power savings absorb arbitrary logarithmic targets;
    %% d=2048S+216064 and T=2S+111 close the exact exponent ledger and give
    %% the conditional full Type II bound C*B/(log P)^S for P<=B<=2P.
    %% Release 3.32: each literal Type I Vaughan block is now an exact
    %% product-restricted outer sum; its inner support is [ceil(a/m),ceil(b/m)),
    %% its phase is rescaled to (N/m,M/m^j), and both full outer families are
    %% reassembled with the unit/log(2B) coefficient envelopes and Abel entry.
    %% Release 3.33: zero outer coefficients are removed before Type I
    %% triangle bounds; active supports have cardinality at most U and UV,
    %% giving exact uniform-callback family losses without an ambient B cost.
    %% Release 3.34: Type I phase scale is invariant at P/m and antitone under
    %% ceiling rounding; fibers of [P,2P) lie in the rounded dyadic interval,
    %% transferring the source fourth-power condition to the Weyl input scale.
    %% Release 3.35: the quadratic fiber is reconstructed from ten short
    %% blocks; five-length fit discharges the four-step endpoint buffer, and
    %% factor-four scale comparability transfers one effective-error budget.
    %% Release 3.36: all local widths are bounded by one source-scale width;
    %% exact ten-block summation covers every subinterval of the dyadic fiber,
    %% including every initial prefix needed for Type I Abel summation.
    %% Release 3.37: substitution at (N/m,M/m^2,ceil(P/m)) produces explicit
    %% unweighted and logarithmic fiber bounds and instantiates both complete
    %% active Vaughan Type I families under named source-budget premises.
    %% Release 3.38: every rescaled fiber now splits exactly at F(D)=D^4;
    %% low fibers use the ten-block Weyl bound, high fibers use Vinogradov,
    %% and both branches propagate through Abel and the active families.
    %% Release 3.39: the low Weyl budget is automatic above one absolute
    %% threshold, while canonical active support forces D>=B^(1/4);
    %% global source frequency bounds therefore imply hybrid admissibility
    %% simultaneously on every active Type I fiber.
    %% Release 3.40: Type I aggregation retains the fiber factor P/m;
    %% reciprocal active supports cost harmonic(U) or harmonic(UV), replacing
    %% the polynomial cardinality losses by logarithmic losses.
    %% Release 3.41: a branch-sensitive envelope absorbs high fibers by the
    %% source Vinogradov bound and low fibers by the explicit Weyl width;
    %% the harmonic family insertion costs exactly 104 logarithmic powers and
    %% closes both complete Type I families at arbitrary requested saving.
    %% Release 3.42: the canonical cutoff term vanishes above B^(1/3), and
    %% the two completed Type I terms plus completed Type II term are inserted
    %% into the exact Vaughan identity, yielding a quadratic Mangoldt phase
    %% bound with arbitrary logarithmic saving.
    %% Release 3.43: F(N,N,2,P)<=2|N| and the converse lower comparison derive
    %% every Type I scale premise from the single Type II-shaped source range;
    %% the exported Mangoldt endpoint now has one frequency interface.
    %% Release 3.44: exact endpoint transport and a quarter-power bound remove
    %% prime powers uniformly on every prefix; reverse Abel removes log p and
    %% exports the unweighted quadratic prime sum on that same source range.
    %% Release 3.45: the (1,1) Fourier sum is identified with the diagonal
    %% prime phase sum; integration by parts bounds its logarithmic integral
    %% by 6*P^2/(|N|*log P), yielding the exact diagonal discrepancy bridge.
    %% General modes are exactly exposed as unequal reciprocal coefficients,
    %% with derivative and same-sign nonstationarity proved; opposite-sign
    %% stationary cases, unequal estimates, and the low/zero modes remain open.
    %% Release 3.46: the Type II high-pair Vinogradov envelope, log saving,
    %% kernel callback, and canonical Vaughan-block callback now retain
    %% independent N and M. The low Weyl distance kernel remains diagonal.
    %% Release 3.47: the transformed quadratic term plus the positive dyadic
    %% lower band closes the unequal low-scale distance-kernel comparison.
    %% Near/far aggregation and the Weyl--Vinogradov split now reach one
    %% actual weighted Vaughan Type II double block with independent N and M;
    %% complete double-family summation and later source transfers remain.
    %% Release 3.48: finite double-family summation, canonical majorant
    %% compression, and arbitrary logarithmic saving now retain independent
    %% N and M. The exact Vaughan identity, prime-power removal, and reverse
    %% Abel transfer yield the unequal Mangoldt and unweighted-prime source
    %% estimates whenever M is nonzero. The zero-quadratic Fourier branch,
    %% unequal integrals, low modes, and final Fourier assembly remain open.
    %% Release 3.49: the exact unequal integration-by-parts amplitude and its
    %% monotonicity close both same-sign Fourier chambers; conjugation moves
    %% the positive estimate to negative coefficients. Combined with the
    %% unequal prime theorem this yields the literal mode discrepancy.
    %% Opposite-sign stationary modes, coordinate axes, low frequencies, and
    %% final Fourier assembly remain open.
    %% Release 3.50: the unique opposite-sign critical point is explicit, and
    %% the derivative factors through distance from it. An interior critical
    %% point plus the source scale gives a quantitative far derivative lower
    %% bound. The integral splits exactly into two far pieces and a central
    %% radius-delta piece bounded by 2*delta/log(P). Far-piece cancellation,
    %% axis modes, and Fourier assembly remain open.
    %% Release 3.51: exact nonvanishing-factor integration by parts closes
    %% both stationary far pieces, including the post-turning right tail.
    %% Source-scale insertion and delta=P/sqrt(L) give the interior bound
    %% 50*P/(sqrt(L)*log(P)). Endpoint clipping, sign conjugation, axis modes,
    %% low modes, and final Fourier assembly remain open.
    %% Release 3.52: exact endpoint clipping preserves the optimized stationary
    %% bound, coefficient negation closes the reflected chamber, and the
    %% unequal prime theorem yields the literal stationary Fourier-mode
    %% discrepancy for two nonzero coefficients. Coordinate axes remain.
    %% Release 3.53: the zero-linear/nonzero-quadratic axis has an exact
    %% positive-variation integral bound, source-scale conversion, and literal
    %% prime discrepancy. The pure linear Type II axis remains open.
    %% Release 3.54: zero-quadratic derivative critical sets are empty. The
    %% high-scale Vinogradov and low-scale four-step Weyl branches now give
    %% pointwise pure-linear Type II correlations. Double-block aggregation
    %% and Vaughan/Mangoldt/prime propagation remain open.
    %% Release 3.55: short and canonical double-block aggregation and the
    %% complete arbitrary-log-saving pure-linear Type II source family are
    %% compiled. Pure-linear Type I, Mangoldt, and prime propagation remain.
    %% Release 3.56: both pure-linear Type I Vaughan families are complete.
    %% Exact Vaughan assembly, prime-power removal, reverse Abel summation,
    %% and the existing integral estimate close the literal zero-quadratic
    %% Fourier discrepancy. Low modes and final Fourier assembly remain.
