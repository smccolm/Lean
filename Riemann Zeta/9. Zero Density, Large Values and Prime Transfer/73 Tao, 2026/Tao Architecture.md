flowchart TD
    MAP["RH Map node 73<br/>Tao, 2026"] --> PAPER["Tao: Products of consecutive integers<br/>with unusual anatomy"]
    PAPER --> SOURCE["arXiv 2603.27990v2<br/>PDF and TeX pinned + SHA-256 verified"]
    SOURCE --> PLAN["Four exact public contracts proved<br/>Release 5.09 canonical verifier PASS"]
    PLAN --> CROSSWALK["Tao Crosswalk<br/>exact public contracts and source consumers mapped;<br/>PNT substitution and unused stronger alternatives explicit"]

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
        FIBERRED["PROVED factorial fibers and Lemma 4.1<br/>F3: H&lt;N, prime-free, a≪H log N;<br/>square Erdos--Selfridge + subpoly gap + T1.9 give T1.10"]
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
        ONETERM["PROVED Lemma 1.6(i),(ii)<br/>one-term scale + critical saddle asymptotic;<br/>sharp fixed dilation via power-of-two bracketing"]
        VBONETERM["PROVED: exact VB1 identity<br/>unique a²b³ + finite squarefree-cube sum"]
        VBLOWER["PROVED VB square-family lower bounds<br/>reverse-big-O square-root scale"]
        VBONESCALE["PROVED complete VB1 square-root scale<br/>convergent b^-3/2 majorant + lower family"]
        VBONEZETA["PROVED exact VB1 asymptotic<br/>dominated limit + zeta(3/2)/zeta(3) identity"]
        PRIMEI["PROVED: Proposition 2.3(i)<br/>exact Bertrand endpoints"]
        PRIMEII["UNPROVED stronger source alternative<br/>Proposition 2.3(ii), BHP 0.525;<br/>not a premise of the final PNT route"]
        PRIMEIII["PROVED: Proposition 2.3(iii)<br/>global prime-free measure power saving"]
        GTPOWER["Compiled quantitative bridge<br/>uniform dyadic discrepancy power xi < 1"]
        DYADICFREE["Compiled dyadic prime-free bridge<br/>prime-power tail retained and absorbed"]
        PREFIX["Compiled constant-length endpoint measure<br/>finite dyadic assembly + full theta range"]
        VINO["PROVED specialized Theorem 2.5<br/>unconditional quantitative PNT + source-faithful IK effective-degree Vinogradov estimate + complete Fourier reconstruction"]
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
        VBSHORT["PROVED Lemma 3.1 contract<br/>(N,H)=(0,1) is the unique H&lt;N exception + obstruction/cutoff/T2.5 upper + both substitutions + periodic slice + unit-cell insertion + unconditional eventual PNT/binomial scale and measure lower bound + fixed-constant contradiction"]
        VBEXTRACT["PROVED Lemma 3.2<br/>polynomial coefficients + powerful relation"]
        VBCOVER["PROVED finite Lemma 3.2 encoding<br/>injective interval codes + subpolynomial budgets"]
        T18["PROVED Theorem 1.8<br/>nontrivial x^(2/5+o(1)) count + zeta-ratio asymptotic"]
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
        FBOUNDS["PROVED Lemmas 4.1 and 4.2<br/>both low/high geometric contradictions;<br/>P=H log² N has 4P≤N from quantitative PNT;<br/>explicit subpolynomial gap budget"]
        FEXTRACT["PROVED Lemma 4.3<br/>canonical square decomposition + exact product envelope<br/>two-half selection + bounded smooth square relation"]
        FCASES["PROVED Section 4 counting assembly<br/>easy cases + residue/fiber sieve + finite Corollaries 2.8--2.9;<br/>maximal-k closure and one-term upper bound"]
        T19["PROVED Theorem 1.9<br/>taoTheorem19_unconditional;<br/>exact nontrivial and total F3 counting contracts"]
        ES2["UNPROVED stronger source alternative<br/>Erdos--Selfridge Theorem 2 for arbitrary exponent;<br/>not used by the square endpoint"]
        ESSQUARE509["PROVED square Erdos--Selfridge specialization<br/>factorial squarefree fibers have cardinality at most two"]
        T110["PROVED Theorem 1.10<br/>taoTheorem110_unconditional;<br/>exact factorial-solution x^(1/2+o(1)) contract"]
        FBOUNDS --> FEXTRACT
        FEXTRACT --> FCASES
        FCASES --> T19
        T19 --> T110
        FBOUNDS --> T110
        ESSQUARE509 --> T110
    end

    PRIMEII -. optional stronger route .-> FBOUNDS
    PNT509["PROVED native quantitative PNT<br/>theta error with arbitrary fixed log saving"]
    GAP509["PROVED prime-free upper scale<br/>eventually, uniformly in H: 4 H log² N≤N"]
    FREEZE --> PNT509
    PNT509 --> GAP509
    PRIMEI --> GAP509
    GAP509 --> FBOUNDS
    PRIMEIII --> FBOUNDS
    VINO --> FBOUNDS
    PELL --> FCASES
    LSIEVE --> FCASES
    SETS --> T19
    FACTEQ --> T110

    subgraph SECTION5["Section 5: character and sieve machinery"]
        direction TB
        DIRICHLET["Normalized prime character sums PROVED<br/>exact Z^(-1/125) threshold + Z^-8 unexceptional moment;<br/>principal split + exact primitive-conductor regrouping PROVED;<br/>exceptional 1000th moment reduced to Lemma 5.1 square"]
        BURGESS["PROVED Lemma 5.2 / explicit cubefree Burgess<br/>unique-tag prime quotient: simple-root Stepanov + Newton amplification;<br/>denominator case: block swap + inverse character;<br/>prime-square stationary phase + CRT + moment and optimization assembled"]
        BHM["Lemma 5.3 PROVED<br/>finite weighted Bombieri--Halasz--Montgomery;<br/>Hermitian row reduction + prime-indicator specialization"]
        FUND["PROVED Selberg alternative used by Lemma 5.1<br/>finite algebra + O(R) floor error;<br/>nonnegative real weights and 2/log R main mass"]
        ROSSER509["UNPROVED optional source construction<br/>Lemma 5.4 literal {-1,0,1} Rosser weights;<br/>replaced by proved Selberg weights in this route"]
        EXCHAR["PROVED Lemma 5.1 consumer chain<br/>Selberg/BHM + conductor families + off-diagonal absorption;<br/>Burgess premise discharged by the proved explicit bound"]
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
        RANDOM["PROVED Proposition 6.6 consumer chain<br/>literal finite prime-tuple probability laws;<br/>forward/reflected moments, counting, and maximal transfer;<br/>Burgess and critical-saddle inputs now proved"]
        MOMENTS["PROVED Propositions 6.7--6.8 consumer chain<br/>prime and prime-pair residue probabilities;<br/>exceptional-character counts and dyadic aggregation;<br/>mean and variance bounds; Burgess input now proved"]
        T17["PROVED Theorem 1.7<br/>taoTheorem17_unconditional;<br/>unconditional explicit Burgess + sharp critical saddle;<br/>exact frozen public conclusion, no analytic premise"]
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
    PUBLIC --> AUDIT["Tao2026/Audit.lean<br/>explicit run: 8340 declaration reports;<br/>8297 nonempty standard-axiom lists + 43 axiom-free"]
    AUDIT --> RUNNER["run_tao_build.bat<br/>hash/file-set/pin/shortcut/audit/build/semantic gates PASS;<br/>complete unsuppressed transcript"]
    RUNNER --> RELEASE["VERIFIED four-public-theorem release 5.09<br/>Theorems 1.7--1.10 unconditional;<br/>canonical verifier exit 0, 2026-09-19"]
    SEMANTIC509["PROVED semantic regressions<br/>10 assertions explicitly rerun;<br/>endpoints, partitions, squarefree conventions, multiplicity, asymptotics"]
    PUBLIC --> SEMANTIC509
    SEMANTIC509 --> RUNNER

    DOCS["Goal Prompt complete<br/>Checklist / Crosswalk / Manifest continuously updated"] --> CROSSWALK
    SHELL["Extension/Tao2026<br/>active pinned Mathlib package builds"] --> CONTRACTS
    MILESTONE["Proposition 2.3(i),(iii), Proposition 2.1 quantified forms,<br/>Lemma 1.6(i), exact one-term sums,<br/>VB1 zeta asymptotic + factorial lower-asymptotic verifier PASS"] --> SHELL
    HULL["PROVED expanded critical hull assembly<br/>same additive deletion bound;<br/>at most two cuts per order"] --> VINO

    LEGEND["Status: green = proved or verified release gate<br/>blue = pinned dependency-supplied foundation<br/>yellow = honestly conditional alternative<br/>red = unused unformalized stronger source statement"]

    classDef complete fill:#d9f7df,stroke:#238636,color:#111
    classDef ready fill:#dbeafe,stroke:#2563eb,color:#111
    classDef pending fill:#fff4cc,stroke:#b7791f,color:#111
    classDef absent fill:#f8d7da,stroke:#b42318,color:#111
    classDef note fill:#f3f4f6,stroke:#6b7280,color:#111

    class MAP,PAPER,SOURCE,PLAN,DOCS,MILESTONE,FREEZE,GTPOWER,DYADICFREE,PREFIX,PRIMEI,PRIMEIII,SMOOTH,ONETERMID,VBONETERM,VBLOWER,VBONESCALE,VBONEZETA,ANATOMY,INTERVALS,FACTEQ,F31,F3LOWER,FIBERRED,HULL,SCALEMONO,VBCOVER,FEXTRACT,VINO,VBSHORT,T17,T18,T19,T110,BURGESS,AUDIT,RUNNER,PUBLIC,RELEASE,CROSSWALK,ONETERM,UNCERT,LSIEVE,POWERREL,VBEXTRACT,FBOUNDS,FCASES,DIRICHLET,BHM,EXCHAR,TYPICAL,ATYPICAL,RANDOM,MOMENTS,PELL,FUND,ASYM,SETS,CONTRACTS,ESSQUARE509,PNT509,GAP509,SEMANTIC509 complete
    class MATHLIB,PNT,GM,GT,E137,SHELL ready
    class NORMALIZE complete
    class PRIMEII,ES2,ROSSER509 absent
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
    %% Release 3.57: dyadic variation, unit-cell integration, and exact
    %% telescoping compare the low-frequency logarithmically weighted integer
    %% sum with its interval integral. Quantitative PNT, the zero mode, and
    %% final Fourier assembly remain.
    %% Release 3.58: weighted Abel summation compares the Mangoldt/log sum
    %% directly with the integral. A global quantitative-PNT proposition is
    %% reduced to the exact uniform dyadic consumer; prime-power removal,
    %% zero mode, and final assembly remain.
    %% Release 3.59: Lambda/log is split exactly into primes and higher prime
    %% powers; the latter retain arbitrary log saving. The conditional result
    %% is transported to every literal Fourier mode, including zero. Final
    %% absorption and high/low partition remain.
    %% Release 3.60: the explicit conditional low-frequency majorant is
    %% absorbed into P/(log P)^S under every fixed polylogarithmic phase-scale
    %% cutoff. The finite high/low partition remains; quantitative PNT stays
    %% explicit and Theorem 2.5 is not claimed.
    %% Release 3.61: stationary cancellation now covers every subinterval when
    %% the critical point lies in the ambient dyadic block, plus the exterior
    %% left range s<=P/2. Same-sign cancellation now uses the total phase
    %% scale. The final finite mode partition remains.
    %% Release 3.62: the specialized M=N, j=2 high/low partition is complete
    %% modewise on natural Ico dyadic subintervals, including axes and both
    %% sign geometries, and its three-term majorant is absorbed into an
    %% arbitrary P/(log P)^S target. Finite mode summation and arbitrary-real-
    %% interval reduction remain.
    %% Release 3.63: the fixed Fourier box is summed with its exact coefficient
    %% l1 norm, absorbed by two spare logarithmic powers. The specialized
    %% polynomial estimate is complete on natural Ico dyadic subintervals;
    %% arbitrary-real-interval endpoint reduction remains.
    %% Release 3.64: the natural core of every order-convex real interval is
    %% one exact Finset.Ico; the prime set and prime sum are unchanged, and
    %% the nonempty-core symmetric difference has volume at most two.
    %% Release 3.65: the core is capped at 2P without losing primes, the
    %% generic set-integral endpoint inequality and empty-core unit-cell
    %% branch are complete, and all endpoint errors are absorbed. Thus the
    %% specialized arbitrary-log-saving theorem holds for every fixed finite
    %% Fourier polynomial on arbitrary measurable order-convex intervals.
    %% Quantitative infinite Fourier reconstruction remains.
    %% Release 3.66: exact torus reconstruction now bounds W minus its square
    %% Fourier truncation by the outer coefficient l1 tail; smooth radial
    %% decay replaces this by 27*taoC3Norm(W) times the universal cubic tail.
    %% The arbitrary-interval discrepancy retains only this tail remainder.
    %% Release 3.67: the cubic tail is O((R+1)^(-1/2)) through a summable
    %% radial 5/2 envelope. The radius ceil((log P)^B) is now admissible
    %% uniformly after spending half the stretched-log epsilon margin.
    %% Coefficient-normalized growing-box assembly, arbitrary-interval
    %% reduction, and uniform C3-normalized smooth reconstruction are proved
    %% on eventual natural scales. The real-scale/small-scale wrapper and the
    %% two explicit analytic inputs remain before Theorem 2.5 is claimed.
    %% Release 3.68: SpecializedRealScale passes P to ceil(P), preserves the
    %% prime set on I intersect Ici(ceil(P)), and bounds the discarded integral
    %% strip by C3/log(P). Real logarithmic exponents and bounded initial scales
    %% are absorbed explicitly. taoTheorem25Specialized_of_analyticInputs now
    %% has the literal TaoTheorem25SpecializedConclusion type. Only the named
    %% quantitative-PNT and Vinogradov propositions remain for this specialization.
    %% Release 3.69: QuantitativePNTBridge identifies the low-frequency input
    %% with the standard de la Vallee Poussin psi error. The exact identity
    %% cumsum Lambda k = psi(k)-Lambda(k), endpoint absorption, and
    %% stretched-exponential-to-arbitrary-log-saving conversion are compiled.
    %% The classical quantitative psi theorem and the residual Vinogradov
    %% polynomial mean-value proposition remain analytic obligations.
    %% Release 3.70: ClassicalQuantitativePNT combines the frozen native Ford
    %% rectangle zero-free region, quadratic Jensen zero count, and sharp
    %% Perron formula at height exp(a*sqrt(log x)). The de la Vallee Poussin
    %% psi bound and ClassicalMangoldtDiscrepancyLogSaving are now
    %% unconditional. Only VinogradovExponentialSumEstimate remains for the
    %% literal specialized Theorem 2.5 conclusion.
    %% Release 3.71: the Iwaniec--Kowalski degree split uses
    %% k=floor(4 log F/log X), while the larger Taylor cutoff is retained only
    %% for the remainder. Quarter-block VMVT mass, Ford for k>=10000, finite
    %% native critical coefficients below 10000, and the trivial complementary
    %% branch prove VinogradovExponentialSumEstimate. Specialized Theorem 2.5,
    %% Lemma 3.1, and the literal Theorem 1.8 endpoint are unconditional.
    %% Release 3.72: normalized tilted smooth-number weights, their first two
    %% log-partition derivatives, and the exact cutoff-factor ratio reduce the
    %% critical saddle theorem to one explicit Gaussian local-limit target.
    %% Release 3.73: those weights are an actual probability measure on log n.
    %% Its characteristic function and the centered variance-normalized saddle
    %% Fourier series are exact and absolutely convergent. Gaussian convergence
    %% and local-limit inversion remain the smooth-number analytic boundary.
    %% Release 3.74: the complex smooth Fourier series factors into the exact
    %% source-prime geometric Euler product. Each normalized prime factor has
    %% squared norm (1-a)^2/((1-a)^2+2a(1-cos(t log p))), yielding the full
    %% centered saddle contraction product. Frequency estimates remain.
    %% Release 3.75: principal-period cosine loss gives quadratic local decay;
    %% a central-window reciprocal estimate upgrades it to Gaussian decay.
    %% The coefficients sum exactly to phiTwo, so variance normalization yields
    %% |char(t)|<=exp(-t^2/pi^2) on one explicit source-scale range.
    %% Release 3.76: that range is the symmetric interval of exact positive
    %% radius pi/2*(1-2^(-sigma))*sqrt(phiTwo)/log(y). Membership is equivalent
    %% to the source-scale condition. The radius tends to infinity, and hence
    %% captures every fixed frequency, once log(y)/sqrt(phiTwo) tends to zero.
    %% Release 3.77: the eight-log Rankin comparison lies below the exact
    %% saddle. PhiTwo antitonicity plus the exact secant identity yields
    %% phiTwo/log(y)^2>=u/(16log(u)); hence the radius diverges unconditionally
    %% and every fixed normalized frequency eventually has Gaussian decay.
    %% Release 3.78: exact centering distributes over the prime factors and
    %% their variance shares sum to one. A finite contraction-product theorem
    %% reduces convergence to exp(-t^2/2) to the summed local quadratic Taylor
    %% error; the maximal share tends to zero by the 3.77 curvature bound.
    %% Release 3.79: exact geometric moments and a global cubic exp(ix)
    %% remainder bound the summed local Taylor error by
    %% 16000*|t|^3*log(y)/sqrt(phiTwo), which tends to zero. Hence the exact
    %% normalized saddle characteristic converges to exp(-t^2/2) at each
    %% fixed frequency. Complementary-frequency decay and inversion remain.
    %% Release 3.80: the cutoff factor is exactly a one-sided Laplace moment
    %% of the normalized logarithmic law at rate sigma*sqrt(phiTwo). The
    %% Gaussian prefactor is sqrt(2*pi) times this diverging rate, and the
    %% saddle asymptotic is equivalent to convergence of that explicit target.
    %% Release 3.81: the exact normalized Laplace kernel times the centered
    %% characteristic is restricted to the expanding central interval and
    %% dominated by exp(-t^2/pi^2). Pointwise Gaussian convergence plus
    %% dominated convergence evaluates the central integral as sqrt(2*pi),
    %% so its normalized contribution tends to one. Only the Perron
    %% truncation identity and complementary-contour error remain here.
    %% Release 3.82: the twisted smooth Dirichlet series at -t, the phase
    %% exp(i*t*log X), and sigma/(sigma+i*t) are proved exactly equal to the
    %% characteristic/Laplace integrand at -t*sqrt(phiTwo). The central height
    %% and standard-deviation interval substitution are exact, so the 3.81
    %% limit is now literally the normalized central Perron-line limit.
    %% Release 3.83: absolute convergence passes the smooth Dirichlet series
    %% through the finite line, identifying it with frozen sharp-Perron
    %% kernels. The inclusive cutoff is psiNat, subtraction is summable, and
    %% lower/upper logarithmic plus endpoint bounds transfer. Their
    %% saddle-scale aggregation remains.
    %% Release 3.84: the frozen kernels tend to 1, 1/2, and 0 below, at, and
    %% above the cutoff. A summable height-independent envelope and Tannery
    %% give the full smooth-series limit psiNat minus the explicit possible
    %% endpoint half-mass, of norm at most 1/2. Only the finite-height
    %% noncentral-line estimate remains in this saddle step.
    %% Release 3.85: the full line is normalized exactly by the saddle main
    %% term. Removing the central Gaussian contribution is literally the two
    %% tail integrals; its infinite-height limit is the corrected saddle ratio
    %% minus the central term. Critical corrected-ratio convergence is
    %% equivalent to vanishing of this named complement, and the normalized
    %% endpoint is bounded by 1/(2*mainTerm).
    %% Release 3.86: phiTwo <= 7*log(y)*phiOne on sigma>=1/2 gives the
    %% explicit saddle-main-term lower bound sqrt(X)/(sqrt(14*pi)*log X).
    %% Thus the main term diverges in every critical regime, the normalized
    %% endpoint vanishes, and the original saddle asymptotic is equivalent to
    %% decay of the named infinite complementary Perron line.
    %% Release 3.87: prime-local contraction is extended through the full
    %% phase range |t log p|<=pi. This gives a Gaussian envelope up to
    %% normalized radius pi*sqrt(phiTwo)/log(y), and dominated convergence
    %% makes the annulus outside the central window negligible. Only the
    %% Perron frequencies beyond physical height pi/log(y) remain.
    %% Release 3.88: the wide normalized annulus is transported exactly to
    %% the two physical Perron segments between the central height and
    %% pi/log(y). Their normalized sum tends to zero, leaving precisely the
    %% two outer vertical-line tails beyond that height.
    %% Release 3.89: those two tails are named at finite and infinite height.
    %% The complementary line is annulus plus outer line, and the critical
    %% saddle asymptotic is equivalent to decay of the infinite outer object.
    %% Release 3.90: every Euler factor admits a global exponential loss.
    %% The full characteristic and literal Perron integrand are bounded by
    %% exp(-sum_{p<=y} p^(-sigma)*(1-cos(t log p))/96). Outer-tail closure is
    %% reduced to a lower bound for this explicit nonnegative cosine loss.
    %% Release 3.91: on pi/log(y)<=t<=4*pi/(3*log(y)), the top dyadic prime
    %% block has nonpositive cosine. Chebyshev--PNT supplies the explicit loss
    %% y^(-sigma)*y/(16*log(y)). Later outer shells and their integral remain.
    %% Release 3.92: N(t)=ceil(exp(pi/t)) moves the dyadic block with frequency.
    %% Exact ceiling/log bounds put it below y and inside the same negative-cosine
    %% window on a controlled small-frequency range; PNT supplies its explicit
    %% N(t)^(-sigma)*N(t)/(16*log(N(t))) loss. Larger frequencies remain.
    %% Release 3.93: all retained CEP dyadic blocks stay in the first-shell
    %% negative-cosine window. Their 1/log(u) reciprocal mass plus exact saddle
    %% and cutoff bounds gives a divergent loss >>u/log(u), hence a uniform
    %% vanishing envelope for the literal Perron integrand on that shell.
    %% Release 3.94: the exact symmetric physical first-shell contribution is
    %% bounded by its interval width times the 3.93 envelope. Curvature gives
    %% standardDeviation/log(y)<=sqrt(7u), and exp(-c*u/log(u)) absorbs this
    %% factor, so the normalized first-shell integral tends to zero. Later
    %% outer-frequency shells and the infinite outer line remain.
    %% Release 3.95: the exact 3/4 logarithmic support extends the same
    %% accumulated loss through height 3*pi/(2*log y). A reusable symmetric
    %% shell norm bound integrates the adjacent band beyond the 3.94 endpoint,
    %% and its normalized contribution tends to zero. Later frequencies remain.
    %% Release 3.96: a full CEP alphabet at floor(sqrt(y)) has logarithmic
    %% support between one third and one half of log(y). Its phases stay in the
    %% negative-cosine window for 3*pi/(2*log y)<=t<=3*pi/log y, yielding an
    %% explicit accumulated loss throughout the second shell.
    %% Release 3.97: that loss is >= c*u^(2/5)/log(u), whose exponential
    %% absorbs the saddle normalization. The exact symmetric second-shell
    %% contribution through physical height 3*pi/log(y) tends to zero.
    %% Release 3.98: the iterated square-root alphabet has logarithmic support
    %% between one sixth and one quarter of log(y), giving accumulated loss on
    %% the full third shell 3*pi/log(y)<=t<=6*pi/log(y).
    %% Release 3.99: the third-shell loss is >=c*u^(1/5)/log(u); exponential
    %% absorption and the symmetric-shell bound make its normalized
    %% contribution through height 6*pi/log(y) tend to zero.
    %% Release 4.00: a third iterated square-root alphabet has retained support
    %% between one twelfth and one eighth of log(y), giving accumulated loss on
    %% the fourth shell 6*pi/log(y)<=t<=12*pi/log(y).
    %% Release 4.01: the fourth-shell loss is >=c*u^(1/9)/log(u); its
    %% exponential absorbs the saddle normalization and its exact symmetric
    %% contribution through height 12*pi/log(y) tends to zero.
    %% Release 4.02: arbitrary iterated-root alphabets have closed-form
    %% logarithmic envelopes, and indexed physical shell endpoints double
    %% exactly while recovering all previously certified concrete scales.
    %% Release 4.03: one four-fifths scale hypothesis yields the retained CEP
    %% support, exact phase window, and accumulated loss for every indexed
    %% shell k>=2.
    %% Release 4.04: terminal noncollapse plus
    %% 10*(2^k-1)*log(2)<=log(y) supplies the four-fifths scale hypothesis
    %% uniformly for the indexed shell range.
    %% Release 4.05: a<=scale(k,y) iff a^(2^k)<=y. Hence every fixed indexed
    %% depth is eventually noncollapsed in a critical regime, and log(y)->∞
    %% makes its explicit rounding criterion eventually automatic.
    %% Release 4.06: at every fixed k, the Rankin ratio is eventually below
    %% sqrt(scale(k,y)); the uniform indexed phase theorem therefore gives
    %% the complete loss bound throughout that fixed physical shell.
    %% Release 4.07: finite-prefix intersections plus the frozen countable
    %% diagonal theorem select K(n)->infinity, with simultaneous loss on all
    %% indexed shells 2<=k<=K(n).
    %% Release 4.08: shell k has explicit loss exponent (4/5)*2^(-k); the
    %% retained scale and universal exp(-16) cofactor penalty yield a loss
    %% tending to infinity for every fixed k.
    %% Release 4.09: positive-power exponential absorption and exact indexed
    %% shell widths show every fixed symmetric indexed Perron contribution
    %% tends to zero.
    %% Release 4.10: a second slow diagonal controls the norm of the complete
    %% finite prefix by 1/(K+1), so K(n)->infinity while the moving indexed
    %% shell sum tends to zero.
    %% Release 4.11: adjacent normalized symmetric shells telescope exactly;
    %% the moving sum is one contiguous segment from indexed height 1 through
    %% height K(n), and its contribution tends to zero.
    %% Release 4.12: the earlier controlled pieces form one vanishing
    %% pre-indexed segment. Subtracting it and the moving indexed segment from
    %% the infinite outer line isolates one post-terminal remainder whose
    %% decay is equivalent to the critical saddle asymptotic.
    %% Release 4.13: terminal iterated-scale survival forces indexed physical
    %% height <=3*pi/(2*log(4)); an admissible growing depth therefore cannot
    %% escape to infinite height, so a second tail mechanism is necessary.
    %% Release 4.14: HT Lemma 8(ii)'s exact loss
    %% u*t^2/((1-sigma)^2+t^2) is named, radially monotone, transferred to the
    %% physical Perron integrand, and integrated on finite symmetric shells.
    %% Release 4.15: the HT Lemma-6 Mangoldt transform and cosine sum are
    %% explicit; real-part subtraction is exact and two transform errors E
    %% yield the cosine-corollary error 2E.
    %% Release 4.16: HT Lemma 6 is stated at its exact
    %% exp((log y)^(3/2-epsilon)) frequency ceiling and equation-(3.10) error;
    %% its complex and cosine main terms are computed in closed form.
    %% Release 4.17: the Mangoldt cosine sum is split exactly into prime and
    %% prime-power terms, yielding the source lower bound for the Euler-product
    %% cosine loss modulo the explicit HT Lemma-5 remainder.
    %% Release 4.18: the HT Lemma-5 remainder is decomposed by prime-power
    %% exponent and bounded by a convergent geometric series times the
    %% weighted Chebyshev sum, giving explicit O(log y) for sigma>=1/2.
    %% Release 4.19: the exact cosine main term is bounded below uniformly by
    %% y^beta*t^2/(2*beta*(beta^2+t^2)) and inserted into the Euler-product
    %% loss bridge together with the explicit prime-power remainder.
    %% Release 4.20: canonical finite Abel summation compares the HT main
    %% coefficient with the exact saddle Rankin ratio, giving the source
    %% rational loss under one explicit cutoff-size hypothesis.
    %% Release 4.21: theta-Abel summation gives the uniform logarithmically
    %% weighted prime bound at scale y^beta/beta, removing the cutoff from
    %% the saddle comparison and source-shaped rational HT main-term loss.
    %% Release 4.22: the HT transform and main term are normalized exactly at
    %% s=1-beta+i*t, the shifted-Perron contract is proved equivalent to the
    %% Lemma-6 contract, and the finite psi-Abel identity is compiled.
    %% Release 4.23: absolute convergence identifies the shifted initial-line
    %% zeta-log-derivative integral with source-weighted frozen Perron kernels;
    %% the exact cutoff yields the source Dirichlet sum and error series.
    %% Release 4.24: a translated zeta-surrogate rectangle crosses only
    %% z=1-s, extracts the exact source main term, and exposes two horizontal
    %% and one left vertical edge under a literal zero-free premise.
    %% Release 4.25: the native rectangle-uniform Vinogradov--Korobov theorem
    %% discharges that premise at left edge beta-eta and height |t|+T under
    %% its explicit source width condition.
    %% Release 4.26 corrected: eta=2*(log y)^(epsilon/2-1), T=2Y_epsilon(y),
    %% right=beta+1/log y give the exact target left-edge decay and constant
    %% right-line cost; the transform error is exactly the three contour
    %% edges minus the finite-height sharp-Perron truncation error.
    %% Release 4.27: exact exponent arithmetic makes eta*VKDenominator(Y)
    %% a negative epsilon/6 power times a log-log factor. Log-versus-power
    %% decay plus the frozen factor-three comparison proves the literal
    %% zero-free width uniformly over every requested translated height.
    %% Release 4.28: the shifted coefficient and selected right-line power
    %% cancel to y^(beta-1) times the frozen optimized Perron exponent.
    %% Below-cutoff, endpoint, and above-cutoff estimates form a nonnegative
    %% summable majorant controlling the complete truncation-error norm.
    %% Release 4.29: integrality of y bounds every nonendpoint reciprocal
    %% logarithmic distance by y+1. The majorant sum is thus one endpoint
    %% plus an optimized positive von Mangoldt Dirichlet series, giving an
    %% explicit complete truncation bound at the selected HT height.
    %% Release 4.30: the source-scale refinement retains reciprocal distance
    %% near n=y and compares it to eight harmonic numbers; the far range has
    %% factor two and one optimized von Mangoldt series. This removes the
    %% coarse extra factor y uniformly over the full epsilon range.
    %% Release 4.31: epsilon/2 < 3/2-epsilon absorbs every fixed logarithmic
    %% loss. Endpoint, near, and far pieces split the scalar target in thirds,
    %% giving the exact complex truncation decay and its inclusion in the
    %% HT Lemma-6 Mangoldt-error allowance.
    %% Release 4.32: generic normalized horizontal/vertical length-times-sup
    %% bounds specialize to the literal HT widths and combine all three
    %% displaced edges into one scalar majorant. Only their pointwise
    %% translated log-derivative bounds and absorption remain in this branch.
    %% Release 4.33: the left-edge Perron denominator stays inside the
    %% integral, giving logarithmic rather than linear height cost. Exact
    %% integrand factorization and a weighted three-edge majorant isolate the
    %% remaining translated zeta log-derivative estimate.
    %% Release 4.34: twice the HT shift fits in the native VK width, giving
    %% quantitative separation from every frozen sharp-Landau zero. The
    %% finite zero sum, large-zero exclusion, frozen partial-fraction bound,
    %% and transport yield zeta'/zeta control at every positive height with
    %% reciprocal-width cost and no selected-good-ordinate hypothesis.
    %% Release 4.35: zeta conjugation covers negative ordinates; choosing
    %% the Landau scale |R| removes unit-interval bookkeeping, and frozen
    %% logarithm/zero-mass estimates give O((1+1/eta)*log |R|) uniformly in
    %% the sign. Only the low-height vertical segment needs separate input.
    %% Release 4.36: on a fixed compact half-VK rectangle the entire
    %% surrogate (s-1)zeta(s) is nonzero, hence has bounded logarithmic
    %% derivative. Restoring zeta gives precisely the 1/eta pole cost on the
    %% low-height left line, completing pointwise coverage of all ordinates.
    %% Release 4.37: twice the shift fits at nine source frequency ceilings.
    %% Exact horizontal coordinate bounds instantiate the high Landau theorem;
    %% a split at the fixed native height combines compact and Landau control
    %% on the full left edge, yielding pointwise bounds on all three edges.
    %% Release 4.38: surrogate nonvanishing supplies every zeta side condition.
    %% The horizontal Perron denominator gives 1/T, the left denominator stays
    %% inside the integral, and the weighted theorem yields a logarithmic-cost
    %% scalar majorant for the complete three-edge contribution.
    %% Release 4.39: the displacement is doubled, still fitting the VK width.
    %% Cubic log-derivative and quadratic reciprocal-distance-log losses spend
    %% one stretched-exponential copy; the other is the exact Lemma-6 target.
    %% Thus every displaced edge is closed uniformly when 2*eta <= beta.
    %% Release 4.40: equation (3.10)'s O_epsilon constant is now explicit.
    %% Moving the complementary contour left of zero crosses both z=1-s and
    %% z=0; the latter residue is -zeta'/zeta(s). The exact two-pole VK contour
    %% and its truncation-error decomposition are proved for the small-beta
    %% branch. Sharp origin control and negative-left edge absorption remain.
    %% Release 4.41: beta <= 2*eta makes the negative-left physical depth at
    %% most 3*eta. Spending this fixed factor in the VK comparison discharges
    %% the complete small-beta contour geometry eventually and uniformly.
    %% The origin is identified with physical -zeta'/zeta; compactness gives
    %% C+1/beta at bounded height. Sharp high-height control remains.
    %% Release 4.42: a VK-scale variable disk centered right of one contains
    %% the small-beta source point at normalized radius at most 5/6. Native
    %% zero-freeness, Euler-product center control, the Pintz disk maximum,
    %% and the frozen disk log-derivative theorem give O(D(A)*loglog A) at
    %% high height. Exact HT scale absorption and compact low-height control
    %% yield the uniform K/beta origin-residue bound. Only the three
    %% negative-left edges remain.
    %% Release 4.43: reflection preserves logarithmic denominator cost on
    %% Re z=-eta. Three-shift VK geometry controls both horizontal edges and
    %% the complete negative-left edge; their scalar majorant fits the two
    %% terms of the literal HT error. Origin, edges, truncation, and the
    %% large-beta contour now give a uniform eventual equation-(3.10) bound.
    %% Only finite initial-y promotion to the named contract remains.
    %% Release 4.44: the transform is bounded by psi(y), the main term by
    %% y/beta, and the literal HT error dominates 1/beta. Monotonicity of psi
    %% absorbs the finite prefix below the eventual contour threshold into
    %% one enlarged constant. The all-y HT Lemma 6 contract is now proved;
    %% outer-frequency Perron decay and local-limit inversion remain.
    %% Release 4.45: the sharp saddle comparison reserves half of the rational
    %% HT loss. If the explicit Lemma-6 and prime-power terms consume one
    %% quarter, the remaining quarter controls the Euler-product cosine loss.
    %% The global characteristic bound yields the exact HT minor-arc contract
    %% with coefficient 1/(384*C_HT). Only uniform scalar absorption remains.
    %% Release 4.46: the first-frequency rational loss is at least
    %% u/(65*(log u)^2) and diverges. Saddle displacement bounds y^(1-sigma)
    %% by u^8, stretched-exponential decay absorbs that power, and the saddle
    %% equation gives (1-sigma)*log y >= (log u)/2. The Lemma-6 error and
    %% prime-power remainder are therefore uniformly absorbed at 1/log y;
    %% radial monotonicity proves the unconditional HT minor-arc contract
    %% through the epsilon=1/2 ceiling. Local-limit inversion remains.
    %% Release 4.47: the exact physical Laplace--Fourier kernel contributes
    %% sigma/sqrt(sigma^2+t^2), preserving reciprocal-frequency decay. Thus
    %% an HT-bounded symmetric finite shell costs only a logarithmic endpoint
    %% ratio. At the source ceiling, log y <= u^2 reduces the normalized
    %% envelope to u^5*exp(-c*u/(log u)^2), which vanishes. Exact adjacent
    %% shell subtraction proves decay from pi/log y through that ceiling.
    %% Sharp finite-height Perron truncation and final inversion remain.
    %% Release 4.48: epsilon=1/4 raises the HT ceiling to
    %% exp((log y)^(5/4)); the minor-arc estimate and its weighted integral
    %% remain vanishing there. Endpoint/near/far arithmetic majorants prove
    %% sharp finite-height Perron inversion at this ceiling. The critical
    %% identity u*log u/log y -> 1/alpha^2 absorbs X^(1-sigma), while exact
    %% saddle cancellation absorbs the far Dirichlet series. Only final
    %% contour/local-limit assembly remains before Theorem 1.7.
    %% Release 4.49: the normalized quarter-height Perron line splits exactly
    %% as central Gaussian + wide annulus + HT outer shell. Their limits are
    %% 1 + 0 + 0, and finite-height inversion transfers this to
    %% psiNat/mainTerm -> 1. The critical smooth saddle asymptotic is now
    %% proved; only the independent explicit Burgess input remains for the
    %% unconditional Theorem 1.7 endpoint.
    %% Release 4.50: positive powers through orderOf chi satisfy exact
    %% geometric-series orthogonality, including at zero. Summing over a
    %% polynomial identifies the powered complete-trace family with
    %% orderOf(chi) times the kernel-fiber count chi(P(x))=1, and the same
    %% identity is transported to the split distinct-root Kummer trace.
    %% The remaining Burgess leaf is now the actual Kummer-cover projective
    %% point-count/Weil estimate, not active-root combinatorics.
    %% Release 4.51: evaluation on a cyclic unit generator computes the
    %% character image and kernel cardinalities. The orderOf(chi)-power image
    %% is contained in that kernel and has the same cardinality, so they are
    %% equal. Hence chi(a)=1 iff a is a nonzero orderOf(chi)-th power. Exact
    %% affine fiber counting, the zero fibers, and projective Weil remain.
    %% Release 4.52: every nonempty unit power-map fiber has cardinality
    %% orderOf(chi), the zero field fiber is {0}, and summing the vertical
    %% fibers proves the exact affine Kummer-cover point count. For nonzero P
    %% the zero-value term is P.roots.toFinset.card. Only projective
    %% completion, points at infinity, and the Kummer Weil estimate remain.
    %% Release 4.53: the affine count equals p plus all proper character-power
    %% traces, uniformly for scalar twists cP. Multiplicative Fourier
    %% inversion in c recovers (p-1)S(chi,P) as the chi^{-1} coefficient of
    %% the twisted defects. Thus a uniform sharp twisted-defect bound transfers
    %% to the individual trace with no orderOf(chi) loss; this is a strong
    %% Fourier criterion, not merely the ordinary total-curve Hasse bound.
    %% Release 4.54: the genuine geometric boundary is now the chosen-character
    %% Frobenius spectrum. Its rank is at most #roots-1, every eigenvalue has
    %% norm at most sqrt(p), and its negative trace is S(chi,P). Triangle inequality
    %% feeds this directly through the polynomial, prime-quotient, composite,
    %% and fixed-r=7 Burgess endpoints. Existence of this isotypic spectrum is
    %% the remaining Kummer cohomology theorem.
    %% Release 4.55: exact norm equality is corrected to the mixed-weight
    %% inequality needed for degenerate Jacobi sums. Rank-zero and rank-one
    %% spectra close one and two roots, the trace equals the chi^{-1} Fourier
    %% projection of twisted affine counts, and the global spectral contract
    %% is equivalent to its genuine three-or-more-root residual.
    %% Release 4.56: each spectral eigenvalue is now required to be an
    %% algebraic integer. Character values are zero or roots of unity, so
    %% complete polynomial correlations and the low-root spectra satisfy this
    %% stronger arithmetic contract. This excludes fractional decompositions,
    %% but the full integral base trace can still occupy one eigenvalue.
    %% Release 4.57: norm-lifted Kummer correlations are defined over every
    %% positive-degree finite extension. A genuine Frobenius system requires
    %% one fixed spectrum to reproduce all of them as successive power sums.
    %% Rank zero forces all traces to vanish; rank one satisfies a checked
    %% geometric recurrence. Forgetting the power traces reaches fixed-r=7.
    %% Release 4.58: norm pullback is an injective character monoid map and
    %% preserves exact order. Single-root base changes are one active power,
    %% so all extension traces vanish and the rank-zero system is constructed.
    %% The full system is equivalent to exact two-root Hasse-Davenport plus
    %% the three-or-more-root Kummer cohomology residual.
    %% Release 4.59: arbitrary-field two-root correlations are evaluated
    %% exactly as Jacobi sums, including the scalar and root-difference
    %% factors after base change. Norm lifting raises base character values
    %% to the extension degree. The literal signed Jacobi Hasse-Davenport
    %% identity therefore constructs the rank-one two-root Frobenius system.
    %% Only that classical identity itself and the three-or-more-root Kummer
    %% cohomology theorem remain as source leaves.
    %% Release 4.60: trace pullback of additive characters preserves
    %% primitivity. The two degenerate Jacobi branches are unconditional; in
    %% the nondegenerate branch, the Jacobi/Gauss product formula reduces the
    %% result to Gauss lifting for chi, phi, and chi*phi. Hence the complete
    %% two-root system follows from one literal norm/trace Gauss
    %% Hasse-Davenport theorem. That theorem and the three-or-more-root
    %% cohomology theorem are the remaining source leaves.
    %% Release 4.61: norm and trace character lifting is transitive through
    %% finite-field towers, and local signed Gauss lifting relations compose
    %% with the exact product degree. Degree one is proved by finite-field
    %% uniqueness, so the prime-field Gauss theorem is equivalent to its
    %% degree-at-least-two restriction. A general-base intermediate-field
    %% construction is still needed before any prime-degree reduction.
    %% Release 4.62: Gauss lifting is invariant under algebra equivalence.
    %% Prime/composite induction realizes a composite degree as two nested
    %% canonical extensions, composes their local relations, and transports
    %% back by finite-field uniqueness. Universal finite-base
    %% Hasse-Davenport is equivalent to its prime-degree fragment and implies
    %% the original prime-field residual. The universal prime-degree formula
    %% and three-or-more-root Kummer cohomology remain the source leaves.
    %% Release 4.63: trace and norm lifting have the exact scalar-shift
    %% compatibility needed by Gauss sums. Finite Pontryagin duality shows
    %% every primitive complex additive character is a nonzero shift of the
    %% canonical one. Thus the universal prime-degree residual is equivalent
    %% to the canonical-character prime-degree formula, which still reaches
    %% Jacobi Hasse-Davenport and the two-root Frobenius system. That formula
    %% and three-or-more-root Kummer cohomology are the source leaves.
    %% Release 4.64: the classical monic-polynomial generating-function route
    %% is now started internally. Fixed-degree monic polynomials are exactly
    %% coefficient vectors; the weighted degree-one sum is the Gauss sum,
    %% while every degree-at-least-two coefficient vanishes for nontrivial
    %% multiplicative character. The remaining finite-field bridge is the
    %% closed-point Euler-product comparison with norm/trace Gauss sums.
    %% Release 4.65: the monic weight is multiplicative and factors exactly
    %% over normalized monic irreducibles with additive total degree. For an
    %% extension element x, the norm/trace weight equals the minimal-
    %% polynomial weight to [L:K(x)], so the lifted Gauss sum is now an exact
    %% closed-point sum. Only the finite logarithmic-derivative recurrence
    %% remains on this Hasse-Davenport route.
    %% Release 4.66: the finite coefficient recurrence X A' = B A is
    %% formalized abstractly, and exact induction shows that A=1+G X forces
    %% B_(n+1)=(-1)^n G^(n+1). The genuine weighted monic coefficient
    %% sequence is proved to be exactly 1, the base Gauss sum, then zero.
    %% Hence the signed Hasse-Davenport powers now follow from the single
    %% remaining closed-point recurrence, whose construction from normalized
    %% irreducible factors and minimal-polynomial sums is the next leaf.
    %% Release 4.67: finite weighted Euler factors (1-wX^d)^-1 are built as
    %% formal power series, their coefficients and logarithmic-derivative
    %% divisor sums are computed exactly, and finite products are proved to
    %% satisfy the release-4.66 recurrence. Only the finite specialization to
    %% bounded-degree monic irreducibles and its minimal-polynomial fiber
    %% interpretation remain on the Hasse-Davenport route.
    %% Release 4.68: monic irreducibles through any cutoff form the actual
    %% finite Euler alphabet. Its recurrence and degree-stratified closed-
    %% point divisor sum are compiled. Degree allocations construct monic
    %% products of irreducible powers with exact degree and exact weight.
    %% The inverse normalized-factor allocation and minimal-polynomial fiber
    %% count remain.
    %% Release 4.69: normalized factorization gives an exact equivalence from
    %% fixed-degree monic polynomials to irreducible multisets, and exact
    %% multiplicity counts identify these with every valid bounded Euler
    %% allocation. The weight-preserving finite sums prove Euler coefficient
    %% = monic sum. A truncated recurrence then evaluates the closed-point
    %% coefficient and degree-stratified irreducible sum as the signed Gauss
    %% power. Only its minimal-polynomial extension-fiber interpretation and
    %% the independent 3+-root Kummer cohomology theorem remain.
    %% Release 4.70: every irreducible minimal-polynomial fiber is equivalent
    %% to an AdjoinRoot algebra-hom/root fiber and has cardinality d exactly
    %% when d divides the extension degree. Its relative multiplicity is the
    %% complementary quotient. Fiberwise regrouping identifies the lifted
    %% norm/trace Gauss sum with release 4.69's divisor sum. Universal Gauss
    %% and Jacobi Hasse--Davenport and the full <=2-root Kummer system are now
    %% unconditional; only the 3+-root Kummer cohomology leaf remains.
    %% Release 4.71: affine Kummer fibers, point counts, proper power traces,
    %% scalar twists, and multiplicative Fourier inversion are generalized to
    %% every finite field. On each canonical extension, the selected inverse-
    %% character Fourier coefficient of twisted affine trace defects equals
    %% (p^(n+2)-1) times the corresponding Kummer extension correlation. The
    %% final 3+-root leaf is therefore a literal all-degree isotypic Kummer
    %% point-count decomposition with bounded rank, integrality, and weight.
    %% Release 4.72: an affine-Fourier Frobenius system records those literal
    %% point-count coefficients. Genuine power traces construct it, and the
    %% nonzero factor p^(n+2)-1 cancels degree by degree to reconstruct the
    %% original system. The 3+-root source propositions are equivalent, and
    %% the geometric form still reaches fixed-r=7 Burgess directly.
    %% Release 4.73: an explicit projective Mobius map reduces every exact
    %% three-root correlation to a Jacobi main term minus one deleted point.
    %% Jacobi Hasse--Davenport makes both terms powers of two integral
    %% weight-at-most-one eigenvalues. This constructs the rank-two system in
    %% every degree-divisible exact-three-root case, including one inactive
    %% root. The residual is now three roots with nondivisible degree or at
    %% least four roots.
    %% Release 4.74: if one of the three roots is inactive, its trivial local
    %% character deletes exactly that point and leaves a two-root Jacobi sum.
    %% The Jacobi and deleted terms yield two integral weight-at-most-one
    %% eigenvalues in every degree, with no degree hypothesis. The exact
    %% three-root residual is therefore only all-active and nondivisible; the
    %% other branch has at least four roots.
    %% Release 4.75: the inactive-root deletion formula is generalized to any
    %% root set and every extension degree. Each deleted value is an integral
    %% weight-zero power eigenvalue. One active root has zero main sum; two
    %% active roots have the Hasse--Davenport Jacobi eigenvalue. Thus every
    %% <=2-active-root system is constructed at rank #roots-1, and the final
    %% geometric source is exactly the >=3-active-root system.
    %% Release 4.76: the final cohomological datum is repackaged as the
    %% unrestricted active-root trace with rank <= #active roots-1. The base
    %% field and every extension split into this trace minus explicit inactive
    %% powers. Appending those integral weight-zero eigenvalues reconstructs
    %% the full system while the active/inactive cardinality identity preserves
    %% rank <= #roots-1. Only the genuine >=3-active-root cohomology remains.
    %% Release 4.77: retaining the leading scalar and only active linear
    %% factors constructs a canonical split polynomial whose root multiset is
    %% exactly the active roots with unchanged multiplicities. Its ordinary
    %% Kummer trace equals the active trace over the base field and every norm-
    %% lifted extension. Full systems for these all-active polynomials convert
    %% losslessly to active systems, making the final source equivalent to
    %% ordinary >=3-root Kummer cohomology with every root active.
    %% Release 4.78: every active multiplicity is reduced modulo orderOf chi.
    %% The residues are nonzero and strictly below the order, the distinct
    %% roots are unchanged, and norm lifting preserves the character-power
    %% identity in every degree. The final source is equivalent to full
    %% Kummer cohomology for split >=3-root polynomials with all multiplicities
    %% in the finite range 1,...,orderOf(chi)-1.
    %% Release 4.79: scalar multiplication contributes the degree-th power of
    %% its base character value to every extension trace. Dividing by the
    %% leading coefficient makes the residual polynomial monic without
    %% changing roots, multiplicities, splitness, or reduced exponents.
    %% Twisting every eigenvalue by that character value reconstructs the
    %% original system at the same rank and weight. The final source is now
    %% monic reduced-exponent >=3-root Kummer cohomology.
    %% Release 4.80: choose distinct roots a,b and apply the affine coordinate
    %% (r-a)/(b-a). The new monic split polynomial has the same distinct-root
    %% count and multiplicities, still has reduced exponents, and contains
    %% roots 0 and 1. Extension traces differ by the d-th power of
    %% chi(b-a)^degree, which is absorbed into every eigenvalue. The final
    %% source is two-point-normalized finite-exponent Kummer cohomology.
    %% Release 4.81: the exactly-three-root branch is represented literally
    %% by a canonical polynomial with roots 0,1,t and positive reduced
    %% exponents m,n,k. The old Jacobi construction removes m+n+k divisible
    %% by orderOf(chi). The residual is precisely the nondivisible Legendre
    %% family together with the normalized >=4-root family.
    %% Release 4.82: the canonical three-root trace over every extension is
    %% identified with the literal power-Legendre sum for chi_E^m, chi_E^n,
    %% chi_E^k at 0,1,t. A dedicated rank<=2 integral weight-one Frobenius
    %% structure is equivalent to the polynomial Kummer system. The residual
    %% three-root input is now a pure hypergeometric power-trace theorem.
    %% Release 4.83: rank<=2 is normalized to a literal ordered eigenpair,
    %% padding ranks 0 and 1 with zero. The converse Fin 2 system is exact.
    %% Its traces satisfy the quadratic recurrence determined by pair sum and
    %% product, and its weight bounds recover the base 2*sqrt(p) Weil bound.
    %% Release 4.84: every monic split higher-root polynomial is replaced
    %% literally by the product of X-C r over its root multiset. Roots, degree,
    %% multiplicities, splitness, and reducedness become exact finite multiset
    %% data. The remaining source is now a Legendre eigenpair together with a
    %% normalized multiset containing 0 and 1 and at least four support points.
    %% Release 4.85: the higher-root system's variable rank is padded with
    %% zeros to the literal maximal vector Fin (#support-1). Exact finite-sum
    %% identities preserve all power traces, and the converse vector gives a
    %% maximal-rank system. The residual is now two explicit finite vectors:
    %% the Legendre pair and the normalized higher-root eigenvalue vector.
    %% Release 4.86: mapped evaluation of the canonical multiset polynomial
    %% is identified with the direct product of local character powers over
    %% its support. This holds in every norm-lifted extension. Both residual
    %% branches are now literal finite-field character sums equipped with
    %% fixed integral weight-one eigenvalue vectors.
    %% Release 4.87: the higher-root vector is quotiented by ordering to an
    %% exact spectral multiset of cardinality #support-1. Conversions preserve
    %% multiplicities and all power traces. Its product of X-C alpha is a
    %% canonical monic split Frobenius polynomial with precisely that root
    %% multiset and degree.
    %% Release 4.88: the Legendre pair is likewise quotiented by ordering to
    %% a two-element spectrum, with a canonical monic split quadratic
    %% Frobenius polynomial. The complete residual is now uniformly two
    %% families of bounded integral spectra realizing explicit character-sum
    %% power traces.
    %% Release 4.89: the two-element Legendre spectrum's multiset sum and
    %% product are its intrinsic integral trace and determinant. Its canonical
    %% Frobenius polynomial is exactly X^2-C(trace)X+C(determinant), and all
    %% extension correlations satisfy the resulting order-two recurrence
    %% without choosing an eigenvalue ordering.
    %% Release 4.90: the unconditional critical saddle theorem is composed
    %% into the public endpoint. Explicit cubefree Burgess alone now implies
    %% Theorem 1.7. Fixed-r=7 complete Weil, the full Kummer system, and the
    %% final two intrinsic spectral sources each map to a concrete Burgess
    %% certificate carrying the public conclusion. Only construction of those
    %% Kummer spectra remains on the Theorem 1.7 route.
    %% Release 4.91: the first two explicit Legendre correlations determine
    %% canonical integral trace and determinant coefficients and therefore one
    %% explicit quadratic Frobenius polynomial. Every possible spectrum has
    %% exactly its roots; spectra for fixed input data form a subsingleton.
    %% The remaining Legendre leaf is existence for this fixed polynomial.
    %% Release 4.92: that explicit quadratic unconditionally has one canonical
    %% two-element complex root multiset. A Legendre spectrum exists exactly
    %% when these roots are integral and sqrt(p)-bounded and the literal
    %% correlations obey the fixed quadratic recurrence. Two-step induction
    %% reconstructs every trace. The abstract Legendre existential is gone;
    %% these concrete conditions and the higher-root spectra remain.
    %% Release 4.93: every literal extension correlation, hence the canonical
    %% trace, is unconditionally an algebraic integer. Both fixed roots are
    %% integral iff the explicit determinant is integral, by an integral-
    %% closure transitivity argument. The Legendre leaf is now determinant
    %% integrality, fixed-root weight bounds, and the literal recurrence.
    %% Release 4.94: quadratic-extension Frobenius orbits and base-pair swap
    %% orbits have the same diagonal, because norm lifting squares every base
    %% weight. The Newton determinant numerator is therefore twice an explicit
    %% finite sum of algebraic integers, proving determinant integrality
    %% unconditionally. Only fixed-root sqrt(p) bounds and the literal
    %% recurrence remain in the Legendre leaf; higher-root spectra remain.
    %% Release 4.95: the recurrence identifies every literal correlation with
    %% the negative power sum of the two canonical roots. A converse power-sum
    %% spectral-radius lemma makes the individual sqrt(p) root bounds exactly
    %% equivalent to sharp Weil bounds in every extension degree. The roots
    %% are unconditionally integral. The Legendre leaf is now stated solely
    %% as the literal all-extension Weil bound plus literal recurrence.
    %% Release 4.96: Newton identities recover every elementary symmetric
    %% coefficient of a finite complex multiset from its positive power sums.
    %% Thus the literal higher-root extension traces and prescribed cardinality
    %% determine the spectral multiset with multiplicity. Its spectrum type is
    %% a subsingleton, so existence is unique existence and its Frobenius
    %% polynomial is canonical. Only existence of this unique higher-root
    %% spectrum and the literal Legendre Weil/recurrence statements remain.
    %% Release 4.97: a well-founded Newton recursion constructs every
    %% higher-root elementary symmetric coefficient from the first literal
    %% correlations. The resulting polynomial is unconditionally monic of
    %% degree #support-1 and has a fixed complex root multiset of that exact
    %% cardinality. Spectrum existence is equivalent to integrality, weight,
    %% and all-trace predicates on these canonical roots; the abstract
    %% higher-root spectral existential is removed from the residual.
    %% Release 4.98: canonical root power sums satisfy the characteristic
    %% recurrence of the Newton polynomial. Monicity proves recurrence
    %% uniqueness from the first degree-many terms. Thus all higher-root
    %% trace identities are replaced by a finite initial segment plus the
    %% explicit Newton recurrence, and this residual reaches Theorem 1.7.
    %% Release 4.99: Vieta coefficient extraction identifies the canonical
    %% roots' elementary symmetric sums with all constructed Newton
    %% coefficients. Inverse Newton induction makes the finite initial power
    %% sums automatic. Only canonical-root integrality, sqrt(p) weight, and
    %% the literal characteristic recurrence remain in the higher-root leaf.
    %% Release 5.00: for a monic split polynomial, integral roots are
    %% equivalent to integral coefficients. Exact Newton degree makes this a
    %% finite coefficient predicate, also equivalent to integrality of the
    %% recursively constructed elementary coefficients. Rootwise integrality
    %% disappears from the residual; weight and recurrence remain.
    %% Release 5.01: Newton identities for every powered finite multiset plus
    %% Cauchy's root bound prove that sharp bounds on all positive power sums
    %% are equivalent to individual root bounds. The higher-root sqrt(p)
    %% clause becomes the literal all-extension Weil bound. Its residual is
    %% now finite coefficient integrality, literal Weil, and recurrence only.
    %% Release 5.02: the quadratic-extension correlation is split into
    %% Frobenius orbits and compared with the coordinate-swap decomposition
    %% of the squared base correlation. Their common fixed-point contribution
    %% proves the second Newton coefficient integral; degrees zero and one are
    %% immediate. Only Newton integrality in degrees at least three remains,
    %% together with the literal Weil bounds and characteristic recurrences.
    %% Release 5.03: a general order-three orbit decomposition handles the
    %% cubic extension. Its fixed points contribute cubes of base weights and
    %% non-fixed points contribute in Frobenius triples. Finite induction on
    %% base weights proves the cubic complete-homogeneous term integral, so
    %% Newton degree three is unconditional. Integrality now remains only in
    %% degrees at least four.
    %% Release 5.04: quartic Frobenius is decomposed into its base-field fixed
    %% points, quadratic-subfield points, and full four-element orbits. Norm
    %% transitivity identifies the middle weights with squares of quadratic
    %% orbit weights. Degree-four complete-homogeneous induction then proves
    %% Newton degree four integral. Integrality remains only in degrees at
    %% least five.
    %% Release 5.05: order-five Frobenius has only fixed points and full
    %% five-element orbits. The fifth Newton numerator reuses the integral
    %% aggregate residuals from degrees two through four and adds the quintic
    %% orbit sum. Newton degree five is unconditional; integrality remains
    %% only in degrees at least six.
    %% Release 5.06 supersedes all finite-degree integrality residuals:
    %% arbitrary subfield embeddings, partial Frobenius norms, and weighted
    %% orbit divisor sums identify the first m Newton coefficients with a
    %% finite Euler product over the degree-m! field. Every coefficient and
    %% every canonical Newton root is integral. The endpoint now consumes
    %% only literal Weil bounds and characteristic recurrences.
    %% Release 5.07: orbit/minimal-polynomial degree and weight identities,
    %% polynomial unique factorization, and interpolation/orthogonality prove
    %% the exact signed monic coefficient identity and Newton degree cutoff.
    %% General and Legendre characteristic recurrences are now proved.
    %% Theorem 1.7 consumes only literal all-extension Weil inequalities.
    %% Historical 5.07 boundary above, superseded by release 5.08 below.
    STEPANOV508["PROVED simple-root Stepanov method<br/>Hasse constraints + separated orders + dimension count<br/>explicit integer parameters + norm-fiber cancellation + translation"]
    RECURRENCE508["PROVED literal Newton recurrence<br/>eventual power-sum spectral amplification"]
    SIMPLEWEIL508["PROVED simple-root sharp Weil bound<br/>all extensions; arbitrary other root multiplicities"]
    STEPANOV508 --> SIMPLEWEIL508
    RECURRENCE508 --> SIMPLEWEIL508
    SIMPLEWEIL508 --> BURGESS
    BURGESS --> T17
    class STEPANOV508,RECURRENCE508,SIMPLEWEIL508 complete
    KUMMERALT509["CONDITIONAL broader Kummer alternatives<br/>arbitrary-multiplicity geometric and literal-Weil interfaces;<br/>not required by the proved unique-tag simple-root route"]
    KUMMERALT509 -. optional stronger route .-> BURGESS
    class KUMMERALT509 pending
