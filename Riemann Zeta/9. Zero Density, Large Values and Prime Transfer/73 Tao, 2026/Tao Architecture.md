flowchart TD
    MAP["RH Map node 73<br/>Tao, 2026"] --> PAPER["Tao: Products of consecutive integers<br/>with unusual anatomy"]
    PAPER --> SOURCE["arXiv 2603.27990v2<br/>PDF and TeX pinned + SHA-256 verified"]
    SOURCE --> PLAN["Whole-proof contract researched<br/>Theorems 1.7--1.10 fixed as release scope"]
    PLAN --> CROSSWALK["Tao Crosswalk<br/>exact source rows still to populate"]

    subgraph FOUNDATION["Immutable foundation boundary"]
        direction TB
        MATHLIB["Mathlib c5ea0035...<br/>factorization, squarefree, smooth numbers,<br/>Dirichlet-character infrastructure inspected"]
        PNT["PNT+ 4ecb9501...<br/>audited Selberg-sieve infrastructure candidate"]
        GM["Node 71 Guth--Maynard<br/>frozen commit 2ace9e7c..."]
        GT["Node 74 Gafni--Tao<br/>2/15 almost-all short-interval PNT available"]
        E137["scottdhughes/erdos137<br/>commit 3027d9a...; partial elementary reuse candidate"]
        FREEZE["Node-73 immutable snapshots + hashes<br/>not yet assembled"]
        MATHLIB --> FREEZE
        PNT --> FREEZE
        GM --> GT
        GT --> FREEZE
        E137 --> FREEZE
    end

    CROSSWALK --> CONTRACTS["Exact Lean statement contracts<br/>not yet frozen"]
    FREEZE --> CONTRACTS

    subgraph OBJECTS["Source objects and asymptotic language"]
        direction TB
        ASYM["Precise O, o(1), x^o(1), and ~ APIs<br/>initial quantified definitions compile"]
        ANATOMY["Largest prime factor, powerful,<br/>squarefree component definitions compile"]
        INTERVALS["Consecutive interval product;<br/>bad, very bad, and type-F3 predicates compile"]
        SETS["Literal B, VB, F3 unions/endpoints<br/>and one-term subsets compile"]
        FACTEQ["Ordered factorial-equation solution set<br/>and finite count compile"]
        ASYM --> SETS
        ANATOMY --> INTERVALS
        INTERVALS --> SETS
        ANATOMY --> FACTEQ
    end

    CONTRACTS --> ASYM
    CONTRACTS --> ANATOMY

    subgraph SECTION2["Section 2 common inputs"]
        direction TB
        SMOOTH["Proposition 2.1<br/>smooth-number asymptotics + stability"]
        ONETERM["Lemma 1.6<br/>B1 exact sum and x/z^(2+o(1))"]
        PRIME["Proposition 2.3<br/>Bertrand + BHP 0.525 + 2/15 almost-all PNT"]
        GTBRIDGE["Node-74 exceptional-measure bridge<br/>density zero alone is insufficient"]
        VINO["Theorem 2.5<br/>two-variable prime equidistribution"]
        UNCERT["Lemma 2.6<br/>Montgomery uncertainty principle"]
        LSIEVE["Corollaries 2.8--2.9<br/>large sieve with exact residue exclusions"]
        PELL["Lemma 2.10<br/>generalized Pell square-solution count"]
        POWERREL["Corollary 2.11<br/>powerful linear-relation count x^(2/5+o(1))"]
        SMOOTH --> ONETERM
        GTBRIDGE --> PRIME
        PRIME --> VINO
        UNCERT --> LSIEVE
        PELL --> POWERREL
    end

    ASYM --> SMOOTH
    ANATOMY --> SMOOTH
    SETS --> ONETERM
    GT --> GTBRIDGE
    ANATOMY --> PELL

    subgraph SECTION3["Section 3: very bad intervals"]
        direction TB
        VBSHORT["Lemma 3.1<br/>H <= exp(log(N)^(2/3+o(1)))"]
        VBEXTRACT["Lemma 3.2<br/>extract powerful relation a*n+h=b*m"]
        T18["PUBLIC: Theorem 1.8<br/>nontrivial VB bound + zeta asymptotic"]
        VBSHORT --> VBEXTRACT
        VBEXTRACT --> T18
    end

    VINO --> VBSHORT
    POWERREL --> T18
    SETS --> T18

    subgraph SECTION4["Section 4: type F3 and factorial equation"]
        direction TB
        FBOUNDS["Lemmas 4.1--4.2<br/>coefficient bound + interval shortness"]
        FEXTRACT["Lemma 4.3<br/>square relation with smooth coefficients"]
        FCASES["Source case split<br/>square counts + large sieve"]
        T19["PUBLIC: Theorem 1.9<br/>nontrivial F3 bound + x^(1/2+o(1))"]
        T110["PUBLIC: Theorem 1.10<br/>factorial solutions x^(1/2+o(1))"]
        FBOUNDS --> FEXTRACT
        FEXTRACT --> FCASES
        FCASES --> T19
        T19 --> T110
    end

    PRIME --> FBOUNDS
    VINO --> FBOUNDS
    PELL --> FCASES
    LSIEVE --> FCASES
    SETS --> T19
    FACTEQ --> T110

    subgraph SECTION5["Section 5: character and sieve machinery"]
        direction TB
        DIRICHLET["Normalized prime character sums<br/>primitive exceptional characters"]
        BURGESS["Lemma 5.2<br/>explicit Burgess saving; not in current Mathlib"]
        BHM["Lemma 5.3<br/>Bombieri--Halasz--Montgomery inequality"]
        FUND["Lemma 5.4<br/>fundamental-lemma sieve weights"]
        EXCHAR["Lemma 5.1<br/>exceptional-character count + norm bounds"]
        DIRICHLET --> EXCHAR
        BURGESS --> EXCHAR
        BHM --> EXCHAR
        FUND --> EXCHAR
    end

    MATHLIB --> DIRICHLET
    PNT --> FUND

    subgraph SECTION6["Section 6: bad intervals and anti-sieve"]
        direction TB
        NORMALIZE["Lemmas 6.1--6.2<br/>admissibility + p0^2 p1...p1000 m' anatomy"]
        TYPICAL["Definitions 6.3--6.4<br/>typical interval contracts"]
        ATYPICAL["Proposition 6.5<br/>non-typical union bound"]
        RANDOM["Proposition 6.6<br/>independent sampled-prime probability bound"]
        MOMENTS["Propositions 6.7--6.8<br/>anti-sieve moments and character expansion"]
        T17["PUBLIC: Theorem 1.7<br/>nontrivial B saving + x/z^(2+o(1))"]
        NORMALIZE --> TYPICAL
        TYPICAL --> ATYPICAL
        TYPICAL --> RANDOM
        RANDOM --> MOMENTS
        ATYPICAL --> T17
        MOMENTS --> T17
    end

    ONETERM --> NORMALIZE
    PRIME --> ATYPICAL
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
    AUDIT --> RUNNER["run_tao_build.bat<br/>evolving warning-failing verifier"]
    RUNNER --> RELEASE["Tao 2026 formal proof release<br/>not achieved"]

    DOCS["Goal Prompt complete<br/>Checklist / Crosswalk / Manifest continuously updated"] --> CROSSWALK
    SHELL["Extension/Tao2026<br/>active pinned Mathlib package builds"] --> CONTRACTS
    SCAFFOLD["Current definitions verifier<br/>pins + imports + shortcut scan + build PASS"] --> SHELL

    LEGEND["Status: green = verified groundwork<br/>blue = inspected candidate/ready shell<br/>yellow = specified but unproved<br/>red = major unformalized input or endpoint"]

    classDef complete fill:#d9f7df,stroke:#238636,color:#111
    classDef ready fill:#dbeafe,stroke:#2563eb,color:#111
    classDef pending fill:#fff4cc,stroke:#b7791f,color:#111
    classDef absent fill:#f8d7da,stroke:#b42318,color:#111
    classDef note fill:#f3f4f6,stroke:#6b7280,color:#111

    class MAP,PAPER,SOURCE,PLAN,DOCS,SCAFFOLD complete
    class MATHLIB,PNT,GM,GT,E137,SHELL,ASYM,ANATOMY,INTERVALS,SETS,FACTEQ ready
    class CROSSWALK,FREEZE,CONTRACTS,ONETERM,PRIME,GTBRIDGE,UNCERT,LSIEVE,POWERREL,VBSHORT,VBEXTRACT,FBOUNDS,FEXTRACT,FCASES,DIRICHLET,BHM,EXCHAR,NORMALIZE,TYPICAL,ATYPICAL,RANDOM,MOMENTS,AUDIT,RUNNER pending
    class SMOOTH,VINO,PELL,BURGESS,FUND,T17,T18,T19,T110,PUBLIC,RELEASE absent
    class LEGEND note
