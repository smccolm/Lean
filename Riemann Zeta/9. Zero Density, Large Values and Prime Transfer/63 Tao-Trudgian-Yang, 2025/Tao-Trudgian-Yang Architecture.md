flowchart TD
    ML["Mathlib analytic and finite foundations<br/>AVAILABLE"]
    ED["ANTEDB Lean asymptotics, phases,<br/>exponential sums, Euler--Maclaurin<br/>AVAILABLE at current pin"]
    GM["Local Guth--Maynard large-values<br/>and zero-density foundation<br/>AVAILABLE and audited"]
    PY["Paper-time ANTEDB Python/blueprint<br/>DISCOVERY AND REPRODUCTION ONLY"]
    SRC["Classical source literature<br/>AVAILABLE AS REFERENCES"]

    TC["EPZAE-01--02 unified toolchain,<br/>package, build and audit<br/>DONE"]
    RC["EPZAE-03--05 exact rational,<br/>piecewise and polyhedral certificates<br/>DONE"]
    GEN["EPZAE-06 deterministic generator<br/>all public tables INSTALLED;<br/>energy projections OPEN"]
    AB["EPZAE-07 asymptotic/phase bridge<br/>DONE"]

    EP["EPZAE-08 exponent-pair semantics<br/>DONE"]
    DU["EPZAE-09 convexity and beta duality<br/>OPEN"]
    PR["EPZAE-10--12 A/B/C/D and<br/>Heath--Brown processes<br/>OPEN"]
    BT["EPZAE-13 certified beta table<br/>OPEN"]
    NEP["EPZAE-14 four new exponent pairs<br/>OPEN"]
    MU["EPZAE-15 zeta-growth bridge<br/>OPEN"]

    LVP["EPZAE-16 large-value patterns<br/>DONE"]
    LVS["EPZAE-17 LV and LV_zeta semantics<br/>DONE"]
    LVC["EPZAE-18--19 elementary and<br/>classical LV calculus<br/>OPEN"]
    GMB["EPZAE-20 exact Guth--Maynard bridge<br/>DONE"]
    ZLV["EPZAE-21 zeta large-values bounds<br/>OPEN"]

    ZCB["EPZAE-22 zero-count convention bridge<br/>DONE"]
    ZDE["EPZAE-23 density exponent A(sigma)<br/>DONE"]
    ZDT["EPZAE-24 LV-to-density transfer<br/>OPEN"]
    CD["EPZAE-25 classical density bridges<br/>DONE"]
    HBD["EPZAE-26 improved Heath--Brown density<br/>OPEN"]
    IBD["EPZAE-27 improved Bourgain density<br/>OPEN"]
    BZD["EPZAE-28 Bourgain pair-to-density theorem<br/>OPEN"]
    OBD["EPZAE-29 optimized eight-piece bound<br/>OPEN"]
    ZTAB["EPZAE-30 best-known density envelope<br/>OPEN"]

    AE["EPZAE-31 additive-energy semantics<br/>DONE"]
    ER["EPZAE-32 energy exponents and regions<br/>DONE"]
    ET["EPZAE-33 energy transfer<br/>zeroe-from-large source inequality DONE;<br/>actual Type-I/II + multiplicities DONE;<br/>symmetric rectangle + sup/limsup DONE;<br/>bounded-range corollary OPEN"]
    PL62["Printed Lemma 62: DISPROVED<br/>kernel-checked counterexample PRESERVED"]
    PW["EPZAE-34 corrected cardinality/energy powering<br/>two-witness target STATED;<br/>finite energy selection CHECKED;<br/>general analytic proof OPEN"]
    PWC["EPZAE-34 cardinality witness<br/>rho/k exact; energy at most rho-star/k;<br/>independent existential sCard; OPEN"]
    PWE["EPZAE-34 energy witness<br/>rho-star/k exact; cardinality at most rho/k;<br/>independent existential sEnergy; OPEN"]
    HBE["EPZAE-35 Heath--Brown energy relation<br/>OPEN"]
    HBA["EPZAE-34/35 powered Heath--Brown application<br/>s-free monotone consumer CHECKED;<br/>analytic inputs OPEN"]
    EC["EPZAE-36 energy polyhedral certificates<br/>OPEN"]
    NAE["EPZAE-37 nine new additive-energy bounds<br/>OPEN"]

    PUB["EPZAE-38 exact public assembly<br/>OPEN"]
    SEM["EPZAE-39 semantic regressions<br/>OPEN"]
    REL["EPZAE-40--41 release reproduction<br/>and synchronized documentation<br/>OPEN"]

    ML --> TC
    ED --> TC
    GM --> TC
    PY --> GEN
    ML --> RC
    TC --> AB
    ED --> AB
    AB --> EP
    EP --> DU
    SRC --> PR
    DU --> PR
    RC --> BT
    GEN --> BT
    PR --> BT
    DU --> BT
    BT --> NEP
    NEP --> MU

    TC --> LVP
    AB --> LVP
    LVP --> LVS
    LVS --> LVC
    SRC --> LVC
    GM --> GMB
    LVS --> GMB
    LVC --> ZLV
    GMB --> ZLV
    MU --> ZLV

    GM --> ZCB
    ZCB --> ZDE
    GM --> CD
    ZDE --> CD
    LVS --> ZDT
    ZLV --> ZDT
    GM --> ZDT
    ZDE --> ZDT
    ZDT --> HBD
    ZDT --> IBD
    NEP --> BZD
    SRC --> BZD
    BZD --> OBD
    RC --> IBD
    RC --> OBD
    HBD --> ZTAB
    IBD --> ZTAB
    OBD --> ZTAB
    GM --> ZTAB

    TC --> AE
    AB --> AE
    AE --> ER
    ER --> ET
    ER --> PW
    PL62 -. "authorized repair: remove false s scaling" .-> PW
    PW --> PWC
    PW --> PWE
    PWC -->|cardinality constraints| EC
    PWE -. "bounded-range energy reduction" .-> ET
    PWE --> HBA
    ZCB --> ET
    ZLV --> ET
    SRC --> HBE
    ER --> HBE
    HBE --> HBA
    RC --> EC
    ET --> EC
    HBA --> EC
    EC --> NAE

    NEP --> PUB
    HBD --> PUB
    IBD --> PUB
    OBD --> PUB
    NAE --> PUB
    PUB --> SEM
    RC --> SEM
    GEN --> SEM
    SEM --> REL

    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef done fill:#d9f2df,stroke:#26753a,color:#123d1e,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef preserved fill:#eee5ff,stroke:#69469b,color:#35204f,stroke-width:2px;
    class ML,ED,GM,PY,SRC available;
    class TC,RC,AB,EP,LVP,LVS,GMB,ZCB,ZDE,CD,AE,ER done;
    class GEN,DU,PR,BT,NEP,MU,LVC,ZLV,ZDT,HBD,IBD,BZD,OBD,ZTAB,ET,PW,PWC,PWE,HBE,HBA,EC,NAE,PUB,SEM,REL open;
    class PL62 preserved;
