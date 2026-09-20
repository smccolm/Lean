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
    ZMK["EPZAE-21 critical-zeta convolution<br/>weighted twelfth-power Holder;<br/>log loss + dyadic/window bridges DONE"]
    ZMI["EPZAE-21 exact coefficient-one Mellin identity<br/>sharp endpoints + negative phase;<br/>critical integral + pole residue DONE"]
    ZMU["EPZAE-21 uniform cutoff derivative masses<br/>Mellin factors + physical-scale kernels DONE"]
    ZPE["EPZAE-21 localized Perron entry estimate<br/>tail + residue absorption;<br/>actual sigma >= 1/2, tau >= 2 windows DONE"]
    ZTM["EPZAE-19/21 critical-line twelfth moment<br/>dyadic height estimate OPEN"]

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
    ET["EPZAE-33 energy transfer<br/>zeroe-from-large source inequality DONE;<br/>actual Type-I/II + multiplicities DONE;<br/>symmetric rectangle + sup/limsup DONE;<br/>general bounded-scale reduction DONE;<br/>zeta endpoint 2 + final corollary OPEN"]
    PL62["Printed Lemma 62: DISPROVED<br/>kernel-checked counterexample PRESERVED"]
    PW["EPZAE-34 corrected cardinality/energy powering<br/>actual normalized powered patterns;<br/>uniform limits + compactness;<br/>full two-witness theorem DONE"]
    PWC["EPZAE-34 cardinality witness<br/>rho/k exact; energy at most rho-star/k;<br/>independent existential sCard; DONE"]
    PWE["EPZAE-34 energy witness<br/>rho-star/k exact; cardinality at most rho/k;<br/>independent existential sEnergy; DONE"]
    HBE["EPZAE-35 Heath--Brown energy relation<br/>native moments + exact source bridges;<br/>full-domain logarithmic limit; DONE"]
    HBA["EPZAE-34/35 powered Heath--Brown application<br/>actual-region consumer;<br/>no analytic theorem parameters; DONE"]
    HUX["EPZAE-19 Huxley energy-region bridge<br/>native finite estimate + exact limits;<br/>corrected cardinality powering DONE"]
    EC1G["EPZAE-36/37 Add-est (i) general half<br/>six-branch endpoint certificates;<br/>actual-region + uniform high-height bounds DONE"]
    EC1Z["EPZAE-36 Add-est (i) zeta certificate<br/>six branches + height transition;<br/>65/86 crossover + envelope DONE"]
    EC1ZA["EPZAE-21/37 actual zeta-energy bound<br/>uniform LV + energy deductions proved;<br/>dyadic critical twelfth moment OPEN"]
    EC["EPZAE-36 energy polyhedral certificates<br/>clause (i) general/zeta certificates DONE;<br/>other eight projections OPEN"]
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
    ML --> ZMK
    GM -->|separated shell occupancy| ZMK
    SRC --> ZPE
    SRC --> ZTM
    LVP --> ZMI
    GM -->|native Mellin inversion and residue calculus| ZMI
    ML -->|smooth transition and L-series| ZMI
    ML --> ZMU
    LVP --> ZMU
    ZMI -->|exact identity with residue| ZPE
    ZMU -->|uniform kernel and fourth-order tail| ZPE
    ZMK -->|finite actual-pattern consumer proved| ZLV
    ZPE -->|proved entry and uniform LV deduction| ZLV
    ZTM -->|moment bound still needed| ZLV

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
    GM -->|uniform polynomial powering| PW
    AB -->|logarithmic limits| PW
    PW --> PWE
    PWC -->|cardinality constraints| EC
    PWE -->|proved general bounded-range reduction| ET
    PWE --> HBA
    ZCB --> ET
    ZLV --> ET
    SRC --> HBE
    GM -->|second and fourth moments| HBE
    ER --> HBE
    HBE --> HBA
    GM -->|classical MHH finite estimate| HUX
    ER --> HUX
    PWC --> HUX
    HUX --> EC1G
    HBA --> EC1G
    RC --> EC1G
    EC1G --> NAE
    RC --> EC1Z
    HUX --> EC1ZA
    HBE --> EC1ZA
    ER --> EC1ZA
    EC1Z --> EC1ZA
    ZLV -->|twelfth-moment cardinality needed| EC1ZA
    EC1ZA --> NAE
    ET -->|short-zeta transfer needed| NAE
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
    class TC,RC,AB,EP,LVP,LVS,GMB,ZCB,ZDE,CD,AE,ER,PW,PWC,PWE,HBE,HBA,HUX,EC1G,EC1Z,ZMK,ZMI,ZMU,ZPE done;
    class GEN,DU,PR,BT,NEP,MU,LVC,ZLV,ZTM,ZDT,HBD,IBD,BZD,OBD,ZTAB,ET,EC1ZA,EC,NAE,PUB,SEM,REL open;
    class PL62 preserved;
