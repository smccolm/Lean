# Tao--Trudgian--Yang 2025 proof architecture

This is the canonical dependency view for the formalization. Green means the
checklist acceptance test is installed and passes the principal runner, blue
means reusable source exists but its target bridge is not yet proved, and red
means open. Checklist numbers are authoritative.

```mermaid
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
    ET["EPZAE-33 energy transfer<br/>IN PROGRESS: perturbation, tolerance normalization,<br/>Type I scale/separation/pattern packaging DONE;<br/>coefficient subpower bound, LV* use + Type II OPEN;<br/>EPZAE-34 OPEN"]
    HBE["EPZAE-35 Heath--Brown energy relation<br/>OPEN"]
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
    ZCB --> ET
    ZLV --> ET
    SRC --> HBE
    ER --> HBE
    RC --> EC
    ET --> EC
    HBE --> EC
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
    class ML,ED,GM,PY,SRC available;
    class TC,RC,AB,EP,LVP,LVS,GMB,ZCB,ZDE,CD,AE done;
    class GEN,DU,PR,BT,NEP,MU,LVC,ZLV,ZDT,HBD,IBD,BZD,OBD,ZTAB,ER,ET,HBE,EC,NAE,PUB,SEM,REL open;
```

## Critical paths

The shortest useful path is:

```text
toolchain -> ANTEDB bridge -> exponent-pair semantics -> beta duality
-> exact envelope certificates -> four new exponent pairs
```

The zero-density path additionally requires large-value semantics and the
source-convention bridge to the completed Guth--Maynard work. The
additive-energy path is last because it depends on nearly the whole
large-value/zero framework and on five-dimensional projection certificates.

## Boundary rules

- `RC` proves only finite arithmetic implications. It cannot manufacture an
  analytic exponent-pair or large-value premise.
- `GMB` must consume the actual local Guth--Maynard theorem, not a separately
  supplied proposition with the desired bound.
- `ZCB` is mandatory even if both projects use the letter `N`; naming does not
  establish equality of zero-count conventions.
- `ET` must preserve the source's possibly different subsequences for
  cardinality, energy, and double-zeta exponents.
- `PUB` remains red until every advertised output has no mathematical theorem
  parameter and is present in the default build and exhaustive audit.
