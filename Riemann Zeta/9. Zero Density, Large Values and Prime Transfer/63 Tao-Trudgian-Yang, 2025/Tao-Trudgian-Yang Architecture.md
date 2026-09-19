# Tao--Trudgian--Yang 2025 proof architecture

This is the canonical dependency view for the planned formalization. Node
status is conservative: blue means a reusable source exists but its target
bridge is not yet proved; red means open. Checklist numbers are authoritative.

```mermaid
flowchart TD
    ML["Mathlib analytic and finite foundations<br/>AVAILABLE"]
    ED["ANTEDB Lean asymptotics, phases,<br/>exponential sums, Euler--Maclaurin<br/>AVAILABLE at current pin"]
    GM["Local Guth--Maynard large-values<br/>and zero-density foundation<br/>AVAILABLE and audited"]
    PY["Paper-time ANTEDB Python/blueprint<br/>DISCOVERY AND REPRODUCTION ONLY"]
    SRC["Classical source literature<br/>AVAILABLE AS REFERENCES"]

    TC["EPZAE-01--02 unified toolchain,<br/>package, build and audit<br/>OPEN"]
    RC["EPZAE-03--06 exact rational,<br/>piecewise and polyhedral certificates<br/>OPEN"]
    AB["EPZAE-07 asymptotic/phase bridge<br/>OPEN"]

    EP["EPZAE-08 exponent-pair semantics<br/>OPEN"]
    DU["EPZAE-09 convexity and beta duality<br/>OPEN"]
    PR["EPZAE-10--12 A/B/C/D and<br/>Heath--Brown processes<br/>OPEN"]
    BT["EPZAE-13 certified beta table<br/>OPEN"]
    NEP["EPZAE-14 four new exponent pairs<br/>OPEN"]
    MU["EPZAE-15 zeta-growth bridge<br/>OPEN"]

    LVP["EPZAE-16 large-value patterns<br/>OPEN"]
    LVS["EPZAE-17 LV and LV_zeta semantics<br/>OPEN"]
    LVC["EPZAE-18--19 elementary and<br/>classical LV calculus<br/>OPEN"]
    GMB["EPZAE-20 exact Guth--Maynard bridge<br/>OPEN"]
    ZLV["EPZAE-21 zeta large-values bounds<br/>OPEN"]

    ZCB["EPZAE-22 zero-count convention bridge<br/>OPEN"]
    ZDE["EPZAE-23 density exponent A(sigma)<br/>OPEN"]
    ZDT["EPZAE-24--25 LV-to-density transfer<br/>and classical density bridges<br/>OPEN"]
    HBD["EPZAE-26 improved Heath--Brown density<br/>OPEN"]
    IBD["EPZAE-27 improved Bourgain density<br/>OPEN"]
    BZD["EPZAE-28 Bourgain pair-to-density theorem<br/>OPEN"]
    OBD["EPZAE-29 optimized eight-piece bound<br/>OPEN"]
    ZTAB["EPZAE-30 best-known density envelope<br/>OPEN"]

    AE["EPZAE-31 additive-energy semantics<br/>OPEN"]
    ER["EPZAE-32 energy exponents and regions<br/>OPEN"]
    ET["EPZAE-33--34 energy transfer and powering<br/>OPEN"]
    HBE["EPZAE-35 Heath--Brown energy relation<br/>OPEN"]
    EC["EPZAE-36 energy polyhedral certificates<br/>OPEN"]
    NAE["EPZAE-37 nine new additive-energy bounds<br/>OPEN"]

    PUB["EPZAE-38 exact public assembly<br/>OPEN"]
    SEM["EPZAE-39 semantic regressions<br/>OPEN"]
    REL["EPZAE-40--41 release reproduction<br/>and synchronized documentation<br/>OPEN"]

    ML --> TC
    ED --> TC
    GM --> TC
    PY --> RC
    ML --> RC
    TC --> AB
    ED --> AB
    AB --> EP
    EP --> DU
    SRC --> PR
    DU --> PR
    RC --> BT
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
    SEM --> REL

    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    class ML,ED,GM,PY,SRC available;
    class TC,RC,AB,EP,DU,PR,BT,NEP,MU,LVP,LVS,LVC,GMB,ZLV,ZCB,ZDE,ZDT,HBD,IBD,BZD,OBD,ZTAB,AE,ER,ET,HBE,EC,NAE,PUB,SEM,REL open;
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
