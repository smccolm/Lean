flowchart TD
    S00["PSH-00 Isolation boundary<br/>DONE: research subtree only"]
    S01["PSH-01 Pinned Zeta23 reproduction<br/>DONE WITH RECORDED UPSTREAM WARNINGS<br/>Comparator Windows replay accepted"]
    S02["PSH-02 Exact paper-to-Lean crosswalk<br/>DONE<br/>specializations and nonmatches explicit"]
    S03["PSH-03 Exact M[P_X,P_X] decomposition<br/>DONE<br/>source theorem recovered as regression"]
    S04["PSH-04 Exact dyadic m=n+h rewrite<br/>DONE<br/>literal kernel is K_N,T(n,h), with<br/>anchor plus variation remainder"]
    S05["PSH-05 Narrow GM finite interface<br/>DONE AS A SPECIFICATION<br/>not assumed and not proved from GM"]
    F1{"PSH-06 F1 collapsed-prefix verdict<br/>FAIL - THEOREM LEVEL"}
    N1["GM collapsed-prefix route killed<br/>exact decomposition preserved;<br/>n-local or direct variation input needed"]
    S07["PSH-07 F2: disconnected-shell<br/>admissibility and cross terms<br/>OPEN"]
    S08["PSH-08 Arithmetic-only<br/>oracle consumer<br/>OPEN"]
    F3{"PSH-09 F3: certified pricing gives<br/>a meaningful new zero theorem?"}
    N2["Stop shell route<br/>record strongest certified bound"]
    S10["PSH-10 Complete informal proof<br/>with all constants and errors<br/>OPEN"]
    S11["PSH-11 Select GM or MRT<br/>from proved gate verdicts<br/>OPEN"]
    S12["PSH-12 Toolchain/integration decision<br/>without modifying frozen GM<br/>OPEN"]
    S13["PSH-13 Formalize native arithmetic input<br/>OPEN"]
    S14["PSH-14 Replace oracle in exact trace<br/>OPEN"]
    S15["PSH-15 Spectral/inertia consumer<br/>OPEN"]
    S16["PSH-16 New unconditional<br/>Prime Shell zero theorem<br/>OPEN"]
    S17["PSH-17 Dependency audit<br/>OPEN"]
    S18["PSH-18 Zero-warning clean build<br/>OPEN"]
    S19["PSH-19 Trusted statement check<br/>OPEN"]
    S20["PSH-20 Reproducible immutable release<br/>OPEN"]
    S21["PSH-21 Independent expert review<br/>OPEN - EXTERNAL"]
    MRT["Next justified source test: MRT<br/>almost-all fixed shifts; candidate<br/>threshold alpha > 33/25<br/>OPEN - Phase II not started"]
    CEIL["PSH-C Optional ceiling audit<br/>reproduce EnclOK before using 0.6818287<br/>as a verified numerical comparator"]

    S00 --> S01 --> S02 --> S03 --> S04 --> S05 --> F1
    F1 -->|NO| N1
    F1 -->|YES| S07 --> S08 --> F3
    F3 -->|NO| N2
    F3 -->|YES| S10 --> S11 --> S12 --> S13 --> S14 --> S15 --> S16 --> S17 --> S18 --> S19 --> S20 --> S21
    N1 --> MRT --> S07
    CEIL -. optional scoreboard .-> F3

    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef open fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef gate fill:#fff2bf,stroke:#9a6a00,color:#332500,stroke-width:2px;
    classDef stop fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    class S00,S01,S02,S03,S04,S05 done;
    class S07,S08,S10,S11,S12,S13,S14,S15,S16,S17,S18,S19,S20,S21,MRT,CEIL open;
    class F3 gate;
    class F1,N1,N2 stop;
