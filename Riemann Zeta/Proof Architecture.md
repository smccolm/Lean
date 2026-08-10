flowchart TD
    MZ["Mathlib analytic, Fourier,<br/>linear-algebra and combinatorics APIs<br/>AVAILABLE"]
    PZ["Pinned PNT+ zeta, Mellin and<br/>Poisson/Euler-Maclaurin stack<br/>AVAILABLE AND AUDITED"]
    ER["ANTEDB classical zero-density blueprint<br/>AVAILABLE AS REFERENCE"]
    MP["Maynard-Pratt Appendix C<br/>AVAILABLE AS REFERENCE"]
    HY["Hughes-Young twisted fourth moment<br/>AVAILABLE AS REFERENCE"]
    DFI["Duke-Friedlander-Iwaniec<br/>quadratic-divisor theorem<br/>AVAILABLE AS REFERENCE"]
    GMR["Guth-Maynard Sections 3-12<br/>AVAILABLE AS REFERENCE"]
    HBR["Heath-Brown 1979<br/>difference-set mean square<br/>AVAILABLE AS REFERENCE"]

    ZB["Zeta analytic foundations<br/>DONE"]
    LZ["Local zero count<br/>DONE"]
    CF["Mollifier and contour foundations<br/>DONE"]
    ZT["Exact Abel/Euler-Maclaurin truncation<br/>DONE"]
    ST["Sharp zero truncation<br/>DONE"]
    VD["#15 van der Corput and Weyl<br/>DONE"]
    CLV["#15 Classical MHH large values<br/>DONE"]
    FDT["#15 Finite transfer machinery<br/>DONE"]
    PW["#15 Exact finite powering<br/>DONE"]
    RA["#15 Exceptional-range arithmetic<br/>DONE"]
    DI["#15 Finite Type-I/Type-II dichotomy<br/>DONE"]
    FA["#15 Finite scale/exponent assembly<br/>DONE"]
    MR["#15 Medium Type-I reflection<br/>OPEN<br/>uniform stationary main term,<br/>dual block and fixed coefficients"]
    TE["#15 Terminal Type-I estimate<br/>DONE<br/>uniform prefix Kusmin-Landau,<br/>Abel weight and sharp cutoff"]
    FR["#15 Finite zero-density reduction<br/>OPEN<br/>consume dichotomy and endpoint certificates"]
    ZD["#15 Ingham and Huxley<br/>OPEN<br/>three boundary cases DONE"]

    BR["#16 Beta removal<br/>DONE"]
    AC["#17 Coefficient bounds<br/>DONE"]
    MV["Montgomery mean value<br/>DONE"]
    HM["Basic Halasz-Montgomery<br/>DONE"]
    EX["Separated Type-I extraction<br/>DONE"]
    CT["Central Type I<br/>DONE CONDITIONALLY<br/>only #19 GM large values remains"]
    DY["Slab to symmetric N<br/>DONE"]

    CI["#18 Coverage-range contract repair<br/>DONE<br/>source range Re rho >= 7/10"]
    GD["#18 Uniform vertical Gamma decay<br/>and contour-integrand integrability<br/>DONE"]
    CV["#18 Appendix C contour coverage<br/>OPEN<br/>Mellin inversion, zero cancellation,<br/>residue and tails"]
    SS["#18 Scaled weighted separation<br/>and bounded overlap<br/>DONE"]
    CR["#18 Type-II fourth-moment reduction<br/>DONE<br/>Gamma tails, scaled overlap,<br/>and epsilon assembly proved"]
    AF["#18 Smooth zeta-squared AFE<br/>and diagonal bound<br/>OPEN"]
    QD["#18 Quadratic-divisor<br/>off-diagonal theorem<br/>OPEN"]
    MS["#18 M-squared expansion, support,<br/>coefficient bound and moment identity<br/>DONE"]
    TM["#18 Generic short-polynomial<br/>twisted fourth moment and native<br/>specialization<br/>OPEN"]
    TR["Primitive-input transfer<br/>DONE CONDITIONALLY<br/>open inputs #15, #18, #19"]
    GCS["#18 Goal C specialization<br/>OPEN<br/>derive zero density from GM large values alone"]

    DR["#19 Delete false decoupling contracts<br/>DONE<br/>file, contracts and both axioms removed"]
    SF["#19 Source-facing finite definitions<br/>DONE<br/>affine reindexing, scaling and<br/>seven-bin exact-energy bridge proved"]
    MX["#19 Sampling matrix and trace reduction<br/>DONE<br/>exact Lemmas 4.1-4.2<br/>operator-norm conclusions proved"]
    PS["#19 Poisson expansion and S1<br/>OPEN"]
    RF["#19 Smooth reflection / AFE<br/>GM Lemma 6.2<br/>OPEN"]
    HB["#19 Heath-Brown difference-set<br/>mean-square estimate<br/>OPEN"]
    S2["#19 S2 estimate<br/>OPEN"]
    EN["#19 Approximate-energy bridge<br/>and R-sum L2/L4 moments<br/>OPEN"]
    SL["#19 S3 localization<br/>change of variables and tails<br/>OPEN"]
    AT["#19 Affine-transformation estimate<br/>GM Proposition 9.1<br/>OPEN"]
    S3["#19 Refined S3 estimate<br/>GM Proposition 10.1<br/>OPEN"]
    EG["#19 GCD/spacing energy theorem<br/>GM Section 11<br/>OPEN"]
    GM["#19 Exact Guth-Maynard large values<br/>Sections 3 and 12 assembly<br/>OPEN"]
    GZD["#19 Concrete GM zero density<br/>OPEN"]
    CB["Combined transfer<br/>DONE CONDITIONALLY<br/>open inputs #15 and #19"]
    CZD["#19 Combined zero density<br/>OPEN"]
    IG["#19 Dependency and integrity layer<br/>DONE<br/>975/975 dependencies,<br/>zero warnings/axioms"]
    QA["#19 Final theorem integration<br/>OPEN<br/>native GM and concrete density<br/>outputs missing; runner FAIL / 1"]

    MZ --> ZB
    MZ --> CF
    PZ --> ZT
    PZ --> ST
    ER --> MR
    ER --> TE
    ZB --> LZ
    ZB --> ZT
    ZT --> ST

    VD --> CLV
    MV --> CLV
    HM --> CLV
    AC --> CLV
    ST --> FDT
    VD --> FDT
    CLV --> FDT
    LZ --> FDT
    AC --> FDT
    FDT --> PW
    AC --> PW
    FDT --> DI
    PW --> DI
    ST --> DI
    DI -->|medium Type I| MR
    DI -->|terminal Type I| TE
    DI -->|short branches| FR
    MR --> FR
    TE --> FR
    PW --> FA
    CLV --> FA
    RA --> FA
    FA --> FR
    FR --> ZD
    DY --> ZD

    LZ --> EX
    BR --> EX
    EX --> CT
    AC --> CT
    MV --> HM
    HM --> CT

    MP --> CI
    CI --> CV
    MP --> CV
    MP --> CR
    PZ --> GD
    MZ --> GD
    PZ --> CV
    MZ --> CV
    GD --> CV
    GD --> CR
    ZB --> CV
    LZ --> SS
    MZ --> SS
    SS --> CR
    HY --> AF
    HY --> QD
    DFI --> QD
    PZ --> AF
    MZ --> AF
    MZ --> QD
    AF --> TM
    QD --> TM
    AC --> MS
    MS --> TM

    CT --> TR
    DY --> TR
    ZD -->|Huxley| TR
    CV --> TR
    CR --> TR
    TM --> TR
    TR --> GCS

    GMR --> MX
    GMR --> PS
    GMR --> RF
    GMR --> SF
    GMR --> SL
    GMR --> AT
    GMR --> EG
    HBR --> HB
    MZ --> SF
    MZ --> MX
    MZ --> PS
    MZ --> HB
    MZ --> EN
    MZ --> SL
    MZ --> AT
    MZ --> EG
    PZ --> PS
    PZ --> RF
    SF --> MX
    SF --> PS
    SF --> RF
    SF --> HB
    SF --> EN
    SF --> SL
    SF --> AT
    MX --> PS
    PS --> S2
    RF --> S2
    HB --> S2
    AC --> S2
    HB --> EN
    PS --> SL
    EN --> SL
    SL --> S3
    AT --> S3
    EN --> S3
    HB --> EG
    EN --> EG
    DR --> GM
    CLV --> GM
    MX --> GM
    S2 --> GM
    S3 --> GM
    EG --> GM
    GM -->|GuthMaynardLargeValues| CT
    GM -->|sole premise after #15/#18| GCS
    GCS --> GZD
    GM --> GZD

    ZD -->|Ingham| CB
    GZD --> CB
    CB --> CZD

    DR --> QA
    IG --> QA
    GZD --> QA
    CZD --> QA
    ZB --> QA
    BR --> QA
    GM --> QA

    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef conditional fill:#fff2bf,stroke:#9a6a00,color:#332500,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;

    class ZB,LZ,CF,ZT,ST,VD,CLV,FDT,PW,RA,DI,FA,TE,BR,AC,MV,HM,EX,DY,CI,GD,SS,CR,MS,DR,SF,MX,IG done;
    class CT,TR,CB conditional;
    class MR,FR,ZD,CV,AF,QD,TM,GCS,PS,RF,HB,S2,EN,SL,AT,S3,EG,GM,GZD,CZD,QA open;
    class MZ,PZ,ER,MP,HY,DFI,GMR,HBR available;
