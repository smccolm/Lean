flowchart TD
    MZ["Mathlib analytic, Fourier,<br/>linear-algebra and combinatorics APIs<br/>AVAILABLE"]
    PZ["Pinned PNT+ zeta, Mellin and<br/>Poisson/Euler-Maclaurin stack<br/>AVAILABLE AND AUDITED"]
    ER["ANTEDB classical zero-density blueprint<br/>AVAILABLE AS REFERENCE"]
    MP["Maynard-Pratt Appendix C<br/>AVAILABLE AS REFERENCE"]
    HY["Hughes-Young twisted fourth moment<br/>AVAILABLE AS REFERENCE"]
    DFI["Duke-Friedlander-Iwaniec<br/>quadratic-divisor theorem<br/>AVAILABLE AS REFERENCE"]
    GMR["Guth-Maynard Sections 3-12<br/>AVAILABLE AS REFERENCE"]

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

    CI["#18 Coverage-range contract repair<br/>OPEN<br/>source range Re rho >= 7/10"]
    GD["#18 Uniform vertical Gamma decay<br/>and contour integrability<br/>OPEN"]
    CV["#18 Appendix C contour coverage<br/>OPEN<br/>Mellin inversion, zero cancellation,<br/>residue and tails"]
    SS["#18 Scaled weighted separation<br/>and bounded overlap<br/>OPEN"]
    CR["#18 Type-II fourth-moment reduction<br/>OPEN"]
    AF["#18 Smooth zeta-squared AFE<br/>and diagonal bound<br/>OPEN"]
    QD["#18 Quadratic-divisor<br/>off-diagonal theorem<br/>OPEN"]
    TM["#18 Generic short-polynomial<br/>twisted fourth moment and M-squared<br/>specialization<br/>OPEN"]
    TR["Primitive-input transfer<br/>DONE CONDITIONALLY<br/>open inputs #15, #18, #19"]
    GCS["#18 Goal C specialization<br/>OPEN<br/>derive zero density from GM large values alone"]

    DR["#19 Delete false decoupling contracts<br/>OPEN<br/>remove both project axioms"]
    MX["#19 Sampling matrix, singular values<br/>and trace-cube reduction<br/>OPEN"]
    PS["#19 Poisson expansion and S1<br/>OPEN"]
    RF["#19 Smooth reflection / AFE<br/>GM Lemma 6.2<br/>OPEN"]
    HB["#19 Heath-Brown difference-set<br/>mean-square estimate<br/>OPEN"]
    S2["#19 S2 estimate<br/>OPEN"]
    AE["#19 Affine transforms, approximate energy<br/>and S3 estimate<br/>OPEN"]
    GM["#19 Guth-Maynard large values<br/>OPEN"]
    GZD["#19 Concrete GM zero density<br/>OPEN"]
    CB["Combined transfer<br/>DONE CONDITIONALLY<br/>open inputs #15 and #19"]
    CZD["#19 Combined zero density<br/>OPEN"]
    QA["#19 Final verification<br/>OPEN<br/>audit clean, zero warnings,<br/>runner PASS / exit 0"]

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
    AC --> TM

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
    GMR --> HB
    GMR --> AE
    MZ --> MX
    MZ --> PS
    MZ --> HB
    MZ --> AE
    PZ --> RF
    MX --> PS
    PS --> S2
    RF --> S2
    HB --> S2
    PS --> AE
    MX --> GM
    S2 --> GM
    AE --> GM
    GM -->|GuthMaynardLargeValues| CT
    GM -->|sole premise after #15/#18| GCS
    GCS --> GZD
    GM --> GZD

    ZD -->|Ingham| CB
    GZD --> CB
    CB --> CZD

    DR --> QA
    GZD --> QA
    CZD --> QA
    ZB --> QA
    BR --> QA
    GM --> QA

    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef conditional fill:#fff2bf,stroke:#9a6a00,color:#332500,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;

    class ZB,LZ,CF,ZT,ST,VD,CLV,FDT,PW,RA,DI,FA,TE,BR,AC,MV,HM,EX,DY done;
    class CT,TR,CB conditional;
    class MR,FR,ZD,CI,GD,CV,SS,CR,AF,QD,TM,GCS,DR,MX,PS,RF,HB,S2,AE,GM,GZD,CZD,QA open;
    class MZ,PZ,ER,MP,HY,DFI,GMR available;
