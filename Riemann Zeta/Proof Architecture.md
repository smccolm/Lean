flowchart TD
    MZ["Mathlib APIs<br/>AVAILABLE"]
    PZ["Pinned PNT+ sharp-zeta stack<br/>AVAILABLE AND AUDITED"]
    ER["ANTEDB reference material<br/>AVAILABLE FOR SELECTIVE ADAPTATION"]

    ZB["Zeta analytic foundations<br/>DONE"]
    LZ["Local zero count<br/>DONE"]
    CF["Mollifier and contour foundations<br/>DONE<br/>retained as optional alternative"]
    ZT["Exact Abel/Euler-Maclaurin truncation<br/>DONE<br/>error <= ||rho|| b^-beta / beta"]
    ST["Sharp zero truncation<br/>DONE<br/>length a comparable to T,<br/>partial sum <= 149 a^-beta"]
    VD["#15 van der Corput and Weyl<br/>DONE<br/>multi-period B and finite A processes,<br/>(1/6,2/3) exponent, uniform prefixes,<br/>weighted blocks for every sigma >= 0"]
    CLV["#15 Classical large values<br/>DONE<br/>finite MHH theorem including<br/>T N^4 V^-6"]
    MR["#15 Medium Type-I reflection<br/>OPEN<br/>infrastructure DONE; uniform stationary main term,<br/>dual block and controlled losses OPEN"]
    FDT["#15 Finite transfer machinery<br/>DONE<br/>exact-beta removal, multiplicity extraction,<br/>normalization and unrestricted MHH bridge"]
    PW["#15 Exact finite powering<br/>DONE<br/>power identity, factorization bound,<br/>normalized powered-block extraction"]
    RA["#15 Exceptional-range arithmetic<br/>DONE<br/>Ingham short-zeta range empty; Huxley range<br/>empty or below proved Weyl threshold"]
    DI["#15 Finite Type-I/Type-II dichotomy<br/>DONE<br/>pointwise q/2 versus 3/4 split; exact-sigma localization;<br/>multiplicity-dominant branch and common scale;<br/>Type I on (Y,A], Type II on (X,X*Y]"]
    FA["#15 Finite scale/exponent assembly<br/>DONE<br/>MHH exponent, two-or-three scale reduction,<br/>Corollary 11.10 envelope and endpoint certificates"]
    TE["#15 Terminal Type-I estimate<br/>OPEN<br/>Euler-Maclaurin/nonstationary control<br/>for scales comparable to T"]
    FR["#15 Finite zero-density reduction<br/>OPEN<br/>consume detector branches, medium reflection,<br/>terminal estimate and assembly certificates"]
    ZD["#15 Ingham and Huxley<br/>OPEN<br/>three endpoint cases DONE;<br/>sigma=3/4 Huxley follows from Ingham"]

    BR["#16 Beta removal<br/>DONE"]
    AC["#17 Coefficient bounds<br/>DONE<br/>divisor count, ordered factorizations,<br/>powered coefficients"]
    MV["Montgomery mean value<br/>DONE"]
    HM["Basic Halasz-Montgomery<br/>DONE"]

    EX["Separated Type-I extraction<br/>DONE"]
    CT["Central Type I<br/>DONE CONDITIONALLY<br/>only #19 GM large values remains"]
    DY["Slab to symmetric N<br/>DONE"]

    T2["#18 Type II contour inputs<br/>OPEN<br/>coverage, fourth-moment reduction,<br/>twisted fourth moment"]
    TR["Primitive-input transfer<br/>DONE CONDITIONALLY"]
    GCS["#18 Goal C specialization<br/>OPEN"]

    DC["#19 Decoupling<br/>OPEN"]
    RF["#19 Smooth reflection principle<br/>OPEN<br/>approximate functional equation<br/>for GM Section 6"]
    GM["#19 GM large values<br/>OPEN"]
    GZD["#19 GM zero density<br/>OPEN"]

    CB["Combined transfer<br/>DONE CONDITIONALLY"]
    CZD["#19 Combined zero density<br/>OPEN"]
    QA["#19 Final verification<br/>OPEN"]

    MZ --> ZB
    MZ --> CF
    PZ --> ST
    ER --> MR
    ER --> VD
    ER --> DI
    ZB --> LZ
    ZB --> CF
    ZB --> ZT
    ZT --> ST

    VD --> CLV
    MV --> CLV
    HM --> CLV
    AC --> CLV
    ST --> FDT
    VD --> FDT
    VD --> MR
    CLV --> FDT
    LZ --> FDT
    AC --> FDT
    HM --> FDT
    FDT --> PW
    AC --> PW
    FDT --> DI
    PW --> DI
    ST --> DI
    DI -->|medium Type I| MR
    DI -->|terminal Type I| TE
    DI -->|short Type I and Type II| FR
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

    CT --> TR
    DY --> TR
    ZD -->|Huxley| TR
    T2 --> TR

    TR --> GCS
    LZ --> GCS
    ZD --> GCS
    BR --> GCS
    AC --> GCS
    MV --> GCS
    T2 --> GCS

    DC --> GM
    RF --> GM
    GM -->|GuthMaynardLargeValues| CT
    GCS --> GZD
    GM --> GZD

    ZD -->|Ingham| CB
    GZD --> CB
    CB --> CZD

    GZD --> QA
    CZD --> QA
    ZB --> QA
    BR --> QA
    DC --> QA

    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef conditional fill:#fff2bf,stroke:#9a6a00,color:#332500,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;

    class ZB,LZ,CF,ZT,ST,VD,CLV,FDT,PW,RA,DI,FA,BR,AC,MV,HM,EX,DY done;
    class CT,TR,CB conditional;
    class MR,TE,FR,ZD,T2,GCS,DC,RF,GM,GZD,CZD,QA open;
    class MZ,PZ,ER available;
