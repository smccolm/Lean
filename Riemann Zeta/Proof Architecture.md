flowchart TD
    MZ["Mathlib APIs<br/>AVAILABLE"]
    ER["PNT+ and expdb source infrastructure<br/>AVAILABLE FOR SELECTIVE PORTING"]

    ZB["Zeta analytic foundations<br/>DONE"]
    LZ["Local zero count<br/>DONE"]
    CF["Mollifier and contour foundations<br/>DONE<br/>retained as optional alternative"]
    ZT["#15 Truncated zeta at zeros<br/>OPEN<br/>uniform Euler-Maclaurin relation"]
    VD["#15 van der Corput and Weyl<br/>OPEN<br/>B/A process instances, exponent pairs<br/>(1/2,1/2) and (1/6,2/3)"]
    CLV["#15 Classical large values<br/>OPEN<br/>full MHH estimate including<br/>T N^4 V^-6"]
    FDT["#15 Finite zero-density transfer<br/>OPEN<br/>separation, Type-I/II alternatives,<br/>Fourier translation, exact sigma"]
    ZD["#15 Ingham and Huxley<br/>OPEN<br/>three endpoint cases DONE;<br/>sigma=3/4 Huxley follows from Ingham"]

    BR["#16 Beta removal<br/>DONE"]
    AC["#17 Coefficient bounds<br/>DONE<br/>divisor count, ordered factorizations,<br/>powered coefficients"]
    MV["Montgomery mean value<br/>DONE"]
    HM["Basic Halasz-Montgomery<br/>DONE"]

    EX["Separated Type-I extraction<br/>DONE"]
    CT["Central Type I<br/>DONE CONDITIONALLY"]
    DY["Slab to symmetric N<br/>DONE"]

    T2["#18 Type II contour inputs<br/>OPEN<br/>coverage, fourth-moment reduction,<br/>twisted fourth moment"]
    TR["Primitive-input transfer<br/>DONE CONDITIONALLY"]
    GCS["#18 Goal C specialization<br/>OPEN"]

    DC["#19 Decoupling<br/>OPEN"]
    GM["#19 GM large values<br/>OPEN"]
    GZD["#19 GM zero density<br/>OPEN"]

    CB["Combined transfer<br/>DONE CONDITIONALLY"]
    CZD["#19 Combined zero density<br/>OPEN"]
    QA["#19 Final verification<br/>OPEN"]

    MZ --> ZB
    MZ --> CF
    ER --> ZT
    ER --> VD
    ZB --> LZ
    ZB --> CF
    ZB --> ZT

    VD --> CLV
    MV --> CLV
    HM --> CLV
    AC --> CLV
    ZT --> FDT
    VD --> FDT
    CLV --> FDT
    LZ --> FDT
    FDT --> ZD
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

    class ZB,LZ,CF,BR,AC,MV,HM,EX,DY done;
    class CT,TR,CB conditional;
    class ZT,VD,CLV,FDT,ZD,T2,GCS,DC,GM,GZD,CZD,QA open;
    class MZ,ER available;
