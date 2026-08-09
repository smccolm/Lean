flowchart TD
    MZ["Mathlib APIs<br/>AVAILABLE"]

    ZB["Zeta analytic foundations<br/>DONE"]
    LZ["Local zero count<br/>DONE"]
    CD["#15 Classical density analysis<br/>OPEN<br/>mollifier algebra, critical-line second moment,<br/>and Jensen bridge DONE;<br/>Littlewood/Gabriel, zeta fourth moment,<br/>right-edge/horizontal estimates,<br/>full MHH N^4 V^-6 branch OPEN"]
    ZD["#15 Ingham and Huxley<br/>OPEN<br/>Ingham sigma=1/2,1 and Huxley sigma=1 DONE;<br/>interior estimates and Huxley sigma=3/4 OPEN"]
    BR["#16 Beta removal<br/>DONE"]
    AC["#17 Coefficient bounds<br/>OPEN"]
    MV["Montgomery mean value<br/>DONE"]

    EX["Separated extraction<br/>DONE"]
    HM["Halasz-Montgomery<br/>DONE"]
    CT["Central Type I<br/>DONE CONDITIONALLY"]
    DY["Slab to symmetric N<br/>DONE"]

    T2["#18 Type II<br/>OPEN"]
    TR["Primitive-input transfer<br/>DONE CONDITIONALLY"]
    GCS["#18 Goal C specialization<br/>OPEN"]

    DC["#19 Decoupling<br/>OPEN"]
    GM["#19 GM large values<br/>OPEN"]
    GZD["#19 GM zero density<br/>OPEN"]

    CB["Combined transfer<br/>DONE CONDITIONALLY"]
    CZD["#19 Combined zero density<br/>OPEN"]
    QA["#19 Final verification<br/>OPEN"]

    MZ --> ZB
    ZB --> LZ
    ZB --> CD
    LZ --> CD
    MV --> CD
    HM --> CD
    AC --> CD
    CD --> ZD
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

    class ZB,LZ,BR,MV,EX,DY done;
    class HM done;
    class CT,TR,CB conditional;
    class CD,ZD,AC,T2,GCS,DC,GM,GZD,CZD,QA open;
    class MZ available;
