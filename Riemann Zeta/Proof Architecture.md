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
    TE["#15 Terminal Type-I estimate<br/>DONE<br/>uniform prefix Kusmin-Landau,<br/>Abel weight and sharp cutoff"]
    PS["#15 Type-I smoothing and scale split<br/>DONE<br/>exact smooth partition, common block<br/>and cardinality-preserving scale selection"]
    MR["#15 Medium Type-I B-process<br/>DONE<br/>interior source boundary removed exactly;<br/>scaled Poisson, symmetric finite dual window,<br/>exact Mellin retained modes and uniform<br/>Q^-101 M^-100 far tail"]
    FD["#15 Shared Type-I Fourier deweighting<br/>DONE<br/>exact short and reflected log weights<br/>to coefficient-one shifted polynomials"]
    PB["#15 X=1 powered-block MHH theorem<br/>DONE<br/>ordinary sharp-zeta coefficients;<br/>not the dichotomy's actual Type-II cutoff"]
    IIE["#15 Actual Type-II powered MHH application<br/>OPEN - ACCESSIBLE FINITE GLUE<br/>generalize from cutoff X=1 to<br/>X=floor(T^(delta2/2)) and apply certificates"]
    TG["#15 Generic direct Type-I MHH helper<br/>DONE<br/>coefficient-uniform cardinality bound<br/>and abstract certificate projections"]
    ZR["#15 Actual Type-I branch resolution<br/>OPEN<br/>enlarged-interval MHH consumer DONE;<br/>unpack conclusion, link tau to N and T,<br/>discharge majorant and endpoint branches"]
    FR["#15 Branch-to-slab density reduction<br/>OPEN<br/>consume the dichotomy, Type-I and Type-II<br/>cardinality bounds, multiplicity and certificates"]
    ZD["#15 Ingham and Huxley<br/>OPEN<br/>three boundary cases DONE"]

    BR["#16 Beta removal<br/>DONE"]
    AC["#17 Coefficient bounds<br/>DONE"]
    MV["Montgomery mean value<br/>DONE"]
    HM["Basic Halasz-Montgomery<br/>DONE"]
    EX["Separated Type-I extraction<br/>DONE"]
    CT["#19-dependent Central Type I<br/>DONE CONDITIONALLY<br/>only GM large values remains"]
    DY["Slab to symmetric N<br/>DONE"]

    CI["#18 Coverage-range contract repair<br/>DONE<br/>source range Re rho >= 7/10"]
    GD["#18 Uniform vertical Gamma decay<br/>and contour-integrand integrability<br/>DONE"]
    CV["#18 Appendix C contour coverage<br/>DONE<br/>Mellin inversion, zero cancellation,<br/>rectangle shift, residue, quantitative tails<br/>and dyadic dichotomy proved"]
    SS["#18 Scaled weighted separation<br/>and bounded overlap<br/>DONE"]
    CR["#18 Type-II fourth-moment reduction<br/>DONE<br/>Gamma tails, scaled overlap,<br/>and epsilon assembly proved"]
    AF["#18 Smooth zeta-squared AFE<br/>and diagonal bound<br/>OPEN - NEXT CLOSEOUT<br/>finite hm=kn phase, integral and norm bound DONE;<br/>completed-zeta-squared AFE and weighted<br/>asymptotic diagonal OPEN"]
    QD["#18 Quadratic-divisor<br/>off-diagonal theorem<br/>OPEN"]
    MS["#18 M-squared expansion, support,<br/>coefficient bound and moment identity<br/>DONE"]
    TM["#18 Generic short-polynomial<br/>twisted fourth moment and native<br/>specialization<br/>OPEN"]
    TR["#15/#18/#19 primitive-input transfer<br/>DONE CONDITIONALLY<br/>three native inputs remain open"]
    GCS["#18 Goal C specialization<br/>OPEN<br/>derive zero density from GM large values alone"]

    DR["#19 Delete false decoupling contracts<br/>DONE<br/>file, contracts and both axioms removed"]
    SF["#19 Source-facing finite definitions<br/>DONE<br/>affine reindexing, scaling and<br/>seven-bin exact-energy bridge proved"]
    EC["#19 Source endpoint convention<br/>DONE<br/>published target is (N,2N];<br/>closed-interval compatibility also proved"]
    SM["#19 Source polynomial to smooth matrix<br/>DONE<br/>exact three-piece localization,<br/>common one-third subfamily and matrix bound"]
    MX["#19 Sampling matrix and trace reduction<br/>DONE<br/>exact Lemmas 4.1-4.2 and<br/>source-facing entry bridge"]
    PF["#19 Fourier/Poisson foundations<br/>DONE<br/>Schwartz kernels, zero-mode decay,<br/>dilation, Poisson and finite support"]
    HT["#19 Hilbert-Schmidt trace expansion<br/>DONE<br/>exact first-trace Poisson formula,<br/>zero mode and uniform N^-100 tail"]
    UF["#19 Uniform two-parameter Fourier decay<br/>DONE<br/>all derivative orders and explicit<br/>T^-100 far-frequency control"]
    CS["#19 Cubic trace split<br/>DONE<br/>exact Lemma 4.5 Poisson expansion,<br/>diagonal plus T^-100 remainder,<br/>and S1/S2/S3 partition"]
    S1["#19 S1 estimate<br/>DONE<br/>epsilon-separated GM Proposition 5.1<br/>with uniform T^-10 decay"]
    RI["#19 Exact smooth-reflection identities<br/>DONE<br/>signed finite modes, Mellin/Fubini formulas,<br/>and two-sign cancellation-preserving bounds"]
    RF["#19 Quantitative smooth reflection / AFE<br/>OPEN<br/>extract uniform T0^-1/2 factor and<br/>sum omitted modes into T^-100 remainder"]
    HB["#19 Heath-Brown difference-set<br/>mean-square estimate<br/>OPEN"]
    S2["#19 S2 estimate<br/>OPEN"]
    EN["#19 Approximate-energy bridge<br/>and R-sum L2/L4 moments<br/>OPEN"]
    SL["#19 S3 localization<br/>change of variables and tails<br/>OPEN"]
    AT["#19 Affine-transformation estimate<br/>GM Proposition 9.1<br/>OPEN"]
    S3["#19 Refined S3 estimate<br/>GM Proposition 10.1<br/>OPEN"]
    EG["#19 GCD/spacing energy theorem<br/>GM Section 11<br/>OPEN"]
    GM["#19 Exact Guth-Maynard large values<br/>Sections 3 and 12 assembly<br/>OPEN"]
    GZD["#19 Concrete GM zero density<br/>OPEN"]
    CB["#15/#19 combined transfer<br/>DONE CONDITIONALLY<br/>native Ingham and GM inputs open"]
    CZD["#19 Combined zero density<br/>OPEN"]
    IG["#19 Dependency and integrity layer<br/>DONE<br/>1177/1177 dependencies,<br/>zero warnings/axioms"]
    QA["#19 Final theorem integration<br/>OPEN<br/>native GM and concrete density<br/>outputs missing; runner FAIL / 1"]

    MZ --> ZB
    MZ --> CF
    PZ --> ZT
    PZ --> ST
    ER --> TE
    ER --> PS
    ER --> MR
    ER --> FD
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
    DI -->|Type I witness| TE
    TE -->|large witness has N below height| PS
    DI -->|fixed sharp coefficients| FD
    PS -->|medium smooth block| MR
    PS -->|short smooth block| FD
    MR -->|reflected short block| FD
    CLV --> TG
    FA --> TG
    DI -->|actual sharp Type-I witness| ZR
    TE -->|terminal majorant| ZR
    TG --> ZR
    DI -->|Type II witness| IIE
    PW --> PB
    AC --> PB
    CLV --> PB
    PW --> IIE
    AC --> IIE
    CLV --> IIE
    PW --> FA
    CLV --> FA
    RA --> FA
    FA -->|endpoint certificate and scale branches| ZR
    FA --> IIE
    ZR --> FR
    IIE --> FR
    PB -->|raised Type-I scales| FR
    VD -->|Weyl exceptional range| FR
    LZ --> FR
    FDT --> FR
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

    GMR --> EC
    GMR --> SM
    GMR --> MX
    GMR --> PF
    GMR --> RI
    GMR --> RF
    GMR --> SF
    GMR --> SL
    GMR --> AT
    GMR --> EG
    HBR --> HB
    MZ --> SF
    MZ --> EC
    MZ --> SM
    MZ --> MX
    MZ --> PF
    MZ --> HB
    MZ --> EN
    MZ --> SL
    MZ --> AT
    MZ --> EG
    PZ --> PF
    PZ --> RI
    PZ --> RF
    EC --> SM
    SF --> SM
    SF --> MX
    SF --> PF
    SF --> RI
    SF --> RF
    SF --> HB
    SF --> EN
    SF --> SL
    SF --> AT
    MX --> HT
    PF --> HT
    PF --> UF
    PF --> CS
    MX --> CS
    UF -->|Lemma 4.3 truncation| RF
    RI --> RF
    HT --> S1
    UF --> S1
    CS --> S1
    UF --> S2
    RF --> S2
    HB --> S2
    AC --> S2
    HB --> EN
    UF --> SL
    EN --> SL
    SL --> S3
    AT --> S3
    EN --> S3
    HB --> EG
    EN --> EG
    DR --> GM
    CLV --> GM
    MX --> GM
    S1 --> GM
    S2 --> GM
    S3 --> GM
    EG --> GM
    SM --> GM
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

    class ZB,LZ,CF,ZT,ST,VD,CLV,FDT,PW,RA,DI,FA,TE,PS,MR,FD,PB,TG,BR,AC,MV,HM,EX,DY,CI,GD,CV,SS,CR,MS,DR,SF,EC,SM,MX,PF,HT,UF,CS,S1,RI,IG done;
    class CT,TR,CB conditional;
    class ZR,IIE,FR,ZD,AF,QD,TM,GCS,RF,HB,S2,EN,SL,AT,S3,EG,GM,GZD,CZD,QA open;
    class MZ,PZ,ER,MP,HY,DFI,GMR,HBR available;
