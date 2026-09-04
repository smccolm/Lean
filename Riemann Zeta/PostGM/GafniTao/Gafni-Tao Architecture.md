flowchart TD

    SRC["SOURCE PIN<br/>Gafni-Tao arXiv 2505.24017v1<br/>Ford, Pintz, Heath-Brown, Wooley"]

    GM["FROZEN GM FOUNDATION<br/>gm-foundation-freeze-v1.0.1<br/>read only"]

    ML["PINNED MATHLIB AND ANALYTIC APIS<br/>measure, zeta, Fourier, contour,<br/>asymptotics, finite combinatorics"]

    DB["SECTION 3 NUMERICAL SOURCES<br/>ANTEDB and pinned source tables"]


    R0["CURRENT RELEASE ROOT<br/>Extension/GafniTao.lean"]

    R1["GT-00 through GT-18<br/>downstream Section 2 machine<br/>ROOT INTEGRATED"]

    R2["Conditional Theorem 1.3 and 1.2<br/>ROOT INTEGRATED"]

    R3["Ford analytic and combinatorial source chain<br/>through Lemma 6.3 and ZeroEnergyLocal<br/>ROOT INTEGRATED"]

    A0["CENTRAL AUDIT<br/>Extension/GafniTao/Audit.lean"]

    A1["Current release-root theorem surface<br/>AUDITED"]

    A2["Native core and Section 3 workbench<br/>CENTRAL AUDIT PENDING"]


    FQ0["QUALITATIVE FORD CHAIN<br/>WORKBENCH"]

    FQ1["Qualitative exponential sum<br/>PROVED"]

    FQ2["Qualitative global zeta growth<br/>PROVED"]

    FQ3["Five-frequency VK detector<br/>PROVED"]

    FQ4["ford_asymptotic_zero_free_native<br/>FordAsymptoticZeroFree<br/>PROVED"]


    PN0["PINTZ NEAR-ONE CHAIN<br/>WORKBENCH"]

    PN1["Corrected Pintz detector<br/>near-one finite envelope<br/>PROVED"]

    PN2["exists_pintz_nearOne_log_density_native<br/>VK count vanishing plus<br/>log-power 524 density bound<br/>PROVED"]


    N0["NATIVE GAFNI-TAO CORE<br/>WORKBENCH"]

    N1["gafniTaoTheorem13_native<br/>exact Theorem 1.3<br/>PROVED"]

    N2["gafniTaoTheorem12_native<br/>exact Theorem 1.2<br/>PROVED"]

    N3["native upper-half max forms<br/>PROVED"]

    N4["gafniTaoTheorem11_guthMaynard_native<br/>A0 = 30/13 specialization<br/>PROVED"]

    N5["All intervals theta > 17/30<br/>PROVED"]

    N6["Almost all theta > 2/15<br/>single measurable density-zero set<br/>PROVED"]


    I0["RELEASE INTEGRATION GATE"]

    I1["Import native core modules<br/>into GafniTao.lean<br/>PENDING"]

    I2["Add native core endpoints<br/>to central Audit.lean<br/>PENDING"]

    I3["Build root and inspect axiom output<br/>PENDING"]


    S0["SECTION 3"]

    S1["PublishedExponentInputs<br/>exact source-facing predicates<br/>DEFINED"]

    S2["Section3Algebra<br/>epsilon removal and exact cells<br/>PROVED"]

    S3["First sample algebra<br/>17/30 gives 7/12<br/>CONDITIONAL"]

    S4["Second sample algebra<br/>2/15 + Delta<br/>Delta <= 1/100<br/>CONDITIONAL"]


    HB0["HEATH-BROWN CAMPAIGN<br/>WORKBENCH"]

    HB1["k-th derivative and pair-count machinery<br/>SUBSTANTIAL"]

    HB2["heathBrownPairCount_card_cast_le_lemma_two<br/>source-scale finite Lemma 2<br/>PROVED"]

    HB3["HeathBrownZeroEnergyBounds<br/>source energy envelope<br/>OPEN"]

    HB4["Unconditional first sample<br/>mu(17/30) <= 7/12<br/>OPEN"]


    P30["PINTZ SECTION 3 CAMPAIGN"]

    P31["PintzFirstDensitySegment<br/>SOURCE PREDICATE"]

    P32["PintzTwentyThreeTwentyFourCutoff<br/>SOURCE PREDICATE OPEN"]

    P33["Unconditional small-Delta sample<br/>OPEN"]


    W0["WOOLEY VMVT CAMPAIGN<br/>WORKBENCH"]

    W1["Source integer sequences and means<br/>boxing and coefficient bridges<br/>PROVED INFRASTRUCTURE"]

    W2["Translation-dilation and conditioning<br/>p-adic separation<br/>PROVED INFRASTRUCTURE"]

    W3["Source Sections 6 through 8<br/>polynomial refinements and arithmetic<br/>ACTIVE"]

    W4["WooleyPolynomialCorollary32<br/>SOURCE TARGET OPEN"]

    W5["wooleyMonomialPadicConcentration<br/>of polynomial Corollary 3.2<br/>BRIDGE PROVED"]

    W6["Critical VMVT consumer<br/>SOURCE CLOSURE ACTIVE"]


    OF0["OPTIMIZED FORD OBJECTIVES<br/>NOT CORE BLOCKERS"]

    OF1["FordTheorem2<br/>optimized 9.463 and 133.66<br/>OPEN"]

    OF2["FordZetaGrowthBound<br/>optimized 76.2 and 4.45<br/>OPEN"]

    OF3["FordNearOneDensityEstimate<br/>optimized 58.05 and log 15<br/>OPEN"]


    G22["GT-22 Published Section 3 inputs<br/>ACTIVE"]

    G23["GT-23 Published sample bounds<br/>ALGEBRA DONE<br/>SOURCE CLOSURE OPEN"]

    G24["GT-24 Full certified optimizer<br/>OPEN"]

    G25["GT-25 Release root and audit synchronization<br/>ACTIVE"]

    G26["GT-26 Publication synchronization<br/>ACTIVE"]


    SRC --> R0
    GM --> R0
    ML --> R0

    R0 --> R1
    R0 --> R3

    R1 --> R2

    R0 --> A0
    A0 --> A1


    SRC --> FQ0
    ML --> FQ0
    R3 --> FQ0

    FQ0 --> FQ1
    FQ1 --> FQ2
    FQ2 --> FQ3
    FQ3 --> FQ4


    SRC --> PN0
    R3 --> PN0
    FQ4 --> PN0

    PN0 --> PN1
    PN1 --> PN2


    R1 --> N0
    PN2 --> N0

    N0 --> N1
    N1 --> N2
    N1 --> N3

    GM --> N4
    N2 --> N4

    N4 --> N5
    N4 --> N6


    N0 --> I0
    N4 --> I0

    I0 --> I1
    I1 --> I2
    I2 --> I3

    I2 --> A2

    I3 --> G25


    N1 --> S0
    SRC --> S0

    S0 --> S1
    S1 --> S2

    S2 --> S3
    S2 --> S4


    SRC --> HB0
    ML --> HB0

    HB0 --> HB1
    HB1 --> HB2
    HB2 --> HB3

    HB3 --> S3
    S3 --> HB4

    HB4 --> G23


    SRC --> P30

    P30 --> P31
    P31 --> P32

    P32 --> S4
    S4 --> P33

    P33 --> G23


    SRC --> W0
    ML --> W0

    W0 --> W1
    W1 --> W2
    W2 --> W3
    W3 --> W4

    W4 --> W5
    W5 --> W6

    W6 -. supports Section 3 source campaign .-> HB3


    SRC --> OF0
    R3 --> OF0

    OF0 --> OF1
    OF1 --> OF2
    OF2 --> OF3

    OF3 -. optimized alternate route .-> PN0


    HB3 --> G22
    P32 --> G22
    W6 --> G22

    G22 --> G23

    DB --> G24
    G23 --> G24

    G25 --> G26
    G23 --> G26
    G24 --> G26


    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef breakthrough fill:#e5f7ea,stroke:#157a3c,color:#102d1c,stroke-width:3px;
    classDef integrated fill:#dff3ff,stroke:#31759b,color:#102b3b,stroke-width:2px;
    classDef conditional fill:#fff0bf,stroke:#9b6a00,color:#3d2900,stroke-width:2px;
    classDef active fill:#ffe4bf,stroke:#b35a00,color:#452000,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef dev fill:#eadcff,stroke:#6840a0,color:#281441,stroke-width:2px;
    classDef sync fill:#f3e4ff,stroke:#7b3ba3,color:#321443,stroke-width:2px;


    class SRC,GM,ML,DB available;

    class R0,R1,R2,R3,A0,A1 integrated;

    class FQ0,PN0,N0 dev;

    class FQ1,FQ2,FQ3,FQ4 breakthrough;
    class PN1,PN2 breakthrough;

    class N1,N2,N3,N4,N5,N6 breakthrough;

    class I0,I1,I2,I3,G25,G26 active;
    class A2 sync;

    class S0,S1 integrated;
    class S2 done;
    class S3,S4 conditional;

    class HB0,HB1 dev;
    class HB2 breakthrough;
    class HB3,HB4 open;

    class P30 dev;
    class P31 integrated;
    class P32,P33 open;

    class W0,W1,W2,W3 dev;
    class W4,W6 open;
    class W5 breakthrough;

    class OF0 active;
    class OF1,OF2,OF3 open;

    class G22 active;
    class G23 conditional;
    class G24 open;