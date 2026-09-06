flowchart TD

    SRC["SOURCE PIN<br/>Gafni-Tao arXiv 2505.24017v1<br/>Ford, Pintz, Heath-Brown, Wooley"]

    GM["FROZEN GM FOUNDATION<br/>gm-foundation-freeze-v1.0.1<br/>read only"]

    ML["PINNED MATHLIB AND ANALYTIC APIS<br/>measure, zeta, Fourier, contour,<br/>asymptotics, finite combinatorics"]

    DB["OPTIONAL SECTION 3 NUMERICAL SOURCES<br/>ANTEDB and pinned source tables"]


    R0["RELEASE ROOT<br/>Extension/GafniTao.lean"]

    R1["GT-00 through GT-18<br/>Section 2 transfer machine<br/>ROOT INTEGRATED"]

    R2["Native Theorems 1.3 and 1.2<br/>ROOT INTEGRATED"]

    R3["Native Theorem 1.1<br/>GM A0 = 30/13<br/>ROOT INTEGRATED"]

    A0["CENTRAL AUDIT<br/>Extension/GafniTao/Audit.lean"]

    A1["Native core theorem surface<br/>AUDIT ENTRIES PRESENT"]

    A2["Final build and axiom-output inspection<br/>FINAL RELEASE GATE"]


    FQ0["NATIVE NEAR-ONE CHAIN<br/>ROOT INTEGRATED"]

    FQ1["Qualitative exponential sum<br/>PROVED"]

    FQ2["Qualitative Ford zeta growth<br/>PROVED"]

    FQ3["Five-frequency VK detector<br/>PROVED"]

    FQ4["ford_asymptotic_zero_free_native<br/>PROVED AND AUDITED"]

    PN1["Native Pintz near-one detector<br/>PROVED"]

    PN2["exists_pintz_nearOne_log_density_native<br/>PROVED AND AUDITED"]


    N1["gafniTaoTheorem13_native<br/>exact Theorem 1.3<br/>PROVED AND AUDITED"]

    N2["gafniTaoTheorem12_native<br/>exact Theorem 1.2<br/>PROVED AND AUDITED"]

    N3["Native max-form corollaries<br/>PROVED AND AUDITED"]

    N4["gafniTaoTheorem11_guthMaynard_native<br/>PROVED AND AUDITED"]

    N5["All intervals<br/>theta > 17/30<br/>PROVED"]

    N6["Almost all intervals<br/>theta > 2/15<br/>single density-zero set<br/>PROVED"]


    W0["WOOLEY TO HEATH-BROWN CHAIN"]

    W1["Wooley source Corollary 3.2<br/>PROVED"]

    W2["p-adic concentration bridge<br/>PROVED"]

    W3["VMVT main conjecture<br/>PROVED"]

    W4["heathBrownVMVTMainConjecture_native<br/>PROVED AND AUDITED"]

    W5["heathBrownKthDerivativeTheorem_native<br/>PROVED AND AUDITED"]


    P0["PINTZ SECTION 3 CHAIN"]

    P1["Native Pintz 2023 source machinery<br/>PROVED"]

    P2["pintzTwentyThreeTwentyFourCutoff_native<br/>PROVED AND AUDITED"]

    P3["Second-sample exponent algebra<br/>PROVED"]

    P4["exceptionalExponent_two_fifteenths_add_le_native<br/>PROVED IN WORKBENCH"]

    P5["Second-sample release promotion<br/>PENDING"]


    HB0["HEATH-BROWN ENERGY CHAIN"]

    HB1["Native kth-derivative theorem<br/>PROVED"]

    HB2["Pair-count and zero-shell machinery<br/>PROVED / SUBSTANTIAL"]

    HB3["Exact GM interval translation<br/>PROVED AND AUDITED"]

    HB4["Powered GM energy bridge<br/>PROVED AND AUDITED"]

    HB5["First HB energy cell<br/>1/2 <= sigma <= 2/3<br/>PROVED IN WORKBENCH"]

    HB6["Second HB energy cell<br/>2/3 < sigma <= 3/4<br/>PROVED IN WORKBENCH"]

    HB7["Full third high-range cell<br/>OPEN / ACTIVE"]

    HB8["Full HeathBrownZeroEnergyBounds<br/>STRONGER OPTIONAL TARGET"]


    S0["FIRST PUBLISHED SAMPLE"]

    S1["Optimizer confined near 7/10<br/>hence below 3/4<br/>PROVED"]

    S2["first_sample_fixed_epsilon_bound_native<br/>PROVED"]

    S3["refinedExceptionalUpperExponent<br/>17/30 <= 7/12<br/>PROVED"]

    S4["exceptionalExponent_seventeen_thirtieths_le_native<br/>mu(17/30) <= 7/12<br/>PROVED IN WORKBENCH"]

    S5["First-sample release promotion<br/>PENDING"]


    RI0["SECTION 3 RELEASE GATE"]

    RI1["Import HeathBrownZeroEnergyLowNative<br/>PENDING"]

    RI2["Import Section3NativeSamples<br/>PENDING"]

    RI3["Add sample endpoints to central Audit.lean<br/>PENDING"]

    RI4["Build and inspect dependency output<br/>PENDING"]


    OF0["OPTIONAL OPTIMIZED FORD OBJECTIVES"]

    OF1["FordTheorem2<br/>optimized constants<br/>OPEN"]

    OF2["FordZetaGrowthBound<br/>optimized constants<br/>OPEN"]

    OF3["FordNearOneDensityEstimate<br/>optimized constants<br/>OPEN"]

    OF4["Not blockers to current GT results"]


    OPT0["OPTIONAL FULL SECTION 3 ENVELOPE"]

    OPT1["Complete high HB energy cell<br/>OPEN"]

    OPT2["Full three-cell HB envelope<br/>OPEN"]

    OPT3["Pinned numerical source tables<br/>OPEN"]

    OPT4["Certified finite optimizer<br/>OPEN"]


    G22["GT-22 Published source inputs<br/>DISPLAYED SAMPLE INPUTS CLOSED"]

    G23["GT-23 Published sample bounds<br/>BOTH PROVED IN WORKBENCH"]

    G24["GT-24 Full certified optimizer<br/>OPTIONAL / OPEN"]

    G25["GT-25 Section 3 release integration<br/>ACTIVE"]

    G26["GT-26 Final publication synchronization<br/>ACTIVE"]


    SRC --> R0
    GM --> R0
    ML --> R0

    R0 --> R1
    R0 --> R2
    R0 --> R3

    R0 --> A0
    A0 --> A1
    A1 --> A2


    SRC --> FQ0
    ML --> FQ0

    FQ0 --> FQ1
    FQ1 --> FQ2
    FQ2 --> FQ3
    FQ3 --> FQ4

    FQ4 --> PN1
    PN1 --> PN2

    PN2 --> N1
    R1 --> N1

    N1 --> N2
    N1 --> N3

    GM --> N4
    N2 --> N4

    N4 --> N5
    N4 --> N6


    SRC --> W0
    ML --> W0

    W0 --> W1
    W1 --> W2
    W2 --> W3
    W3 --> W4
    W4 --> W5


    SRC --> HB0
    ML --> HB0

    W5 --> HB1
    HB1 --> HB2
    HB2 --> HB3
    HB3 --> HB4

    HB4 --> HB5
    HB4 --> HB6

    HB6 --> HB7

    HB5 --> HB8
    HB6 --> HB8
    HB7 --> HB8


    HB5 --> S1
    HB6 --> S1

    S1 --> S2
    S2 --> S3

    N1 --> S4
    S3 --> S4


    SRC --> P0

    P0 --> P1
    P1 --> P2
    P2 --> P3

    N1 --> P4
    P3 --> P4


    HB5 --> G22
    HB6 --> G22
    P2 --> G22

    S4 --> G23
    P4 --> G23


    S4 --> RI0
    P4 --> RI0

    RI0 --> RI1
    RI1 --> RI2
    RI2 --> RI3
    RI3 --> RI4

    RI4 --> G25

    S5 --> G25
    P5 --> G25

    RI2 --> S5
    RI2 --> P5


    SRC --> OF0
    OF0 --> OF1
    OF1 --> OF2
    OF2 --> OF3
    OF3 --> OF4


    SRC --> OPT0
    DB --> OPT0

    HB7 --> OPT1
    OPT1 --> OPT2
    OPT2 --> OPT3
    OPT3 --> OPT4

    OPT4 --> G24


    G22 --> G23
    G23 --> G25

    G25 --> G26
    G24 --> G26
    A2 --> G26


    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef breakthrough fill:#e5f7ea,stroke:#157a3c,color:#102d1c,stroke-width:3px;
    classDef integrated fill:#dff3ff,stroke:#31759b,color:#102b3b,stroke-width:2px;
    classDef conditional fill:#fff0bf,stroke:#9b6a00,color:#3d2900,stroke-width:2px;
    classDef active fill:#ffe4bf,stroke:#b35a00,color:#452000,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef optional fill:#eeeeee,stroke:#777777,color:#222222,stroke-width:2px;


    class SRC,GM,ML,DB available;

    class R0,R1,R2,R3,A0,A1 integrated;

    class FQ0,FQ1,FQ2,FQ3,FQ4 breakthrough;
    class PN1,PN2 breakthrough;

    class N1,N2,N3,N4,N5,N6 breakthrough;

    class W0,W1,W2,W3,W4,W5 breakthrough;

    class P0,P1,P2,P3,P4 breakthrough;
    class P5 active;

    class HB0,HB1,HB2,HB3,HB4 breakthrough;
    class HB5,HB6 breakthrough;
    class HB7 open;
    class HB8 optional;

    class S0,S1,S2,S3,S4 breakthrough;
    class S5 active;

    class RI0,RI1,RI2,RI3,RI4 active;

    class OF0,OF1,OF2,OF3,OF4 optional;
    class OPT0,OPT1,OPT2,OPT3,OPT4 optional;

    class G22 done;
    class G23 breakthrough;
    class G24 optional;

    class G25,G26,A2 active;