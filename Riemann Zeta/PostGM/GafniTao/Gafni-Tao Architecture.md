flowchart TD

    SRC["SOURCE PIN<br/>Gafni-Tao arXiv 2505.24017v1<br/>Ford, Pintz, Heath-Brown, Wooley"]

    GM["FROZEN GM FOUNDATION<br/>gm-foundation-freeze-v1.0.1<br/>read only"]

    ML["PINNED MATHLIB AND ANALYTIC APIS<br/>measure, zeta, Fourier, contour,<br/>asymptotics, finite combinatorics"]

    DB["SECTION 3 NUMERICAL SOURCES<br/>ANTEDB and pinned source tables"]


    R0["RELEASE ROOT<br/>Extension/GafniTao.lean"]

    R1["GT-00 through GT-18<br/>Section 2 transfer machine<br/>ROOT INTEGRATED"]

    R2["Native Theorems 1.3 and 1.2<br/>ROOT INTEGRATED"]

    R3["Native Theorem 1.1<br/>GM A0 = 30/13<br/>ROOT INTEGRATED"]

    A0["CENTRAL AUDIT<br/>Extension/GafniTao/Audit.lean"]

    A1["Native core theorem surface<br/>AUDIT ENTRIES PRESENT"]

    A2["Final audit execution and inspection<br/>FINAL RELEASE GATE"]


    FQ0["NATIVE NEAR-ONE CHAIN<br/>ROOT INTEGRATED"]

    FQ1["Qualitative exponential sum<br/>PROVED"]

    FQ2["Qualitative Ford zeta growth<br/>PROVED"]

    FQ3["Five-frequency VK detector<br/>PROVED"]

    FQ4["ford_asymptotic_zero_free_native<br/>PROVED AND AUDITED"]

    PN1["Native Pintz near-one detector<br/>PROVED"]

    PN2["exists_pintz_nearOne_log_density_native<br/>PROVED AND AUDITED"]


    N1["gafniTaoTheorem13_native<br/>exact Theorem 1.3<br/>PROVED AND AUDITED"]

    N2["gafniTaoTheorem12_native<br/>exact Theorem 1.2<br/>PROVED AND AUDITED"]

    N3["native max-form corollaries<br/>PROVED AND AUDITED"]

    N4["gafniTaoTheorem11_guthMaynard_native<br/>PROVED AND AUDITED"]

    N5["All intervals<br/>theta > 17/30<br/>PROVED"]

    N6["Almost all intervals<br/>theta > 2/15<br/>single density-zero set<br/>PROVED"]


    W0["WOOLEY TO HEATH-BROWN CHAIN"]

    W1["Wooley source machinery<br/>PROVED"]

    W2["wooleyPolynomialCorollary32_native<br/>PROVED"]

    W3["p-adic concentration bridge<br/>PROVED"]

    W4["heathBrownVMVTMainConjecture_native<br/>PROVED AND AUDITED"]

    W5["heathBrownKthDerivativeTheorem_native<br/>PROVED AND AUDITED"]


    P0["PINTZ SECTION 3 CHAIN"]

    P1["Native Pintz 2023 source machinery<br/>PROVED"]

    P2["pintzTwentyThreeTwentyFourCutoff_native<br/>PROVED AND AUDITED"]

    P3["Second-sample exponent algebra<br/>PROVED"]

    P4["Public unconditional small-Delta theorem<br/>COMPOSITION PENDING"]


    HB0["HEATH-BROWN ENERGY CAMPAIGN"]

    HB1["Native kth-derivative theorem<br/>PROVED"]

    HB2["Finite pair-count machinery<br/>PROVED / SUBSTANTIAL"]

    HB3["Signed zero-shell energy extraction<br/>PROVED INFRASTRUCTURE"]

    HB4["Exact translation into GM base interval<br/>PROVED AND AUDITED"]

    HB5["Powered GM energy bridge<br/>PROVED AND AUDITED"]

    HB6["HeathBrownZeroEnergyBounds<br/>THREE-CELL ENERGY ENVELOPE<br/>OPEN"]

    HB7["First published sample<br/>mu(17/30) <= 7/12<br/>OPEN"]


    S0["SECTION 3 ALGEBRA"]

    S1["First-sample algebra<br/>PROVED CONDITIONAL ON HB ENERGY"]

    S2["Second-sample algebra<br/>PROVED"]

    S3["Pintz source gate<br/>CLOSED"]

    S4["Heath-Brown source gate<br/>OPEN"]


    OF0["OPTIONAL OPTIMIZED FORD OBJECTIVES"]

    OF1["FordTheorem2<br/>optimized constants<br/>OPEN"]

    OF2["FordZetaGrowthBound<br/>optimized constants<br/>OPEN"]

    OF3["FordNearOneDensityEstimate<br/>optimized constants<br/>OPEN"]

    OF4["Not blockers to native GT core"]


    G22["GT-22 Published Section 3 inputs<br/>ONE MAIN MATHEMATICAL GATE OPEN"]

    G23["GT-23 Published sample bounds<br/>SECOND SOURCE GATE CLOSED<br/>FIRST SOURCE GATE OPEN"]

    G24["GT-24 Full certified optimizer<br/>OPEN"]

    G25["GT-25 Final integration and audit<br/>ACTIVE"]

    G26["GT-26 Publication synchronization<br/>ACTIVE"]


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


    SRC --> P0

    P0 --> P1
    P1 --> P2

    P2 --> S3
    P2 --> P3
    P3 --> P4

    N1 --> P4


    SRC --> HB0
    ML --> HB0

    W5 --> HB1
    HB0 --> HB2
    HB1 --> HB2

    HB2 --> HB3
    HB3 --> HB4
    HB4 --> HB5
    HB5 --> HB6

    HB6 --> S4
    HB6 --> S1

    S1 --> HB7
    N1 --> HB7


    S3 --> S2
    S2 --> P4

    S4 --> G22

    HB7 --> G23
    P4 --> G23


    SRC --> OF0
    OF0 --> OF1
    OF1 --> OF2
    OF2 --> OF3
    OF3 --> OF4


    G22 --> G23

    DB --> G24
    G23 --> G24

    R0 --> G25
    A2 --> G25
    G23 --> G25

    G25 --> G26
    G24 --> G26


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

    class P0,P1,P2 breakthrough;
    class P3,S2,S3 done;
    class P4 conditional;

    class HB0 active;
    class HB1,HB2,HB3,HB4,HB5 breakthrough;
    class HB6,HB7 open;

    class S0 integrated;
    class S1 conditional;
    class S4 open;

    class OF0,OF1,OF2,OF3,OF4 optional;

    class G22 active;
    class G23 conditional;
    class G24 open;

    class A2,G25,G26 active;