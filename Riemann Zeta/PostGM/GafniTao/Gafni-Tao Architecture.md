flowchart TD

    SRC["SOURCE PIN<br/>Gafni-Tao arXiv 2505.24017v1<br/>Ford, Guth-Maynard, Pintz, Heath-Brown,<br/>Tao-Trudgian-Yang"]

    GM["FROZEN GM FOUNDATION<br/>tag gm-foundation-freeze-v1.0.1<br/>read-only"]

    ML["PINNED MATHLIB / ANALYTIC APIS<br/>measure, Chebyshev psi, zeta,<br/>Fourier, contour, asymptotics"]

    DB["ANTEDB / NUMERICAL SOURCES<br/>Section 3 source tables and<br/>optimizer cross-check only"]


    G00["GT-00 Isolation and source freeze<br/>DONE"]

    G01["GT-01 Exact paper-to-Lean crosswalk<br/>SYNC REQUIRED"]

    G02["GT-02 Asymptotic and exponent language<br/>EReal infimum / supremum<br/>fixed-power and epsilon bridges<br/>SUBSTANTIALLY IMPLEMENTED"]

    G03["GT-03 Exact exceptional set<br/>Lebesgue measure and measurability<br/>mu_delta and mu machinery<br/>DONE"]

    G04["GT-04 Multiplicity-weighted zero model<br/>zero count and occurrences<br/>strip localization<br/>DONE"]

    G05["GT-05 Zero additive energy N*<br/>ordered quadruples and multiplicities<br/>A* exponent machinery<br/>DONE"]

    G06["GT-06 Chebyshev / Mangoldt interval identity<br/>endpoint conventions and prime powers<br/>DONE"]

    G07["GT-07 Brun-Titchmarsh localization<br/>local scale and replacement errors<br/>finite multiplicative cover<br/>DONE"]

    G08["GT-08 Sharp truncated explicit formula<br/>NATIVE DONE<br/>arbitrary real endpoints<br/>all 2 <= T <= x"]


    F0["OPTIMIZED FORD SOURCE CONTRACTS"]

    F1["FordZetaGrowthBound<br/>76.2 and 4.45<br/>OPEN"]

    F2["FordNearOneDensityEstimate<br/>58.05 eta^(3/2), log^15<br/>OPEN"]

    F3["FordAsymptoticZeroFree<br/>positive VK width<br/>OPEN"]

    F4["FordTheorem2<br/>9.463 and 133.66<br/>OPEN"]


    FIA["ROOT-INTEGRATED FORD ANALYTIC CHAIN"]

    FIA1["Trigonometric positivity<br/>Fourier kernel<br/>Euler product / prime powers<br/>Ford Lemma 5.1"]

    FIA2["Cotangent detector<br/>residues and corrections<br/>finite detector rectangles and edges"]

    FIA3["Left-line analysis<br/>Laplace inversion<br/>K-function contour machinery"]

    FIA4["K zero series and limits<br/>native K-formula<br/>explicit zeta and log-derivative infrastructure"]


    FIC["ROOT-INTEGRATED FORD COMBINATORIAL CHAIN"]

    FIC1["Vinogradov moments and counts<br/>Holder and fibre decomposition<br/>equations 5.2, 5.3, 5.4"]

    FIC2["Vandermonde and polynomial systems<br/>finite differences and complete counts<br/>prime selection and Newton congruence"]

    FIC3["Power-residue fibres<br/>Jacobian avoidance<br/>prime-power Newton and lifts"]

    FIC4["B-star and collision counts<br/>S3 / S4 / S6 machinery<br/>equations 3.4 and 3.7"]

    FIC5["Maximal K and repeated coordinates<br/>good-prime equation 3.3<br/>Ford Lemma 3.2 source assembly"]

    FIC6["Ford Lemma 3.3 finite source<br/>Lemma 3.4 exponent machinery<br/>effective canonical prime packet"]

    FIC7["Count monotonicity<br/>Lemma 6.3 moment-integral entry<br/>ROOT FRONTIER"]


    AUD["CENTRAL AUDIT"]

    AUD1["Downstream GT chain<br/>AUDITED"]

    AUD2["Ford analytic chain<br/>AUDITED"]

    AUD3["Lemma 3.3 and Lemma 3.4 arithmetic<br/>prime packet and count monotonicity<br/>AUDITED"]

    AUD4["Some Lemma 3.2 / Lemma 6.3 endpoints<br/>AUDIT SYNC STILL REQUIRED"]


    FQ["QUALITATIVE FORD WORKBENCH<br/>PROVED IN FILES<br/>NOT ROOT-INTEGRATED"]

    FQ1["Complete qualitative exponential sum<br/>ford_exponential_sum_qualitative<br/>D = 3000000"]

    FQ2["Qualitative Richert-Ford zeta growth<br/>ford_qualitative_general_zeta_growth<br/>explicit positive A and B"]

    FQ3["General local zero-count theorem<br/>multiplicity-weighted<br/>explicit Richert majorant"]

    FQ4["Potential qualitative zero-free closure<br/>NEXT HIGH-VALUE TARGET"]


    FO["OPTIMIZED FORD WORKBENCH"]

    FO1["Ford Theorem 2 exact constants<br/>9.463 / 133.66<br/>ACTIVE"]

    FO2["Optimized zeta-growth constants<br/>76.2 / 4.45<br/>ACTIVE"]

    FO3["Near-one density coefficient<br/>58.05<br/>OPEN"]


    G09["GT-09 Vinogradov-Korobov zero-free input<br/>consumer bridge DONE<br/>SOURCE OUTPUT OPEN"]

    G10["GT-10 Near-one logarithmic density<br/>normalization bridge DONE<br/>SOURCE OUTPUT OPEN"]

    G11["GT-11 Lemma 2.1 right-edge decay<br/>downstream machinery implemented<br/>CONDITIONAL on GT-09 and GT-10"]

    G12["GT-12 Lemma 2.2 L-infinity bound<br/>physical zero-sum supremum<br/>DONE"]

    G13["GT-13 Complex Fourier bump and c_rho<br/>uniform decay and coefficient bounds<br/>DONE"]

    G14["GT-14 Lemma 2.3 L2 bound<br/>physical second moment<br/>epsilon exponent<br/>DONE"]

    G15["GT-15 Schur / energy bridge<br/>pair autocorrelation to actual N*<br/>DONE"]

    G16["GT-16 Lemma 2.4 L4 bound<br/>quartic expansion<br/>multiplicity-weighted A* exponent<br/>DONE"]

    G17["GT-17 Finite J-strip assembly<br/>half-open strips and Markov<br/>equation 2.7<br/>DONE"]

    G18["GT-18 Limit and envelope assembly<br/>epsilon then J<br/>no continuity shortcut<br/>DONE"]

    G19["GT-19 Gafni-Tao Theorem 1.3<br/>conditional max-form implemented<br/>exact unconditional theorem OPEN"]

    G20["GT-20 Theorem 1.2 and Theorem 1.1<br/>conditional Theorem 1.2 max-form exists<br/>exact 1.2 and 1.1 OPEN"]

    G21["GT-21 Native ordinary-density consumer<br/>GM A0 = 30/13<br/>17/30 and 2/15 arithmetic<br/>DONE"]

    G22["GT-22 Published Section 3 inputs<br/>Pintz ordinary density<br/>Heath-Brown A* segment<br/>OPEN"]

    G23["GT-23 Published sample bounds<br/>mu(17/30) <= 7/12<br/>small-Delta bound<br/>OPEN"]

    G24["GT-24 Certified Section 3 optimizer<br/>exact finite cells and source tables<br/>OPEN"]

    G25["GT-25 Integration and release audit<br/>qualitative Ford chain outside root<br/>some audit synchronization pending<br/>ACTIVE"]

    G26["GT-26 Publication synchronization<br/>README / agenda / architecture / crosswalk<br/>ACTIVE"]


    SRC --> G00
    GM --> G00
    ML --> G00

    G00 --> G01

    G01 --> G02
    G01 --> G03
    G01 --> G04
    G01 --> G06

    GM --> G04
    G04 --> G05

    ML --> G06
    G03 --> G07
    G06 --> G07

    G07 --> G08
    ML --> G08


    SRC --> FIA
    ML --> FIA

    FIA --> FIA1
    FIA1 --> FIA2
    FIA2 --> FIA3
    FIA3 --> FIA4


    SRC --> FIC
    ML --> FIC
    FIA1 --> FIC1

    FIC --> FIC1
    FIC1 --> FIC2
    FIC2 --> FIC3
    FIC3 --> FIC4
    FIC4 --> FIC5
    FIC5 --> FIC6
    FIC6 --> FIC7


    FIA --> AUD2
    FIC6 --> AUD3
    FIC7 --> AUD4

    G08 --> AUD1
    G18 --> AUD1
    G19 --> AUD1


    SRC --> FQ
    FIA4 --> FQ
    FIC7 --> FQ

    FQ --> FQ1
    FQ1 --> FQ2
    FQ2 --> FQ3
    FQ3 --> FQ4


    SRC --> FO
    FIC7 --> FO

    FO --> FO1
    FO1 --> FO2
    FO2 --> FO3


    SRC --> F0
    F0 --> F1
    F0 --> F2
    F0 --> F3
    F0 --> F4

    FQ1 -. qualitative analogue .-> F4
    FQ2 -. qualitative analogue .-> F1
    FQ4 -. intended existential closure .-> F3

    FO1 -. intended exact closure .-> F4
    FO2 -. intended exact closure .-> F1
    FO3 -. intended exact closure .-> F2


    F3 --> G09
    ML --> G09

    F2 --> G10
    G04 --> G10

    G08 --> G11
    G09 --> G11
    G10 --> G11

    G02 --> G12
    G04 --> G12
    G08 --> G12

    ML --> G13
    G08 --> G13

    G13 --> G14
    G04 --> G14

    G05 --> G15
    G13 --> G15

    G15 --> G16

    G03 --> G17
    G11 --> G17
    G12 --> G17
    G14 --> G17
    G16 --> G17

    G02 --> G18
    G17 --> G18

    G18 --> G19
    G19 --> G20


    GM --> G21
    G20 --> G21

    SRC --> G22
    G05 --> G22

    G19 --> G23
    G21 --> G23
    G22 --> G23

    DB --> G24
    G19 --> G24
    G22 --> G24


    AUD --> G25
    AUD1 --> G25
    AUD2 --> G25
    AUD3 --> G25
    AUD4 --> G25

    FQ --> G25
    FO --> G25
    G19 --> G25
    G20 --> G25
    G21 --> G25
    G23 --> G25
    G24 --> G25

    G25 --> G26


    classDef done fill:#d7f5dd,stroke:#187a2f,color:#102814,stroke-width:2px;
    classDef conditional fill:#fff0bf,stroke:#9b6a00,color:#3d2900,stroke-width:2px;
    classDef active fill:#ffe4bf,stroke:#b35a00,color:#452000,stroke-width:2px;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    classDef dev fill:#eadcff,stroke:#6840a0,color:#281441,stroke-width:2px;
    classDef sync fill:#f3e4ff,stroke:#7b3ba3,color:#321443,stroke-width:2px;
    classDef integrated fill:#dff3ff,stroke:#31759b,color:#102b3b,stroke-width:2px;
    classDef breakthrough fill:#e5f7ea,stroke:#157a3c,color:#102d1c,stroke-width:3px;


    class SRC,GM,ML,DB available;

    class G00,G03,G04,G05,G06,G07,G08,G12,G13,G14,G15,G16,G17,G18,G21 done;

    class G02 conditional;
    class G11,G19,G20 conditional;

    class G09,G10,G22,G23,G24,F0,F1,F2,F3,F4 open;

    class FIA,FIA1,FIA2,FIA3,FIA4 integrated;
    class FIC,FIC1,FIC2,FIC3,FIC4,FIC5,FIC6,FIC7 integrated;

    class AUD,AUD1,AUD2,AUD3 integrated;
    class AUD4 sync;

    class FQ dev;
    class FQ1,FQ2,FQ3 breakthrough;
    class FQ4 active;

    class FO,FO1,FO2,FO3 active;

    class G25,G26 active;