flowchart TD

    SRC["SOURCE PIN<br/>Gafni-Tao arXiv 2505.24017v1<br/>Ford, Guth-Maynard, Pintz, Heath-Brown,<br/>Tao-Trudgian-Yang"]

    GM["FROZEN GM FOUNDATION<br/>tag gm-foundation-freeze-v1.0.1<br/>read-only"]

    ML["PINNED MATHLIB / ANALYTIC APIS<br/>measure, Chebyshev psi, zeta,<br/>Fourier, contour, asymptotics"]

    DB["ANTEDB / NUMERICAL SOURCES<br/>Section 3 source tables and<br/>optimizer cross-check only"]


    G00["GT-00 Isolation and source freeze<br/>DONE"]

    G01["GT-01 Exact paper-to-Lean crosswalk<br/>SYNC REQUIRED"]

    G02["GT-02 Asymptotic and exponent language<br/>EReal infimum / supremum<br/>fixed-power and epsilon bridges<br/>SUBSTANTIALLY IMPLEMENTED"]

    G03["GT-03 Exact exceptional set<br/>Lebesgue measure, measurability<br/>mu_delta and mu machinery<br/>DONE"]

    G04["GT-04 Multiplicity-weighted zero model<br/>zero count, occurrences<br/>strip localization<br/>DONE"]

    G05["GT-05 Zero additive energy N*<br/>ordered quadruples, multiplicities<br/>A* exponent machinery<br/>DONE"]

    G06["GT-06 Chebyshev / Mangoldt interval identity<br/>endpoint conventions and prime powers<br/>DONE"]

    G07["GT-07 Brun-Titchmarsh localization<br/>local scale, replacement errors<br/>finite multiplicative cover<br/>DONE"]

    G08["GT-08 Sharp truncated explicit formula<br/>NATIVE DONE<br/>arbitrary real endpoints<br/>all 2 <= T <= x"]


    F0["FORD SOURCE CONTRACTS<br/>OPEN"]

    F1["FordZetaGrowthBound<br/>Ford Theorem 1 contract<br/>OPEN"]

    F2["FordNearOneDensityEstimate<br/>58.05 eta^(3/2), log^15<br/>OPEN"]

    F3["FordAsymptoticZeroFree<br/>VK-width source output<br/>OPEN"]

    F4["FordTheorem2<br/>shifted exponential-sum estimate<br/>9.463 and 133.66<br/>OPEN"]


    FIA["INTEGRATED + CENTRAL-AUDITED<br/>FORD ANALYTIC CHAIN"]

    FIA1["Trigonometric positivity<br/>Fourier kernel<br/>Euler product / prime powers<br/>Ford Lemma 5.1<br/>DONE"]

    FIA2["Cotangent detector kernel<br/>residues and corrections<br/>finite detector rectangles and edges<br/>DONE"]

    FIA3["Left-line analysis<br/>Laplace inversion<br/>K finite rectangles and edges<br/>DONE"]

    FIA4["K zero series and limits<br/>native K-formula<br/>explicit zeta bounds<br/>log-derivative infrastructure<br/>DONE"]


    FIR["NEW ROOT-INTEGRATED<br/>FORD SOURCE CHAIN<br/>CENTRAL AUDIT SYNC PENDING"]

    FIR1["Vinogradov moments and counts<br/>torus Fourier orthogonality<br/>equations 1.3-1.5 infrastructure<br/>ROOT-INTEGRATED"]

    FIR2["Ford Lemma 5.1 source derivation<br/>Holder, fibers, spacing<br/>equations 5.2, 5.3, 5.4<br/>ROOT-INTEGRATED"]

    FIR3["Tent weights, resonance<br/>shift and averaging<br/>real-parameter normalization<br/>ROOT-INTEGRATED"]

    FIR4["Vandermonde and polynomial systems<br/>finite differences, complete counts<br/>prime selection, Newton congruence<br/>ROOT-INTEGRATED"]

    FIRA["Central audit synchronization<br/>for new root-integrated Ford endpoints<br/>PENDING"]


    FD["FORD DEVELOPMENT WORKBENCH<br/>PRESENT IN REPOSITORY<br/>NOT ROOT-INTEGRATED"]

    FD1["Shifted detector rectangles<br/>selected shifts and heights<br/>pole and edge corrections<br/>ACTIVE"]

    FD2["Local zero-disk detector<br/>multiplicity-weighted local count<br/>growth-bound assembly<br/>ACTIVE"]

    FD3["Ford Theorem 2 machinery<br/>dyadic decomposition<br/>cubic exponent and scaling<br/>ACTIVE"]

    FD4["Exact numerical certification<br/>polynomial / Taylor / Bernstein<br/>Lean checks certificate data<br/>ACTIVE"]


    G09["GT-09 Vinogradov-Korobov zero-free input<br/>consumer bridge DONE<br/>SOURCE THEOREM OPEN"]

    G10["GT-10 Near-one logarithmic zero density<br/>normalization bridge DONE<br/>SOURCE THEOREM OPEN"]

    G11["GT-11 Lemma 2.1 right-edge decay<br/>downstream machinery implemented<br/>CONDITIONAL on GT-09 and GT-10"]

    G12["GT-12 Lemma 2.2 L-infinity bound<br/>physical zero-sum supremum<br/>DONE"]

    G13["GT-13 Complex Fourier bump and c_rho<br/>uniform decay and coefficient bounds<br/>DONE"]

    G14["GT-14 Lemma 2.3 L2 bound<br/>physical second moment<br/>epsilon exponent<br/>DONE"]

    G15["GT-15 Schur / energy bridge<br/>pair autocorrelation to actual N*<br/>DONE"]

    G16["GT-16 Lemma 2.4 L4 bound<br/>quartic expansion<br/>multiplicity-weighted A* exponent<br/>DONE"]

    G17["GT-17 Finite J-strip assembly<br/>half-open strips, Markov<br/>equation 2.7<br/>DONE"]

    G18["GT-18 Limit and envelope assembly<br/>epsilon then J<br/>no continuity shortcut<br/>DONE"]

    G19["GT-19 Gafni-Tao Theorem 1.3<br/>conditional max-form implemented<br/>exact unconditional theorem OPEN"]

    G20["GT-20 Theorem 1.2 and Theorem 1.1<br/>conditional Theorem 1.2 max-form exists<br/>exact 1.2 and 1.1 OPEN"]

    G21["GT-21 Native ordinary-density consumer<br/>GM A0 = 30/13<br/>17/30 and 2/15 arithmetic<br/>DONE"]

    G22["GT-22 Published Section 3 inputs<br/>Pintz ordinary density<br/>Heath-Brown A* segment<br/>OPEN"]

    G23["GT-23 Exact published sample bounds<br/>mu(17/30) <= 7/12<br/>small-Delta bound<br/>OPEN"]

    G24["GT-24 Certified Section 3 optimizer<br/>exact finite cells and source tables<br/>OPEN"]

    G25["GT-25 Root imports, audit and release runner<br/>new Ford source chain root-integrated<br/>central audit sync pending<br/>later Ford workbench still outside root<br/>ACTIVE"]

    G26["GT-26 Publication synchronization<br/>README / agenda / architecture / crosswalk<br/>SYNC REQUIRED"]


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


    SRC --> F0
    F0 --> F1
    F0 --> F2
    F0 --> F3
    F0 --> F4


    SRC --> FIA
    ML --> FIA

    FIA --> FIA1
    FIA1 --> FIA2
    FIA2 --> FIA3
    FIA3 --> FIA4


    SRC --> FIR
    ML --> FIR
    FIA1 --> FIR

    FIR --> FIR1
    FIR1 --> FIR2
    FIR2 --> FIR3
    FIR3 --> FIR4
    FIR4 --> FIRA

    FIR2 -. source proof infrastructure .-> F2
    FIR4 -. source proof infrastructure .-> F2
    FIR4 -. source proof infrastructure .-> F4


    SRC --> FD
    FIA4 --> FD
    FIR4 --> FD

    FD --> FD1
    FD1 --> FD2

    FD --> FD3
    FD3 --> FD4

    FD2 -. intended source closure .-> F2
    FD2 -. still consumes growth contract .-> F1

    FD3 -. intended proof route .-> F4
    F4 -. density source input .-> F2

    FIA4 -. source closure work .-> F1
    FIA4 -. source closure work .-> F3


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


    FIA --> G25
    FIR --> G25
    FIRA --> G25
    FD --> G25
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

    class SRC,GM,ML,DB available;

    class G00,G03,G04,G05,G06,G07,G08,G12,G13,G14,G15,G16,G17,G18,G21 done;

    class G02 conditional;
    class G11,G19,G20 conditional;

    class G09,G10,G22,G23,G24,F0,F1,F2,F3,F4 open;

    class FIA,FIA1,FIA2,FIA3,FIA4 done;

    class FIR,FIR1,FIR2,FIR3,FIR4 integrated;
    class FIRA sync;

    class FD,FD1,FD2,FD3,FD4 dev;

    class G25 active;

    class G01,G26 sync;