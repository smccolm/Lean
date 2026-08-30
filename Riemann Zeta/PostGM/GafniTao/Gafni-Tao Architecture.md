# Gafni-Tao Lean architecture

Status: proposed architecture. Every numbered `GT-*` proof node is open.

The graph is ordered by proof dependency, not by estimated difficulty. The
frozen Guth-Maynard package is an imported dependency and remains read-only.

```mermaid
flowchart TD
    SRC["SOURCE PIN<br/>Gafni-Tao arXiv:2505.24017v1<br/>Guth-Maynard, Heath-Brown, Ford,<br/>Tao-Trudgian-Yang"]
    GM["FROZEN GM FOUNDATION<br/>tag gm-foundation-freeze-v1.0.1<br/>read-only"]
    ML["PINNED MATHLIB / PNT+ APIs<br/>measure, Chebyshev psi, zeta,<br/>Mellin, Fourier, contour"]
    DB["ANTEDB SNAPSHOT<br/>formula/optimizer cross-check only"]

    G00["GT-00 Isolation and source freeze<br/>OPEN"]
    G01["GT-01 Exact paper-to-Lean crosswalk<br/>OPEN"]
    G02["GT-02 Asymptotic and exponent language<br/>EReal infimum/supremum plus epsilon bridges<br/>OPEN"]
    G03["GT-03 Exact exceptional set<br/>Lebesgue measure and measurability<br/>OPEN"]
    G04["GT-04 Multiplicity-weighted zero model<br/>N bridge and strip localization<br/>OPEN"]
    G05["GT-05 Zero additive energy N*<br/>quadruple multiplicities and A*<br/>OPEN"]
    G06["GT-06 Chebyshev interval identity<br/>(x,x+y], endpoints and prime powers<br/>OPEN"]
    G07["GT-07 Brun-Titchmarsh localization<br/>tau=X^(1-theta), local covering and losses<br/>OPEN"]
    G08["GT-08 Sharp truncated explicit formula<br/>T=J log(X)^2 tau and full error ledger<br/>OPEN"]
    G09["GT-09 Vinogradov-Korobov zero-free region<br/>OPEN"]
    G10["GT-10 Near-one logarithmic zero density<br/>no T^epsilon substitute<br/>OPEN"]
    G11["GT-11 Lemma 2.1 right-edge decay<br/>OPEN"]
    G12["GT-12 Lemma 2.2 L-infinity bound<br/>OPEN"]
    G13["GT-13 Complex Fourier bump and c_rho<br/>decay, normalization and Fubini<br/>OPEN"]
    G14["GT-14 Lemma 2.3 L2 bound<br/>unit local zero count<br/>OPEN"]
    G15["GT-15 Schur/double-counting energy bridge<br/>smoothed quadruple sum to N*<br/>OPEN"]
    G16["GT-16 Lemma 2.4 L4 bound<br/>OPEN"]
    G17["GT-17 Finite J-strip assembly<br/>pigeonhole, Markov and Eq. (2.7)<br/>OPEN"]
    G18["GT-18 Limit and envelope assembly<br/>epsilon then J; no continuity shortcut<br/>OPEN"]
    G19["GT-19 Gafni-Tao Theorem 1.3<br/>exact refined bound<br/>OPEN"]
    G20["GT-20 Theorem 1.2 and Theorem 1.1<br/>exact corollaries<br/>OPEN"]
    G21["GT-21 Native ordinary-density consumer<br/>GM A0=30/13, 17/30 and 2/15 thresholds<br/>OPEN"]
    G22["GT-22 Published exponent inputs<br/>Pintz ordinary and Heath-Brown A* segments;<br/>optional full TT-Y table<br/>OPEN"]
    G23["GT-23 Exact sample bounds<br/>mu(17/30)<=7/12 and<br/>mu(2/15+Delta)<=1-9Delta/13<br/>OPEN"]
    G24["GT-24 Certified Section 3 optimizer<br/>exact rational cells and source table checks<br/>OPEN"]
    G25["GT-25 Root imports, audits and runner<br/>zero warnings / no forbidden dependencies<br/>OPEN"]
    G26["GT-26 Publication synchronization<br/>crosswalk, exposition and reproduction log<br/>OPEN"]

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

    SRC --> G09
    SRC --> G10
    ML --> G09
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
    G21 --> G23
    G22 --> G23
    DB --> G24
    G19 --> G24
    G22 --> G24

    G19 --> G25
    G20 --> G25
    G21 --> G25
    G23 --> G25
    G24 --> G25
    G25 --> G26

    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b,stroke-width:2px;
    classDef available fill:#dcecff,stroke:#245b9e,color:#0d2542,stroke-width:2px;
    class SRC,GM,ML,DB available;
    class G00,G01,G02,G03,G04,G05,G06,G07,G08,G09,G10,G11,G12,G13,G14,G15,G16,G17,G18,G19,G20,G21,G22,G23,G24,G25,G26 open;
```

## Proposed isolated Lean modules

The implementation should be a separate package at
`PostGM/GafniTao/Extension/`, pinned to the frozen foundation rather than the
moving workspace root.

| Module | Owns |
| --- | --- |
| `GafniTao.Asymptotics` | parameter-dependent big-O, epsilon-power bounds, `EReal` exponent infima/suprema and limiting bridges |
| `GafniTao.ExceptionalSet` | exact `(x,x+x^theta]` Mangoldt discrepancy, measurable exceptional set, `mu_delta`, `mu` |
| `GafniTao.Zeros` | frozen `N` bridge, multiplicity-weighted finite zero sums, real-part strips |
| `GafniTao.ZeroEnergy` | exact `N*`, `A*`, monotonicity and finite-energy bridges |
| `GafniTao.ChebyshevIntervals` | `psi` difference identity, floor/endpoints and prime powers |
| `GafniTao.BrunTitchmarsh` | local replacement of `x^theta` by `x/tau` and finite covering |
| `GafniTao.ExplicitFormula` | sharp truncated formula and all boundary/error terms |
| `GafniTao.NearOne` | Vinogradov-Korobov region, logarithmic density, Lemma 2.1 |
| `GafniTao.ZeroSumSup` | equation (2.4) and Lemma 2.2 |
| `GafniTao.ZeroSumL2` | complex Fourier bump, coefficient bounds, local zero count, Lemma 2.3 |
| `GafniTao.ZeroSumL4` | pair-count function, Schur test, `N*` bridge, Lemma 2.4 |
| `GafniTao.RefinedBound` | equations (2.1)-(2.7), strip split, Markov, limits, Theorems 1.2-1.3 |
| `GafniTao.NativeInputs` | actual frozen GM and published Pintz/Heath-Brown/TT-Y consumers |
| `GafniTao.Corollaries` | Theorem 1.1 thresholds and exact Section 3 sample bounds |
| `GafniTao.Optimizer` | optional exact rational certification of the complete Section 3 table/figure envelope |
| `GafniTao.Audit` | explicit `#print axioms` list for every public and agenda-critical theorem |
| `GafniTao.lean` | imports every production module in the isolated package |

## Public acceptance layer

Names may change after exact type design, but the final public layer must contain
the following mathematical objects rather than theorem-equivalent hypotheses:

- `shortIntervalExceptionalSet delta X theta` with Lebesgue measure;
- `exceptionalExponentDelta delta theta` and `exceptionalExponent theta`, with
  the paper's empty-set/`-infinity` convention;
- `zeroDensityExponent sigma` for the actual multiplicity count `N`;
- `zeroAdditiveEnergyCount sigma T` and `zeroAdditiveEnergyExponent sigma` for
  the actual four-zero count;
- `gafniTao_refined_bound_native`, equivalent to Theorem 1.3;
- `gafniTao_general_bound_native`, equivalent to Theorem 1.2;
- `gafniTao_zero_density_short_intervals_native`, equivalent to Theorem 1.1;
- `gafniTao_seventeen_thirtieth_native` proving
  `mu(17/30) <= 7/12`;
- `gafniTao_near_two_fifteenths_native` proving the quantified small-positive-
  `Delta` bound `mu(2/15+Delta) <= 1-9 Delta/13`.

A theorem parameter may expose a narrower source estimate while developing a
consumer, but a node is not done until the final native theorem derives that
estimate from the actual formalized source input.
