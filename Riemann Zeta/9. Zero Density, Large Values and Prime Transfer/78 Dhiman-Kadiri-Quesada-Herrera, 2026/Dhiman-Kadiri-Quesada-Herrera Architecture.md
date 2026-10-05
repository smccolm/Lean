# Proof architecture

**PLANNING ONLY. 0/20 proof gates complete.** All numbered nodes are future obligations. Existing proved libraries feed these nodes through adapters; no edge denotes a new installed import.

```mermaid
flowchart TD
  G01["DKKH-01 Source edition and errata<br/>OPEN"]
  G02["DKKH-02 Actual objects and conventions<br/>OPEN"]
  G03["DKKH-03 Harmonic and digamma estimates<br/>OPEN"]
  G04["DKKH-04 Finite exponential sums<br/>OPEN"]
  G05["DKKH-05 Oscillatory tails<br/>OPEN"]
  G06["DKKH-06 Stationary phase and weighted integrals<br/>OPEN"]
  G07["DKKH-07 Explicit χ and gamma constants<br/>OPEN"]
  G08["DKKH-08 Theorem 8 Part I<br/>OPEN"]
  G09["DKKH-09 Theorem 8 Part II<br/>OPEN"]
  G10["DKKH-10 Poisson corollaries<br/>OPEN"]
  G11["DKKH-11 Explicit B-process<br/>OPEN"]
  G12["DKKH-12 Theorem 9 AFE1<br/>OPEN"]
  G13["DKKH-13 Corollary 0.3 and AFE1 constants<br/>OPEN"]
  G14["DKKH-14 Theorem 10 direct branch<br/>OPEN"]
  G15["DKKH-15 Theorem 10 reflected branch<br/>OPEN"]
  G16["DKKH-16 Corollary 0.4 / Table 1<br/>OPEN"]
  G17["DKKH-17 Corollary 0.5 / Tables 2–3<br/>OPEN"]
  G18["DKKH-18 Reuse and package integration<br/>OPEN"]
  G19["DKKH-19 Semantic regressions and audit<br/>OPEN"]
  G20["DKKH-20 Final sequential verification<br/>OPEN"]
  G01 --> G02
  G02 --> G03
  G02 --> G04
  G03 --> G05
  G04 --> G05
  G02 --> G06
  G03 --> G07
  G03 --> G08
  G04 --> G08
  G05 --> G08
  G08 --> G09
  G05 --> G09
  G08 --> G10
  G09 --> G10
  G06 --> G11
  G10 --> G11
  G08 --> G12
  G02 --> G12
  G12 --> G13
  G03 --> G13
  G06 --> G14
  G07 --> G14
  G09 --> G14
  G14 --> G15
  G07 --> G15
  G15 --> G16
  G14 --> G16
  G16 --> G17
  G02 --> G18
  G18 --> G19
  G11 --> G19
  G13 --> G19
  G15 --> G19
  G17 --> G19
  G19 --> G20
  L["Existing nodes 63 / 71 / 73 / 74 / 77 and pinned Mathlib/PNT+"]
  L -. inspect exact type and closure .-> G18
  L -. truncation and analytic adapters .-> G12
  L -. digamma and gamma adapters .-> G03
  L -. Poisson and phase adapters .-> G08
```

Source review precedes a fixed Lean signature. The two Poisson estimates are substantive independent outputs; an AFE specialization alone does not close the general theorem. The reflected AFE branch must consume the actual direct-branch remainder and χ identity. Numerical certification follows the analytic assembly. Preserve the distinct scaffold, development and release statuses.
