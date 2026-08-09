# Proof Architecture

**Last synchronized:** 8 August 2026

**Task authority:** `Lean Alignment Fix Agenda.md`

**Progress authority:** `Research Agenda Progress.MD`

This is the canonical logical dependency map for the proof, not an import graph.

## Part 1 — Explanation

### Status key

- **Blue — available:** existing Mathlib foundations.
- **Green — done:** kernel-checked at the stated boundary.
- **Amber — done conditionally:** the deduction is kernel-checked, while one or more upstream inputs shown in red remain open.
- **Red — open:** unfinished work. Every red node names its owning Shitlist item.

### Node details

| Node | Meaning and principal files |
|---|---|
| Zeta analytic foundations | **Done in #15:** `ZetaBounds.lean` and `ZeroCount.lean`; Abel continuation, pole-safe polynomial vertical growth, right-half-plane control, and the Euler/Möbius lower bound are kernel-checked. No project axiom remains in this layer. |
| Local zero count | **Done in #15:** `ExtractSeparated.lean`; Jensen's formula is bridged to analytic multiplicity and proves `localZeroMultiplicityBound_native`. |
| Classical density analysis | **#15:** the critical-line fourth moment, Littlewood/Gabriel step, mollified contour identity, and Huxley approximate-functional-equation/large-values estimate required by the primary sources are not yet formalized. |
| Density endpoints | **#15:** `InghamBound.lean`; the concrete Ingham and Huxley estimates for the project's symmetric multiplicity-weighted `N` remain open. |
| Beta removal | **#16:** `BetaDependence.lean`; Fourier decay, contour shifting, truncation, averaging, and pigeonholing. |
| Coefficient bounds | **#17:** `ZeroDetector.lean` and `PolynomialPowers.lean`; divisor and factorization estimates. |
| Mean value | **Done in #17:** `MeanValueProof.lean`; Montgomery's estimate on `[0,T]` and its Halász–Montgomery consequence are kernel-checked. |
| Type-II inputs | **#18:** `TypeIIZeros.lean`; coverage, fourth-moment reduction, and twisted zeta fourth moment. |
| Goal C specialization | **#18:** transfer integration producing a theorem whose only remaining premise is `GuthMaynardLargeValues`. |
| Decoupling and GM large values | **#19:** `Decoupling.lean` and `LargeValues.lean`. |
| Final results and gates | **#19:** concrete Guth–Maynard and combined zero-density theorems, `Audit.lean`, documentation, and `run_lake_build.bat`. |

The completed conditional path consists of the #13 separated extraction, the now-unconditional Montgomery mean-value and Halász–Montgomery estimates, the #14 central Type-I estimate, the slab-to-symmetric-count transfer, the #14 primitive-input transfer, and the combined-exponent transfer.

The #15 foundation and mean-value prerequisites are complete. Its remaining dependency chain is **critical-line fourth moment and zero-detection identities → Ingham; approximate functional equation and powered large-values estimate → Huxley → concrete symmetric-count endpoints**. #16 can proceed independently before #18; #18 must produce the Goal C specialization before #19 can apply the proved large-values theorem and close the project.

An item is crossed out only when every red node bearing its number is kernel-checked and its Shitlist completion test passes.

### Synchronization rule

Any change to proof status, open obligations, dependency edges, or Shitlist numbering must update these three artifacts together:

1. `Lean Alignment Fix Agenda.md` — authoritative task number, scope, and completion test;
2. `Research Agenda Progress.MD` — evidence-based current assessment; and
3. this Mermaid diagram — matching node status and dependencies.

No unfinished diagram node may omit its Shitlist number. No crossed-out item may retain a red node. No new red node may be added without assigning it to one of the five exhaustive remaining items unless the project owner explicitly changes the completion contract.

## Part 2 — Diagram

```mermaid
flowchart TD
    MZ["Mathlib APIs<br/>AVAILABLE"]

    ZB["Zeta analytic foundations<br/>DONE"]
    LZ["Local zero count<br/>DONE"]
    CD["#15 Classical density analysis<br/>OPEN"]
    ZD["#15 Ingham and Huxley<br/>OPEN"]
    BR["#16 Beta removal<br/>OPEN"]
    AC["#17 Coefficient bounds<br/>OPEN"]
    MV["Montgomery mean value<br/>DONE"]

    EX["Separated extraction<br/>DONE CONDITIONALLY"]
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
    CD --> ZD

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

    class ZB,LZ,MV,DY done;
    class HM done;
    class EX,CT,TR,CB conditional;
    class CD,ZD,BR,AC,T2,GCS,DC,GM,GZD,CZD,QA open;
    class MZ available;
```
