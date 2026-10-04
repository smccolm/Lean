# Planned proof architecture

4 October 2026. PLANNING ONLY; 0/20 proof gates complete. Blue nodes are available references or reuse candidates, **not audited node-77 dependencies**. Every red node is an OPEN checklist gate. The map's node-71-to-node-77 relationship does not make global density a premise of the pointwise inverse theorem.

```mermaid
flowchart TD
    SRC["Pinned paper and Granville–Soundararajan<br/>REFERENCE"]
    ML["Installed Mathlib + foundation<br/>REUSE CANDIDATES"]
    XI["Local PNT+/node-74 xi and Hadamard<br/>REUSE CANDIDATES; closure audit needed"]
    EP["Node-63 A/B, first derivative, log phase<br/>REUSE CANDIDATES"]
    G01["DWWZ-01 package, pins and BAT<br/>OPEN"]
    G02["DWWZ-02 exact public contracts<br/>OPEN"]
    G03["DWWZ-03 actual sum and spectral shift<br/>OPEN"]
    G04["DWWZ-04 multiplicity-faithful zero objects<br/>OPEN"]
    G05["DWWZ-05 mean-value / Lipschitz inputs<br/>OPEN"]
    G06["DWWZ-06 maximizing twist; Lemma 2.2<br/>OPEN"]
    G07["DWWZ-07 crude uniform zeta; Lemma 3.1<br/>OPEN"]
    G08["DWWZ-08 xi product and convergence<br/>OPEN"]
    G09["DWWZ-09 zero repulsion; Lemma 3.2<br/>OPEN"]
    G10["DWWZ-10 Gaussian identity WITH residue<br/>OPEN"]
    G11["DWWZ-11 log derivative; Lemma 3.4<br/>OPEN"]
    G12["DWWZ-12 actual weighted forcing; Prop. 4.1<br/>OPEN"]
    G13["DWWZ-13 near/far zero count and scales<br/>OPEN"]
    G14["DWWZ-14 THEOREM 1.1<br/>one center, every L; OPEN"]
    G15["DWWZ-15 all large x; Lemma 5.1<br/>OPEN"]
    G16["DWWZ-16 THEOREM 1.2<br/>local-zero implication; OPEN"]
    G17["DWWZ-17 semantic regressions<br/>OPEN"]
    G18["DWWZ-18 imports and exhaustive audits<br/>OPEN"]
    G19["DWWZ-19 both proof BATs and reproduction<br/>OPEN"]
    G20["DWWZ-20 synchronized release docs<br/>OPEN"]
    ML --> G01
    SRC --> G02
    G01 --> G02
    G01 --> G03
    G01 --> G04
    SRC --> G05
    G03 --> G05
    G05 --> G06
    ML --> G07
    G03 --> G07
    XI --> G08
    G04 --> G08
    G08 --> G09
    G07 --> G09
    G03 --> G10
    G07 --> G10
    ML --> G10
    G08 --> G11
    G06 --> G12
    G07 --> G12
    G09 --> G12
    G10 --> G12
    G04 --> G13
    G11 --> G13
    G12 --> G13
    G02 --> G14
    G06 --> G14
    G13 --> G14
    EP --> G15
    G03 --> G15
    G14 --> G16
    G15 --> G16
    G02 --> G16
    G14 --> G17
    G16 --> G17
    G17 --> G18
    G01 --> G18
    G18 --> G19
    G19 --> G20
    classDef reference fill:#dcecff,stroke:#245b9e,color:#0d2542;
    classDef open fill:#ffd9d9,stroke:#a32121,color:#3d0b0b;
    class SRC,ML,XI,EP reference;
    class G01,G02,G03,G04,G05,G06,G07,G08,G09,G10,G11,G12,G13,G14,G15,G16,G17,G18,G19,G20 open;
```

The live analytic priority after activation is DWWZ-05 → DWWZ-06 → DWWZ-12. Gaussian and xi branches are independent prerequisites; their available libraries do not supply the missing mean-value estimate automatically. DWWZ-15 can be tackled independently, but is not a replacement for T1.
