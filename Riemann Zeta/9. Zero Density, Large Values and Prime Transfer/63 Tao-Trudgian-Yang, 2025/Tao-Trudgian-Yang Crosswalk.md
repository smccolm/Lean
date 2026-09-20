# Tao--Trudgian--Yang 2025 source-to-Lean crosswalk

## Status key

- **Available:** an upstream source or local theorem exists; no target bridge
  is claimed.
- **Planned:** statement/module design only.
- **Kernel-checked:** reserved for a compiled theorem with audited dependencies.

Current kernel-checked infrastructure comprises EPZAE-00--05, EPZAE-07--08,
EPZAE-16--17, EPZAE-20, EPZAE-22--23, EPZAE-25, and EPZAE-31. Every
public-result row below remains **planned**.

## Public result ledger

| Paper label | Exact source conclusion | Planned Lean home | Checklist |
|---|---|---|---:|
| `new-exp-pair` | `(89/1282,997/1282)`, `(652397/9713986,7599781/9713986)`, `(10769/351096,609317/702192)`, and `(89/3478,15327/17390)` are exponent pairs | `NewExponentPairs.lean` | EPZAE-14 |
| `hb-density2` | `A(sigma) <= 3/(10 sigma-7)` for `7/10 < sigma <= 1` | `ImprovedHeathBrownDensity.lean` | EPZAE-26 |
| `bourgain-density-improved` | `A(sigma) <= max(2/(9 sigma-6), 9/(8(2 sigma-1)))` for `17/22 <= sigma <= 4/5` | `ImprovedBourgainDensity.lean` | EPZAE-27 |
| `bourgain-zero-density-optimized` | eight-piece bound below | `BourgainOptimizedDensity.lean` | EPZAE-29 |
| `Add-est` | nine energy bounds below | `NewAdditiveEnergy.lean` | EPZAE-37 |

### Exact optimized Bourgain pieces

For `3/4 < sigma < 1`, the target is the following source function:

| Range | Upper bound for `A(sigma)` |
|---|---|
| `3/4 < sigma <= 14/15` | `11 / (12*(4*sigma-3))` |
| `14/15 < sigma <= 2841/3016` | `391 / (2493*sigma-2014)` |
| `2841/3016 < sigma <= 859/908` | `22232 / (163248*sigma-134765)` |
| `859/908 < sigma <= 1625/1692` | `356 / (2742*sigma-2279)` |
| `1625/1692 < sigma <= 3334585/3447984` | `2609588 / (20732766*sigma-17313767)` |
| `3334585/3447984 < sigma <= 974605/1005296` | `75872 / (9*(81024*sigma-69517))` |
| `974605/1005296 < sigma <= 5857/6032` | `288 / (3616*sigma-3197)` |
| `5857/6032 < sigma < 1` | `86152 / (1447460*sigma-1311509)` |

`GeneratedCertificates.lean` now reconstructs these eight rows by exact
rational arithmetic from the first eight Bourgain candidates in the pinned
paper-time ANTEDB driver. `BourgainPiecewiseCertificates.lean` consumes the
generated rational functions and kernel-checks all seven crossovers and the
full interval cover. It also proves for every row that the normalized generated
fraction is exactly Bourgain's `4k/(2(1+k)sigma-1-l)` expression for its stored
candidate. This is certificate-layer progress only; EPZAE-28--29 still require
the analytic Bourgain theorem and its application to proved exponent pairs.

The source best-known table later clips some of these pieces against Pintz
and other bounds. EPZAE-29 proves the theorem as stated; EPZAE-30 separately
proves the clipped envelope.

### Exact additive-energy clauses

Every bound below is for `A*(sigma) * (1-sigma)`.

The generator extracts the corresponding nine source theorem blocks from the
pinned ANTEDB blueprint, removes the common `(1-sigma)` denominator factor,
normalizes signs, and emits exact `RationalAffineFraction` lists. Lean
regression-checks the nine target intervals and each maximum's arity;
`EnergyCertificates.lean` additionally proves every generated denominator is
strictly positive throughout its generated interval. These are source-table
certificates, not proofs of the energy-region projections.

| Clause/range | Upper bound |
|---|---|
| (i), `3/4 <= sigma <= 5/6` | `max((18-19*sigma)/(2*(3*sigma-1)), 4*(10-9*sigma)/(5*(4*sigma-1)))` |
| (ii), `7/10 <= sigma <= 3/4` | `max(5*(18-19*sigma)/(2*(5*sigma+3)), 2*(45-44*sigma)/(2*sigma+15))` |
| (iii), `173/229 <= sigma <= 443/586` | `max((173-270*sigma)/(16*(93-125*sigma)), (653-890*sigma)/(10*(93-125*sigma)), (1151-1190*sigma)/(20*(15*sigma-2)))` |
| (iv), `443/586 <= sigma <= 373/493` | `max((593-810*sigma)/(5*(171-230*sigma)), 4*(266-275*sigma)/(5*(55*sigma-7)))` |
| (v), `373/493 <= sigma <= 103/136` | `max((533-730*sigma)/(30*(26-35*sigma)), 3*(26-33*sigma)/(85*sigma-62), (174-185*sigma)/(31*sigma+2))` |
| (vi), `103/136 <= sigma <= 42/55` | `max((72-91*sigma)/(7*(11*sigma-8)), 5*(18-19*sigma)/(2*(5*sigma+3)))` |
| (vii), `42/55 <= sigma <= 79/103` | `max((18-19*sigma)/(6*(15*sigma-11)), 3*(18-19*sigma)/(4*(4*sigma-1)))` |
| (viii), `79/103 <= sigma <= 84/109` | `max((18-19*sigma)/(2*(37*sigma-27)), 5*(18-19*sigma)/(2*(13*sigma-3)))` |
| (ix), `84/109 <= sigma <= 5/6` | `max((18-19*sigma)/(9*(3*sigma-2)), 4*(10-9*sigma)/(5*(4*sigma-1)))` |

## Definition crosswalk

| Paper object/label | Intended semantics | Existing reusable code | Lean module/status |
|---|---|---|---|
| `auto` | automatic uniformity for variable families | ANTEDB `Basic.AutomaticUniformity` | `AsymptoticBridge`, kernel-checked import |
| `phase-def`, `fpu` | model phase through derivative convergence on `[1,2]` | ANTEDB `ExponentialSums.PhaseFunctions` | `AsymptoticBridge`, kernel-checked import |
| `energy-def` | approximate additive quadruples of a finite multiset | no exact upstream Lean object found | `AdditiveEnergy`, unit-tolerance indexed definition, multiplicity expansion, `n²`/one-separated cubic bounds, and the local-mass-times-cube bound kernel-checked |
| `beta-def`, `beta-asymp` | least exponential-sum growth exponent and epsilon/delta form | ANTEDB `ExponentSumGrowth` and `ExponentSumGrowthNonAsymptotic` | `AsymptoticBridge`, kernel-checked import |
| `exp-pair-def` | analytic exponent-pair estimate | not present in current ANTEDB Lean tree | `ExponentPair`, definition and non-asymptotic equivalence kernel-checked |
| `lv-def` | large-value exponent for one-separated ordinates | not present | `LargeValuePattern` and `LargeValueExponent`, exact pattern and epsilon-loss infimum interfaces kernel-checked |
| `zero-def` | multiplicity-weighted zeros with `Re >= sigma`, `|Im| <= T` | local Guth--Maynard has rectangle counts | `ZeroCountBridge` and `ZeroDensityExponent`, exact count and epsilon-loss infimum kernel-checked |
| `lve-def`, `zeroe-def` | energy large-value and zero-density exponents | not present | `EnergyExponents`, `EnergyBoundAsymptotics`, `ZeroEnergyMultiplicity`, and `EnergyRegionSupremum`; equivalent asymptotic/non-asymptotic bound interfaces, exact multiplicity-copy/local-weight conversion, the extended-real general/zeta inequalities `2LV ≤ LV* ≤ 3LV`, exact feasible-region supremum characterizations on the source domain, the unconditional `2A ≤ A* ≤ 4A`, and the sharp source-range `2A ≤ A* ≤ 3A` for `1/2 < σ`, all kernel-checked without finiteness assumptions |
| `lv-edef`, `lve-asymp` | five-dimensional feasible energy tuples | Python polytope model only | `EnergyRegions`, `EnergyRegionAsymptotics`, and `EnergyRegionSupremum`; exact double-zeta sum, source-facing unbounded-family and non-asymptotic general/zeta predicates with proved equivalences, zeta-to-general inclusion, the necessary `ρ ≤ τ`, `2ρ ≤ ρ* ≤ 3ρ`, and `ρ+2 ≤ s ≤ 2ρ+2` constraints, plus both directions of the general and zeta `LV*` region-supremum characterizations |

## Supporting theorem crosswalk

| Paper label | Role | Planned dependency/status |
|---|---|---|
| `exp-process` | A/B/C preservation | analytic proof from Ivić/Sargos; planned EPZAE-10 |
| `D-process` | beta upper bound and derived pair | Sargos 1995; planned EPZAE-11 |
| `beta-duality` | converts global affine beta bound to exponent pair | core planned theorem EPZAE-09 |
| `heath-brown-2017` | kth derivative beta estimate | source PDF/TeX available; EPZAE-12 |
| `old-exp-pair` | `(3/40,31/40)` input | derive from cited beta table; needed by `hb-density2` |
| `exp-pair-mu`, `mu-bound` | zeta-growth application | EPZAE-15 |
| `hux-sub` | subdivision in `tau` | EPZAE-18 |
| `l2-mvt` | basic large-values estimate | mathlib/local analytic input; EPZAE-18 |
| `huxley-lvt`, `hb-opt`, `jutila-lvt` | classical LV bounds | literature formalization; EPZAE-19 |
| `guth-maynard-lvt` | modern LV bound | `guthMaynard_largeValueBound`, with exact closed-support, reflection, phase-twist, separation, coefficient-norm, threshold, and epsilon-loss conversions; kernel-checked EPZAE-20 |
| `bourgain-lvt` | optimized LV inequality | Bourgain 2000; EPZAE-19 |
| `power-lemma` | Dirichlet-polynomial powering | local GM coefficient machinery may help; EPZAE-18 |
| `twelfth-bound`, `lvz-340` | zeta-specific nonexistence/bound | HB twelfth moment plus old pair; EPZAE-21 |
| `zero-from-large` | Type I/II transfer | local GM zero-density transfer is related but conventions must be matched; EPZAE-24 |
| `zero-large-cor*` | optimized transfer corollaries | exact finite supremum reasoning; EPZAE-24 |
| `thm:ingham_zero_density2` | `A <= 3/(2-sigma)` | `ingham_isZeroDensityBound` and `zeroDensityExponent_le_ingham`, kernel-checked |
| `huxley-bound` | `A <= 3/(3 sigma-1)` | `huxley_isZeroDensityBound_inclusive` and `zeroDensityExponent_le_huxley`, kernel-checked |
| `guth-maynard-density` | `A <= 15/(3+5 sigma)` | `guthMaynard_isZeroDensityBound_inclusive` and `zeroDensityExponent_le_guthMaynard`, kernel-checked |
| `bourgain-zd` | pair-to-density formula | Bourgain 1995, planned EPZAE-28 |
| `zeroe-from-large` | zero-energy from LV energy | EPZAE-33 in progress: bounded perturbation and arbitrary-to-unit tolerance normalization retain analytic-multiplicity indices. `typeIZero_exists_shifted_detector` chooses one native beta-removal shift per underlying zero. `typeIZeroCopy_shifted_unitBin_card_le` transfers the native Jensen unit-bin bound to multiplicity copies. `EnergyPartition` supplies indexed scale aggregation, while `EnergySeparation` colors by unit-bin parity and rank. The composed theorem `typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies` controls actual Type I zero energy by four multiplicity-safe, one-separated, single-scale detector classes with explicit losses. `DetectorPattern` supplies exact closed-support coefficient normalization and packages each inhabited class as a `LargeValuePattern`, with exact equality between its finset energy and the indexed class energy. A subpower bound for the normalization, application of `LV*`, the Type II transfer, and final assembly remain open |
| `power-energy` | weakened energy powering | planned EPZAE-34 |
| `hbt` | Heath--Brown five-variable energy relation | Heath--Brown 1979; planned EPZAE-35 |

## Source-convention bridges requiring proofs

1. **Asymptotics:** paper sequences indexed by an unspecified variable set
   versus Lean filters/sequences and ANTEDB `VariableObject`.
2. **Intervals:** real intervals versus natural dyadic support; open, closed,
   and half-open endpoint effects.
3. **Phase sign:** `n^{-it}` in large-value patterns versus local theorems that
   may use `n^{it}`.
4. **Coefficients:** defined only on `[N,2N]` versus ambient sequences extended
   by zero.
5. **Separation:** finite set/multiset one-separation versus indexed families.
6. **Zeros:** `Re rho >= sigma`, `|Im rho| <= T`, analytic multiplicity versus
   local rectangles and positive dyadic slabs.
7. **Energy:** approximate equality within one, multiplicity, and perturbation
   from each zero ordinate to a nearby large-value ordinate.
8. **Infinity values:** source uses `LV_zeta = -infinity` to express no pattern;
   Lean should prefer an explicit nonexistence proposition unless an extended
   real API is genuinely helpful.
9. **Suprema:** every displayed supremum over `tau` must be linked to the
   certificate's compact rational interval and endpoint convention.

## Source errata/audit ledger

These are editorial or semantic points to resolve against the rendered paper,
ANTEDB blueprint, and cited source before freezing Lean statements:

- The TeX line for `exp-pair-def` contains `T >= N <= 1`, while the displayed
  estimate immediately continues with `T >= N >= 1`; Lean must use the latter
  intended range and document the correction.
- The `lv-edef` binder lists `rho, rho' >= 0` although the tuple uses `rho*`
  and `s`; the non-asymptotic lemma clarifies the intended variables.
- The prose after the proof of additive-energy clause (i) concludes one
  intermediate line with `min` where the target and preceding derivation use a
  maximum. This must be checked rather than copied mechanically.
- The best-known density table calls the optimized Bourgain result a
  “Corollary” although the labeled source declaration is a theorem.
- The paper records exact rational calculations as computer assisted and not
  formally certified; all certificate data must be independently checked.

No item in this ledger authorizes silently changing a source theorem. Each
resolution belongs in a theorem docstring and semantic regression.
