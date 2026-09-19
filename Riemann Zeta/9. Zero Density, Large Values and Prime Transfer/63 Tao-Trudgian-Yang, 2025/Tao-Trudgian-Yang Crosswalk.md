# Tao--Trudgian--Yang 2025 source-to-Lean crosswalk

## Status key

- **Available:** an upstream source or local theorem exists; no target bridge
  is claimed.
- **Planned:** statement/module design only.
- **Kernel-checked:** reserved for a compiled theorem with audited dependencies.

At scaffold creation every target row is **planned**.

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

The source best-known table later clips some of these pieces against Pintz
and other bounds. EPZAE-29 proves the theorem as stated; EPZAE-30 separately
proves the clipped envelope.

### Exact additive-energy clauses

Every bound below is for `A*(sigma) * (1-sigma)`.

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

| Paper object/label | Intended semantics | Existing reusable code | Planned module |
|---|---|---|---|
| `auto` | automatic uniformity for variable families | ANTEDB `Basic.AutomaticUniformity` | `AsymptoticBridge` |
| `phase-def`, `fpu` | model phase through derivative convergence on `[1,2]` | ANTEDB `ExponentialSums.PhaseFunctions` | `PhaseBridge` |
| `energy-def` | approximate additive quadruples of a finite multiset | no exact upstream Lean object found | `AdditiveEnergy` |
| `beta-def`, `beta-asymp` | least exponential-sum growth exponent and epsilon/delta form | ANTEDB `ExponentSumGrowth` and `ExponentSumGrowthNonAsymptotic` | bridge/reuse |
| `exp-pair-def` | analytic exponent-pair estimate | not present in current ANTEDB Lean tree | `ExponentPair` |
| `lv-def` | large-value exponent for one-separated ordinates | not present | `LargeValueExponent` |
| `zero-def` | multiplicity-weighted zeros with `Re >= sigma`, `|Im| <= T` | local Guth--Maynard has rectangle counts | `ZeroCountBridge`, `ZeroDensityExponent` |
| `lve-def`, `zeroe-def` | energy large-value and zero-density exponents | not present | `EnergyRegions` |
| `lv-edef` | five-dimensional feasible energy tuples | Python polytope model only | `EnergyRegions`, `PolyhedralCertificates` |

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
| `guth-maynard-lvt` | modern LV bound | exact bridge from local completed project; EPZAE-20 |
| `bourgain-lvt` | optimized LV inequality | Bourgain 2000; EPZAE-19 |
| `power-lemma` | Dirichlet-polynomial powering | local GM coefficient machinery may help; EPZAE-18 |
| `twelfth-bound`, `lvz-340` | zeta-specific nonexistence/bound | HB twelfth moment plus old pair; EPZAE-21 |
| `zero-from-large` | Type I/II transfer | local GM zero-density transfer is related but conventions must be matched; EPZAE-24 |
| `zero-large-cor*` | optimized transfer corollaries | exact finite supremum reasoning; EPZAE-24 |
| `thm:ingham_zero_density2` | `A <= 3/(2-sigma)` | local theorem available; bridge EPZAE-25 |
| `huxley-bound` | `A <= 3/(3 sigma-1)` | local theorem available; bridge EPZAE-25 |
| `guth-maynard-density` | `A <= 15/(3+5 sigma)` | local theorem available; bridge EPZAE-25 |
| `bourgain-zd` | pair-to-density formula | Bourgain 1995, planned EPZAE-28 |
| `zeroe-from-large` | zero-energy from LV energy | planned EPZAE-33 |
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
