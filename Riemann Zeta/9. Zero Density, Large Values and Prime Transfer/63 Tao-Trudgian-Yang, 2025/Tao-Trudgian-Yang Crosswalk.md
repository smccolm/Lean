# Tao--Trudgian--Yang 2025 source-to-Lean crosswalk

## Status key

- **Available:** an upstream source or local theorem exists; no target bridge
  is claimed.
- **Planned:** statement/module design only.
- **Kernel-checked:** reserved for a compiled theorem with audited dependencies.

Current kernel-checked infrastructure comprises EPZAE-00--05, EPZAE-07--08,
EPZAE-16--17, EPZAE-20, EPZAE-22--23, EPZAE-25, EPZAE-31--32, and
EPZAE-34--35, together with the precisely scoped partial results below.
Every final public-result row below remains **planned**; the general-energy
half of `Add-est (i)` is now kernel-checked.

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
| `huxley-lvt` | classical LV bound | `ClassicalLargeValueRegions` proves the exact finite native Montgomery--Halasz--Huxley bridge and its actual energy-region cardinality consequence, including corrected cardinality powering. The standalone uniform `LV` interface remains open under EPZAE-19 |
| `hb-opt`, `jutila-lvt` | other classical LV bounds | literature formalization; EPZAE-19 |
| `guth-maynard-lvt` | modern LV bound | `guthMaynard_largeValueBound`, with exact closed-support, reflection, phase-twist, separation, coefficient-norm, threshold, and epsilon-loss conversions; kernel-checked EPZAE-20 |
| `bourgain-lvt` | optimized LV inequality | Bourgain 2000; EPZAE-19 |
| `power-lemma` | Dirichlet-polynomial powering | local GM coefficient machinery may help; EPZAE-18 |
| `twelfth-bound`, `lvz-340` | zeta-specific nonexistence/bound | HB twelfth moment plus old pair; EPZAE-21 |
| Ivić Orsay 83.06, Theorem 6.2 route: exact square entry | actual local zeta second moment to complete ordinary-divisor contour series | `hasSum_zetaSquareLocalMean` proves the exact source identity, including all contour limits, absolute integrated-norm summability, Gamma normalization, and compact-height interchange. The initial six `ZetaSquare*` modules have no moment premise. Averaging and the actual unit phase are proved below; the uniform amplitude/complete-series remainder is also proved below; divisor shortening, Voronoi/stationary phase, sharp remainders, and the Atkinson inequality remain open under EPZAE-21 |
| Ivić (6.27), first Gaussian majorization and window tail | actual local second moment and physical `T ± G L` window | `zetaSquareLocalMean_le_gaussian_divisor_series` proves the weighted-series majorization with constant `exp(1)`. `exists_zetaSquareGaussian_source_approximation` gives the literal whole-line Gaussian mean up to `G T^(-A)` on `L=log T`, uniformly for `0<G≤T`. The later oscillatory source reduction remains open |
| Ivić (6.32)--(6.33), quadratic Gaussian kernel | exact transform and frequency damping | `zetaGaussianQuadraticIntegral_eq` and `norm_zetaGaussianQuadraticIntegral_le` prove the transform with coefficient `G^(-2)+i/(2T)` and bound `sqrt(pi) G exp(-(Gv)²/8)` for `G²≤2T`. The actual unit-phase substitution and error are proved by the next row; the amplitude continuation below gives a uniform complete-source remainder, but these helpers do not establish the source's shortened divisor sum |
| DLMF 5.11.2 leading term; Ivić (6.28)--(6.33) phase component | actual digamma/Gamma quotient to quadratic Gaussian phase | `norm_digamma_sub_log_le` derives the explicit `4/abs(Im z)` error from the pinned series. `hasDerivAt_zetaSquareReflectedGammaPhase` and the actual functional-equation/source-normalization consumers identify the true phase. `norm_zetaSquareGammaGaussianTransform_sub_quadratic_le` proves its whole-line transform error `2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)` on `T≥4`, `0≤r≤T/2`, `G>0`. The following consumer uses actual quadratic damping when `G²≤2T`. The following continuation proves the uniform amplitude and complete reflected-source remainder; divisor shortening remains open, so this is not the complete Ivić source inequality |
| Exact square-source continuation toward Ivić Theorem 6.2 | actual shifted Gamma/pole amplitudes to the complete reflected divisor integral | `norm_gammaReal_shift_sq_sub_exp_le` derives the relative error from the actual digamma/log path and Gronwall. `exists_norm_zetaSquareRightKernel_sub_leading_le` combines near and far estimates, including the actual inverse Gamma normalization. `hasSum_zetaSquareLeadingDivisorContribution` and `exists_norm_zetaSquareDivisorIntegral_sub_leading_le` prove the full ordinary-divisor series and one uniform `O(1)` source remainder for all `t≥4`. No moment premise. Weight control/shortening, Gaussian assembly, Voronoi/stationary phase and Theorem 6.2 remain open under EPZAE-21 |
| `add-bound (ii)`, critical line and twelfth power | uniform moment-to-zeta-polynomial large values | `zetaTwelfth_largeValueBound_of_dyadic` proves `IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))` for `σ ≥ 1/2`, `τ ≥ 2`, conditional only on the genuine dyadic critical-line twelfth moment. The actual Perron entry, window, logarithmic losses, and epsilon--delta conversion are proved. The moment itself and the general source parameters remain open under EPZAE-19/21 |
| `add-bound (ii)`, exact coefficient-one source entry | sharp polynomial to localized critical-zeta convolution | `ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin` retains both integer endpoints and residue `mellin cutoff (1-it)`. `ZetaMellinUniform` and `ZetaMellinLocalization` prove physical-scale kernels and the far integral. `ZetaLargeValuePattern.perron_entry` bounds and absorbs both errors; `exists_zetaPerron_uniform_threshold` derives its physical conditions from all actual windows `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`. This critical-line entry edge is complete, not the full EPZAE-21 work package |
| `zero-from-large` | Type I/II transfer | local GM zero-density transfer is related but conventions must be matched; EPZAE-24 |
| `zero-large-cor*` | optimized transfer corollaries | exact finite supremum reasoning; EPZAE-24 |
| `thm:ingham_zero_density2` | `A <= 3/(2-sigma)` | `ingham_isZeroDensityBound` and `zeroDensityExponent_le_ingham`, kernel-checked |
| `huxley-bound` | `A <= 3/(3 sigma-1)` | `huxley_isZeroDensityBound_inclusive` and `zeroDensityExponent_le_huxley`, kernel-checked |
| `guth-maynard-density` | `A <= 15/(3+5 sigma)` | `guthMaynard_isZeroDensityBound_inclusive` and `zeroDensityExponent_le_guthMaynard`, kernel-checked |
| `bourgain-zd` | pair-to-density formula | Bourgain 1995, planned EPZAE-28 |
| `zeroe-from-large` | zero-energy from LV energy | Source inequality proved by `zeroDensityEnergyExponent_le_sup_limsup` in `EnergyExponentTransfer`, with exact domain `1/2 < σ < 1`, zeta supremum over `τ ≥ 1`, and general-energy limsup. The proof consumes actual Type-I/II source fibers, analytic multiplicity, compact-range uniformity, all explicit losses, and signed dyadic symmetric-rectangle assembly. No mathematical theorem parameter remains |
| `zeroe-large-cor-0` | bounded-range zero-energy transfer | Still open under EPZAE-33. The general interval `τ₀ ≤ τ ≤ 2τ₀` now controls all higher scales via `isLargeValueEnergyBound_of_bounded_power_range`. `isZeroDensityEnergyBound_of_bounded_energy_ranges` consumes that result with zeta bounds on `[1,τ₀)`. The source's lower zeta endpoint `2` and exact supremum statement remain open; neither endpoint nor empty-interval convention may be silently changed |
| `power-energy` | printed five-coordinate powering | **Disproved and preserved:** `energyPowering_source_counterexample` gives input `(3/4,2,0,0,2)` and excludes any `k=2` output with `s' ≤ 1`; every region point has `s' ≥ 2`. Not an upstream theorem |
| Owner-authorized repair of `power-energy` | two cardinality/energy witnesses | EPZAE-34 **DONE**: `correctedCardinalityEnergyPowering` proves the full `CorrectedCardinalityEnergyPowering` target; `InLargeValueEnergyRegion.corrected_powering` gives one `ρ/k` witness and one `ρ*/k` witness, with the other retained coordinate bounded above and each `s` separately existential. Actual powered patterns, uniform normalization, and coordinate-preserving compactness are proved. `InCardinalityEnergyRegion.heathBrown_powered` now consumes the proved analytic relation too. See the Energy Powering Repair document |
| `hbt` | Heath--Brown five-variable energy relation | EPZAE-35 **DONE**: `InLargeValueEnergyRegion.heathBrown_relation`, independently derived from native second/fourth moments with exact source bridges; corrected powered consumer and the `τ ≤ 3/2` consequence also proved |
| `imphb-lver-ineq` | general-energy half of `Add-est (i)` | `EnergyClauseOneGeneral` proves both source pieces on `3/4 ≤ σ ≤ 5/6`, `8σ-4 ≤ τ ≤ 2(8σ-4)`, with the exact `σ=4/5` crossover, using actual Huxley cardinality witnesses and Heath--Brown energy witnesses. Its uniform energy bound and extension to every `τ ≥ 8σ-4` are kernel-checked; this is a completed sub-result of EPZAE-36/37, not the whole clauses |
| Conditional `Add-est (i)` assembly | remaining zeta input separated from proved general half | `energyClauseOne_of_zeta_range` proves the advertised zero-energy bound from explicit uniform zeta-energy bounds on `[1,8σ-4)`. Those zeta bounds and the source endpoint-two reduction remain open; no final `Add-est` clause is claimed |
| `imphb-zlver-ineq` | zeta-energy half of `Add-est (i)` | The six-branch rational certificate, `τ=4σ-1` transition, `σ=65/86` crossover, and public-envelope comparison are kernel-checked in `EnergyClauseOneZeta`. Its actual-region and uniform-energy consumers are **conditional** on the independent twelfth-moment cardinality bound; Huxley's cap and the uniform-LV-to-region bridge are proved |
| Short-height coefficient-one entry | threshold-relative Perron bound | `ZetaLargeValuePattern.perron_entry_with_scaled_error` and `exists_zetaPerron_short_uniform_threshold` prove actual entry uniformly for `σ ≥ 3/4`, `τ ≥ 3/2`, `δ ≤ 1/16`. The moment-to-LV deduction is proved from the genuine dyadic moment |
| Short-zeta nonexistence | actual patterns eventually empty | `exists_zetaShort_empty_uniform_threshold` and `zetaShort_largeValueExponent_eq_bot` prove emptiness and `LV_ζ=-∞` for `σ ≥ 3/4`, `1 ≤ τ < 3/2`, consuming exact sharp-interval first/second derivative bounds. This is a proved subrange, not the full source `lvz-340` or reflection theorem |
| Refined conditional `Add-est (i)` assembly | genuine dyadic moment is the sole analytic input | `energyClauseOne_of_dyadic_moment` derives the complete short-zeta range from cancellation, threshold-relative Perron entry, and cubic energy, then consumes the repaired witnesses, Heath--Brown relation, exact optimizations, and endpoint-one transfer. The dyadic twelfth moment is unproved. The independent endpoint-two source theorem and all nine unconditional outputs remain open |

The positive-height normalization of ANTEDB Lemma 8.4 is now proved by
`zetaLargeValueExponent_eq_bot_iff_neg`,
`zetaLargeValueExponent_eq_bot_iff_empty_threshold`, and
`zetaLargeValueExponent_eq_bot_iff_pointwise_powerSaving`. The last theorem
uses the actual sharp interval and `n^(-it)` phase, constructs an actual
singleton, and pays for the upper `2T` endpoint in the reverse direction.
`zetaLargeValueExponent_le_iff` supplies the exact non-asymptotic
infimum semantics. `zetaShort_pointwise_powerSaving` is the unconditional
short-range consumer. Other nonexistence ranges and reflection remain open.

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

- **Substantive contradiction, not an editorial repair:** `power-energy`
  (paper Lemma 62; live blueprint Lemma 10.12) scales the unnormalized
  double-zeta-sum exponent to at most `s/k`, contradicting the diagonal
  lower bound on a singleton pattern. The kernel-checked counterexample and
  exact source references are in `Tao-Trudgian-Yang Energy Powering Obstruction.md`.
  The source and final output contracts have not been modified. The owner
  explicitly authorized the separate two-witness supporting-lemma repair;
  it is not represented as a proof of the printed statement.

- The TeX line for `exp-pair-def` contains `T >= N <= 1`, while the displayed
  estimate immediately continues with `T >= N >= 1`; Lean must use the latter
  intended range and document the correction.
- The `lv-edef` binder lists `rho, rho' >= 0` although the tuple uses `rho*`
  and `s`; the non-asymptotic lemma clarifies the intended variables.
- In the prose proof of `hbt`, the last finite-estimate factor is printed
  as `E₁(W)^(3/4) N T^(1/2)`, whereas the displayed exponent relation has
  `3ρ*/4 + ρ + τ/2`. These are not the same exponent comparison. EPZAE-35
  now has an independent kernel-checked derivation: native
  `gmDiscreteFourthMoment_native` has the required `E^(3/4) |W| T^(1/2) N`
  term. Together with the second moment, Hölder, and native large-value
  energy inequality, `heathBrown_largeValuePattern_energy_squared` and
  `InLargeValueEnergyRegion.heathBrown_relation` prove the displayed source
  relation. The archived text is unchanged; its mismatched line is not used.
- The prose after the proof of additive-energy clause (i) concludes one
  intermediate line with `min` where the target and preceding derivation use a
  maximum. `EnergyClauseOneZeta` now proves the displayed target maximum
  from its exact cardinality constraints, not that concluding `min`.
  In the same proof's second case, substituting `ρ ≤ 4-4σ` in the middle
  branch gives `23/2 - (25/2)σ + τ/4`; the archived line omits the `σ`
  after `25/2`. The Lean certificate performs the substitution from the
  proved branch formula and does not use that mismatched printed line.
- The best-known density table calls the optimized Bourgain result a
  “Corollary” although the labeled source declaration is a theorem.
- The paper records exact rational calculations as computer assisted and not
  formally certified; all certificate data must be independently checked.

No item in this ledger authorizes silently changing a source theorem. Each
resolution belongs in a theorem docstring and semantic regression.

The live [ANTEDB zeta-moment chapter](https://teorth.github.io/expdb/blueprint/zeta-moment-chapter.html)
was checked on 20 September 2026. Its Theorem 9.7 proof displays a `min`,
although [Lemma 8.11](https://teorth.github.io/expdb/blueprint/largevalue-zeta-chapter.html)
provides a `max`. The Lean branch lemma retains that maximum: if
`a = τ-6(σ-1/2)` is nonnegative, `max(a,2a)=2a`; if negative, the actual
zeta exponent is negative infinity. This does not establish the input
analytic maximum bound. No archived source is edited. The pinned Ivić
scan is *Topics in Recent Zeta Function Theory*, Orsay report 83.06,
and uses Theorem 7.1/Corollary 7.2 for this route; it is not the book
edition whose Theorem 8.2 is cited by the live blueprint.
