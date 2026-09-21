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
| Ivić Orsay 83.06, Theorem 6.2 route: exact square entry | actual local zeta second moment to complete ordinary-divisor contour series | `hasSum_zetaSquareLocalMean` proves the exact source identity, including all contour limits, absolute integrated-norm summability, Gamma normalization, and compact-height interchange. The initial six `ZetaSquare*` modules have no moment premise. Averaging and the actual unit phase are proved below; the uniform amplitude/complete-series remainder is also proved below; uniform Bessel/stationary estimates, sharp remainders, and the Atkinson inequality remain open under EPZAE-21 |
| Ivić (6.27), first Gaussian majorization and window tail | actual local second moment and physical `T ± G L` window | `zetaSquareLocalMean_le_gaussian_divisor_series` proves the weighted-series majorization with constant `exp(1)`. `exists_zetaSquareGaussian_source_approximation` gives the literal whole-line Gaussian mean up to `G T^(-A)` on `L=log T`, uniformly for `0<G≤T`. The later oscillatory source reduction remains open |
| Ivić (6.32)--(6.33), quadratic Gaussian kernel | exact transform and frequency damping | `zetaGaussianQuadraticIntegral_eq` and `norm_zetaGaussianQuadraticIntegral_le` prove the transform with coefficient `G^(-2)+i/(2T)` and bound `sqrt(pi) G exp(-(Gv)²/8)` for `G²≤2T`. The actual unit-phase substitution and error are proved by the next row; the amplitude continuation below gives a uniform complete-source remainder, but these helpers do not establish the source's shortened divisor sum |
| DLMF 5.11.2 leading term; Ivić (6.28)--(6.33) phase component | actual digamma/Gamma quotient to quadratic Gaussian phase | `norm_digamma_sub_log_le` derives the explicit `4/abs(Im z)` error from the pinned series. `hasDerivAt_zetaSquareReflectedGammaPhase` and the actual functional-equation/source-normalization consumers identify the true phase. `norm_zetaSquareGammaGaussianTransform_sub_quadratic_le` proves its whole-line transform error `2r²(18/T+2r²/T²)+2sqrt(2pi)G exp(-(r/G)²/2)` on `T≥4`, `0≤r≤T/2`, `G>0`. The following consumer uses actual quadratic damping when `G²≤2T`. The following continuation proves the uniform amplitude and complete reflected-source remainder; the uniform stationary reduction remains open, so this is not the complete Ivić source inequality |
| Exact square-source continuation toward Ivić Theorem 6.2 | actual shifted Gamma/pole amplitudes to the complete reflected divisor integral | `norm_gammaReal_shift_sq_sub_exp_le` derives the relative error from the actual digamma/log path and Gronwall. `exists_norm_zetaSquareRightKernel_sub_leading_le` combines near and far estimates, including the actual inverse Gamma normalization. `hasSum_zetaSquareLeadingDivisorContribution` and `exists_norm_zetaSquareDivisorIntegral_sub_leading_le` prove the full ordinary-divisor series and one uniform `O(1)` source remainder for all `t≥4`. No moment premise. Weight control and the complete quadratic Gaussian-window comparison are proved in the following rows; uniform Bessel/stationary estimates and Theorem 6.2 remain open under EPZAE-21 |
| Leading Mellin weight toward Ivić (6.34)--(6.35) | actual complex weight, height variation and summable coefficient mass | `zetaDivisorWeight_add_neg` proves the residue reflection. The exact source argument has imaginary part `pi/2`; `exists_norm_source_zetaDivisorWeight_height_sub_le` gives `C(abs x/T) min(T/(2pi n),2pi n/T)`. The true coefficient mass is `Oε(T^(1/2+ε))`. `exists_norm_zetaSquareLeadingDivisor_sub_frozen_le` freezes only the weight, with error `Cε abs(x) T^(-1/2+ε)` for `T≥8`, `abs x≤T/2`. No moment or pointwise divisor asymptotic premise |
| Actual Gaussian-window assembly before shortening | real zeta square to complete quadratic divisor sum | `zetaSquareNorm_eq_reflected_source` proves the conjugate pairing and factor two. `hasSum_zetaFrozenDivisorGaussianMean` exchanges the actual series/integral using absolute integrated-norm summability. `exists_abs_zetaSquareGaussianWindow_sub_quadratic_le` consumes the real source, weight freeze, true Gamma-phase transform and Gaussian tails on `T≥8`, `G>0`, `G²≤2T`, `0≤r≤T/2`, with one source-error constant for each positive epsilon. Nine modules, 78 named public audits and 20 regressions. This is the complete quadratic sum, source-scale shortening is proved in the next row, while uniform Bessel/stationary estimates, Theorem 6.2 and the twelfth moment remain open; EPZAE-21/37 remain open |
| Source-scale finite divisor entry toward Ivić (6.34)--(6.35) | actual local zeta second moment to a finite oscillatory divisor sum | `exists_zetaSquarePhysicalGaussian_short_approximation` gives error `Cδ G log T` uniformly for all `0<G≤T^(1/2-δ)` after one threshold. `exists_zetaSquareLocalMean_le_short_divisor` is the unsmoothed source consumer. The actual finite band is `G abs(log n-log(T/(2pi)))≤log T`; its omitted tail is smaller than `G T^(-A)` for every `A`. On `G≥T^δ`, its physical radius is `T log T/(pi G)` and indices remain in `[T/(4pi),T/pi]`. `zetaShortQuadraticDivisorSum_eq_divisor_test` retains the exact complex test function. Six modules, 29 public audits and 18 regressions. The next row proves the actual smooth Voronoi/Bessel entry and its paid cutoff error; uniform stationary estimates, Theorem 6.2 and the twelfth moment remain open under EPZAE-21/37 |
| Actual smooth Voronoi and literal Bessel entry toward Ivić Theorem 6.2 | actual local zeta second moment to the logarithmic main term and literal Y0/K0 divisor integrals | `zetaSmoothDivisorVoronoiTest` constructs the actual globally smooth positive-support test. `norm_zetaSmoothDivisorSum_sub_short_le` pays all transition terms; logarithmic tails are at most `G T^(-A)` for every fixed `A`. `zetaSmoothDivisorSum_eq_voronoi` consumes native modulus-one Voronoi; both actual Bessel bridges retain factors `-2pi`, `4` and `d(0)=0`. `exists_zetaSquarePhysicalGaussian_bessel_approximation` and `exists_zetaSquareLocalMean_le_bessel` give uniform `Cδ G log T` source error on `0<G≤T^(1/2-δ)` beyond one threshold. Eight modules, 43 public audits, 18 regressions. No analytic source premise. The following rows discharge K0 and the phase-adjusted main term; oscillatory Y0 stationary reduction, sharp Theorem 6.2, twelfth moment and EPZAE-21/37 remain open |
| Complete modified-Bessel branch toward Ivić Theorem 6.2 | literal K0 decay and actual smooth support to complete arithmetic power saving and source removal | `exists_zetaDivisorBesselPlus_powerSaving` proves `norm(VK)≤G T^(-A)` for every fixed real `A`, on `T^δ≤G≤T^(1/2-δ)` beyond one uniform threshold. The proof constructs support `[T/16,T]`, actual integrability and summation from the ordinary-divisor series at two. `exists_zetaSquarePhysicalGaussian_main_minus_approximation` and `exists_zetaSquareLocalMean_le_main_minus` consume the bound, retaining only the full logarithmic main integral and actual Y0 sum, with `Cδ G log T` error. Seven modules, 29 public audits, 16 regressions. The phase-adjusted main-term estimate is proved below. The sharp stationary reduction, Atkinson inequality, twelfth moment and EPZAE-21/37 remain open; the conditional Add-est premise is not discharged |
| Ivić Orsay 83.06 (6.36), (6.38), (6.47): source-aligned lattice phase and saddle | actual unchanged divisor coefficients to the phase-adjusted local source and exact carrier geometry | `zetaDivisorLatticePhase_nat` proves the conjugate-sign insertion `exp(-2pi i n)=1`; the actual continuous test changes. `zetaSmoothDivisorSum_eq_atkinson_bessel` reapplies native Voronoi. `exists_zetaAtkinsonBesselPlus_powerSaving` proves the new complete K0 estimate; `exists_zetaSquareLocalMean_le_atkinson_reduced` consumes it, giving uniform `Cδ G log T` error on the same source widths. `zetaAtkinsonDivisorTest_mul_carrier` preserves all complex amplitudes. `zetaAtkinsonPhase_stationary_iff` and `zetaAtkinsonPhase_secondDeriv_saddle_neg` prove the unique nondegenerate positive saddle for every real carrier parameter, including both signs. Six modules, 40 public audits, 22 regressions. The main estimate is proved in the next row. The Y0 expansion is proved below; uniform stationary approximation, sharp Atkinson inequality and genuine twelfth moment remain open. Old and new continuous integrals are not equated; EPZAE-21/37 remain open |
| Phase-adjusted logarithmic main term in the Ivić source route | actual smooth-amplitude variation to the main-integral bound and Y0-only physical source | `exists_norm_zetaAtkinsonVoronoiMain_le` proves `norm(V0_A)≤C G log T` for `T≥16`, `log T≥1`, `G>0`, `G²≤2T`, `L>0`, `8L≤G`. The actual cutoff, fixed rescaled Mellin profile, square-root/log factors, unit Gamma factor and damped quadratic Gaussian have constructed norm/variation bounds; native `norm_weighted_gmReflectionIntegral_le` supplies square-root cancellation. The main integrand is absolutely integrable and its positive-support/reflection identity is proved. `exists_zetaSquarePhysicalGaussian_atkinson_minus_approximation` and `exists_zetaSquareLocalMean_le_atkinson_minus` consume this bound and retain only the complete phase-adjusted Y0 divisor sum, with uniform `Cδ G log T` error. Nine modules, 38 public audits, 20 regressions. No analytic premise. The literal Y0 expansion is proved in the next row; uniform stationary reduction, sharp Atkinson inequality, twelfth moment and unconditional Add-est outputs remain open under EPZAE-21/37 |
| Literal Neumann two-term expansion toward Ivić Theorem 6.2 | native Schläfli kernel to exact decaying ray, complete arithmetic replacement and actual zeta consumers | `dfiBesselY0_eq_neumannLaplaceIntegral` proves the actual contour/branch bridge; `abs_dfiBesselY0_sub_neumannTwoTerm_le` gives explicit `K x^(-5/2)` error for every `x>0`. Physical support links this to `T^(-5/4) n^(-5/4)`. `exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le` sums the error using the genuine divisor series at `5/4` and gives `C G`; native complete Voronoi summability identifies the original series. `exists_zetaSquarePhysicalGaussian_atkinson_twoTerm_approximation` and `exists_zetaSquareLocalMean_le_atkinson_twoTerm` consume the complete replacement with uniform `Cδ G log T` error on `T^δ≤G≤T^(1/2-δ)`. Thirteen modules, 71 public audits, 25 regressions. No analytic premise or changed kernel. Uniform stationary reduction, sharp Atkinson inequality, genuine twelfth moment and all unconditional Add-est outputs remain open under EPZAE-21/37 |
| `add-bound (ii)`, critical line and twelfth power | uniform moment-to-zeta-polynomial large values | `zetaTwelfth_largeValueBound_of_dyadic` proves `IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))` for `σ ≥ 1/2`, `τ ≥ 2`, conditional only on the genuine dyadic critical-line twelfth moment. The actual Perron entry, window, logarithmic losses, and epsilon--delta conversion are proved. The moment itself and the general source parameters remain open under EPZAE-19/21 |
| Actual signed carriers toward Ivić Theorem 6.2 | actual power-weighted oscillatory integrals to uniform summand bounds and complete physical source identities | `exists_norm_atkinsonPowerIntegral_le` proves `norm(Iα)≤Cα G T^(-α)` for all real b and α, with Cα depending only on α, on `T>0, G>0, G²≤2T, L>0, 8L≤G`. The proof consumes the actual square-substituted amplitude and native first-derivative test in both orientations. `zetaAtkinsonTwoTerm_eq_carrierIntegral` proves all four signed quarter-power carriers with exact factors and n=0 handling; their complete weighted series is genuinely summable. `exists_norm_zetaAtkinsonTwoTerm_le` gives the actual `n^(-1/4)` and `n^(-3/4)` summand bounds, which are not summable majorants. `exists_zetaSquarePhysicalGaussian_carrier_approximation` and `exists_zetaSquareLocalMean_le_carriers` retain the complete carrier series and uniform `Cδ G log T` source error. Ten modules, 43 public audits, 24 regressions. No analytic premise. Uniform stationary main values, sharper arithmetic tails, sharp Atkinson inequality, genuine twelfth moment and all unconditional Add-est outputs remain open under EPZAE-21/37 |
| `add-bound (ii)`, exact coefficient-one source entry | sharp polynomial to localized critical-zeta convolution | `ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin` retains both integer endpoints and residue `mellin cutoff (1-it)`. `ZetaMellinUniform` and `ZetaMellinLocalization` prove physical-scale kernels and the far integral. `ZetaLargeValuePattern.perron_entry` bounds and absorbs both errors; `exists_zetaPerron_uniform_threshold` derives its physical conditions from all actual windows `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`. This critical-line entry edge is complete, not the full EPZAE-21 work package |
| Summable correction removal toward Ivić Theorem 6.2 | actual near/far signed carriers to a leading-only physical source | `exists_norm_atkinsonPowerIntegral_far_le` proves both signs with `Cα G T^(-α)/b` for `b≥8sqrt(T)` on the full physical support. `exists_norm_atkinsonCorrectionTerm_le` combines near and far ranges into the actual divisor-Dirichlet majorant at `5/4`; `exists_norm_atkinsonCorrectionSum_le` sums the entire correction with bound `C G`. `summable_atkinsonLeadingTerm` and `zetaAtkinsonTwoTermSum_eq_leading_sub_correction` justify the complete leading series. `exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation` and `exists_zetaSquareLocalMean_le_atkinson_leading` consume that error, retaining both leading carriers and uniform `Cδ G log T` source error. Four modules plus the generalized weighted-primitive helper; 19 new public audits, 16 regressions. No analytic premise or discarded source factor. Leading stationary main values, sharper leading arithmetic tails, sharp Atkinson inequality, genuine twelfth moment and all unconditional Add-est outputs remain open under EPZAE-21/37 |
| Coarse quantitative leading truncation toward Ivić Theorem 6.2 | actual C2 root amplitude to exact signed Fourier identity and finite physical source | `atkinsonPowerIntegral_eq_fourier` retains the Jacobian, constant unit phase and frequency `-2b sqrt(T)`. Constructed order-two bounds give `C G T^(5/4) |divisorDirichletTerm(5/4,n)|` for actual leading terms. `exists_norm_atkinsonLeadingSum_sub_finite_le` uses the true divisor series at `9/8` to give tail `C G T^(5/4) N^(-1/8)`. The Gaussian and local-mean consumers in `AtkinsonFiniteSource` use the `C G` consequence for every `N≥T^10`, on the original physical power-width range with uniform `Cδ G log T` error and no analytic premise. Fifteen modules, 59 public audits, 20 regressions. This establishes coarse polynomial truncation; the later continuations below prove the evaluated stationary mains and source-scale cutoff. Summed stationary errors and sharp Atkinson assembly, the twelfth moment and all unconditional Add-est outputs remain open under EPZAE-21/37 |
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

## Actual stationary source bridge toward Ivić Theorem 6.2

The source logarithmic saddle identities (Orsay (6.48)–(6.51)) and the
literal phase (6.22) now have exact consumers at both signed saddles.
`AtkinsonSignedStationaryMain` retains (-1)^n, both pi/4 signs,
the common actual quadratic Gaussian and separate actual cutoff/Mellin profiles.

`exists_atkinsonPowerIntegral_finite_stationary_approximation` consumes
the actual positive-support carrier and proves its finite-quadratic
main term with error Cα G T^(-α)[4/(pi H)+4(G/sqrt(T))H²+16T H⁴/r³].
The physical consumer derives containment for 10000n≤T and
0<H≤sqrt(T)/12, on T>0, G≥1, G²≤2T, L≥1, 8L≤G, for both signs.
These are locally proved reductions, not Ivić's complete sharp formula.
No stationary estimate is a theorem parameter.

Twelve modules, 71 named audits and 22 regressions are in the root and
`run_tao_trudgian_yang_build.bat` inventory. Fresnel evaluation is now
proved below. Sharp source localization/error summation, sharp Atkinson, genuine twelfth
moment and all unconditional Add-est outputs remain open under EPZAE-21/37.
The repaired powering chain and original counterexample are unchanged.

## Evaluated stationary main: exact source-phase continuation

`FresnelEvaluation` proves the negative-phase value (1-i)/(2sqrt(c))
and tail 2/(c H pi). `AtkinsonStationaryMain` substitutes it in the
actual carrier. `AtkinsonEvaluatedPhases` cancels the positive pi/4
and gives -i on the negative branch; both actual profiles and (-1)^n remain.

`exists_atkinsonPowerIntegral_source_power_saving` proves both
±sqrt(n) errors Cα G T^(-α) T^(-min(δ/3,1/10)) for 10000n≤T on
the original power-width range with L=log T, eventually.
This locally derived per-carrier estimate is not Ivić Theorem 6.2:
sharp source localization and a summed stationary error remain missing.
Nine modules, 35 audits and 16 regressions are in the exact runner scope.
The twelfth moment, EPZAE-21/37 and unconditional Add-est remain open.

## Source-scale leading truncation: actual consumers

The cutoff itself yields |b|≤3sqrt(T)L/G for a nonzero stationary main.
The actual carrier is restricted to its original root band; it does
not vanish merely because its stationary main does. Proved endpoints,
actual reciprocal-slope derivatives and two integrations by parts give
Cα G² T^(-α) L/(sqrt(T)n) for both signs when n≥36T(L/G)².

The ordinary-divisor Dirichlet series at 5/4 sums this tail.
`exists_zetaSquarePhysicalGaussian_atkinson_band_approximation` and
`exists_zetaSquareLocalMean_le_atkinson_band` consume it with
N≥36T(log T/G)², source factors 2 and 2exp(1), and Cδ G log T error.
The explicit ceiling cutoff eventually has 10000N≤T; every retained
index is linked to both evaluated stationary estimates.

This locally proved truncation is not the complete Ivić Theorem 6.2:
a sufficiently strong summed stationary error and remaining main
assembly are still required. Eleven modules, 53 audits and 22 regressions
are in the exact runner scope. The twelfth moment, EPZAE-21/37 and
unconditional Add-est remain open; the repaired chain is unchanged.

## Summed stationary approximation: source factors and width restriction

The actual carrier's symmetric integral kills the linear amplitude and
cubic phase terms exactly. On T^(1/4)≤G≤sqrt(T), the derived radius gives
Cα G sqrt(G) T^(-α-1/4) for both signs and every 10000n≤T.

`atkinsonStationaryLeadingSum` uses both original Bessel coefficients,
ordinary-divisor weights and separate evaluated source profiles. Its
finite-support theorem consumes the actual cutoff; no summability is
postulated. The quarter-weighted divisor prefix, the same ceiling cutoff
and logarithmic absorption give the full leading error O(G+T^(1/4+ε)).

The Gaussian and local-mean consumers retain factors 2 and 2exp(1).
Their error is Cδ,ε (G log T+T^(1/4+ε)) for G≥T^(1/4), and
Cδ,κ G log T for G≥T^(1/4+κ), within the original power-width range.
This is not the full-width source Theorem 6.2 or its final Atkinson
main-amplitude assembly. Those obligations and the genuine twelfth
moment remain open. Ten modules, 43 audits and 24 regressions cover
this continuation; no Add-est output or frozen contract changed.

## Normalized main and partial-summation checkpoint

Five new modules, 30 named audits and 24 regressions derive the actual
common fourth-root coefficient from the original saddle power, curvature
and Bessel constants. Both signed main sums retain separate cutoff/Mellin
weights. Only the raw phase sums are conjugated.

The actual weights have a proved uniform bound
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) on n≤T,
T,G,L>0, G²≤2T and 8L≤G. The exact Abel bound retains literal finite
weight differences. Both physical zeta consumers are linked to the same
explicit source cutoff and normalized mains. Errors remain
Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or Cδ,κ G log T above
T^(1/4+κ), within the original power-width range.

The continuation below proves uniform damped variation and the actual
source-block bound. Global dyadic/Gram assembly, smaller source widths or
a proved lower-value-range reduction, and the genuine twelfth moment remain open. No unconditional Add-est clause is closed.
The original counterexample and corrected powering/Heath–Brown chain
are unchanged. The exact `run_tao_trudgian_yang_build.bat` inventory
is synchronized; maintain it and rerun both principal evaluation scopes.

## Damped variation and source-block checkpoint

Six new modules, from `FiniteWeightVariation` through
`AtkinsonPhaseBlockBound`, have 36 named public audits and 24 regressions.
The actual Gaussian increments telescope against a decreasing real
envelope. Ordered actual saddle samples, the constructed Mellin bound,
both original cutoff transitions and the decreasing fourth-root
coefficient give uniform variation for both separate normalized weights.

`exists_finiteVariationBound_atkinsonMainWeights` bounds both the
supremum on indices 0..N and the adjacent-difference sum by
C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)), for
T,G,L>0, G²≤2T, m>0 and 10000(m+N)≤T.
No 8L≤G condition or conjugacy of residual weights is assumed.

The actual stationary Bessel/divisor block at m..m+N-1 is bounded by
that same shape times the maximum of the actual raw phase partial sums,
with a larger uniform C. `exists_atkinsonSourceCutoff_block_bound`
derives its small-frequency and scale conditions for every retained
block from the original power-width range and the exact source ceiling
cutoff, beyond a δ-dependent threshold.

ZVB records these proved consumers; the continuation below also proves
global dyadic assembly. The phase-sum/Gram bound, smaller-width stationary errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
The block theorem has no fourth-root-width restriction; the earlier
stationary-error/zeta consumer still does. No unconditional Add-est
clause or full EPZAE-00--41 completion is claimed.

The original counterexample and independent-coordinate powering/
Heath–Brown chain are unchanged. The exact
`run_tao_trudgian_yang_build.bat` root/audit/PowerShell inventory is
synchronized; maintain it and rerun both principal evaluation scopes.
See the Reproduction Manifest for the semantic audit and terminal evidence.

## Complete dyadic-source checkpoint

Three new modules, `TruncatedDyadicPartition`, `AtkinsonDyadicMain`
and `AtkinsonDyadicZetaConsumer`, have 20 named public audits and
24 regressions. The exact partition uses M=2^j and block length
min(M,N-M), for j<clog(2,N). Every retained endpoint stays at or below
the original cutoff; zero/one cutoffs and exact powers of two are covered.

The actual complete stationary Bessel/divisor series is now bounded by
C G T^(-1/4) times the sum of
M^(-1/4) exp(-G²M/(12T)) times the actual block phase-prefix maximum.
The same source ceiling cutoff supplies every block's small-frequency
geometry. Enlarging only the last raw phase maximum to a full block
does not enlarge the stationary source.

Four Gaussian/local-mean consumers use this complete dyadic bound.
Their error remains Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or
Cδ,κ G log T for G≥T^(1/4+κ), within the original power-width range.
The stationary-main bound itself has no fourth-root-width restriction.
ZDA records this exact assembly and these physical consumers.

Global dyadic assembly is now proved. The maximal phase-sum/Gram
estimate, the source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.
