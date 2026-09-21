# Tao--Trudgian--Yang 2025 source-to-Lean crosswalk

Current analytic progress: [Jutila physical-scale smoothing and uniform pattern bounds](#jutila-physical-scale-smoothing-and-uniform-pattern-bounds--current-checkpoint).
The moments and full-domain clauses (i)--(ii) are proved; clauses (iii)--(ix) and the full goal remain open.
Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


## Status key

- **Available:** an upstream source or local theorem exists; no target bridge
  is claimed.
- **Planned:** statement/module design only.
- **Kernel-checked:** reserved for a compiled theorem with audited dependencies.

Current kernel-checked infrastructure comprises EPZAE-00--05, EPZAE-07--08,
EPZAE-16--17, EPZAE-20, EPZAE-22--23, EPZAE-25, EPZAE-31--32, and
EPZAE-34--35, together with the precisely scoped partial results below.
`Add-est (i)` is now proved on its full closed interval by `add_est_i`.
The other eight clauses and all exponent-pair/density public outputs remain planned.

## Public result ledger

| Paper label | Exact source conclusion | Planned Lean home | Checklist |
|---|---|---|---:|
| `new-exp-pair` | `(89/1282,997/1282)`, `(652397/9713986,7599781/9713986)`, `(10769/351096,609317/702192)`, and `(89/3478,15327/17390)` are exponent pairs | `NewExponentPairs.lean` | EPZAE-14 |
| `hb-density2` | `A(sigma) <= 3/(10 sigma-7)` for `7/10 < sigma <= 1` | `ImprovedHeathBrownDensity.lean` | EPZAE-26 |
| `bourgain-density-improved` | `A(sigma) <= max(2/(9 sigma-6), 9/(8(2 sigma-1)))` for `17/22 <= sigma <= 4/5` | `ImprovedBourgainDensity.lean` | EPZAE-27 |
| `bourgain-zero-density-optimized` | eight-piece bound below | `BourgainOptimizedDensity.lean` | EPZAE-29 |
| `Add-est` | nine energy bounds below; clause (i) proved, (ii)--(ix) open | `NewAdditiveEnergy.lean` (installed for clause (i)) | EPZAE-37 |

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

Global dyadic assembly is now proved; the continuation below proves
finite maximal-prefix Gram assembly. The numerical phase-difference
estimates, source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.

## Height-dependent maximal Gram checkpoint

Eight production modules, from `FinitePrefixGram` through
`AtkinsonGramPhysicalCutoff`, add 41 named public theorem audits
and 24 `HeightDependentPrefixGramRegression` examples.

Finite Gram duality now consumes the actual divisor coefficients and
raw phase sums on [M,M+j). Each height has its own maximizing prefix;
the exact paired Gram entry uses the minimum of the two prefix lengths.
Its finite maximum has diagonal M and is symmetric in the two heights.
The separate arithmetic theorem proves coefficient energy
E(M,N)≤Cε M^(1+ε) for 0<M and N≤M; it does not assert a sharp
logarithmic divisor-square asymptotic.

The actual complete stationary packet and two actual local-mean excess
packets now consume the maximal Gram inequality. Their common cutoff is
derived from the source: for heights in [H,2H], it is bounded by
ceil(72H(log(2H)/G)²). The nonnegative Gram budget, not the stationary
source, is enlarged. Gaussian damping is removed by a proved upper bound;
the final budget retains literal coefficient energy E.

The stationary packet bound requires only the original power-width
range, eventually. The local-mean excess subtracts the proved error
Cδ,ε(G log t+t^(1/4+ε)) with G≥t^(1/4), or Cδ,κ G log t with
G≥t^(1/4+κ). Those restrictions are not discharged.
ZMG is DONE for finite maximal Gram assembly and these actual physical
consumers. The continuation below proves uniform truncated cancellation and its
physical consumers; ZGB retains separated-height summation and scale
optimization as open.

The source-form bridge, smaller-width error or a proved lower-value
reduction, genuine twelfth moment and unconditional Add-est remain open.
EPZAE-21/37 and the complete EPZAE-00--41 goal are unchanged.
The original counterexample and proved independent powering/
Heath–Brown chain remain intact; no false fifth-coordinate scaling returns.

Maintain all eight root imports, 41 named audits, 24 regressions and
the exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`.
Update that interface and its implementation as needed, and run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records semantic fidelity separately from terminal build/audit evidence.

## Uniform truncated cancellation and numerical source budgets

Thirteen production modules, from `AtkinsonIndexPhase` through
`AtkinsonArithmeticGapPackets`, add 79 named public theorem audits
and 30 `TruncatedPhaseCancellationRegression` examples.

The literal source phase now has proved real-index slope, curvature,
height variation and uniform box bounds. Native second-derivative
cancellation and decreasing-increment Kusmin–Landau are applied to
every prefix [M,M+j), j≤N, with fixed ambient parameters. The result
covers empty prefixes, both height orders and the exact diagonal.
It is not an application of a full-block bound to an unknown prefix.

The resulting numerical entry majorant takes the minimum of N, the
explicit B-process expression and, when its exact half-period condition
holds, the reciprocal-gap first-derivative bound. It retains the physical
height gap and radical scales; no oscillatory sum remains in this
majorant.

The actual cutoff at 2H supplies every full block's two extra mean-value
endpoints: eventually 2*ceil(72H(log(2H)/G)²)+2≤H from H^δ≤G.
That lower-width condition is derived from an actual height in a
nonempty source packet; empty packets are handled separately.

All three actual stationary/local-excess packets consume the numerical
entry bounds. The final `arithmeticGap` versions also consume
E(M,M)≤Cη M^(1+η), yielding the explicit dyadic weight M^(1/2+η).
Their right sides have no unevaluated phase sum or coefficient-energy
sum. The local-mean errors and G≥t^(1/4), or G≥t^(1/4+κ), remain
unchanged; the stationary-only bound has no such restriction.

ZPC is DONE for uniform truncated cancellation, derived physical
geometry and these actual numerical consumers. ZGB is OPEN for
separated-height summation of the explicit gap bounds and scale
optimization. No height-separation estimate is claimed by the present
finite double sum. The source-form bridge, smaller-width error or a
proved lower-value reduction, genuine twelfth moment and unconditional
Add-est remain open. EPZAE-21/37 and the full EPZAE-00--41 goal are
unchanged.

Maintain all thirteen root imports, 79 named audits, 30 regressions and
the exact backing inventory of `run_tao_trudgian_yang_build.bat`.
Update that interface and its implementation as needed and run both
principal evaluation scopes. The original counterexample remains
byte-preserved, with the corrected independent powering witnesses and
actual Heath–Brown application intact. No false fifth-coordinate
scaling or third witness returns. See the Reproduction Manifest for
the separate semantic and terminal verification evidence.

## Constructed covering and local-mean counts — preceding checkpoint

EPZAE-21 now proves a sixth-power superlevel counting estimate for
the actual critical-line local zeta integral. For every δ>0, ε>0
and ν>0 there are C,D>0 and H0≥40000, before H,G,Y,W, such that

```text
card {t in W : C*(G*log(t)+t^(1/4+ε)) + Y
                 <= integral_(t-G)^(t+G) |zeta(1/2+i*u)|^2 du}
 <= D*H^ν * (H/(G*Y^2) + H^2/Y^6).
```

The hypotheses are H≥H0, G>0, Y>0, G-separation of W, and for
each t in W, `H<=t<=2H`,
`t^δ<=G<=t^(1/2-δ)`, and `t^(1/4)<=G`.
The above-fourth-root version instead has error `C*G*log(t)`
and requires `t^(1/4+κ)<=G`, κ>0. All source restrictions
remain explicit. Both theorems count the literal integral's
superlevel set; no analytic packet estimate, prescribed covering,
absorption inequality or cardinality bound is a premise.

The preceding physical packet theorem remains installed:
the square of the sum of actual excesses is at most
`D0*H^a*(R*H/G+R^2*sqrt(G*L))`, with uniform constants
before the localization interval. Its cutoff/logarithmic optimization,
including the literal source ceiling and derived width bounds,
is unchanged.

The new deduction constructs the length and bins. Put
`A=D0*H^a` and `L=(Y^2/(4*A))^2/G`. Then L>0 and

```text
sqrt(G*L) = Y^2/(4*A)
2*A*sqrt(G*L) <= Y^2.
```

The bin of t is `floor((t-H)/L)`. Its actual fiber is contained
in `[H+k*L,H+(k+1)*L]`; the bins partition W for
`0<=k<floor(H/L)+1`. This includes the terminal height 2H,
even when H/L is integral. Separation and every original source
range are inherited by each fiber.

On a fiber whose actual excess is at least Y, the packet inequality
and the proved absorption give `R<=2*A*H/(G*Y^2)`.
Summing the exact fiber cardinalities and paying the final bin gives

```text
card(W) <= 2*A*H/(G*Y^2) + 32*A^3*H^2/Y^6.
```

Choosing the packet exponent a=ν/3 and absorbing constants yields
the displayed global estimate. The exact positive-threshold
equivalence between excess≥Y and integral≥error+Y is proved,
then used on the actual filtered superlevel set.

Four root-reachable modules are installed:
`AtkinsonCardinalityAbsorption`, `AtkinsonHeightCover`,
`AtkinsonGlobalCardinality` and `AtkinsonLocalMeanCounting`.
All 17 new public theorems have named audits. The 27 new regressions
cover every public theorem type, exact chosen-length arithmetic,
empty fibers, unit/terminal bins, zero threshold geometry and the
complete source-consumer signatures. Earlier work remains installed.

ZLC is complete for constructed covering, absorption and actual
local-mean superlevel counting. This is not yet a pointwise zeta
large-value count: the entry from point values to these local
integrals, a compatible physical width choice, an occupancy-preserving passage
from unit-separated points to G-separated local windows, and the
remaining value-range reduction are still required. ZGB, ZAT, the genuine
critical twelfth moment ZTM, all unconditional Add-est conclusions,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Preserve the original Lemma 62 counterexample byte-for-byte.
The corrected independent ρ/k and ρ*/k witnesses, independent
fifth coordinates and actual Heath–Brown application are unchanged.
Never restore false s-scaling or a third s-preserving witness.
Maintain and update `run_tao_trudgian_yang_build.bat` and its
backing implementation as needed; its exact inventory includes
all four new modules. Run it and `run_lake_build.bat` after
relevant changes. Keep the full goal active.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions and linter
failures. The target audited 2,847 declarations (2,842 discovered
target theorems plus five imported contracts); all 27 new regressions
passed. Exact commands, logs, hashes and coverage are in the current
Reproduction Manifest. This verifies local-integral superlevel counting,
not pointwise zeta large values, the twelfth moment or Add-est.

## Point-entry kernels and literal zeta overlap — preceding checkpoint

The preserved Lemma 62 counterexample and the proved corrected two-witness
powering/Heath–Brown chain are unchanged. EPZAE-21 now additionally proves
the Gamma-kernel and bounded-overlap components needed for point-value entry.

For every 0<δ≤1/4 and a,b independently chosen from {δ,-δ}, the
literal product

```text
P(a,b,u,w) = |Gamma(a+i*w)| |Gamma(b+i*(u-w))|
```

is integrable in w, and a single absolute C>0 gives
`integral P <= (C/δ)*exp(-|u|)`. The public consumer
`exists_pointMeanGammaProduct_integral_le` derives integrability and
uses both proved shifted-Gamma bounds and the numerical convolution.
Its height-linked companion
`exists_pointMeanGammaProduct_log_integral_le` substitutes
δ=1/log(t), derives 0<δ≤1/4 from t≥exp(4), and proves
`integral P <= C*log(t)*exp(-|u|)`. Both displacement signs and
zero ordinate are retained; no Gamma or convolution estimate is assumed.

For a unit-separated finite W, the actual exponential kernels satisfy
`sum_(t in W) exp(-|t-u|) <= 4`. The moving-window consumer
`sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment` proves

```text
sum_(t in W) integral_(t-L)^(t+L)
  exp(-|t-u|) |zeta(1/2+i*u)|^2 du
 <= 4 * integral_(center-G)^(center+G) |zeta(1/2+i*u)|^2 du.
```

It assumes G,L≥0, W⊂[center-G/2,center+G/2],
G/2+L≤G and unit separation. It derives every interval enlargement
and finite integral interchange. The cost is the absolute factor four,
not the cluster occupancy or the physical width G.

The previously proved local-integral superlevel count remains:
`card <= D*H^ν*(H/(G*Y^2)+H^2/Y^6)`, with all original physical
width restrictions, actual source errors, positive thresholds and
uniform constant dependencies retained. This new overlap theorem does
not yet connect pointwise zeta largeness to that count.

Eight root-reachable modules are installed: `PointMeanDigamma`,
`PointMeanGammaShift`, `PointMeanGammaDecay`, `PointMeanGammaKernel`,
`PointMeanGammaConvolution`, `PointMeanExponentialOverlap`,
`PointMeanIntegralOverlap` and `PointMeanGammaProduct`.
All 38 public theorems have named audits; 46 new regressions cover
their exact types and shell endpoints, empty sets, zero ordinates,
and the negative displacement. Seven modules adapt inspected node-74
proofs to the existing target/native imports and actual
`zetaMomentCriticalNorm`; the eighth supplies new literal Gamma consumers.
No adjacent package, dependency pin, source archive, or frozen foundation
has been changed.

ZGK is complete only for the literal Gamma convolution and its
height-linked logarithmic bound. ZEO is complete only for the actual
exponential local-integral overlap. The complete contour proof of
Heath–Brown Lemma 3 is NOT yet installed in this target. Its residue,
displaced zeta bounds, horizontal edges, truncated tail and compact range
remain to be assembled. Pointwise large-value counting also still needs
occupancy-aware clustering, compatible G selection and the lower-value
reduction. ZGB, ZAT, ZTM, unconditional Add-est, EPZAE-21/37 and the full
EPZAE-00–41 completion contract remain OPEN.

Preserve `EnergyPoweringObstruction.lean` byte-for-byte. Never restore
false s-scaling or a third s-preserving witness. The independent ρ/k and
ρ*/k witnesses and actual Heath–Brown application remain intact.
Maintain and update `run_tao_trudgian_yang_build.bat` and its backing
implementation as needed, including all eight modules in the exact
inventory. Run it and `run_lake_build.bat` after relevant changes.
Keep the full goal active.

Verification (2026-09-21): both principal runners reached terminal
exit 0 with zero Lean errors, warnings, tactic suggestions or linter
failures. The target audited 2,890 declarations (2,885 discovered
target theorems plus five imported contracts); all 46 new regressions
passed. The foundation audit covered 14,290 declarations and its
manifest reports PASS with no failed stages. Exact logs and hashes
are in the current Reproduction Manifest. This verifies the Gamma
and overlap components, not the still-open pointwise zeta entry,
twelfth moment or unconditional Add-est.

## Heath–Brown point-to-local-mean entry — historical checkpoint

The original Lemma 62 counterexample is preserved byte-for-byte. The corrected
independent cardinality and energy witnesses, and their proved Heath–Brown
application, are unchanged. This checkpoint closes an analytic input to the
remaining zeta/Add-est branch; it does not change the frozen public outputs.

`heathBrownLemmaThree_native` now proves the complete source-shaped estimate:
one absolute C>0 works for every t≥10,

```text
|zeta(1/2+i*t)|^2
 <= C*log(t)*(1 + integral_(-log(t)^2)^(log(t)^2)
      exp(-|u|)*|zeta(1/2+i*(t+u))|^2 du).
```

The proposition and moment definitions unfold to this literal integral.
The proof derives the smoothed divisor Mellin identity, both pole residues,
the infinite shifts, both displaced-line estimates, the finite rectangle's
four edge bounds, the full-to-truncated tail estimate and the compact range.
The strong Gamma reserve makes the nested integral lose only δ⁻¹;
δ=1/log(t) is linked to the source height. None of these estimates is an
analytic hypothesis of the final theorem.

`heathBrown_equation44_native` consumes that theorem and the actual
factor-four exponential-overlap theorem. For R=card(W) it proves

```text
V^2*R <= C*log(T)*(R + 4*integral_(center-G)^(center+G)
                                  |zeta(1/2+i*u)|^2 du).
```

Here T≥10, V>0, G,L≥0; W is unit-separated and contained in
[center-G/2,center+G/2]⊂[10,T]; every t∈W has log(t)^2≤L;
G/2+L≤G; and every t∈W satisfies V≤|zeta(1/2+i*t)|.
All parameters follow the absolute constant. The final consumer has no
Lemma-3 hypothesis and does not discard cluster occupancy.

Nineteen additional production modules are root-reachable and included in
the exact inventory behind `run_tao_trudgian_yang_build.bat`.
There are 129 new public theorem audits and 136 new regressions, including
the unfolded literal source inequality and the endpoints t=10 and t=exp(4).
The adjacent node-74 proof bodies were inspected and adapted to existing
target/native imports; unrelated import chains were not added. No package
pin, source archive, counterexample or adjacent project was changed.

ZL3 is complete for the full source Lemma 3; ZQ44 is complete for its
literal finite peak-to-local-integral consumer. ZGB still needs constructed
occupancy-aware clusters, compatible physical width selection, absorption
of the actual local-source error, and the remaining value ranges.
The installed local-integral superlevel count still has its original
fourth-root width restrictions. ZAT, ZTM, unconditional Add-est,
EPZAE-21/37 and the full EPZAE-00–41 goal remain OPEN.

Keep the complete goal active. Preserve `EnergyPoweringObstruction.lean`
and the independent fifth coordinates; never reintroduce false s-scaling
or a third s-preserving witness. Maintain the principal
`run_tao_trudgian_yang_build.bat`, its backing implementation, root imports,
exact inventory, audits and regressions as the proof grows. After relevant
changes, run both it and the foundation's `run_lake_build.bat`.

Verification (2026-09-21): both principal scripts were polled to terminal
exit 0. The target reports `LEAN VERIFICATION PASS`, covering all 299
package files and 3,104 audited declarations (3,099 discovered target
theorems plus five imported contracts). All 129 new named audits and
136 new regressions pass. The foundation reports `PASS`, with 14,290
discovered theorems audited and all six stages passed. Neither final
evaluation has a Lean error, warning, tactic suggestion or linter failure.
Exact logs, hashes and the repaired intermediate comment-scan failure are
recorded in the current Reproduction Manifest. The counterexample hash is
unchanged. This verifies Lemma 3 and the finite point-entry consumer;
occupancy-aware counting, the genuine twelfth moment, unconditional Add-est
and the full goal remain open.

## Occupancy-preserving peak count and derived growth — historical checkpoint

The printed Lemma 62 counterexample is still byte-preserved. The proved
corrected two-witness powering, independent fifth coordinates and actual
Heath–Brown energy application are unchanged.

Three additional EPZAE-21 consumers are now proved:

- `exists_pointValue_card_le_with_width` counts the original unit-separated
  zeta peaks, retaining every cluster occupancy. Half-G floor bins keep
  occupied centers in [H,2H], including the terminal endpoint. Both parity
  classes are G-separated. The actual equation-(44) entry and Atkinson
  excess count bound each occupancy superlevel; exact layer-cake summation
  and the inverse-square sum recover all points with no factor G loss.
- `exists_pointValue_card_le_source_range` constructs
  G=V²/(K log(3H)²), absorbs the actual source error and derives all window
  and width conditions. For δ,κ,ν>0 with δ≤1/4, there are K,D>0 and H₀≥40000,
  chosen before H,V,W, such that for H≥H₀ and V>0,
  `K log(3H)² (2H)^(1/4+κ) ≤ V² ≤ K log(3H)² H^(1/2−δ)`,
  every unit-separated W⊂[H,2H] with |ζ(1/2+it)|≥V satisfies
  `card(W) ≤ D H^ν (H log(3H)^4/V^6 + H² log(3H)^6/V^12)`.
  The fourth-root margin is retained, not removed.
- `exists_zetaMomentCriticalNorm_lt_sixth_power` proves that for every ε>0
  there is H₀≥40000 such that H≥H₀ and H≤t≤2H imply
  |ζ(1/2+it)|<H^(1/6+ε). A singleton peak at H^(1/6+η),
  η=min(ε,1/48), satisfies the proved source range but its cardinality bound
  is eventually less than one. This derives the actual zeta growth estimate;
  it does not assume one or substitute a Dirichlet-block estimate.

The six modules `FiniteOccupancy`, `PointClusters`, `PointClusterEntry`,
`PointClusterCounting`, `PointValueWidth` and `PointValueGrowth` are covered
by the root and exact production inventory. Their 29 public theorems have
named audits, and 37 added regressions check every public type plus actual
endpoints, occupancy, parity and the unfolded zeta-growth conclusion.

Architecture nodes ZOC, ZVW and ZPG record these exact consumers as DONE.
ZGB remains OPEN for the remaining value-range reductions and their
moment-ready aggregation. ZAT's smaller-width/source-form bridge, the genuine
dyadic twelfth moment ZTM, all unconditional Add-est clauses, EPZAE-19/21/37
and the full EPZAE-00–41 goal remain OPEN. This critical-line growth result
does not complete the distinct exponent-pair-to-mu contract EPZAE-15.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation as
needed: root imports, exact inventory, named/exhaustive audits and regressions
must grow together. Run both principal scripts after relevant changes.
Preserve the counterexample and do not restore false s-scaling or a third
s-preserving witness. No dependency pin, source archive or adjacent proof
was changed in this checkpoint.

Verification (2026-09-21): both principal runners reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 305 package files, 316 Lean
files in its integrity scan, 3,187 audited declarations (3,182 discovered
target theorems plus five imported contracts), all 29 new named audits and
all 37 added regressions passed. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final evaluations
have zero Lean errors, warnings, tactic suggestions or linter failures.
The counterexample SHA256 is unchanged. Exact logs, hashes and repaired
focused-build diagnostics are recorded in the current Reproduction Manifest.
This verifies the occupancy/width consumers and actual critical-line growth,
not the genuine twelfth moment, unconditional Add-est or the full goal.

## High-value twelfth moment and fourth-moment reduction — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. Corrected
cardinality/energy powering, the independent ρ/k and ρ*/k witnesses with
independent fifth exponents, and the actual Heath–Brown energy application
remain unchanged.

The following actual-zeta consumers are now proved. Write
S(H,V)={t∈[H,2H] : |ζ(1/2+it)|≥V}. For every ε>0 and sufficiently large H,
uniformly for V≥H^(1/8+ε):

- `exists_pointValue_twelfth_weighted_card_le` gives
  card(W) V^12≤H^(2+ε) for every unit-separated W⊂S(H,V).
  There is no upper-amplitude hypothesis: the proved actual growth estimate
  controls that range, and the source-width and logarithmic margins are paid.
- `exists_volume_pointValueSuperlevel_le` gives
  volume(S(H,V))≤2H^(2+ε)/V^12. A maximal finite separated family is
  constructed from the proved cardinality bound; its closed unit balls
  cover the entire superlevel set, with the factor two accounted for.
- `exists_zeta_twelfth_high_integral_le` proves
  integral over S(H,H^(1/8+ε)) of |ζ(1/2+it)|^12≤H^(2+ε).
  The actual measure bound, actual height-cube bound for |ζ|^12 and exact
  logarithmic layer-cake integral are composed without analytic hypotheses.

`zeta_twelfth_integral_le_high_add_fourth` proves the exact low/high
reduction: the full twelfth moment on [H,2H] is at most the high-set
integral plus V^8 times the unweighted fourth moment on [H,2H].
`zeta_twelfth_dyadic_of_fourth` performs the full deduction but is
explicitly CONDITIONAL on the genuine upstream estimate

```text
for every η>0 there exist C≥0 and H₀, chosen before H, such that
H≥H₀ and H>0 imply integral_H^(2H) |ζ(1/2+it)|^4 dt ≤ C H^(1+η).
```

That unweighted fourth-moment instance is still OPEN. The foundation's
`twistedZetaFourthMoment_native` instead bounds the fourth power of a
short Möbius polynomial multiplied by ζ; its factor cannot simply be
removed. No mollified result is claimed to prove the unweighted estimate.

The six modules `PointValueRanges`, `PointValueMeasure`,
`TruncatedLayerCake`, `PointValueTailIntegral`,
`PointValueHighMoment` and `PointValueLowMoment` are in the root and exact
production inventory. All 24 public theorems have named audits; 30 new
regressions cover their exact signatures, boundary cases and the literal
high-value zeta integral. ZHR/ZHM and the reduction ZLF are DONE; ZGB now
identifies the missing genuine fourth-moment source theorem. ZTM, ZAT,
EPZAE-19/21/37, unconditional Add-est and the full EPZAE-00–41 goal remain OPEN.
No other frozen public output or acceptance test is weakened.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed, including root imports, exact module coverage, named/exhaustive
audits and regressions. Run both principal scripts after relevant changes.
Preserve the counterexample, never restore false s-scaling or a third
s-preserving witness, and keep the full goal active. No source pin,
archive or adjacent/native proof was changed in this checkpoint.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 311 package files, 322 Lean
files in its integrity scan, 3,232 audited declarations (3,227 discovered
target theorems plus five imported contracts). All 24 new named audits
and all 30 added regressions pass. The foundation reports `PASS`: all six
stages passed, with 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample SHA256 is unchanged; source and runner hashes
were rechecked after both gates. Exact logs, hashes and repaired focused
diagnostics are in the current Reproduction Manifest. These gates verify
the high-value bound and explicitly conditional fourth-moment deduction,
not the missing fourth-moment instance, unconditional Add-est or full goal.

## Actual fourth-moment contour bounds and mixed-line truncation — historical checkpoint

The printed Lemma 62 counterexample is preserved byte-for-byte. The
authorized corrected cardinality/energy powering, independent ρ/k and
ρ*/k witnesses (with independent fifth exponents), and actual Heath–Brown
energy application remain unchanged. False s-scaling is not restored.

The new source is genuinely unweighted zeta. Write
J(t)=zetaSquareDivisorIntegral(-t)/zetaSquareGammaNormalization(t).
`zetaSquareNorm_eq_two_re_fourthRightPiece` proves
|ζ(1/2+it)|²=2 Re J(t), and `zeta_fourth_le_four_mul_rightPiece_sq`
proves |ζ|⁴≤4|J|². The actual Gamma quotient and pole factors are retained;
the native mollified fourth-moment theorem is not substituted.

`exists_norm_zetaFourthKernel_le` proves, for each c>0, a constant K_c>0
chosen before t and u such that t≥4 and t≥4c imply
|K(t,c+iu)|≤K_c t^c exp(-98u²) on the complete line. Near-height
Gronwall bounds and far-height Gamma bounds are both consumed.
A separate, height-dependent strip bound justifies holomorphy,
integrability and disappearing horizontal sides; it is not advertised
as the uniform moment bound.

`zetaFourthContribution_line_eq` proves equality of each actual
integrated ordinary-divisor contribution on any two positive lines.
`hasSum_zetaFourthContribution` transports the convergent integrated
series from c=1. This does NOT assert pointwise Dirichlet-series
convergence to the left of its half-plane.

For t≥0, a,b>0 and any finite S, the actual source now satisfies
J(t)=Prefix(t,a,S)+Tail(t,b,S). The prefix is proved equal to the
integral of the finite ordinary-divisor polynomial times the actual kernel.
For b>3/2, one constant K_b>0 works for all t≥max(4,4b) and all S:
|Tail|≤K_b t^b Σ_(n∉S) d(n)n^(-1/2-b).
The displayed positive tail is summable, not an assumed small error.
`exists_zeta_fourth_le_prefix_add_weightTail` consumes these results
to bound the literal |ζ|⁴ by eight times the squared prefix norm plus
eight times the squared displayed tail bound.

Twelve new `ZetaFourth*` modules are root-reachable and in the exact
production inventory; 53 public theorems have named dependency audits.
Sixty new regressions cover every signature, zero/empty/singleton cases,
different contour lines and literal critical-zeta consumers. The final
principal-runner evidence is recorded below.

Z4K (uniform kernel) and Z4C (actual mixed-line truncation) are supporting
results, not the unweighted fourth-moment theorem. ZGB still requires the
finite-polynomial mean square, quantitative cutoff-tail decay and their
integrated assembly. Thus ZGB/ZTM/ZAT, EPZAE-19/21/37, unconditional Add-est
and the full EPZAE-00–41 goal remain OPEN. No frozen public contract is
weakened, and no source pin, archive or adjacent/native proof is changed.

Maintain `run_tao_trudgian_yang_build.bat` and its backing implementation
as needed: exact module coverage, root imports, named/exhaustive audits and
regressions are part of the goal. Run it and `run_lake_build.bat` after
relevant changes; a passing audit establishes integrity, not completion
of the missing moment or of all advertised Add-est clauses.

Verification (2026-09-21): both principal scripts reached terminal exit 0.
The target reports `LEAN VERIFICATION PASS`: 323 package files, 334 Lean
files in its integrity scan, 3,296 audited declarations (3,291 discovered
target theorems plus five imported contracts). All 53 new named audits
and 60 added regressions pass. The foundation reports `PASS`: all six
stages passed and 14,290 discovered theorems audited. Both final
evaluations have zero Lean errors, warnings, tactic suggestions or linter
failures. The counterexample is byte-preserved; all source/runner hashes
were rechecked after both gates. Exact logs, hashes and the repaired
comment-scanner false positive are in the current Reproduction Manifest.
These gates verify the actual contour and truncation consumers, not the
missing fourth-moment integral, unconditional Add-est or the full goal.

## Unweighted moments and Add-est (i) — historical checkpoint

The printed Lemma 62 singleton counterexample is preserved byte-for-byte.
The corrected theorem still returns independent ρ/k and ρ*/k witnesses,
with independent existential fifth coordinates. No false s'/s scaling or
third s-preserving witness is restored.

`zeta_fourth_dyadic` now proves the genuine unweighted estimate: for every
η>0, constants C≥0 and H₀ are chosen before H, and H≥H₀, H>0 imply
integral_H^(2H) |ζ(1/2+it)|⁴ ≤ C H^(1+η).
It consumes the actual normalized divisor-contour source, not the native
mollified fourth moment and not an assumed fourth-moment bound.

The finite prefix is exactly {1,...,2^M}, including its first coefficient.
Unit-modulus endpoint twists prove a mean square uniform under every real
imaginary translation u, including the reflected phase u-t. The ordinary
divisor coefficient-square bound is derived from the native divisor bound.
Weighted Cauchy–Schwarz, product integrability and Fubini are proved for the
actual Gaussian kernel and complete finite polynomial.

The separate right line b=2+2/δ gives an actual bounded tail when
N≥H^(1+δ), uniformly for H≤t≤2H. A dyadic N between H^(1+q) and
2H^(1+q), with q=min(η,1)/20, pays the block-count loss. The exact exponent
1+5q+2q² is at most 1+7q≤1+η. Neither the cutoff error nor the polynomial
mean square remains a theorem parameter.

`zeta_twelfth_dyadic` applies the installed high/low decomposition to this
proved fourth moment. For every ε>0 it gives constants D≥0 and H₀ before H:
integral_H^(2H) |ζ(1/2+it)|¹² ≤ D H^(2+ε).
`zetaTwelfth_largeValueBound` and its short-height companion discharge
the actual Perron consumers: LV_ζ≤2τ−12(σ−1/2) for σ≥1/2, τ≥2,
and for σ≥3/4, τ≥3/2, respectively.

`add_est_i` in `NewAdditiveEnergy.lean` proves the literal printed clause on the entire
closed interval 3/4≤σ≤5/6:

```text
A*(σ)(1−σ) ≤ max((18−19σ)/(2(3σ−1)), 4(10−9σ)/(5(4σ−1))).
```

The actual declarations are `add_est_i`, `add_est_i_bound` and
`add_est_i_zero_energy` in `NewAdditiveEnergy.lean`.
The last exposes ∀ε>0 ∃C≥1 ∃δ>0 ∀T≥C, with the genuine shifted zero
energy at σ−δ, preserving analytic multiplicities and unit tolerance.
The epsilon--delta bound is proved first; the extended-real infimum
inequality is its consequence, not a substitute. At σ=3/4 the rate is
3/2 and A*≤6; at σ=5/6 the rate is 6/7 and A*≤36/7.

The dependency chain consumes corrected powering, the actual Heath–Brown
energy relation, certified general/zeta optimization, the proved twelfth
moment, and the proved endpoint-one zero-energy transfer. The separate
EPZAE-33 endpoint-two theorem is not assumed and remains open.

Seventeen new production modules are root-reachable and explicitly listed
in the batch runner's inventory. All 49 new public theorems have named
dependency audits. Sixty-one new regressions cover every public signature,
literal zeta integrals, coefficient/prefix endpoints, negative translated
intervals, both LV threshold boundaries and both printed energy endpoints.

ZGB, ZTM and clause (i)'s actual zeta/short-energy consumers are proved.
The other eight Add-est clauses, their remaining optimization certificates,
the separate sharp Atkinson source-form theorem, the other EPZAE-19/21
inputs, and the exponent-pair/density outputs remain OPEN. EPZAE-36/37 and
the full EPZAE-00–41 goal are not complete; the frozen contract is unchanged.

Keep `run_tao_trudgian_yang_build.bat` and its backing implementation
synchronized with root imports, exact inventory, named/exhaustive audits
and regressions. Run it and `run_lake_build.bat` after relevant changes.
This checkpoint's terminal gate evidence is recorded in the Reproduction
Manifest; earlier checkpoint PASS records are historical.

Verification (2026-09-21): both principal BAT scripts reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 340 package files,
351 integrity-scanned Lean files and 3,357 audited declarations
(3,352 discovered target theorems plus five imported contracts).
All 49 new named audits and all 61 new regressions pass.
The foundation reports PASS: all six stages passed, with 14,290
discovered theorems audited. Both final logs contain zero Lean errors,
warnings, tactic suggestions or linter failures. The counterexample
SHA256 is unchanged. Exact logs, source/runner hashes and repaired
focused diagnostics are recorded in the current Reproduction Manifest.
These gates verify the genuine moments and full-domain Add-est (i),
not clauses (ii)--(ix) or completion of the full goal.

## Add-est (ii): repaired powering to actual zero energy — verified checkpoint

Printed Lemma 62 remains disproved. Its singleton counterexample is
byte-preserved (SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The authorized replacement still uses independent cardinality-preserving
ρ/k and energy-preserving ρ*/k witnesses with independent existential fifth
coordinates. No false s'/s scaling or third witness is restored.

`add_est_ii`, `add_est_ii_bound`, and `add_est_ii_zero_energy` in
`NewAdditiveEnergy.lean` prove the complete second printed clause on
the closed interval 7/10 ≤ σ ≤ 3/4:

```text
A*(σ)(1−σ) ≤ max(5(18−19σ)/(2(5σ+3)), 2(45−44σ)/(2σ+15)).
```

The actual shifted-zero epsilon--delta bound is proved first, with analytic
multiplicity and unit-tolerance energy retained. The extended-real
infimum inequality follows from it. At σ=7/10 the rate is 47/26 and
A*≤235/39; at σ=3/4 the rate is 16/11 and A*≤64/11.
These endpoint checks supplement, not replace, the full interval proof.

For general patterns, `energyClauseTwo_general_bound` proves the rate on
2≤τ≤4. Actual mean-square and Guth--Maynard cardinality consumers use the
ρ/k witness at k and k+1. The actual Heath--Brown relation uses independent
energy witnesses at k and k−1, where k is two or three. All nine affine
branches are checked; the exceptional branches consume the first powered
energy inequality. Every height and coordinate is linked to its original
region point. Compactness promotes the region result to a uniform bound.

For zeta patterns, sixth-order decay is applied to the actual critical
Mellin integrand. Both the residue and the complete far tail
240 C₆ N^(11/2)/T⁴ are retained before absorption at T≥N^(11/8).
`zetaTwelfth_lower_short_largeValueBound` consumes the proved dyadic
twelfth moment and this entry bridge for σ≥7/10, τ≥7/5.
Actual cancellation gives eventual emptiness for 1≤τ<2σ on the clause
interval; mean-square powering and the twelfth-moment cap handle
2σ≤τ≤2 through nine exact branches with crossing τ=4σ−1.
`energyClauseTwo_short_zeta` therefore supplies all of [1,2].

`energyClauseTwo` composes the two uniform ranges with the already proved
endpoint-one bounded-range zero-energy transfer. The separate printed
endpoint-two transfer (EPZAE-33) is neither assumed nor marked complete.
Clause (i) remains proved. Clauses (iii)--(ix), the remaining optimization
projections, the source-form sharp Atkinson obligation, the other
EPZAE-19/21 inputs, and the exponent-pair/density/release outputs remain OPEN.
EPZAE-36/37 and the full EPZAE-00–41 objective are unchanged and incomplete.

Eleven new production modules are root-reachable and explicitly included
in the principal runner inventory. Eighty-four new public theorems have
named dependency audits; 92 added regressions cover all signatures and
literal physical/source endpoints. Keep `run_tao_trudgian_yang_build.bat`
and its backing inventory synchronized; run it and `run_lake_build.bat`
after relevant changes. Current gate evidence belongs in the Reproduction
Manifest; earlier PASS records are historical.

Verification (2026-09-21): both principal BATs reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 351 package files, 362
integrity-scanned Lean files and 3,504 audited declarations (3,499 discovered
target theorems plus five imported contracts). All 84 new named audits and
92 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions or linter failures. The
counterexample and all 18 recorded source/runner hashes were rechecked.
Exact log paths and hashes appear in the current Reproduction Manifest.
These gates verify full-domain Add-est (ii), not the other seven clauses or
completion of the unchanged whole-proof goal.

## Jutila source entry and uniform powered moments — verified checkpoint

The printed Lemma 62 counterexample is preserved unchanged. Corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Four new production modules advance the missing EPZAE-19 Jutila input:
`JutilaGram`, `JutilaPatternEntry`, `JutilaPoweredMoments`, and
`JutilaReflectedEntry`. They do **not** yet prove Jutila's large-values
estimate or another Add-est clause.

`jutila_smooth_amplified_gram` proves actual phase-aligned smoothed duality,
removes the diagonal before Hölder, and gives, for every positive integer k,
either R V² ≤ 2N² or R² V^(4k) ≤ (2N)^(2k) times the actual off-diagonal
2k-th trace moment. No moment or cardinality bound is assumed.

`LargeValuePattern.jutila_gram_entry` consumes an actual source pattern.
Its fixed smoothed subfamily retains at least a third of the ordinates,
the exact threshold (V−1)/3, unit separation, the actual height, and
N/2 ≤ Q ≤ 2N. The spaced consumer keeps the explicit packing loss
6(2⌈δ⌉+1). `jutila_reflected_pattern_entry` then consumes complete native
reflection on that same subfamily, with one common dual cutoff M.
The main factor uses the actual |u−t|. Mellin truncation, omitted-frequency,
and zero-mode errors all remain in `jutilaReflectionEnvelope`.

`jutila_weighted_power_moment_uniform` proves the actual critical-line
2k-th ordered-difference moment bound. With U=2^k N^k and R=|W|, its RHS is
C (U^η)² T^ε (R² + R U + R^(5/4) T^(1/2)).
C and the height threshold depend only on k, ε, η, and are chosen before
N, T, W. The proof consumes the uniform divisor bound, actual powered
coefficients, dyadic decomposition, coefficient majorant, and the proved
native weighted Heath--Brown theorem. That second-moment theorem is an
input to this deduction, not a substitute for Jutila's large-values theorem.

Remaining: pass from complete reflected prefixes to uniformly bounded
powered difference moments, sum the reflected integrals with all errors,
and perform the local-to-global large-values optimization. Then establish
the actual region and uniform exponent consumers before using them in the
seven remaining energy optimizations. EPZAE-19, 33, 36, 37 and the full
EPZAE-00–41 goal remain open; the distinct endpoint-two transfer, source-form
sharp Atkinson obligation, and other exponent-pair/density/release tasks
are unchanged.

The four modules are included in the root and the exact production
inventory of `run_tao_trudgian_yang_build.bat`. Thirteen new public theorems
have named audits and sixteen regressions cover their exact signatures,
literal diagonal removal, the k=13 power, and all reflected error terms.
Keep that BAT and its backing inventory synchronized, and execute it and
`run_lake_build.bat` after relevant changes. Terminal verification evidence
for this checkpoint is recorded below and in the Reproduction Manifest.

Verification (2026-09-21): both principal BAT runners reached terminal exit 0.
The target reports LEAN VERIFICATION PASS: 355 package files, 366
integrity-scanned Lean files, and 3,530 audited declarations (3,525 discovered
target theorems plus five imported contracts). All 13 new named audits and
16 new regressions pass. The foundation reports PASS: all six stages passed
and all 14,290 discovered theorems were audited. Final logs contain zero
Lean errors, warnings, tactic suggestions, or linter failures. All eleven
recorded source/runner hashes were rechecked unchanged after the gates,
including the original counterexample. Repository scans found no forbidden
proof terms; the twelve raw postulate-pattern matches are the same ten
comments and two rational structure fields already reviewed. Git
`diff --check` passes (Git's LF/CRLF notices are not Lean diagnostics).
Exact commands, logs and hashes are in the Reproduction Manifest.
These gates verify the Jutila entry and powered-moment inputs, not the
remaining Jutila large-values theorem, other seven Add-est clauses, or
completion of the unchanged whole-proof goal.

## Jutila reflected-prefix moments and near/far assembly — verified history

The printed Lemma 62 counterexample is preserved unchanged. The corrected
independent cardinality and energy witnesses remain the only powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Six new production modules advance EPZAE-19: `JutilaPolynomialMoments`,
`JutilaPrefixMoments`, `JutilaReflectionIntegrals`, `JutilaTraceBins`,
`JutilaBinnedPatterns`, and `JutilaHybridPatterns`.

`jutila_source_power_moment_uniform` handles arbitrary unit coefficients,
with constants chosen before their values and the physical length.
`jutila_reflected_prefix_moment_uniform` consumes the actual complete
reflected prefix, including n=1. With U=(2M)^k, R=|W|, and L=ceil(log₂ M),
its bound is C (L+1)^(2k) U (U^η)² T^ε
(R² + R U + R^(5/4) T^(1/2)). The constant is uniform in M, T, W and
the translation parameter. Neither the initial term nor a power of U is
discarded.

`jutila_reflected_bin_integral_moment_uniform` applies interval Jensen and
the proved full ordered-pair majorant before restricting to a difference
bin. Its extra interval factor is exactly (2H)^(2k).
`jutila_binned_pattern_bound` connects those estimates to the actual
source pattern, with bin-dependent positive dual lengths and all Mellin,
omitted-frequency, and zero-mode errors retained.

`jutila_hybrid_pattern_bound` additionally consumes native square-root
cancellation of the complete nonzero Poisson tail below the stationary
scale, keeping the separate zero-mode decay. Above that scale it uses the
actual ceiling length max(1,ceil(2^j H/Q)). The same subfamily retains
the packing loss 6(2 ceil(δ)+1), threshold (V−1)/3, N/2 ≤ Q ≤ 2N, the
actual height, and δ-separation. The condition 4H ≤ δ derives reflection
admissibility on occupied bins; it is not an independently assumed bin
estimate. The three new majorant definitions are notation, not proofs.

Remaining: bound this explicit near/far sum at source scale, absorb all
errors and logarithmic losses uniformly, perform the local-to-global
large-values optimization, and prove the exponent/energy-region consumers.
The target remains
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k), k ≥ 1.
Only then can k=13 enter Add-est (iii) and the other remaining optimizations.
EPZAE-19, 33, 36, 37 and the full EPZAE-00–41 goal remain open. The distinct
endpoint-two transfer, sharp source-form Atkinson bridge, exponent-pair,
density, and release obligations are unchanged.

All six modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Seventeen new public theorems have
named audits; 23 regressions cover their exact signatures, the n=1 term at
k=13, zero interval width, the literal ceiling, and both schedule branches.
Both that BAT and `run_lake_build.bat` remain required evaluation gates.
This is finite-scale proof progress, not completion of Jutila or another
Add-est clause.

### New exact consumers

| Source obligation | Public Lean consumer | Status |
| --- | --- | --- |
| Uniform arbitrary-coefficient 2k moment | `jutila_source_power_moment_uniform` | Kernel-checked |
| Complete reflected prefix and integral | `jutila_reflected_prefix_moment_uniform`, `jutila_reflected_bin_integral_moment_uniform` | Kernel-checked |
| Actual near/far source pattern | `jutila_hybrid_pattern_bound` | Kernel-checked finite-scale bound |
| Uniform optimized Jutila LV exponent | Not yet assembled | OPEN, EPZAE-19 |

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 361 package files, 372
integrity-scanned Lean files, and 3,564 audited declarations (3,559 discovered
target theorems plus five imported contracts). All 17 new named audits and
23 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All seventeen
recorded source/build hashes are unchanged after the gates, including the
original counterexample. Repository scans find no forbidden proof terms;
the twelve raw postulate-pattern matches are the previously reviewed ten
comments and two rational structure fields. Git `diff --check` passes.
Exact commands, logs, hashes, and the corrected initial scan failure are
recorded in the Reproduction Manifest. These checks certify the stated
finite-scale scope, not the remaining Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

## Jutila physical-scale smoothing and uniform pattern bounds — current checkpoint

The printed Lemma 62 counterexample remains byte-for-byte unchanged. The
authorized independent cardinality and energy witnesses remain the powering
replacement. Full Add-est (i) and (ii) remain proved; (iii)--(ix) remain OPEN.

Seven new production modules advance EPZAE-19: `JutilaDualScales`,
`JutilaPhysicalMain`, `JutilaPhysicalPatterns`, `JutilaSmoothingErrors`,
`JutilaSmoothingProfile`, `JutilaSmoothingLosses`, and
`JutilaSmoothedPatterns`.

`jutila_reflection_main_core_le` cancels each actual powered dual length
against its own displacement denominator before imposing the common cap.
`jutila_physical_pattern_bound` consumes the complete near/far pattern
theorem, retaining all main terms, logarithmic/divisor costs, and sharp
reflection errors. The common ceiling is used only for losses.

Native smoothing uses H=max(1,ceil(T^θ)) and derivative order
q=max(2,ceil(4/θ)+1). The zero mode and all three reflection errors are
controlled by proved native estimates, not assumed numerical certificates.
The smoothing-error bridge explicitly requires Q≤2T. The complete profile
is uniformly O(T^(2θ)); its full powered cost, including the bin count,
is O(T^((16k+3)θ)). The actual thinning cost is at most 108 T^θ.

`jutila_smoothed_pattern_bound` chooses positive B and T₀≥2 before every
actual `LargeValuePattern`. For scale≥30, V>1, T≥T₀, and **N≤T**, it
constructs a subset W of the reflected ordinates and Q with N/2≤Q≤2N.
Writing R=|W| and V'=(V−1)/3, the original count is at most B T^ν R,
W is 1-separated in the actual height interval, and either

- R (V')² ≤ 2Q²; or
- R² (V')^(4k) ≤ B T^ν (2Q)^(2k)
  (R²Q^k + R T^k + R^(5/4) T^(1/2) Q^k).

This holds for every k≥1 and ν>0. The choice of θ absorbs both losses
without changing the physical height or assuming the desired LV estimate.
The N≤T restriction derives Q≤2T and is not silently removed.

Remaining: solve the cardinality recurrence with its value threshold,
cover the complementary short-height range, perform the local-to-global
optimization, and prove the actual uniform LV and energy-region consumers.
The unchanged target is
LV(σ,τ) ≤ max(2−2σ, τ+4−2/k−(6−2/k)σ, τ+(6−8σ)k).
Only then can k=13 enter Add-est (iii) and the other seven-clause work.
EPZAE-19, 33, 36, 37 and the whole EPZAE-00–41 goal remain open. The
distinct endpoint-two transfer, sharp source-form Atkinson, exponent-pair,
density and release obligations are unchanged.

All seven modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`. Twenty-one new public theorems
have named audits. Twenty-seven regressions cover every exact signature
plus the actual k=13 source-pattern consumer, its three literal terms,
the empty-family boundary, ceiling padding, genuine zero-mode decay,
and the derived thinning cost. Both that BAT and `run_lake_build.bat`
remain mandatory; build integrity is separate from source completeness.
