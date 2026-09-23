# Tao--Trudgian--Yang 2025 checklist

Current analytic progress: [Actual endpoint-one cardinality-to-density transfer](#actual-endpoint-one-cardinality-to-density-transfer--current-checkpoint).
The actual Type-I/II, slab and symmetric-rectangle cardinality chain proves the endpoint-one density predicate. The exact sup/limsup and endpoint-two source contract remain open. EPZAE-18, corrected powering, all nine repaired Add-est clauses and the counterexample are preserved.

Earlier checkpoint sections retain historical status and next-step notes;
the frozen public contract is unchanged.


No item is complete at scaffold creation. A checked box requires the exact
acceptance test below, not merely a definition, a Python reproduction, or a
conditional wrapper.

Checklist identifiers use `EPZAE` for **exponent pairs, zero density, and
additive energy**, the three output families covered by the paper.

## Groundwork

- [x] **EPZAE-00 -- Source freeze.** Primary PDF/TeX, both ANTEDB snapshots,
  relevant source papers, URLs, versions, licenses, and SHA-256 values are
  recorded and verified by a script.
- [x] **EPZAE-01 -- Toolchain and dependency unification.** One pinned Lean and
  mathlib graph imports both the selected ANTEDB foundations and the completed
  Guth--Maynard source. A clean two-module spike builds with zero warnings.
- [x] **EPZAE-02 -- Package/audit bootstrap.** Root module, production-module
  inventory, semantic regression file, exhaustive axiom audit, forbidden-
  shortcut scan, and warning-failing runner exist and pass for the bootstrap
  scope.

## Exact certificate layer

- [x] **EPZAE-03 -- Rational-function signs.** Exact arithmetic normalizes the
  paper's rational bounds and proves every denominator positive on its claimed
  interval.
- [x] **EPZAE-04 -- Piecewise envelopes.** Lean checks rational interval covers,
  affine/rational comparisons, crossover points, endpoint agreement, and
  finite max/min envelopes.
- [x] **EPZAE-05 -- Convex/polyhedral certificates.** Convex-combination,
  half-space, projection, and optimization witnesses are represented as data
  with kernel-checked soundness theorems.
- [ ] **EPZAE-06 -- Deterministic generator.** A pinned script reproduces the
  certificate data from the paper-time ANTEDB snapshot; regeneration is
  byte-stable and Lean checks the generated result.
  The installed partial generator now extracts the four advertised new pairs
  and reconstructs the eight exact Bourgain lower-envelope pieces (candidate
  provenance, rational functions, and crossover intervals), as well as all
  nine public energy-clause tables from the frozen blueprint. Deterministic reproduction of the
  archived energy projection recipes and pinned execution of the Python
  stack remain open. Independent kernel-checked certificates now prove all
  nine energy clauses (EPZAE-36/37); they do not close this reproduction item.

## Asymptotics and exponent pairs

- [x] **EPZAE-07 -- ANTEDB asymptotic bridge.** The selected upstream definitions
  are reused or ported faithfully; automatic uniformity, power asymptotics,
  model phases, and exponent-sum growth compile in the target graph.
- [x] **EPZAE-08 -- Exponent-pair semantics.** `ExponentPair (k,l)` unfolds to
  the intended uniform exponential-sum estimate, and the non-asymptotic
  equivalent is proved.
- [x] **EPZAE-09 -- Convexity and duality.** Convex closure and both directions of
  beta/exponent-pair duality are kernel-checked, including endpoints and beta
  reflection.
  `ExponentPair.convexCombination` and `exponentPair_iff_beta_bound`
  prove convex closure and exact two-way duality on the closed unit interval.
  `exponentSumGrowthExponent_endpoints` proves beta(0)=0 and beta(1)=1/2.
  `exponentSumGrowthExponent_reflection` proves
  beta(1-alpha)=1/2-alpha+beta(alpha) for every 0<=alpha<=1.
  The complete original-source reflection estimate is combined with the
  independently proved `alpha_sub_half_le_exponentSumGrowthExponent`.
  Its actual resonant logarithmic model sums have derived finite jets,
  integer endpoints and exact T^alpha=N; no reflected nonnegativity or
  coherent-sum premise remains. All new modules, explicit audits and
  semantic regressions are covered by both mandatory verified BATs.

- [x] **EPZAE-10 -- A/B/C processes.** The three source transformations preserve
  exponent pairs with exact formulas.
  The classical analytic seed (1/2,1/2) is proved by `exponentPair_half_half`.
  The exact analytic A/B transformations are proved by `ExponentPair.aProcess`
  and `ExponentPair.bProcess`. A derives the actual shifted closed model,
  all-height correlations, summed source Weyl inequality, natural shift
  optimization and every epsilon loss. Its empty and bounded-N cases are
  included. The exact C transformation is proved by `ExponentPair.cProcess`:
  actual frequency aggregation, linked real optimum, natural floor H,
  epsilon budgets, short/singleton/reversed windows, bounded N and the
  genuine A-cubed-B low-height input are all assembled. Its theorem consumes
  the original analytic exponent pair and no optimized-bound hypothesis.
  All modules, exact-signature regressions and audits are covered by both
  mandatory verified BATs. The unchanged A/B/C acceptance test is satisfied.
  Unused stronger printed intermediate variants are not claimed as proved.
  See the current checkpoint for public source signatures and audit evidence.

- [ ] **EPZAE-11 -- Sargos D-process.** The beta bound is proved from the cited
  analytic theorem, then duality yields every D-derived exponent pair actually
  used downstream.
- [x] **EPZAE-12 -- Heath--Brown derivative input.** The source kth-derivative
  estimate implies the paper's beta formula with all scale/range conditions.
- [ ] **EPZAE-13 -- Beta table.** Every segment consumed by `new-exp-pair` has a
  proved analytic source and a checked exact envelope certificate.
- [ ] **EPZAE-14 -- Four new exponent pairs.** The exact four public
  `new-exp-pair` conclusions are proved and audited without a conclusion-shaped
  hypothesis.
- [ ] **EPZAE-15 -- Zeta growth bridge.** Exponent-pair-to-`mu` and
  `mu(7/10) <= 3/40` are proved in the source convention.

## Large values

- [x] **EPZAE-16 -- Large-value patterns.** Coefficients, dyadic support,
  interval length, one-separation, phase sign, and lower threshold are modeled
  exactly.
- [x] **EPZAE-17 -- LV semantics.** `LV` and `LV_zeta` have faithful
  epsilon-loss and least-exponent/non-asymptotic interfaces.
- [x] **EPZAE-18 -- Elementary LV calculus.** Subdivision, lower/L2 bounds,
  obvious bounds, and raising-to-a-power are proved with uniform coefficient
  normalization. The full actual-pattern source proofs are complete in
  `LargeValueSubdivisionBounds`, `LargeValueLowerBound`,
  `LargeValueHalfExponent`, `LargeValueElementaryBounds`,
  `LargeValueExponent` and `LargeValuePowering`.
  `LargeValueElementaryCalculus` assembles the exact known equality ranges.
- [ ] **EPZAE-19 -- Classical LV inputs.** Exact consumed Huxley, Jutila,
  Heath--Brown, twelfth-moment, and Bourgain interfaces are proved/imported.
  The native MHH finite estimate and Huxley cardinality constraints on actual
  energy regions are now proved in `ClassicalLargeValueRegions`, including
  full-domain height-padding removal and corrected cardinality powering.
  The genuine dyadic twelfth moment is now proved by `zeta_twelfth_dyadic`.
  The exact full-domain Jutila input is now proved by `jutila_largeValueBound`
  and `largeValueExponent_le_jutila`, with actual corrected-powering region
  consumers in `JutilaEnergyRegions`. The standalone uniform Huxley `LV`
  API is now proved in `LargeValueHuxleyBound`; other listed inputs remain
  open, so EPZAE-19 is not checked off.
  The actual `hb-double` and mixed t−u Cauchy--Schwarz source inputs are now
  proved. The actual Bourgain region dichotomy and four low-height rows are
  proved for sigma>3/4 and tau-chi>1, with the ninth row used by Add-est.
  The unrestricted source range and standalone uniform LV assembly remain open.
- [x] **EPZAE-20 -- Guth--Maynard bridge.** The completed local theorem proves the
  exact `guth-maynard-lvt` interface after all convention conversions; no
  generic restatement is accepted as a bridge.
- [ ] **EPZAE-21 -- Zeta LV inputs.** Reflection, moment, and
  `LV_zeta = -infinity`/nonexistence statements used by density are proved.
  The clause-(i) energy consumer now accepts the exact uniform twelfth-moment
  LV predicate and proves all downstream rational and uniform-energy steps.
  `zeta_twelfth_dyadic` now proves the genuine moment and discharges both
  `zetaTwelfth_largeValueBound` interfaces. Sixth-order localization now
  proves `zetaTwelfth_lower_short_largeValueBound` for sigma >= 7/10 and
  tau >= 7/5; actual cancellation below twice sigma and nine-branch
  certificates supply the full short-zeta range for Add-est (ii). The nearby Gafni--Tao proposition
  is not used as proof evidence. The historical implementation sequence follows;
  `ZetaMomentKernel`, `ZetaMomentTransfer`, and `ZetaMomentAsymptotics`
  now prove the actual critical-zeta convolution estimate, weighted
  twelfth-power Hölder, logarithmic-loss absorption, and exact
  dyadic/source-window normalization. Their assembled finite-pattern
  consumer exposes pointwise entry and moment inputs separately.
  The exact sharp-polynomial-to-whole-critical-integral identity is now
  proved in `ZetaIntervalCutoff`, `ZetaMellinEntry`, `ZetaMellinContour`,
  and `ZetaMellinShift`, with actual-pattern consumers, exact integer
  endpoints, and the pole residue retained. The smooth-test object and
  contour hypotheses are derived. `ZetaCutoffDerivatives`,
  `ZetaMellinDerivative`, `ZetaMellinUniform`, `ZetaMellinLocalization`,
  and `ZetaPerronEntry` now prove uniform physical-scale Mellin bounds,
  window localization, and residue/tail absorption. The actual source
  exponent windows `σ ≥ 1/2`, `τ ≥ 2` discharge the entry conditions.
  `zetaTwelfth_largeValueBound_of_dyadic` proves the full uniform
  `LV_ζ ≤ 2τ-12(σ-1/2)` deduction from the genuine dyadic twelfth-moment
  hypothesis alone. `ZetaShortPerron` extends the actual entry and this
  deduction to `σ ≥ 3/4`, `τ ≥ 3/2`; its error is absorbed against `V`.
  `ZetaShortPatterns` proves actual eventual nonexistence and `LV_ζ = -∞`
  for `σ ≥ 3/4`, `1 ≤ τ < 3/2`, with exact sharp endpoints.
  `ZetaLargeValueDiscreteness` now proves the exact infimum/uniform-bound
  equivalence and `LV_ζ < 0 iff LV_ζ = -∞`, through actual eventual
  emptiness. `ZetaPointwiseNonexistence` also proves the equivalent strict
  power-saving characterization for every sharp interval at positive
  heights, with a genuine singleton and explicit `[T,2T]` radius loss.
  `zetaShort_pointwise_powerSaving` consumes the proved cancellation.
  The maximum-to-double branch reduction is proved, but does not supply
  the analytic maximum estimate used in the twelfth-moment argument.
  The six `ZetaSquare*` modules now prove the exact reflected one-sided
  contour identity, complete ordinary-divisor expansion with absolute
  integrated-norm summability, Gamma normalization back to actual
  `|ζ(1/2+it)|²`, and termwise integration on finite local intervals.
  `hasSum_zetaSquareLocalMean` is an actual-source consumer with no
  analytic theorem premise. This does not close Ivić's Theorem 6.2:
  the oscillatory Atkinson reduction, uniform source-scale errors, and
  subsequent scale/spacing assembly remain under EPZAE-21.
  Gaussian averaging is now proved with a scale-independent `exp(1)`
  constant and weighted divisor-series exchange. The actual whole-line
  zeta tail outside `T ± G log T` is at most `G T^(-A)` uniformly for
  `0<G≤T` past a common threshold. The quadratic Gaussian transform
  and its `G²≤2T` frequency bound are proved. The actual reflected
  Gamma phase now has a proved logarithmic derivative, closed-window
  quadratic approximation, integrated error, and whole-line transform
  with both Gaussian tails. The four `ZetaDigammaLog`/`ZetaSquareGamma*`
  modules now have 26 named public audits and 12 phase regressions.
  The seven-module amplitude continuation adds 44 public audits and
  14 regressions: actual digamma/Gronwall shift estimate, pole factor,
  near/far whole-contour error, and complete ordinary-divisor consumer.
  `exists_norm_zetaSquareDivisorIntegral_sub_leading_le` proves one
  uniform `O(1)` remainder for the actual normalized reflected source
  integral, for all `t≥4`, without a moment premise. Nine further modules
  now prove the actual Mellin weight/reflection, signed source argument,
  height variation, square-root coefficient mass, and frozen source.
  `exists_abs_zetaSquareGaussianWindow_sub_quadratic_le` consumes the
  real zeta square (with proved factor two), physical window, actual
  Gamma phase, frozen coefficients and Gaussian tails. It bounds the
  difference from the complete quadratic divisor sum; 78 public audits
  and 20 regressions are covered by the principal runner.
  Six further modules now prove finite frequency shortening, uniform
  logarithmic power tails and the source-scale `Oδ(G log T)` error.
  `exists_zetaSquareLocalMean_le_short_divisor` consumes the actual
  unsmoothed local second moment, with a threshold before every width
  `0<G≤T^(1/2-δ)`. The finite band and the exact complex divisor test
  function are proved; its physical radius is `T log T/(pi G)` on
  `G≥T^δ`. The 29 named audits and 18 regressions are in the runner.
  Eight further modules now prove entire complex-weight smoothness,
  a fixed-profile positive-support cutoff, its actual paid transition
  error, and the native modulus-one Voronoi consumer. Both canonical
  transforms are identified with literal `Y0`/`K0` integrals.
  `exists_zetaSquareLocalMean_le_bessel` consumes the actual local
  moment with uniform `Cδ G log T` error; it assumes no smoothness,
  support, Voronoi or moment theorem. All 43 public audits and 18
  regressions are covered by the root and exact batch-runner inventory.
  Seven further modules now prove literal `K0` exponential decay,
  the full smooth support in `[T/16,T]`, actual integrability and
  complete arithmetic summation from the divisor series at two.
  `exists_zetaDivisorBesselPlus_powerSaving` gives `G T^(-A)` for
  every fixed real `A`, uniformly on `T^δ≤G≤T^(1/2-δ)`.
  `exists_zetaSquareLocalMean_le_main_minus` consumes this bound
  to remove the actual branch, leaving the unchanged main and `Y0`
  terms. Its 29 public audits and 16 regressions are covered by the
  root and exact batch runner. Six further modules now prove the
  source-required lattice phase `exp(-2pi i x)`, unchanged integer
  coefficients/norm/support, the actual phase-adjusted Voronoi source,
  and its complete K0 bound and removal.
  `exists_zetaSquareLocalMean_le_atkinson_reduced` consumes the
  genuine local zeta moment with uniform `Cδ G log T` error.
  Exact source amplitude/carrier factorization, the unique positive
  saddle and negative second derivative are kernel-checked for both
  signs. All 40 public audits and 22 regressions are covered. The
  old continuous integrals are not equated with the new ones. Nine
  further modules now prove the phase-adjusted main-integral bound
  `C G log T` from the actual amplitude variation and native
  logarithmic reflection. `exists_zetaSquareLocalMean_le_atkinson_minus`
  consumes that bound, retaining only the complete phase-adjusted
  Y0 divisor sum with uniform `Cδ G log T` error. The physical
  Gaussian companion is also proved. All 38 public audits and 20
  regressions are covered by the root and exact batch runner. Thirteen
  further modules prove the literal Y0 ray representation and two-term
  expansion with explicit `K x^(-5/2)` error for all `x>0`.
  `exists_norm_zetaAtkinsonBesselMinus_sub_twoTerm_le` sums the
  actual remainder against the ordinary-divisor series at `5/4`;
  `exists_zetaSquareLocalMean_le_atkinson_twoTerm` consumes it,
  retaining the complete oscillatory series and uniform `Cδ G log T`
  error with no analytic premise. The Gaussian companion, all 71
  public audits and 25 regressions are included in the root and runner.
  Ten further modules prove uniform signed-carrier cancellation by
  the exact square substitution, actual slope factorization and native
  first-derivative estimates in both orientations. The actual
  power amplitude has a constructed variation bound, yielding
  `|Iα(T,G,L,b)|≤Cα G T^(-α)` for every real b. Exact four-carrier
  algebra, positive-support integrability and complete summability
  link this to the actual two-term series. Its `n^(-1/4)` and
  `n^(-3/4)` summand bounds are proved, not presumed summable.
  `exists_zetaSquareLocalMean_le_carriers` and its Gaussian
  companion retain the complete source and uniform error.
  All 43 public audits and 24 regressions are in the root and
  exact batch inventory. Four further modules and a generalized
  weighted-primitive lemma prove the actual `1/|b|` gain for
  `|b|≥8sqrt(T)`, with both signs and the equality boundary.
  Near/far combination bounds the actual correction by the divisor
  Dirichlet series at `5/4`; its complete sum costs `C G`.
  `exists_norm_zetaAtkinsonTwoTermSum_sub_leading_le` consumes
  this estimate with proved complete-series identities.
  `exists_zetaSquareLocalMean_le_atkinson_leading` and its
  Gaussian companion retain only the full leading signed carriers
  with uniform source error. All 19 new public audits and 16
  regressions are covered by the root and exact batch runner.
  Fifteen further modules construct the actual C2 amplitude and its
  positive-root smooth extension. `atkinsonPowerIntegral_eq_fourier`
  retains both signed frequencies, the unit constant phase and Jacobian.
  `exists_norm_atkinsonLeadingSum_sub_finite_le` proves the quantitative
  tail `C G T^(5/4) N^(-1/8)` from the true divisor series at `9/8`.
  `exists_zetaSquarePhysicalGaussian_atkinson_finite_approximation`
  and `exists_zetaSquareLocalMean_le_atkinson_finite` consume its
  `C G` specialization for every `N≥T^10`, with uniform source
  error and no analytic theorem premise. All 59 public audits and 20
  regressions are covered by the root and exact batch inventory.
  This is coarse polynomial truncation, not the sharp cutoff.
  The later continuations below prove evaluated stationary mains and
  source-scale localization. Summed stationary errors and final main
  assembly still precede the sharp Atkinson inequality.
  These are proved source
  components, not a closed Theorem 6.2;
  EPZAE-21/37 stay open.
  The genuine moment is now proved; other source parameters, the sharp
  source-form Atkinson statement and zeta-LV inputs remain open, so
  EPZAE-21 is not closed.

## Zero density

- [x] **EPZAE-22 -- Zero-count convention.** The paper's multiplicity-weighted
  `N(sigma,T)` and local rectangle count are related by a proved exact bridge.
- [x] **EPZAE-23 -- Density exponent.** `A(sigma)` and its non-asymptotic
  epsilon-loss interface are defined faithfully.
- [ ] **EPZAE-24 -- LV-to-density transfer.** `zero-from-large` and all corollaries
  used in the paper consume actual large-value patterns and actual zeta zeros.
- [x] **EPZAE-25 -- Classical density bridges.** Local Ingham, Huxley, and
  Guth--Maynard public theorems instantiate the paper's interfaces exactly.
- [ ] **EPZAE-26 -- Improved Heath--Brown density.** `hb-density2` is proved on
  `7/10 < sigma <= 1` with the correct endpoint handling.
- [ ] **EPZAE-27 -- Improved Bourgain density.** The max formula and both stated
  subranges of `bourgain-density-improved` are proved.
- [ ] **EPZAE-28 -- Bourgain pair-to-density theorem.** All hypotheses and the
  two alternative side conditions of `bourgain-zd` are formalized.
- [ ] **EPZAE-29 -- Optimized Bourgain density.** All eight pieces, admissibility
  checks, crossovers, and interval coverage are proved.
- [ ] **EPZAE-30 -- Best-known density table.** The source table is reproduced as
  a proved envelope from individually identified theorems; it is validation,
  not a substitute for EPZAE-26--29.

## Additive energy

- [x] **EPZAE-31 -- Additive-energy semantics.** Approximate quadruple energy of
  an indexed multiset is defined with unit tolerance and multiplicity; the
  paper's basic bounds are proved.
- [x] **EPZAE-32 -- Energy exponents/regions.** `LV*`, `LV*_zeta`, `A*`, `E`, and
  `E_zeta` have faithful asymptotic and non-asymptotic interfaces.
- [ ] **EPZAE-33 -- Energy-density transfer.** `zeroe-from-large` and its
  corollary preserve bounded perturbations and zero multiplicity.
  The Type-I and Type-II source-class consumers prove uniform compact-scale
  energy estimates `C*T^(B+ε)`, with actual thresholds, physical windows, and
  multiplicity indices retained. The positive dyadic zero-slab theorem chooses
  the common cutoffs and shifted line and absorbs all outer coloring losses.
  The signed dyadic assembly now concludes the paper's shifted symmetric
  zero-energy predicate, preserving conjugate multiplicities and low heights.
  `zeroDensityEnergyExponent_le_sup_limsup` now proves `zeroe-from-large`
  itself, with the exact source domain and no extra mathematical hypothesis.
  The general bounded-scale reduction is now proved in `EnergyPoweringBounds`:
  `IsLargeValueEnergyBound.of_powered` and
  `isLargeValueEnergyBound_of_bounded_power_range` consume the corrected
  witness. `isZeroDensityEnergyBound_of_bounded_energy_ranges` combines this
  with zeta bounds on `[1,τ₀)` and general bounds on `[τ₀,2τ₀]`.
  This item remains open for the source's stronger lower zeta endpoint `2`
  and the final exact `zeroe-large-cor-0` supremum statement.
- [x] **EPZAE-34 -- Corrected cardinality/energy powering.** Owner-authorized
  replacement of the false printed Lemma 62: for every positive integer `k`,
  an actual region point yields one output with cardinality exponent `ρ/k`
  and energy exponent at most `ρ*/k`, and a possibly different output with
  energy exponent `ρ*/k` and cardinality exponent at most `ρ/k`. The fifth
  coordinates are separately existential, with no `s/k` restriction and no
  third witness. Prove the full `CorrectedCardinalityEnergyPowering` target.
  `correctedCardinalityEnergyPowering` proves the complete target;
  `InLargeValueEnergyRegion.corrected_powering` exposes its two independent
  fifth coordinates. `EnergyPoweredPatterns` constructs the actual normalized
  dyadic blocks and finite witnesses; `EnergyPoweringLimits` absorbs the
  accuracy-dependent constants before choosing scales, proves the logarithmic
  limits, and extracts the new double-zeta coordinates. No mathematical
  theorem parameter remains in the full powering theorem.
  Preserve `energyPowering_source_counterexample` and its audits permanently.
  See the Energy Powering Repair and Energy Powering Obstruction documents.
- [x] **EPZAE-35 -- Heath--Brown relation.** The exact two-max five-variable
  inequality is proved from the cited large-values estimate.
  Its powered application uses the corrected energy witness from EPZAE-34;
  `InLargeValueEnergyRegion.heathBrown_relation` proves the source relation
  through the native second/fourth moments and exact finite-pattern bridges.
  `InCardinalityEnergyRegion.heathBrown_powered` consumes both proved inputs,
  with no analytic theorem parameter. Height padding is removed for all
  `τ ≥ 0`; the `τ ≤ 3/2` three-branch consequence is also proved.
  The mismatched printed finite factor is bypassed by this independent
  kernel-checked derivation, not silently corrected in the archived paper.
- [x] **EPZAE-36 -- Energy optimization certificates.** Every projection and
  piecewise maximum needed by clauses (i)--(ix) has a checked rational
  certificate and denominator/range proof.
  Rebuild powered constraints in the four-coordinate projection using the
  separate witnesses and proved monotonicity; never scale an `s` constraint.
  The clause-(i) general six-branch projection and its `σ=4/5` crossover
  are now certified by `energyClauseOneGeneral_branch_bound` and the two
  `energyClauseOneGeneralRate_*_piece` theorems. The actual-region consumer,
  uniform bound, and high-height extension are proved, not supplied premises.
  The clause-(i) zeta six-branch certificate is also proved by
  `energyClauseOneZeta_branch_bound`, including the `τ=4σ-1` transition,
  `σ=65/86` crossover, and comparison with the advertised maximum.
  Its actual-region/uniform consumers now use the proved twelfth-moment
  cardinality bound through `energyClauseOne`, with no analytic premise.
  `energyClauseOne_short_cubic_bound` now certifies the remaining short
  height comparison on the exact closed interval `0 ≤ τ ≤ 2`.
  Clause (ii)'s complete general and zeta nine-branch certificates now feed
  actual uniform consumers in `EnergyClauseTwo`. Clause (iii)'s 67 exact
  closed-interval certificates now feed the general and short-zeta
  consumers in `EnergyClauseThree`, including both sigma branches and
  explicit denominator signs. Clause (iv)'s 67 exact certificates feed
  the actual general and short-zeta consumers in `EnergyClauseFour`,
  including the 409/541 split, both tall pieces and all nine branches.
  Clause (v)'s 60 certificates feed `EnergyClauseFive`: the 171/226
  sigma split and new (31σ+2)/22 energy-power switch are exact,
  and every middle/tall and short-zeta branch is covered.
  Clause (vi)'s 53 certificates feed `EnergyClauseSix` on the full
  blueprint interval [664/877,31/40]: the sigma split 281/371 and
  both moving-height energy-power switches are proved, with all
  middle/tall and short-zeta branches covered. The literal blueprint
  normalization and the exact paper interval restriction are proved.
  Clauses (vii) and (viii) each have 35 exact certificates feeding
  `EnergyClauseSeven` and `EnergyClauseEight`: both sigma ranges,
  diagonal and companion-cardinality crossovers, all independent-power
  branches, and the full short-zeta range are covered. The clause-(viii)
  proof derives [2,4] at fixed τ₀=2; it does not assume the blueprint's
  varying-height intermediate bounds.
  Clause (ix) now has 42 exact branch certificates with denominator and
  closed-range proofs, consumed by actual corrected witnesses in
  `energyClauseNine_general_bound` and `energyClauseNine_zeta_bound`.
  The source cutoff is tau0=8sigma-4. All nine projections are complete;
  the independent full release and deterministic replay gates remain open.
- [x] **EPZAE-37 -- Nine new energy estimates.** Every clause of `Add-est` is
  proved on its exact interval and audited.
  Clause (i)'s general intermediate `imphb-lver-ineq` is proved on the exact
  two-piece sigma range and compact height interval, with a uniform extension.
  `energyClauseOne_of_dyadic_moment` now derives the complete short-zeta
  input from the genuine dyadic critical-line twelfth moment: proved
  cancellation below `3/2`, and short Perron entry plus cubic energy on
  `[3/2,2]`. This composes the corrected witnesses, Heath--Brown relation,
  exact general/zeta optimizations, and actual endpoint-one zero transfer.
  `zeta_twelfth_dyadic` now discharges that moment parameter. The literal
  `add_est_i`, the bound predicate and shifted-zero epsilon--delta theorem
  prove clause (i) on all of [3/4,5/6], including both endpoints.
  `add_est_ii`, its bound predicate and actual shifted-zero epsilon--delta
  consumer now prove clause (ii) on all of [7/10,3/4], using the corrected
  witnesses, actual sixth-order entry and proved twelfth moment.
  `add_est_iii`, `add_est_iii_bound` and `add_est_iii_zero_energy` now
  prove the exact three-fraction maximum on [173/229,443/586], with
  corrected independent powering witnesses, full Jutila, actual
  Heath--Brown energy, the proved moment and endpoint-one transfer.
  `add_est_iv`, `add_est_iv_bound` and `add_est_iv_zero_energy` now
  prove the exact two-fraction maximum on [443/586,373/493], with
  actual k=12 Jutila cardinality caps, independent Heath--Brown energy
  witnesses, the complete short-zeta range and endpoint-one transfer.
  `add_est_v`, `add_est_v_bound` and `add_est_v_zero_energy` now
  prove the exact three-fraction maximum on [373/493,103/136],
  with actual k=11 Jutila caps, the new independent energy-power
  switch, the complete short-zeta range and endpoint-one transfer.
  `add_est_vi`, `add_est_vi_bound` and `add_est_vi_zero_energy`
  now prove the exact two-fraction maximum on [103/136,42/55],
  using actual k=10 Jutila witnesses and the full short-zeta range.
  `energyClauseSix` and `energyClauseSix_blueprint` also establish
  the full [664/877,31/40] blueprint bound, including its literal A*
  normalization; the paper result restricts the proved uniform bound.
  `add_est_vii` and `add_est_viii`, with their bound predicates
  and actual shifted-zero epsilon--delta consumers, now prove the
  exact two-fraction maxima on [42/55,79/103] and [79/103,84/109].
  The full blueprint `imp-energy-bound6` and `imp-energy-bound7`
  statements, including literal A* normalization, are also proved.
  All actual Jutila, independent energy, short-zeta and endpoint-one
  inputs are derived; none is supplied as an analytic hypothesis.
  `add_est_ix`, `add_est_ix_bound` and `add_est_ix_zero_energy` now
  prove the final printed maximum on all of [84/109,5/6], including both
  endpoints. Its actual-region/general/zeta consumers use the corrected
  independent witnesses, proved Bourgain rows, Jutila and twelfth moment.
  All nine clauses are explicitly audited. EPZAE-37 is complete; EPZAE-33's
  independent source endpoint-two theorem remains in the full contract
  and is not assumed by the proved endpoint-one Add-est route.

## Release

- [ ] **EPZAE-38 -- Public assembly.** One public module exports all advertised
  new results with exact source-facing statements and no mathematical theorem
  parameters.
- [ ] **EPZAE-39 -- Semantic regressions.** Tests cover zero rectangles,
  multiplicity, approximate energy, phase sign, coefficient support,
  epsilon-loss quantifiers, and every table crossover/endpoint.
- [ ] **EPZAE-40 -- Final reproduction.** Clean source hashes, paper-time Python
  reproduction, deterministic certificate regeneration, full build, zero
  warnings, repository-wide integrity scans, and exhaustive axiom audit all
  pass in one logged runner invocation.
- [ ] **EPZAE-41 -- Documentation synchronization.** README, goal prompt,
  checklist, crosswalk, research agenda, architecture, sources, and manifest
  make identical claims and cite the exact public theorems.

## Completion rule

The paper-level project is complete only when EPZAE-00 through EPZAE-41 are all
checked. If one advertised output remains conditional, disconnected from its
real upstream object, outside the build, or absent from the axiom audit, the
project remains incomplete.

## EPZAE-21 stationary continuation: precise partial completion

Kernel-checked helpers: twelve modules, 71 named audits and 22 regressions.
`exists_atkinsonPowerIntegral_finite_stationary_approximation` consumes
the actual carrier, constructed natural-scale amplitude derivatives, cubic
logarithmic error and weighted nonstationary tails. It proves the finite
quadratic main approximation with error
Cα G T^(-α)[4/(pi H)+4(G/sqrt(T))H²+16T H⁴/r³].
`exists_atkinsonPowerIntegral_small_n_pair_approximation` derives both
signs' geometric conditions from 10000n≤T, 0<H≤sqrt(T)/12 and replaces
the last term by 432H⁴/sqrt(T), on T>0, G≥1, G²≤2T, L≥1, 8L≤G.
Both signed main terms have exact source-phase and Gaussian identities.

The Fresnel limit is proved below. Sharp localization and summable stationary errors,
sharp Atkinson inequality, dyadic/Gram assembly and genuine twelfth
moment remain required. EPZAE-21 and EPZAE-37 are not crossed out.
All unconditional Add-est outputs remain open. The full completion
contract and byte-preserved Lemma 62 counterexample are unchanged.
Maintain the root, named audits, regressions and backing inventory of
`run_tao_trudgian_yang_build.bat`; rerun both principal scopes.

## EPZAE-21 evaluated stationary continuation

Kernel-checked: Fresnel value exp(-i pi/4)/sqrt(2c), finite-window error
2/(c H pi), actual evaluated-main approximation, both source-phase
identities and physical per-carrier power saving.
`exists_atkinsonPowerIntegral_source_power_saving` derives all window
and scale conditions and proves both ±sqrt(n) errors Cα G T^(-α) T^(-η)
for 10000n≤T, η=min(δ/3,1/10), L=log T and the original power-width
range beyond a uniform threshold.

Nine more modules, 35 named audits and 16 regressions are in the root
and exact batch inventory. ZFE is green for this consumer only.
Sharp localization and a sufficiently strong summed error still separate
it from sharp Atkinson and the genuine twelfth moment. EPZAE-21/37 and
unconditional Add-est remain open; preserve the original counterexample,
repaired chain and full EPZAE-00--41 completion contract.

## EPZAE-21 source-scale truncation continuation

Kernel-checked: original-cutoff saddle localization, exact root-band
restriction, vanishing endpoints, natural reciprocal-slope C2 bounds,
both inverse-square frequency estimates and complete arithmetic tail.
`exists_atkinsonLeading_source_band_bound` proves O(G) for
N≥36T(log T/G)², eventually on the original power-width range.
Both physical zeta consumers use this tail and retain their actual
finite leading integrals and Cδ G log T error.

`exists_atkinsonSourceCutoff_carrier_approximation` links the explicit
ceiling cutoff to the existing evaluated stationary estimates for every
retained index. Eleven modules, 53 audits and 22 regressions are covered
by the root and exact batch inventory. ZBT is green for these consumers.

A sufficiently strong summed stationary error and main-amplitude/source
assembly still precede sharp Atkinson and the genuine twelfth moment.
EPZAE-21/37 and unconditional Add-est remain open. The full goal and
byte-preserved counterexample contract are unchanged.

## EPZAE-21 symmetric stationary summation continuation

Kernel-checked: exact cancellation of the linear-amplitude and cubic-phase
corrections on the symmetric quadratic window; a derived radius
T^(1/4)/(12sqrt(G)); and both actual carrier estimates at G≥T^(1/4).
The actual divisor prefix and ceiling cutoff now give a summed retained
error Oε(T^(1/4+ε)); the complete leading tail contributes O(G).

Both physical zeta consumers retain the complete evaluated series and
prove Cδ,ε (G log T+T^(1/4+ε)), on the original power-width range with
G≥T^(1/4). Their above-fourth-root consumers prove Cδ,κ G log T
for G≥T^(1/4+κ). Ten modules, 43 named audits and 24 regressions are
covered by the root and exact runner inventory. ZSE is green only for
these precise consumer statements.

Smaller widths and remaining main-amplitude/source assembly still separate
this from the full sharp Atkinson theorem. Any lower-value-range
replacement must itself be proved. EPZAE-21/37, the genuine twelfth
moment, every unconditional Add-est clause and the full goal remain open.
The byte-preserved counterexample and repaired energy chain are unchanged.

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

## Jutila physical-scale smoothing and uniform pattern bounds — verified history

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

Verification (2026-09-21): both principal BAT runners reached terminal
exit 0. The target reports LEAN VERIFICATION PASS: 368 package files, 379
integrity-scanned Lean files, and 3,619 audited declarations (3,614 discovered
target theorems plus five imported contracts). All 21 new named audits and
27 regressions pass. The foundation reports PASS: all six stages passed,
with 14,290 discovered theorems audited. Final logs contain zero Lean
errors, warnings, tactic suggestions, or linter failures. All twenty-four
recorded source/build hashes are unchanged after the gates, including the
original counterexample and all ten earlier Jutila modules. Repository
scans find no forbidden proof terms; the twelve raw postulate-pattern
matches are the previously reviewed ten comments and two rational
structure fields. Git `diff --check` passes. Exact commands, logs and hashes
are recorded in the Reproduction Manifest. These checks certify the
stated finite-pattern scope, not the final Jutila exponent, seven Add-est
clauses, or completion of the unchanged whole-proof goal.

## Full Jutila theorem and corrected energy-region constraints — verified history

The complete source `jutila-lvt` inequality is now proved, not just its
physical-pattern precursor. For every positive integer k, fixed
1/2 ≤ σ ≤ 1 and τ ≥ 0, `jutila_largeValueBound` gives the uniform
epsilon--delta bound on actual large-value patterns with exponent

```text
max(2-2σ, τ+4-2/k-(6-2/k)σ, τ+(6-8σ)k).
```

`largeValueExponent_le_jutila` gives the paper's least-exponent
conclusion; `zetaLargeValueExponent_le_jutila` gives the valid zeta
specialization. No cutoff, moment estimate, physical absorption threshold,
or assumed cardinality bound remains in these source-facing signatures.

### Mathematical dependency and semantic checks

`jutila_local_pattern_cardinality` consumes both alternatives returned by
the proved `jutila_smoothed_pattern_bound`. It solves the actual Gram
recurrence, pays the thinning loss, and retains the endpoint correction
(V−1)/3. `jutila_local_cardinality_uniform` exposes the three physical
terms N²/(V−1)², T^k N^(2k)/(V−1)^(4k), and
T N^(6k)/(V−1)^(8k), with one arbitrary epsilon loss.

`LargeValuePattern.localized` constructs genuine floor-bin patterns:
coefficients, support, threshold and N are unchanged. Their cards sum to
the original card. `jutila_subdivided_cardinality_native` applies the
local theorem to these objects and uses the already constructed smooth
cutoff. The original T is unrestricted, including T<N and a chosen
local height larger than T.

`jutila_largeValueBound_of_local_exponent` chooses the actual local
height L=N^ℓ, derives the absorption threshold from σ>3/4, and removes
V−1 using the actual exponent windows. Constants and the positive window
radius precede every pattern. The optimized ℓ is
min((4−2/k)σ−(2−2/k), (8k−2)σ−6k+2).
`jutila_optimization_identity` identifies the exact three-term maximum.
The σ≤3/4 range uses the proved obvious bound; ℓ<1 uses the proved
`meanSquare_largeValueBound`, derived from the actual finite MHH
estimate with height padding removed. Thus no short-height gap remains.

`InLargeValueEnergyRegion.rho_le_of_largeValueBound` compares the
uniform bound with actual feasible-region witnesses.
`InCardinalityEnergyRegion.jutila_cardinality_powered` consumes the
cardinality branch of `correctedCardinalityEnergyPowering`, giving
ρ/q ≤ jutilaLargeValueExponent k σ (τ/q) for q≥1.
The literal k=13 consumer gives the two affine terms
τ/q+50/13−76σ/13 and τ/q+78−104σ needed for Add-est (iii).
Different powering applications remain independent. No relation between
either fifth coordinate and s/q is asserted.

### Scope, preservation, and continuation

The full Jutila subnode of EPZAE-19 is DONE. EPZAE-18 and EPZAE-19 as whole
checklist items remain OPEN: the other elementary/classical interfaces
still require their own acceptance tests, including the standalone
uniform Huxley API. EPZAE-36/37 still have Add-est (iii)--(ix) OPEN;
clauses (i)--(ii), corrected two-witness powering, and the full
Heath--Brown energy relation remain proved. The endpoint-two transfer,
sharp Atkinson source-form bridge, exponent-pair/density work, and full
EPZAE-00--41 release contract remain in scope.

The printed Lemma 62 counterexample is preserved byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the paper nor the advertised Add-est statements are changed.

Eleven new production modules are root-imported and included in the
exact PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`JutilaRecurrence`, `JutilaLocalCardinality`, `JutilaLocalAlgebra`,
`JutilaLocalUniform`, `LargeValueSubdivision`, `JutilaSubdivision`,
`JutilaPowerWindows`, `JutilaWindowBound`, `ClassicalMeanSquareBound`,
`JutilaLargeValues`, and `JutilaEnergyRegions`.
All 32 new public theorems have named dependency audits. There are
43 new semantic regressions: 32 exact signatures plus 11 localization,
endpoint, short-height, uniform-pattern and corrected-witness consumers.
Both human-facing BATs remain mandatory and must be updated as needed.

### Completed verification

Both mandatory BAT processes terminated with exit 0 and PASS on
21 September 2026. The target ran 9,234 build jobs, all 43 new semantic
regressions, deterministic regeneration, the exact 379-file package
inventory, and the 390-file integrity scan. All 3,669 audited declarations
(3,664 discovered target theorems plus five imported contracts) have
permitted dependencies; all 32 new named theorem audits are present.

The foundation's six stages also passed: 8,857 root build jobs, 7,636
explicit public declarations, and 14,290 discovered nonprivate theorems.
Its classification remains 301 root modules, two regressions, zero
excluded and zero unclassified. Both final gates have zero Lean errors,
warnings, tactic suggestions or linter failures; there are no failed
stages. Only standard Lean/Mathlib logical axioms occur.

Repository-wide placeholder and unsafe-bypass scans have no matches.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
Git `diff --check` passes; Git's LF-to-CRLF notices are file-conversion
notices, not Lean diagnostics. No scan or warning policy was weakened.
All 35 source/integration/runner hashes match across the gates, including
the original counterexample. Exact commands, log paths, hashes and
checkout identity are in the Reproduction Manifest. This verifies the
full Jutila source theorem and the stated consumers, not the seven
remaining Add-est clauses or the unchanged whole-proof goal.

## Add-est (iii) from corrected powering — verified history

The complete third printed Add-est clause is now proved on
173/229 ≤ σ ≤ 443/586. `NewAdditiveEnergy.lean` exports
`add_est_iii`, `add_est_iii_bound`, and
`add_est_iii_zero_energy`. Their exact source rate is

```text
max((173−270σ)/(16(93−125σ)),
    (653−890σ)/(10(93−125σ)),
    (1151−1190σ)/(20(15σ−2))).
```

The first theorem bounds A*(σ)(1−σ); the last states the fully quantified
epsilon--delta estimate for `zeroAdditiveEnergy (σ−δ) T`. This is the
actual unit-tolerance energy of the paper's zeros with analytic
multiplicity, not a numerical certificate or an assumed energy estimate.
No large-value, moment, powering, or transfer theorem remains an input.

### Source-to-consumer checks

`InCardinalityEnergyRegion.energyClauseThree_cardinality_caps`
applies the proved k=13 Jutila theorem to separate corrected cardinality
witnesses at q and q+1, with q=2 or 3 linked to the original height.
The companion witness gives ρ/q ≤ 3−3σ. The actual Guth--Maynard
consumer supplies the other cardinality cap.

`InCardinalityEnergyRegion.energyClauseThree_general` consumes
those caps and the independent corrected energy witness: power q at
local height at least 6/5, and power q−1 below 6/5. The nine-branch
Heath--Brown relation is used only through its proved monotonicity in
cardinality. No fifth coordinate is scaled or identified.

The 67 closed-interval rational certificates cover both sigma ranges
split at 241/319, all three short-height pieces, both tall-height
pieces, and the nine short-zeta branches. The first two printed fractions
are explicitly normalized by reversing numerator and denominator signs;
`energyClauseThreeRate_eq_printed` proves the exact displayed formula.
The 4359/5770 equality of the first two rates is regression-checked.

`energyClauseThree_short_zeta` supplies the entire [1,2] range:
actual cancellation below 3/2, then the proved dyadic twelfth moment and
the actual Heath--Brown relation on [3/2,2]. Thus
`energyClauseThree` uses the already proved endpoint-one transfer,
with both general [2,4] and short-zeta hypotheses derived. It does not
assume or complete the independent source endpoint-two corollary.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseThreeCaps`, `EnergyClauseThreeRates`,
`EnergyClauseThreeLowCertificates`, `EnergyClauseThreeHighCertificates`,
`EnergyClauseThreeTallCertificates`, `EnergyClauseThreeBranches`,
`EnergyClauseThreeGeneral`, `EnergyClauseThreeZetaCertificates`, and
`EnergyClauseThree`. The existing public `NewAdditiveEnergy` module
now exports clauses (i)--(iii). All 89 new public theorems have named
audits; 103 new regressions include every exact signature, both closed
sigma endpoints, height transitions, the rate crossover and actual
corrected-witness/region consumers.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The archived paper and all advertised outputs remain frozen.

EPZAE-36/37 now have clauses (i)--(iii) DONE and (iv)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
EPZAE-33's endpoint-two corollary, other classical inputs, the sharp
Atkinson source-form bridge, exponent-pair/density outputs, and every
remaining EPZAE-00--41 acceptance condition stay in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,243 build jobs and all 103 new regressions.
Its complete inventory covers 388 package files and 399 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,780 audited declarations (3,775 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 45 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete third source clause and its real consumers,
not the other six clauses or the whole EPZAE-00--41 goal.

## Add-est (iv) from corrected powering — verified history

The complete fourth printed Add-est clause is now proved on the exact
closed interval 443/586 ≤ σ ≤ 373/493. The public
`NewAdditiveEnergy` module exports `add_est_iv`,
`add_est_iv_bound`, and `add_est_iv_zero_energy`, with rate

```text
max((593−810σ)/(5(171−230σ)),
    4(266−275σ)/(5(55σ−7))).
```

The first public theorem bounds A*(σ)(1−σ). The final consumer gives the
uniform epsilon--delta estimate for the actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height
and with the paper's unit tolerance and analytic zero multiplicities.
No analytic, powering, moment or transfer theorem is accepted as input.

### Source-to-consumer checks

`jutila_twelve_formula` specializes the proved full Jutila theorem to
the literal k=12 maximum. The actual-region consumer
`InCardinalityEnergyRegion.energyClauseFour_cardinality_caps`
applies it to separate corrected cardinality witnesses at q and q+1.
Here q=2 or 3 is chosen from the original τ∈[2,4]; τ/q∈[1,3/2]
and τ/(q+1)≤1 are derived. The companion witness gives
ρ/q≤3−3σ, and the actual Guth--Maynard bridge gives the second cap.

`InCardinalityEnergyRegion.energyClauseFour_general` then consumes
the independent corrected energy witness at q when τ/q≥6/5, or
at q−1 below 6/5. The sigma split is 409/541. All nine Heath--Brown
branches and all three short-height pieces are checked. The 67 exact
closed-interval certificates also cover both tall-height pieces and
all nine short-zeta branches. Numerical exploration is not proof evidence.

`energyClauseFourRate_eq_printed` proves equality with the printed
fractions after explicitly reversing both signs in the first fraction.
Both the Jutila affine-term equality and the two-rate equality at
409/541 are regression-checked, along with denominator signs and every
shared domain endpoint.

`energyClauseFour_short_zeta` supplies all of [1,2]: actual
cancellation below 3/2, and the proved twelfth moment plus the actual
Heath--Brown energy relation on [3/2,2]. `energyClauseFour` uses
the proved endpoint-one transfer with both required energy ranges
derived. The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new production modules are root-imported and covered by the exact
PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFourCaps`, `EnergyClauseFourRates`,
`EnergyClauseFourLowCertificates`, `EnergyClauseFourHighCertificates`,
`EnergyClauseFourTallCertificates`, `EnergyClauseFourBranches`,
`EnergyClauseFourGeneral`, `EnergyClauseFourZetaCertificates`, and
`EnergyClauseFour`. The existing public output module now exports
clauses (i)--(iv). All 89 new public theorems have named audits.
There are 104 new regressions: 89 exact signatures and 15 endpoint,
split, sign, height-transition and actual independent-witness consumers.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the original paper nor any advertised output was changed.
No powered fifth-coordinate bound is reintroduced.

EPZAE-36/37 now have clauses (i)--(iv) DONE and (v)--(ix) OPEN; neither
whole checklist item is checked off. The full Jutila theorem, corrected
two-witness powering and Heath--Brown energy relation remain proved.
The independent endpoint-two transfer, other classical inputs, the
sharp Atkinson source-form bridge, exponent-pair/density outputs, and
all remaining EPZAE-00--41 requirements remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,252 build jobs and all 104 new regressions.
Its complete inventory covers 397 package files and 408 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,888 audited declarations (3,883 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 89
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 54 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fourth source clause and its real consumers,
not the other five clauses or the whole EPZAE-00--41 goal.

## Add-est (v) from corrected powering — verified history

The complete fifth printed Add-est clause is now proved on the exact
closed interval 373/493 ≤ σ ≤ 103/136. `NewAdditiveEnergy` exports
`add_est_v`, `add_est_v_bound`, and `add_est_v_zero_energy`, with rate

```text
max((533−730σ)/(30(26−35σ)),
    3(26−33σ)/(85σ−62),
    (174−185σ)/(31σ+2)).
```

These give the literal A*(σ)(1−σ) inequality and the uniform
epsilon--delta bound for actual `zeroAdditiveEnergy (σ−δ) T`.
The constants precede the height; unit tolerance and analytic zero
multiplicities are preserved. There is no analytic, moment, powering
or transfer theorem parameter.

### Source-to-consumer checks

`jutila_eleven_formula` specializes the proved Jutila theorem to k=11.
`InCardinalityEnergyRegion.energyClauseFive_cardinality_caps`
consumes actual corrected cardinality witnesses at q and q+1, with
q=2 or 3 selected from the original height τ∈[2,4]. It derives
τ/q∈[1,3/2], the literal Jutila cap, the Guth--Maynard cap and
ρ/q≤3−3σ. No property of an independently chosen witness is
silently transferred to another point.

`InCardinalityEnergyRegion.energyClauseFive_general` applies the
independent energy witness at q−1 for short local height and at q
for the middle/tall ranges. The Jutila sigma split is 171/226.
For σ above that split the energy-power switch is
h(σ)=(31σ+2)/22, not the preceding clause's fixed 6/5 switch.
Both the ninth q−1 branch and the first q branch meet the third
printed rate at h(σ); the exact identities are regression-checked.

All 60 closed-interval rational certificates feed actual consumers:
27 low-sigma short certificates, 18 high-sigma short certificates,
two middle certificates, four tall certificates and nine short-zeta
certificates. Numerical exploration is not proof evidence.
`energyClauseFiveRate_eq_printed` proves the first fraction's
simultaneous sign reversal and preserves the complete three-rate maximum.

`energyClauseFive_short_zeta` supplies [1,2] explicitly: actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. `energyClauseFive` then consumes
the proved endpoint-one transfer, with both energy ranges derived.
The independent source endpoint-two corollary is not assumed.

### Inventory and remaining whole-proof scope

Nine new modules are root-imported and included in the exact inventory
behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseFiveCaps`, `EnergyClauseFiveRates`,
`EnergyClauseFiveLowCertificates`, `EnergyClauseFiveHighCertificates`,
`EnergyClauseFiveTallCertificates`, `EnergyClauseFiveBranches`,
`EnergyClauseFiveGeneral`, `EnergyClauseFiveZetaCertificates`, and
`EnergyClauseFive`. All 85 new public theorems have named audits.
There are 104 new regressions: 85 exact signatures and 19 endpoint,
split, sign, witness-switch and actual independent-witness checks.

The original printed Lemma 62 counterexample remains byte-for-byte
unchanged: `EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Neither the frozen source nor an advertised output was altered.
No scaled fifth-coordinate restriction is reintroduced.

Clauses (i)--(v) are proved; (vi)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 acceptance condition remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,261 build jobs and all 104 new regressions.
Its complete inventory covers 406 package files and 417 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 3,995 audited declarations (3,990 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 85
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 63 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete fifth source clause and its real consumers,
not the other four clauses or the whole EPZAE-00--41 goal.

## Add-est (vi) from corrected powering — verified history

The complete sixth printed Add-est clause is proved on the exact
closed interval 103/136 ≤ σ ≤ 42/55. `NewAdditiveEnergy` exports
`add_est_vi`, `add_est_vi_bound`, and `add_est_vi_zero_energy`,
with the unchanged rate

```text
max((72−91σ)/(7(11σ−8)),
    5(18−19σ)/(2(5σ+3))).
```

The proof also establishes the larger blueprint theorem
`imp-energy-bound4` on its full interval [664/877,31/40].
`energyClauseSix` gives the actual uniform zero-energy bound there;
`energyClauseSix_blueprint` gives the literal source-facing A*
maximum, with (1−σ) inside both printed denominators.
`energyClauseSixRate_div_eq_blueprint` proves that normalization.
The paper theorem is a proved interval restriction, not a weaker
replacement for the blueprint statement.

### Source-to-consumer checks

`jutila_ten_formula` specializes the full Jutila theorem to k=10.
`InCardinalityEnergyRegion.energyClauseSix_cardinality_caps`
derives the literal cap from the actual corrected cardinality witness
at q, and the companion cap ρ/q≤3−3σ from a separate witness at q+1.
It derives τ/q∈[1,3/2] from the original τ∈[2,4] with q=2 or 3.
The actual Guth--Maynard bridge supplies the tall-height cap.

`InCardinalityEnergyRegion.energyClauseSix_general` consumes the
independent energy witness at q−1 below the moving switch and at q
above it. The sigma split is 281/371; the two switches are
77σ/2−28 and (14σ+1)/10. Their agreement at the split and the
actual branch-balance identities are regression-checked.
The companion cardinality point is never identified with the
energy-preserving point, and no fifth coordinate is scaled.

All 53 exact closed-interval certificates feed the actual consumers:
18 low-sigma short, 18 high-sigma short, four middle, four tall and
nine short-zeta certificates. Numerical exploration is not evidence
for any theorem. The low switch realizes the first rate; the tall
cardinality crossover realizes the second rate.

`energyClauseSix_short_zeta` supplies all of [1,2], using actual
cancellation below 3/2 and the proved twelfth moment with the actual
Heath--Brown relation above it. The final source theorem consumes
the proved endpoint-one transfer with both required energy ranges
derived. It does not assume the independent endpoint-two corollary.
The epsilon--delta public conclusion uses actual
`zeroAdditiveEnergy (σ−δ) T`, with constants preceding the height,
unit tolerance, and analytic zero multiplicities.

### Inventory and remaining whole-proof scope

Nine production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`:
`EnergyClauseSixCaps`, `EnergyClauseSixRates`,
`EnergyClauseSixLowCertificates`, `EnergyClauseSixHighCertificates`,
`EnergyClauseSixTallCertificates`, `EnergyClauseSixBranches`,
`EnergyClauseSixGeneral`, `EnergyClauseSixZetaCertificates`, and
`EnergyClauseSix`. All 80 new public theorems have named audits.
There are 102 new regressions: 80 exact signatures and 22 source/paper
endpoint, normalization, switch, height and actual-witness checks.

The original Lemma 62 counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The frozen paper and all advertised outputs are unchanged.

Clauses (i)--(vi) are proved; (vii)--(ix) remain open.
EPZAE-36/37 remain unchecked as whole items. The independent
endpoint-two transfer, other classical inputs, sharp Atkinson
source-form bridge, exponent-pair/density outputs and every other
unfinished EPZAE-00--41 requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,270 build jobs and all 102 new regressions.
Its complete inventory covers 415 package files and 426 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,094 audited declarations (4,089 discovered target theorems and five
imported contracts) have permitted dependencies; every one of the 80
new named audits was checked in the complete log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 72 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete sixth source clause, its real consumers and
the full blueprint `imp-energy-bound4`, not the other three clauses
or the whole EPZAE-00--41 goal.

## Add-est (vii) and (viii) from corrected powering — verified history

The exact seventh and eighth printed Add-est clauses are proved on
their full closed intervals. `NewAdditiveEnergy` exports
`add_est_vii`, `add_est_vii_bound`, `add_est_vii_zero_energy`,
`add_est_viii`, `add_est_viii_bound`, and
`add_est_viii_zero_energy`.

For [42/55,79/103], the unchanged rate for A*(σ)(1−σ) is

```text
max((18−19σ)/(6(15σ−11)), 3(18−19σ)/(4(4σ−1))).
```

For [79/103,84/109], it is

```text
max((18−19σ)/(2(37σ−27)), 5(18−19σ)/(2(13σ−3))).
```

`energyClauseSeven_blueprint` and `energyClauseEight_blueprint`
also give the literal full-source conclusions of `imp-energy-bound6`
and `imp-energy-bound7`, respectively. Their (1−σ) factors occur
inside both printed denominators, with proved normalization identities.
The public epsilon--delta conclusions use actual
`zeroAdditiveEnergy (σ−δ) T`, analytic zero multiplicities and unit
tolerance; constants and the positive sigma loss precede the height.

### Actual witnesses and complete interval consumers

The full Jutila theorem is specialized to k=6 for clause (vii) and
k=5 for clause (viii). The respective sigma splits are 97/127 and
33/43. Each `energyClauseSeven_cardinality_caps` /
`energyClauseEight_cardinality_caps` theorem derives both the literal
Jutila cap at q and the companion bound ρ/q≤3−3σ at q+1 from
actual corrected cardinality witnesses. The energy witness is separate.

For τ∈[2,4], the proved cover chooses q=2 or 3 and derives τ/q∈[1,3/2].
Below the diagonal-cardinality crossover, the proof consumes the actual
q−1 energy witness and all nine Heath--Brown branches. Above it, the
actual q energy witness supplies the two proved small-height branches.
The crossover pairs are 46σ−34 and (11σ−5)/3 for clause (vii), and
38σ−28 and (18σ−8)/5 for clause (viii). The companion-cap crossover
pairs are 45σ−33 and (8σ−2)/3, and 37σ−27 and (13σ−3)/5.
The second q-energy branch realizes the corresponding printed rate
at each companion crossover; exact identities are regression-checked.

Each clause has 35 kernel-checked interval certificates: nine low-sigma
short, nine high-sigma short, eight tall, and nine short-zeta certificates.
All feed actual region consumers and uniform bounds. The independent
power ratio is bounded at 2/3 only for branch 0 and at 1/2 for the other
eight branches; the sign-sensitive branch 2 has an explicit regression.
No fifth coordinate is scaled or identified across the witnesses.
Numerical exploration is not proof evidence.

For both clauses the full short-zeta range [1,2] is derived from actual
cancellation below 3/2 and the proved twelfth moment above it. The final
theorems consume the proved endpoint-one transfer with τ₀=2.
For clause (viii), this is a documented proof refactoring: the blueprint
uses a varying τ₀, whereas Lean derives all required bounds on [2,4]
and [1,2] directly. The exact source conclusion is unchanged; no
varying-height intermediate bound or endpoint-two corollary is assumed.

### Inventory and unchanged whole-proof scope

Eighteen production modules are root-imported and included in the exact
inventory behind `run_tao_trudgian_yang_build.bat`. Each
`EnergyClauseSeven` / `EnergyClauseEight` family contains `Caps`,
`Rates`, `LowCertificates`, `HighCertificates`, `TallCertificates`,
`Branches`, `General`, `ZetaCertificates`, and the final assembly.
All 122 new public theorems have named audits. There are 172 new
regressions: 122 exact signatures and 50 endpoint, normalization,
crossover, height and actual-witness checks.

The original counterexample is unchanged byte-for-byte:
`EnergyPoweringObstruction.lean` SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The original paper and source pins are unchanged.

Clauses (i)--(viii) are proved; (ix) remains open. EPZAE-36/37 remain
unchecked as whole items. The independent endpoint-two transfer,
remaining classical inputs, sharp Atkinson source-form bridge,
exponent-pair/density outputs and every other unfinished EPZAE-00--41
requirement remain in the active goal.

### Completed verification

Both mandatory BATs terminated with exit 0 and PASS on 21 September 2026.
The target completed 9,288 build jobs and all 172 new regressions.
Its complete inventory covers 433 package files and 444 integrity-scanned
Lean files. Deterministic regeneration and all pinned-source checks pass.
All 4,249 audited declarations (4,244 discovered target theorems and five
imported contracts) have permitted dependencies; all 122 new named audits
were checked in the complete target log.

The foundation completed all six stages, 8,857 root build jobs, 7,636
explicit public declarations and 14,290 discovered nonprivate theorems.
Classification remains 301 root modules, two regressions, zero excluded
and zero unclassified. Both final gates have no Lean errors, warnings,
tactic suggestions, linter failures or failed stages.

Whole-repository scans find no forbidden placeholders or unsafe bypasses.
The twelve raw postulate-pattern matches are the reviewed ten comments
and two rational structure fields, not postulated declarations.
`git diff --check` passes; Git's LF/CRLF notices are conversion notices,
not Lean diagnostics. No warning policy or scan was weakened.
All 90 checked source/integration/runner hashes, including the preserved
counterexample, match before and after the gates. The Reproduction
Manifest records exact commands, logs, hashes and checkout identity.

This verifies the complete seventh and eighth paper clauses, their real
consumers and their full blueprint conclusions. Clause (ix) and all other
unfinished EPZAE-00--41 requirements remain in the unchanged active goal.

## Double-zeta source bounds and Bourgain algebra — verified history

The corrected powering theorem and Add-est (i)--(viii) remain proved.
The printed Lemma 62 counterexample is byte-for-byte unchanged:
SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.

Four new modules advance the remaining clause-(ix) route:

- `HeathBrownDoubleZetaFinite` proves the uniform finite double-zeta bound
  on actual closed-support patterns, with the one-endpoint error and
  reflected interval proved explicitly.
- `HeathBrownDoubleZeta` proves the full frozen `hb-double` conclusion
  `s ≤ max(max(ρ+1,2ρ),5ρ/4+τ/2)+1` for actual region points,
  including τ=0. Its small-height and diagonal-equality consumers are proved.
- `MixedDoubleZeta` proves the mixed Cauchy--Schwarz inequality with the
  actual kernel at **t−u**, and consumes actual patterns with common support.
- `BourgainLargeValueAlgebra` proves witness elimination and the exact
  certificate for the row `ρ ≤ 9−12σ+2τ/3`. The resulting cardinality
  bound is **conditional on the explicitly displayed Bourgain dichotomy**;
  the finite analytic selection and its limiting bridge remain OPEN.

The row certificate uses α₁=(τ+9−12σ)/6 and
α₂=max(0,4σ+4τ/3−5), a proved alternative to the table's α₂.
All five branches are checked on the complete stated closed row.
A rational regression at σ=771/1000 detects the gap in simply extrapolating
the previous Jutila/HB local peak rate; numerical sampling is not evidence
for clause (ix).

There are 25 new named audits and 35 new regressions. All four modules are
in the root imports and the `run_tao_trudgian_yang_build.bat` PowerShell
inventory. No source archive, dependency pin, public Add-est statement,
or counterexample was changed. In particular, no constraint on s′/s
has been reintroduced.

Add-est (ix), its actual Bourgain input and final general/zeta optimization,
the other public outputs, and every remaining EPZAE-00--41 acceptance test
remain OPEN. EPZAE-19, 36 and 37 are not checked off by these supporting results.

### Current verification evidence

On dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  437 package Lean files, 448 integrity-scanned files, 9,292 build jobs,
  4,277 discovered target theorems and 4,282 audited declarations.
  All 25 new named audits permit only the standard logical axioms.
  Log: `logs/tao-trudgian-yang-build-20260921-110817-ade1e44e.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: PASS, exit 0;
  all six verification stages pass, with 301 root modules, 2 explicit
  regressions, 0 unclassified files, and 14,290 discovered theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_110818.log`;
  manifest: `logs/foundation_freeze_20260921_110818.json`.

Both runs have zero Lean errors, warnings, tactic suggestions or linter failures.
There are no remaining failed verification stages. These are build/integrity
results for the installed scope, not a claim that clause (ix) or the whole goal
is complete. The reproduction manifest records hashes of the tested sources.

## Bourgain difference counts and actual zeta moments — verified history

The corrected independent cardinality/energy powering route and Add-est
(i)--(viii) are preserved. The printed Lemma 62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No fifth-coordinate scaling or third witness has been restored.

Five production modules now prove actual upstream inputs to Bourgain's
remaining analytic dichotomy:

- `BourgainDifferenceCounts`: the strict ordered-pair count
  Δ(ℓ)=#{(t,u)∈W²: |t−u−ℓ|<1}, a finite support cover, exact double
  counting, ΣΔ≤2|W|², and ΣΔ²≤2|W|³ for two-separated W.
  The cover may contain zero-count integers; these are not fabricated
  positive bins.
- `BourgainDifferenceLevels`: genuine nonempty dyadic level selection
  from positive weighted mass, with the exact log₂|W|+1 loss and
  2ʲ|Dⱼ|≤2|W|². No selector is assumed.
- `BourgainIntegerWindows`: overlap at most 2⌈H⌉+1 and the real-difference
  to integer-bin integral bridge. The latter explicitly enlarges H to H+1;
  it does not assert a same-radius replacement.
- `BourgainZetaDifferenceMoments`: actual local critical-line zeta-square
  integrals and multiplicities, their Cauchy--Schwarz/fourth-moment
  reduction, positive-mass level selection, and the actual real-pair
  consumer with the unit window enlargement.
- `BourgainFourthMoment`: the genuine symmetric fourth moment, derived
  from the proved dyadic theorem, compact initial interval and conjugation;
  it supplies the actual weighted-moment bound below.

Writing M(W,H)=Σℓ Δ(ℓ) ∫[-H,H] |ζ(1/2+i(ℓ+u))|² du, the final consumer
proves, for every η>0, uniform positive C and T₀≥1 such that

```text
M(W,H)² ≤ C H (2⌈H⌉+1) |W|³ (T+H+1)^(1+η)
```

for T≥T₀, H≥0, two-separated W⊂[0,T]. Constants precede W, T and H.
The global fourth moment is proved, not an extra theorem parameter.
The exact window loss is retained; no small-power absorption or logarithmic
large-values limit is being claimed here.

There are 31 new named audits and 45 new regressions, including strict
endpoints, empty/zero-radius cases, and a one-separated four-point set
where Δ(2)=5>|W|=4. This guards the necessary stronger separation.
All five modules are root-imported and included in the exact production
inventory behind `run_tao_trudgian_yang_build.bat`.

The retained-zeta source estimate (Bourgain (4.7)), zeta-superlevel/common-shift
selection, the full finite dichotomy and its actual-pattern logarithmic
bridge remain OPEN. The earlier `bourgain_ninth_row_of_log_dichotomy`
still has its explicit dichotomy premise. Add-est (ix), EPZAE-19/36/37
as whole items, and every other unfinished EPZAE-00--41 requirement remain
in the unchanged goal. These supporting theorems do not close those items.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: 442 package
  Lean files, 453 integrity-scanned files, 9,297 build jobs,
  4,322 discovered target theorems and 4,327 audited declarations.
  All 31 new named audits have only permitted logical dependencies,
  and all 45 new regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-115007-09779b5b.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages
  pass, 301 root modules, 2 explicit regressions, 0 excluded or
  unclassified files, 8,857 build jobs and 14,290 discovered
  nonprivate theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_115008.log`;
  manifest: `logs/foundation_freeze_20260921_115008.json`.

There are zero Lean errors, warnings, tactic suggestions, linter failures
or remaining failed verification stages. All 99 checked source,
integration and runner hashes match before and after the gates,
including the preserved counterexample. No source pin or public
Add-est statement changed. The Reproduction Manifest records the
exact evidence and hashes.

These gates establish integrity of the installed scope. The full
Bourgain dichotomy, Add-est (ix) and the unchanged whole-proof goal
are not complete.

## Bourgain critical-block Mellin localization — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Five new production modules supply a genuine retained-zeta estimate for
finite critical dyadic blocks:

- `BourgainCriticalMellin`: real-power weighting and physical dilation of
  an actual compact smooth test, exact critical-line Mellin identity, and
  its moving-pole residue. The kernel norm is scale independent; the
  residue has its explicit square-root scale factor.
- `BourgainMellinLocalization`: all polynomial Mellin moments are
  integrable; the actual zeta/Mellin tail is bounded at arbitrary order.
  The local norm estimate separates residue, local zeta integral and tail,
  with constants independent of L, t and H.
- `BourgainSmoothedPolynomial`: the fixed profile
  w(x)=`zetaIntervalCutoff 1 2 x`, equal to one on [1,2] and zero at and
  outside [1/2,5/2], produces a genuine finite-support critical polynomial.
  Its square bound consumes the Mellin theorem and interval
  Cauchy--Schwarz; its pair moment consumes the actual H-to-H+1 bridge.
- `BourgainSmoothedMoments`: proved distance-shell occupancy bounds the
  reciprocal-square overlap by four. For every positive integer q the
  complete pole sum is at most 4|W|, not an assumed diagonal estimate.
- `BourgainCriticalMajorant`: the actual finite block is zero-extended
  onto the smooth support and consumed by the native positive-kernel
  coefficient majorant. This is a full ordered-pair argument, not a
  pointwise or arbitrarily restricted-pair majorization.

The public consumer
`bourgain_critical_block_retained_zeta_moment` proves: for each integer
q >= 1 there is C_q > 0, independent of all physical parameters, such that
for L > 0, B,T,H >= 0, one-separated W in [0,T], finite
I contained in [L,2L], and |a_n| <= B n^(-1/2),

```text
sum_(t,v in W) |sum_(n in I) a_n n^(-i(t-v))|^2
 <= C_q B^2 [
      L |W| + H M(W,H+1)
      + |W|^2 (1+T)^2 / (1+H)^(2q)
    ],
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

Here Delta is the previously proved strict integer difference count, and
M is the actual finite weighted zeta-square moment. The H+1 enlargement,
coefficient factor B^2, pole term and tail are all retained. No moment,
contour shift, residue estimate, smoothness certificate or selector is
assumed. One-unit separation suffices for this consumer; the earlier
Delta <= |W| and fourth-moment count bounds still require two-unit
separation as documented.

This does **not** yet prove Bourgain (2000), equation (4.7), or the full
analytic dichotomy. The actual reflected-prefix fourth-power convolution,
dyadic assembly and Gram/reflection consumer must still feed this block
estimate. The zeta-superlevel/common-shift and local-mean lower bound,
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are not closed by
these supporting results.

All five modules are added to the root import graph and the exact
production inventory used by `run_tao_trudgian_yang_build.bat`.
The explicit audit adds 30 public theorems; 44 new regression examples
cover their exact signatures, support/plateau endpoints, the nontrivial
scale-one polynomial, the surviving diagonal and empty sets. Continue
maintaining this BAT, its PowerShell driver and the foundation
`run_lake_build.bat` whenever proof/build coverage changes. Neither
runner's warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  447 package Lean files, 458 integrity-scanned files, 9,302 build jobs,
  4,374 discovered target theorems and 4,379 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 44 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-123028-c1ae7ae1.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_122534.log`;
  manifest: `logs/foundation_freeze_20260921_122534.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 104 checked source,
integration and runner hashes match before and after these gates, including
the preserved counterexample. The Reproduction Manifest records full log
hashes and the five new/four updated build-integration file hashes.

These are integrity checks for the installed scope, not completion of
source-(4.7), the Bourgain dichotomy, Add-est (ix), or the whole-proof goal.

## Bourgain retained-zeta pattern entry — verified historical checkpoint

The authorized independent cardinality/energy powering repair and Add-est
(i)--(viii) remain intact. The printed Lemma 62 counterexample is preserved
byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Twelve new production modules now consume the previously proved critical
block estimate in actual source-pattern bounds:

- `BourgainWeightedMoments`, `BourgainPolynomialMoments` and
  `BourgainPrefixMoments`: exact phase/half-weight bridges, genuine
  powered coefficients, all dyadic prefix pieces and the literal n=1
  term. The native reflected prefix is **unweighted**. Its factor
  U=(2M)^k is retained; it is not silently treated as a critical prefix.
- `BourgainReflectionIntegrals`, `BourgainTraceBins`,
  `BourgainPatternEntry` and `BourgainHybridEntry`: interval Jensen,
  actual difference bins, native reflection and source Gram subfamilies,
  with the actual ceiling dual length and all reflection errors.
- `BourgainPhysicalMain` and `BourgainPhysicalPatterns`: the
  unweighted-prefix factor is cancelled against its own displacement
  scale before taking terminal length bounds. Near bins, the retained
  main term and all three reflection errors are assembled.
- `BourgainSmoothingErrors` and `BourgainSmoothedPatterns`: native
  smoothing discharges the Mellin tail and reflection errors; logarithmic,
  divisor and integration-length costs are absorbed uniformly.
- `BourgainRetainedCardinality`: the quadratic recurrence is solved
  with the actual zeta moment retained. Exact source-power and
  value-threshold identities account for every numerical factor.

For every integer k>0 and nu>0,
`bourgain_smoothed_pattern_retained` supplies theta,B,T0 independently
of the actual pattern, with 0<theta<=min(1,nu), B>0 and T0>=2.
For scale>=30, V>1, T>=T0 and N<=T, it constructs a genuine
two-separated W in the reflected ordinates, contained in [0,T], and
a positive integer Q with N/2<=Q<=2N. Write

```text
R = |W|, V0 = (V-1)/3, Z = B*T^nu,
H = heathBrownSmoothingHeight T theta,
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

It proves |P.ordinates|<=Z*R and the alternative

```text
R*V0^2 <= 2*Q^2
  OR
R^2*V0^(4k) <= Z*(2Q)^(2k) *
  [ R^2*Q^k + R*T^k + Q^k*M(W,H+1) ].
```

The actual integer-window moment, two-unit separation, H+1 enlargement
and source endpoint V-1 are explicit. No analytic moment or reflection
estimate is a theorem premise.

For k=2, `bourgain_high_value_pattern_retained` solves this alternative
under the additional **numerical high-value condition**

```text
2*[Z*(4N)^4]*(2N)^2 <= V0^8.
```

With D=Z*(4N)^4, its actual subfamily satisfies

```text
|P.ordinates| <= Z * [
  2*(2N)^2/V0^2 + 2*D*T^2/V0^8
  + sqrt(2D)*(2N)*sqrt(M(W,H+1))/V0^4
].
```

This is a proved high-value retained-moment consumer, **not the full
parameter range of printed Bourgain (2000), Lemma 4.1/(4.7)**. Its
absorption condition must be derived in the intended asymptotic range;
the unrestricted source statement needs additional control of the near
contribution. Neither obligation is concealed by the exact algebra.

The zeta-superlevel/common-shift and local-mean lower bound, actual
finite/logarithmic dichotomy, ninth-row discharge and Add-est (ix) remain
open. EPZAE-19/36/37 and the whole EPZAE-00--41 goal are unchanged.

All twelve modules enter the default root, the target BAT's exact production
inventory, 30 explicit public-theorem audits and 43 semantic regressions.
The regressions include actual unweighted prefixes at lengths 0, 1 and 2,
the surviving literal-one pair moment, empty sets, zero radius and the
zero retained-moment specialization. Continue maintaining
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat`; no warning, integrity or dependency gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  459 package Lean files, 470 integrity-scanned files, 9,314 build jobs,
  4,429 discovered target theorems and 4,434 audited declarations.
  All 30 new explicit audits use only permitted logical dependencies;
  all 43 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-131005-aaa8691f.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_131248.log`;
  manifest: `logs/foundation_freeze_20260921_131248.json`.

Both completed logs have zero Lean errors or warnings. The foundation also
records zero tactic suggestions and linter failures in every stage.
There are no remaining failed verification stages. All 116 checked source,
integration and runner hashes match before and after the final gates,
including the preserved counterexample.

The first foundation attempt,
`logs/foundation_freeze_20260921_130845.log`, exited 1: a prose line
beginning with the word "constant" matched its postulate scan. Rewording
that comment resolved the match; the proofs and scanner policy were not
changed. The complete rerun above is the current verification evidence.

These are integrity checks for the installed scope, not completion of
the full source-(4.7) range, Bourgain dichotomy, Add-est (ix), or the
whole-proof goal.

## Bourgain power windows and mass-level alternative — verified history

The authorized two-witness powering repair and Add-est (i)--(viii) remain
intact. `EnergyPoweringObstruction.lean` is unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness has been restored.

Six new production modules advance the actual Bourgain source chain:

- `BourgainMomentWindows`: monotonicity of the genuine local zeta
  integrals and weighted difference moment; the native integer smoothing
  radius plus one fits a larger small power at a proved threshold.
- `BourgainRetainedUniform`: all constants and the square-root loss
  are absorbed into one physical epsilon loss. Its intermediate numerical
  high-value threshold remains visible.
- `BourgainRetainedPowerWindows`: exact three-term powers and their
  bounds from the same physical N,T,V and retained moment.
- `BourgainRetainedSource`: derives the numerical threshold and V-1
  endpoint loss from sigma>3/4 and the actual power windows. The abstract
  cutoff is discharged by the existing constructed smooth cutoff.
- `BourgainSmallMass`: solves the three-quarter-power recurrence,
  including zero cardinality, and derives the exact small-mass powers.
- `BourgainMassDichotomy`: consumes the actual source subfamily,
  either obtains the small-mass cardinality estimate or selects an
  actual nonempty dyadic integer difference level with all losses.

For sigma>3/4, any fixed real tau and epsilon>0,
`bourgain_retained_source_power_bound` supplies C>=1 and delta>0
before the pattern. If

```text
C <= N <= T, T <= N^(tau+delta), N^(sigma-delta) <= V,
```

it constructs two-separated W contained in the reflected source ordinates
and in [0,T]. With R0=|P.ordinates|, R=|W| and the genuine moment

```text
M(W,h) = sum_l Delta_W(l) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
```

the conclusion is

```text
R0 <= C*N^epsilon*R,
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(3-4sigma+epsilon)*sqrt(M(W,N^epsilon))
].
```

The numerical high-value condition is no longer a premise here. The proof
chooses a positive exponent gap, dominates its actual constant, absorbs
V-1, and links T to N before bounding the smoothing radius. It retains
N<=T explicitly and permits tau=1 whenever that physical condition holds.
The exact regression at sigma=84/109 checks the strict gap
8sigma-6=18/109; no endpoint of Add-est (ix) was discarded.

The stronger actual-pattern consumer
`bourgain_retained_difference_level_dichotomy` chooses the same W
before any real alpha. Put h=N^(epsilon/8). For every alpha it proves
one of the following:

```text
R0 <= C * [
  N^(2-2sigma+epsilon) + N^(2tau+4-8sigma+epsilon)
  + N^(-2alpha+tau+12-16sigma+epsilon)
]
```

or an actual integer j with D=bourgainDifferenceLevel W j such that

```text
L_R = Nat.log 2 R + 1, 0 <= j < L_R, D nonempty,
2^j <= R, 2^j*|D| <= 2*R^2,
N^(-alpha)*R^(3/2)*N^(tau/2) < M(W,h),
M(W,h) <= L_R*2^(j+1)*
           sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du.
```

The index condition is exactly
`j in Finset.range (Nat.log 2 W.card + 1)`; no logarithmic limit has
been taken. The small branch uses the actual subset-cardinality bridge
from R to R0.
The large branch derives positive mass and consumes the proved selector.
No analytic mass bound, auxiliary set or selector is postulated.

This is the **small-mass/heavy-difference-level alternative**, not the
full frozen Bourgain logarithmic dichotomy. Zeta superlevel selection,
subdivision with common parameters/shift, the local-mean lower bound and
the final mixed-moment comparison still have to be assembled. The
unrestricted low-value range of printed Lemma 4.1/(4.7), remaining physical
range bridges, the finite/logarithmic transfer, ninth-row discharge and
Add-est (ix) remain open. EPZAE-19/36/37 and the full EPZAE-00--41 contract
are not closed by this increment.

All six modules enter the root import graph and the exact production
inventory used by `run_tao_trudgian_yang_build.bat`. Twelve explicit
public-theorem audits and 23 regression examples cover the full signatures,
zero/empty windows, the native ceiling, zero-cardinality recurrence and
the exact sigma=84/109, tau=1 source-window specialization. Both the target
BAT and foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  465 package Lean files, 476 integrity-scanned files, 9,320 build jobs,
  4,441 discovered target theorems and 4,446 audited declarations.
  All 12 new explicit audits use only permitted logical dependencies;
  all 23 new regression examples pass.
  Log: `logs/tao-trudgian-yang-build-20260921-133945-11e430fe.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_133728.log`;
  manifest: `logs/foundation_freeze_20260921_133728.json`.

Both completed logs have zero Lean errors, warnings or tactic-info
diagnostics. Every foundation stage also records zero linter failures.
There are no remaining failed verification stages. All 122 checked
source, integration and runner hashes are unchanged across the final
gates, including the preserved printed-Lemma-62 counterexample.
The Reproduction Manifest records the full log and new-source hashes.

This verifies the installed theorem scope, not the full source-(4.7)
range, the complete Bourgain logarithmic dichotomy, Add-est (ix), or
the unchanged whole-proof goal.

## Bourgain actual zeta bands and shifted slices — verified history

The authorized independent cardinality/energy powering repair and
Add-est (i)--(viii) remain intact. The printed-Lemma-62 counterexample is
unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
No false fifth-coordinate scaling or third witness is restored.

Eight new production modules extend the genuine Bourgain large-mass chain:

- `BourgainZetaBands`: actual critical-line amplitude bands, measurable
  finite support, the proved fourth-moment measure bound and a genuine
  global linear growth majorant.
- `BourgainBandOccupancy`: literal translated integer counts, finite
  interval integrability, and both cardinality and integer-overlap bounds.
- `BourgainDyadicBands`: half-open amplitude partition and an explicit
  ceiling-logarithmic terminal count derived from actual zeta growth.
- `BourgainBandSelection` and `BourgainPositiveBand`: integration,
  finite maximization, and a positive band selected from the actual mass.
  The low-amplitude contribution is retained, then absorbed by a proved
  choice of floor; no selector or growth estimate is assumed.
- `BourgainBandShift`: the first moment method selects a real shift
  for a finite weighted family, and an actual nonempty integer slice for
  positive band mass.
- `BourgainBandCorrelation`: the normalized occupancy is defined from
  actual mass, measure and cardinality; its identity and finite bounds
  are proved.
- `BourgainPatternBand`: consumes the same W and heavy difference level
  returned by the existing actual-pattern dichotomy and assembles all
  these conclusions.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_zeta_band_dichotomy` supplies B>0, C>=1 and delta>0
before the actual pattern. Under
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`,
it chooses two-separated W in the reflected ordinates and [0,T],
with `|P.ordinates|<=C*N^epsilon*|W|`, before every real alpha.

The small branch retains the three previously proved cardinality powers.
In the large branch put R=|W| and use the returned integer j and
D=bourgainDifferenceLevel W j. The theorem retains
`j<log_2(R)+1`, D nonempty, `2^j<=R`, and `2^j*|D|<=2R^2`.
Define the actual quantities

```text
h = N^(epsilon/8), U = T+h+1,
L = sum_(l in D) integral_(-h)^h |zeta(1/2+i(l+u))|^2 du,
a = sqrt(L/(4h|D|)),
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

Then L,a>0, and some q<J gives v=a*2^q>0. The band and its mass are

```text
S = {t in [-U,U] : v <= |zeta(1/2+it)| < 2v},
I = integral_(-h)^h #{l in D : l+u in S} du,
mu = Lebesgue measure(S), K_h = 2 Nat.ceil(h)+1,
K = 2 (Nat.log 2 R+1) 2^(j+1) J (2v)^2.
```

The assembled actual-pattern theorem proves

```text
I>0, mu>0,
N^(-alpha) R^(3/2) N^(tau/2) < K I,
v^4 mu <= C U^(1+epsilon),
I <= 2h|D|, I <= K_h mu.
```

The floor has the exact identity `2h a^2 |D|=L/2`; the other half
selects the band. Spatial enlargement U is derived from the actual
difference support, including its unit integer-rounding loss. The
extra final dyadic band handles equality at powers of two.

For the actual correlation `r=I/(sqrt(mu)*sqrt(|D|))`:

```text
r>0, I=r sqrt(mu) sqrt(|D|),
r^2 <= 2h K_h,
r^2 mu <= 4h^2 |D|,
r^2 |D| <= K_h^2 mu.
```

There is a real u in (-h,h] for which
`D_u={l in D : l+u in S}` is nonempty and
`N^(-alpha) R^(3/2) N^(tau/2) < K (2h) |D_u|`.
This is a genuine shifted slice, not an abstract mass witness.
The separate weighted-family shift theorem uses one shift for the whole
supplied finite family; common band parameters across source subdivisions
have **not** yet been constructed.

The ceiling-logarithmic J and all finite losses remain explicit. No
uniform logarithmic absorption, full source subdivision, local-mean
lower estimate, final mixed-moment comparison, frozen logarithmic
dichotomy or ninth-row discharge is claimed. The unrestricted printed
Lemma 4.1/(4.7) range and remaining physical-range bridges also remain
open. Add-est (ix), EPZAE-19/36/37 and the whole EPZAE-00--41 goal
retain their existing acceptance tests.

All eight modules enter the root imports and the exact BAT inventory.
There are 29 new explicit public-theorem audits and 43 semantic
regressions, including full signatures, empty/zero windows, half-open
band boundaries, exact dyadic counts, the half-mass identity and
weighted common shifts. The target
`run_tao_trudgian_yang_build.bat`, its PowerShell driver and foundation
`run_lake_build.bat` remain mandatory; no verification gate is narrowed.

### Completed verification for this checkpoint

Both mandatory BATs terminated with PASS and exit 0 on 21 September 2026,
on dirty `main` at HEAD `e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`.

- Target `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  473 package Lean files, 484 integrity-scanned files, 9,328 build jobs,
  4,476 discovered target theorems and 4,481 audited declarations.
  All 29 new explicit public audits have only permitted logical dependencies;
  all 43 new semantic regressions pass.
  Log: `logs/tao-trudgian-yang-build-20260921-141745-d2685809.log`.
- Foundation `cmd /c run_lake_build.bat --no-pause`: all six stages pass,
  301 root modules, 2 explicit regressions, 0 excluded/unclassified files,
  8,857 build jobs, 7,636 explicit public declarations and 14,290 discovered
  nonprivate project theorems audited.
  Foundation-root log: `logs/foundation_freeze_20260921_141746.log`;
  manifest: `logs/foundation_freeze_20260921_141746.json`.

Both completed logs have zero Lean errors, warnings or tactic diagnostics.
Every foundation stage also records zero linter failures. There are no
remaining failed verification stages. All 130 checked source, integration
and runner hashes are unchanged across the gates, including the preserved
counterexample. Repository scans found no prohibited proof shortcut;
the broad postulate search has only the same ten prose and two rational
structure-field matches. `git diff --check` passes; its 16 LF/CRLF notices
are Git normalization notices, not Lean diagnostics.

This verifies the installed scope. It does not complete the full Bourgain
source range/dichotomy, Add-est (ix), or the unchanged whole-proof goal.

## Bourgain shared grids and actual subdivision — verified historical checkpoint

The corrected independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. The printed-Lemma-62 counterexample remains
byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The false fifth-coordinate scaling and third witness remain excluded.

Six new production modules advance the actual Bourgain source chain:

- `BourgainSharedFloor`: a physical amplitude floor independent of the
  selected difference set, local mass and component. Its doubled low-value
  cost is bounded using the actual source cardinality and heavy-level bounds.
- `BourgainFixedBand`: selection on this supplied common floor. Its
  explicit low-mass condition is discharged in the actual-pattern consumer.
- `BourgainBandLogBounds`: the exact ceiling-logarithmic band count is
  bounded by a linear logarithm, and by an arbitrary small positive power
  with fixed-parameter constants.
- `BourgainSharedGrid`: the existing actual source dichotomy now selects
  its bands on that shared grid, retaining the complete measure, occupancy,
  correlation and shifted-slice conclusions.
- `BourgainRetainedPullback`: inverse local reflection preserves actual
  cardinality, separation, the original coefficient polynomial and every
  strict ordered integer difference count. Local source bins, and retained
  subsets pulled back into distinct bins, are disjoint.
- `BourgainSubdivisionGrid`: constructs retained subfamilies in every
  actual localized pattern and assembles their disjoint original-source union
  with exact cardinality and packing cost.

For sigma>3/4, fixed real tau and epsilon>0,
`bourgain_retained_shared_grid_dichotomy` gives B>0, C>=2 and
0<delta<=1 before the pattern. It retains the physical conditions
`C<=N<=T`, `T<=N^(tau+delta)` and `N^(sigma-delta)<=P.V`.
The same W is selected before every real alpha. Its small branch is
unchanged; its large branch now uses

```text
A = |alpha|+4|tau|+epsilon+20,
a = N^(-A), h = N^(epsilon/8), U = T+h+1,
J = Nat.clog 2 (Nat.ceil (B(1+U)/a)) + 1.
```

This a is independent of W, the difference index j, D and its actual local
mass L_D. For the returned heavy level the proof derives

```text
2 (Nat.log 2 |W|+1) 2^(j+1) [2h a^2 |D|]
  <= N^(-alpha) |W|^(3/2) N^(tau/2)
  < M(W,h)
  <= (Nat.log 2 |W|+1) 2^(j+1) L_D.
```

Thus `2(2h a^2 |D|)<L_D`, so the fixed-floor selector genuinely
applies. The floor's crude numerical margin is proved, including negative
alpha and tau; no new mass estimate is postulated.

The proved physical radius bound and actual-pattern count conclusion are

```text
U <= 3 N^(|tau|+epsilon+1),
J <= 2 + [log(4B+1) + (|tau|+epsilon+1+A) log N]/log 2.
```

For fixed B,A,u and any eta>0, the separate uniform theorem bounds J by
C_eta N^eta whenever 0<=U<=3N^u and N is sufficiently large.
Those constants may depend on A, hence on alpha; no uniform-in-alpha
small-power absorption is asserted.

The new public subdivision theorem `bourgain_subdivided_shared_grid`
uses the actual `P.localized L hL i` patterns, with unchanged N,
threshold, support and coefficients. Here L is the chosen local height;
tau controls L, **not the unrestricted original height P.T**. It assumes
`N<=L<=N^(tau+delta)` and the same scale/value conditions. It constructs
W_i for every local component, before alpha. All components therefore use
the same a,h,U=L+h+1,J, though their chosen amplitude index q may differ.

For I=range(floor(P.T/L)+1), let

```text
S_i = { (P.localized L hL i).intervalRight - w : w in W_i },
S = union_(i in I) S_i.
```

The source consumer proves S is contained in P.ordinates, S is one-separated,
the original negative-phase polynomial is large at every point of S, and

```text
|S| = sum_(i in I) |W_i|,
|P.ordinates| <= C N^epsilon |S|,
Delta_(S_i)(l) = Delta_(W_i)(l) for every integer l.
```

The count identity uses inverse reflection and swapping the ordered pair,
so the strict unit boundary and the same integer bin are preserved.
One must use these pulled-back subsets for the global source union;
normalized reflected sets from different components can overlap.

Common amplitude indices, relative difference levels and correlation levels
across the large components are still open. The shared grid and actual
subdivision do not by themselves prove source (4.43)--(4.47). The remaining
local-mean lower estimate, mixed-moment comparison, logarithmic transfer,
ninth-row discharge, unrestricted source-(4.7) range and other required
physical-range bridges remain open. Add-est (ix), EPZAE-19/36/37 and the
whole EPZAE-00--41 completion contract are unchanged.

All six modules are included in the root and the target BAT's exact
inventory, with 22 new explicit public-theorem audits and 37 semantic
regressions. Tests cover full signatures, common physical floors/counts,
unchanged localized coefficients, empty unions, inverse reflection and
strict integer-bin endpoints. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-145545-b9986edf.log`.
  All 479 package Lean files are covered, 490 Lean files scanned, and
  9334 build jobs pass. The audit checks 4501 discovered target theorems
  plus five imported boundary declarations: all 4506 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_145042.log`
  with its matching JSON manifest. All six stages pass; 301 root modules,
  two explicit regressions and no exclusions remain classified.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 22 newly explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 37 new semantic regressions
pass. Both full logs contain zero Lean errors, warnings or tactic
suggestions. Repository-wide shortcut scans found no prohibited proof term
or postulate; broad textual matches are existing prose or rational
structure-field names. The 136 recorded source/integration/runner hashes
are unchanged across verification, including the preserved counterexample.
The architecture has 160 distinct nodes and 397 resolved edges.
`git diff --check` passes; Git emits 16 existing LF/CRLF normalization
notices, not Lean diagnostics.

This verifies the installed supporting theorem scope, not the remaining
Bourgain dichotomy, Add-est (ix), or whole-proof completion.

## Bourgain common component levels and correlation product — verified historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses, unrestricted fifth
coordinates, and Add-est (i)--(viii) remain unchanged. No false scaling or
third witness is restored.

Five production modules advance the actual Bourgain component selection:

- `BourgainComponentSelection` proves weighted finite-fiber selection and
  the small/large partition estimate with its exact counting cost.
- `BourgainCommonBand` consumes `bourgain_subdivided_shared_grid`,
  selects one common actual zeta-amplitude index on the large components,
  and constructs their original-source union.
- `BourgainRelativeLevels` regrids the relative multiplicity
  `2^j/|W|`, with a shared physical floor, logarithmic count, and
  factor-four bounds on the actual ordered integer difference counts.
- `BourgainCorrelationProduct` derives a finite relative/correlation
  product lower bound from actual component mass and the fourth moment.
- `BourgainCommonLevels` consumes the common-band family, performs the
  second weighted selection, and derives that product inequality on the
  actual retained components.

The named proposition `BourgainComponentBand` records literal difference
sets, zeta-band integrals, measures, correlation and shifted-slice data.
It is a specification, not a theorem by itself. Both public subdivision
consumers construct these witnesses from the existing analytic theorem;
they do not accept that proposition as an analytic input.

The strongest consumer is `bourgain_subdivided_common_levels`.
For sigma>3/4, fixed real tau and epsilon>0, its constants B>0, C>=2 and
0<delta<=1 precede the pattern. It keeps
`C<=N<=L`, `L<=N^(tau+delta)`, and `N^(sigma-delta)<=P.V`.
The retained W_i are chosen before alpha. Here tau controls the local
height L, not the unrestricted original height P.T.

For fixed alpha let I=range(floor(P.T/L)+1), m=|I| and

```text
h=N^(epsilon/8), U=L+h+1,
a=N^(-(|alpha|+4|tau|+epsilon+20)),
J=bourgainZetaBandCount B U a,
Q=bourgainRelativeLevelCount N tau,
F=C [N^(2-2sigma+epsilon)+N^(2tau+4-8sigma+epsilon)
     +N^(-2alpha+tau+12-16sigma+epsilon)].
```

The theorem selects a common q<J, p<Q, and actual component indices A
contained in I. Every selected component has original local cardinality
strictly larger than F. Set V=a*2^q and d=N^(-(|tau|+2))*2^p.
For each selected i, D_i is the actual heavy difference level j_i of W_i,
R_i=|W_i|, and

```text
0<d<=1,
d R_i <= 2^j_i < 2 d R_i,
d R_i <= Delta_(W_i)(ell) < 4 d R_i  (ell in D_i),
d |D_i| <= 2 R_i.
```

The common relative index is not an absolute difference index.
The proved uniform count is

```text
Q <= 2+[log 5+(|tau|+2) log N]/log 2.
```

Writing r_i for the actual normalized band occupancy and
Z_i=Nat.log 2 R_i+1, the consumer also proves

```text
N^(-2alpha) N^tau < 1024 Z_i^2 J^2 C U^(1+epsilon) d r_i^2.
```

This follows by squaring the actual large-mass inequality, using
V^4 times the actual band measure <= C U^(1+epsilon), and cancelling
the positive R_i^3. No correlation lower bound is assumed.

Let S be the union of the retained sets pulled back into their original
local bins. The consumer proves S is contained in P.ordinates,
one-separated, and large for the unchanged original negative-phase
coefficient polynomial. Its cardinality is exactly sum_(i in A) R_i;
each component's strict ordered integer difference counts are preserved.
The original total satisfies

```text
|P.ordinates| <= m F + C N^epsilon J Q |S|.
```

The selected family may be empty when the small bound suffices. No
nonempty large family or unaccounted logarithmic loss is silently assumed.

Common correlation-level selection and its finite/logarithmic losses,
the full integer-slice common-shift inequality, the local-mean lower
estimate and actual mixed-moment comparison remain open. So do the
finite/logarithmic Bourgain dichotomy, its remaining physical-range
bridges and Add-est (ix). EPZAE-19/36/37 and the whole EPZAE-00--41
completion contract remain open and unchanged.

The root and exact target BAT inventory include all five modules,
with nine new explicit theorem audits and 23 semantic regressions.
Both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` remain mandatory, with unchanged coverage,
integrity and zero-warning gates.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-152459-3040905f.log`.
  All 484 package Lean files are covered, 495 Lean files scanned, and
  9339 build jobs pass. The exhaustive audit checks 4517 discovered target
  theorems and five imported boundary declarations: all 4522 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_152045.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All nine new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 23 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
the broad text search matches only existing prose and rational structure
fields. All 141 checkpoint source/integration/runner hashes are unchanged
between the pre-target-gate snapshot and post-gate check, including the
preserved counterexample. The architecture has 164 distinct nodes and
406 resolved edges. `git diff --check` passes; the 16 Git LF/CRLF
normalization notices are not Lean diagnostics.

Semantic edge check: CSEL is realized by
`bourgain_subdivided_common_band`, which consumes the actual subdivision
and weighted partition theorem. CRG is realized by
`bourgain_retained_relative_level` and
`bourgainRelativeLevelCount_log_bound`. CCP is the derived
`BourgainComponentBand.relative_correlation_lower`, not a field assumed
in the component predicate. CLEV is
`bourgain_subdivided_common_levels`, which constructs its selected
family from those actual outputs and derives the product inequality on it.

This verifies the installed supporting theorem scope, not the remaining
correlation selection, Bourgain dichotomy, Add-est (ix), or whole-proof goal.

## Bourgain common correlation and uniform selection losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est
(i)--(viii) are preserved. False fifth-coordinate scaling and a third
witness remain excluded.

Five new production modules complete the next finite selection step:

- `BourgainCorrelationScales`: a coarse polynomial amplitude-count
  bound and shared inverse-power correlation floor, with proved exponent
  margin and coefficient balance.
- `BourgainCorrelationWindow`: actual retained cardinality, spatial
  enlargement and mass/fourth-moment data force each component's correlation
  into that shared physical window.
- `BourgainCorrelationGrid`: a genuine finite correlation grid, its
  logarithmic count and fixed-parameter small-power bound, and actual
  component selection with two-sided occupancy bounds.
- `BourgainCommonCorrelation`: consumes the actual common-amplitude/
  relative-level family and performs the third retained-cardinality-weighted
  selection, preserving the original-source union.
- `BourgainSelectionLosses`: proves a joint arbitrary-small-power
  bound for all three actual selection counts.

The prior common-level module's introductory comment now scopes its
remaining work to downstream consumers; its theorem statement is unchanged.

For the already fixed B>0, C>=2, alpha, tau and epsilon>0, define

```text
u=|tau|+epsilon+1,
A0=|alpha|+4|tau|+epsilon+20,
E=2(|tau|+1)+2(u+A0)+u(1+epsilon),
A1=|alpha|+|tau|+E+1,
K0=4096 C (4B+2)^2 3^(1+epsilon)+1,
b=N^(-A1)/K0, h=N^(epsilon/8).
```

The floor b is independent of the local component, difference level,
local mass and band index. The proved actual-component window is
`0<b<r_i<=4h`. Its lower endpoint follows from the existing actual
correlation-product inequality, not an assumed correlation estimate.
The proof bounds its coefficient by `(K0-1)N^E` and proves

```text
(K0-1) N^E b^2 <= N^(-2alpha) N^tau.
```

The shared finite count and its bound are

```text
Kc = bourgainZetaBandCount (4K0) (h-1) (N^(-A1)),
Kc <= 2+[log(16K0+1)+(epsilon/8+A1) log N]/log 2.
```

The terminal bound is strict, including exact dyadic endpoints.
For fixed parameters and any eta>0, the count is <=D_eta N^eta
beyond a proved threshold. Alpha is an allowed dependency; no
uniform-in-alpha threshold is asserted.

The main consumer `bourgain_subdivided_common_correlation` retains
sigma>3/4, `C<=N<=L<=N^(tau+delta)`,
`N^(sigma-delta)<=P.V`, and `0<delta<=1`.
B,C,delta precede the pattern; the same W_i precede alpha.
Tau still describes the local height L, not the unrestricted original P.T.

It constructs common indices q<J, p<Q and k<Kc and actual selected bins.
All previous component data remain available. With
V=N^(-A0)2^q, d=N^(-(|tau|+2))2^p, s=b2^k,
U=L+h+1, actual difference set D_i, actual band measure mu, and
actual correlation r_i, each selected component satisfies

```text
0<s,  s<=r_i<2s,  s<=4h,
s sqrt(mu) sqrt(|D_i|) <= actual band occupancy
  < 2s sqrt(mu) sqrt(|D_i|),
N^(-2alpha) N^tau
  < 4096 (Nat.log 2 |W_i|+1)^2 J^2 C U^(1+epsilon) d s^2.
```

The factor 4096 is derived from the prior product bound and the
two-sided correlation band; it is not added as a field in the source
component predicate.

Let m=floor(P.T/L)+1 and F be the unchanged three-term small-component
bound from the preceding checkpoint. The selected original-source union S
has exact cardinality sum_i |W_i|, is one-separated, and is large for the
unchanged original coefficient polynomial. Every component's strict ordered
integer difference counts are preserved. The proved global bound is

```text
|P.ordinates| <= m F + C N^epsilon J Q Kc |S|.
```

The family may be empty when the small bound suffices. No nonempty large
family is silently assumed. The main consumer retains the finite counts;
their absorption is proved separately by
`bourgain_selection_counts_uniform_power`: for fixed B,C,alpha,tau,epsilon
and every eta>0, constants D,N0 precede the actual pattern and its
physical-window parameter, and for N>=N0, `J Q Kc<=D N^eta`. For the selected
family this applies to the actual localized pattern of height L.

The full integer-slice common-shift inequality, local-mean lower estimate,
actual mixed-moment comparison, finite/logarithmic Bourgain dichotomy and
remaining physical-range bridges are still open. Add-est (ix),
EPZAE-19/36/37 and the whole EPZAE-00--41 contract remain open.

The root and exact target BAT inventory include all five modules, with
17 new explicit theorem audits and 31 semantic regressions. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`;
no coverage, warning, integrity or dependency gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-155221-a509a790.log`.
  All 489 package Lean files are covered, 500 Lean files scanned, and
  9344 build jobs pass. The exhaustive audit checks 4543 discovered target
  theorems and five imported boundary declarations: all 4548 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_154836.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 17 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 31 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 146 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 168 distinct nodes and 417 resolved edges.
`git diff --check` passes; 16 Git LF/CRLF normalization notices are
not Lean diagnostics.

Semantic edge check: CSCL is realized by
`bourgain_component_correlation_window`, consuming the actual component
product, retained-cardinality bound and proved floor balance.
CGR is realized by `bourgain_component_correlation_grid`,
`bourgainCorrelationLevel_terminal` and
`bourgainCorrelationLevelCount_log_bound`.
CCOR is `bourgain_subdivided_common_correlation`, which consumes the
actual prior family, derives all component grid witnesses and constructs
the third weighted fiber and original-source union.
SLOSS is `bourgain_selection_counts_uniform_power`, whose conclusion
uses the actual counts and linked physical height of the supplied pattern.
These are supporting results; the full integer-slice shift, Bourgain
dichotomy, Add-est (ix), and whole-proof contract remain unfinished.

## Bourgain full integer slice and source mixed lower bound — historical checkpoint

The printed-Lemma-62 counterexample is preserved byte-for-byte, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses and Add-est (i)--(viii)
are unchanged. False fifth-coordinate scaling and a third witness stay excluded.

Twelve new production modules prove a full two-term common shift for the
actual selected family, a power-window local mean for the original polynomial,
and their actual source-pattern mixed lower-bound consumer:

- `BourgainIntegerSlice`, `BourgainSliceSelection`: the complete integer
  slice, its integrated cardinality and square-root bounds, and simultaneous
  weighted selection against both profiles.
- `BourgainComponentMass`, `BourgainFamilySlice`, `BourgainCommonSlice`:
  derive both weighted mass lower bounds from actual component occupancy,
  fourth moment and common levels, then consume the actual three-level family.
- `BourgainSliceGeometry`: the real image has the same cardinality, is
  one-separated, and has proved spatial bounds and shifted zeta membership.
- `BourgainLocalMean`, `BourgainPowerMean`, `BourgainLocalSquare`:
  frequency-center the original closed-support negative-phase polynomial,
  consume the native finite exponential-sum Fourier estimate, absorb its tail,
  and prove the displaced local-square estimate.
- `BourgainMixedLower`, `BourgainMixedFamily`, `BourgainCommonMixed`:
  preserve strict ordered difference counts and original-source pullbacks,
  sum over the disjoint bins, and assemble the actual mixed lower bound.

### Exact finite physical statement and semantic edges

Write h=N^(epsilon/8), U=L+h+1, Vb for the selected common zeta amplitude,
mu for the measure of its actual band, and K=2 ceil(h)+1. The full slice is

```text
Z(u) = {ell in [-ceil(U+h),ceil(U+h)] in Z : ell+u belongs to the band}.
```

For every u in [-h,h] it contains every integer whose translate lies in the
band, not just the integers from one component's difference level.
`bourgainIntegerSlice_integral_card_le` and
`bourgainIntegerSlice_integral_sqrt_card_le` prove, over [-h,h],

```text
integral |Z(u)| <= K mu,
integral sqrt(|Z(u)|) <= sqrt(2h K mu).
```

Let R_i=|W_i|, D_i be the actual heavy difference level, d the common relative
multiplicity, s the common correlation level, J the actual amplitude count,
and Zlog=3+(|tau|+1) log(N)/log(2). Define

```text
beta = N^(-alpha) N^(tau/2) / [32 Zlog J d sqrt(C U^(1+epsilon))],
a = s^2/(8hK),    b = beta/[4 sqrt(2hK)].
```

The theorem `BourgainComponentBand.weighted_mass_lower` derives its two
mass inequalities from the actual band, not from assumed desired lower bounds.
`bourgain_component_family_slice` consumes them and the complete slice
moments. `bourgain_subdivided_common_slice` constructs the actual selected
family and proves either the genuine small-component bound or a common
u in (-h,h] with nonempty Z=Z(u) and

```text
a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)
  < sum_i R_i |D_i intersect Z|.
```

Here S is exactly the disjoint union of retained sets pulled back into their
original bins; |S|=sum_i R_i. The common levels, unchanged original
coefficients, source containment, one-separation, strict difference counts,
and global packing cost m F + C N^epsilon J Q Kc |S| are retained.
No nonempty selected family is assumed; the empty case gives the small bound.

For every eta>0, `bourgain_power_window_displaced_square` provides constants
M>0 and N0>=2 before the actual pattern and points, and proves

```text
P.V^2 <= M N^eta integral_[-r,r] |F_P(x+v)|^2 dv,
r=1+2 pi N^eta,
```

when N>=N0, sigma>=0, delta<=1, N^(sigma-delta)<=P.V, and x is within one
unit of an actual large ordinate. The underlying exact modulation is
exp(i log(N)t) F_P(t); its frequencies are log(N)-log(n), of absolute value
at most one on the literal closed support [N,2N]. It uses the already
kernel-checked native `norm_gmFiniteExpSum_le_localIntegral_add_tail`,
then absorbs the actual tail using P.V>=N^(-1). No analytic local-mean
hypothesis is supplied by a caller.

This is a directly proved **power-window** route to the needed mixed lower
bound, not a proof of the printed logarithmic-window lemma (4.48).
That sharper printed statement is not marked complete.

The strongest consumer `bourgain_subdivided_mixed_lower` retains
sigma>3/4, epsilon>0, eta>0, C<=N, N0<=N,
N<=L<=N^(tau+delta), N^(sigma-delta)<=P.V and 0<delta<=1.
B,C,delta,M,N0 precede the actual pattern; W_i still precede alpha.
Tau governs the local L, not the unrestricted original P.T.
On its large branch it constructs the same nonempty full slice and proves

```text
P.V^2 d [a |Z| |S| + b sqrt(|Z|) sum_i R_i^(3/2)]
  < M N^eta integral_[-r,r] sum_(t in S) sum_(ell in Z)
      |F_P(t-ell+v)|^2 dv.
```

The strict-bin first-coordinate injection uses each W_i's two-separation.
The proof transports each component's ordered counts into its original bin
and sums over the disjoint source union. It does not identify the union's
total difference count with the sum of component counts.

This closes the finite physical common-shift and source mixed **lower**
steps (the roles of source (4.47) and (4.53)). It does not yet combine the
mixed upper bound with Heath--Brown, prove (4.57)--(4.63), or discharge
the ninth-row logarithmic-dichotomy premise. Add-est (ix), EPZAE-19/36/37,
and the whole EPZAE-00--41 goal remain open.

Root imports, the exact target BAT inventory, explicit audit and semantic
regressions include all twelve modules: 39 new public theorem audits and
59 new regression examples, including closed endpoints, strict excluded
difference boundaries, zero amplitude, unchanged coefficients and both
source-facing consumer types. Both `run_tao_trudgian_yang_build.bat` and
foundation `run_lake_build.bat` remain mandatory; no gate is narrowed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-164830-0fe87f33.log`.
  All 501 package Lean files are covered, 512 Lean files scanned, and
  9356 build jobs pass. The exhaustive audit checks 4601 discovered target
  theorems and five imported boundary declarations: all 4606 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_164601.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 39 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 59 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 158 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 172 distinct nodes and 428 resolved edges.

Semantic green-node check: ISL uses
`bourgainIntegerSlice_integral_card_le`,
`bourgainIntegerSlice_integral_sqrt_card_le` and
`bourgainRealSlice_separated`/`bourgainRealSlice_bounds` on the defined
complete slice. CSH is `bourgain_subdivided_common_slice`, which consumes
the actual common-correlation family and derived weighted mass bounds.
LPM is `bourgain_power_window_displaced_square`, using the proved exact
modulation, native Fourier estimate, tail absorption and interval translation.
MLB is `bourgain_subdivided_mixed_lower`, which unpacks the actual source
family and composes CSH, LPM, strict difference counts and original pullbacks.
These statements preserve the stated parameter ranges and constant order.
The full mixed upper assembly, Bourgain dichotomy, Add-est (ix) and
whole-proof contract remain open; audit counts do not close those obligations.

## Bourgain Heath–Brown comparison and linked subdivision — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The authorized independent cardinality/energy witnesses and Add-est (i)--(viii)
are preserved; false fifth-coordinate scaling and a third witness stay excluded.

Ten new production modules advance the actual mixed lower bound through
Heath--Brown, remove the common multiplicity/correlation levels, and link
the subdivision to the original physical height:

- `BourgainSeparatedSelf`: the native Heath--Brown self-moment bound on
  arbitrary one-separated sets, with the original polynomial's closed support
  and explicit endpoint error. The auxiliary slice is not falsely made into
  a large-value pattern for the original polynomial.
- `BourgainMixedShift`, `BourgainMixedUpper`: exact unit-norm coefficient
  twist, integer-to-real sum bridge, integration length, and the actual
  source-set/full-slice mixed upper bound.
- `BourgainCommonComparison`: consumes the already constructed selected
  family and both actual analytic estimates.
- `BourgainLevelElimination`, `BourgainLevelFreeComparison`: use the
  genuine component product to remove correlation and multiplicity from
  the first coefficient; cancel multiplicity exactly in the second; replace
  the component three-halves sum by the retained union's cardinality,
  paying the square root of the actual bin count.
- `BourgainPhysicalUpper`, `BourgainPhysicalComparison`: prove the
  slice's enclosing height is at most 8 times the original height when
  N<=L<=T and epsilon<=8; absorb the constant-factor enlargement uniformly.
- `BourgainSubdivisionScale`, `BourgainLinkedComparison`: link
  L=T/N^chi with both original-height power bounds, prove the finite bin
  count, and instantiate the actual comparison at the ninth-row choice.

### Source-facing physical comparison

The strongest general linked consumer is
`bourgain_linked_subdivision_comparison`. It assumes sigma>3/4,
chi>=0, lambda=tau-chi>1, eta>0, theta>0 and 0<epsilon<=8.
Its positive constants B,C,M,D,N0 and
0<delta<=min(1,(lambda-1)/2) precede the actual pattern.

For N>=max(C,N0), N^(tau-delta)<=T<=N^(tau+delta),
N^(sigma-delta)<=P.V and the literal L=T/N^chi, it derives N<=L<=T,
the required local upper-height bound, and

```text
m = floor(T/L)+1 <= 2 N^chi.
```

The local band/selection constructions use **lambda**, not global tau.
The same genuine reflected W_i are chosen before alpha. For every alpha
the consumer preserves all three common levels, every actual component band,
the disjoint original-source union S, exact cardinality, one-separation,
the unchanged original polynomial and the strict ordered difference counts.

Write h=N^(epsilon/8), U=L+h+1, K=2 ceil(h)+1,
Zlog=3+(|lambda|+1) log(N)/log(2), J for the actual amplitude count,
R=|S|, and x=|Z(u)| for the nonempty complete integer slice.
Define the two level-free coefficients

```text
gamma = N^(-2alpha) N^lambda /
  [32768 h K Zlog^2 J^2 C U^(1+epsilon)],
beta = N^(-alpha) N^(lambda/2) /
  [128 Zlog J sqrt(C U^(1+epsilon)) sqrt(2hK)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The exact Lean names are `bourgainEliminatedCardCoefficient`,
`bourgainSliceSqrtCoefficient ... 1`, and `bourgainSecondBudget`.
Both lower coefficients are proved positive. Either the actual original
cardinality obeys the small-component bound m F, or S is nonempty and the
consumer constructs u in (-h,h] and the nonempty full slice satisfying

```text
P.V^2 [gamma x R + beta sqrt(x) R^(3/2)/sqrt(m)]
  < M N^eta 2(1+2 pi N^eta) D T^theta
      sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

F is the unchanged three-term small-component bound, now with local lambda.
The companion global selection inequality remains
`|P.ordinates| <= m F + C N^epsilon J Q Kc R`, with actual finite counts.
No Heath--Brown, local-mean, desired correlation, or mixed-bound hypothesis
is left for the caller to provide. Both height hypotheses and coefficient
normalization are discharged on the actual objects.

This is the full finite physical mixed comparison with the third
Heath--Brown term retained. It is not a claim that the paper's simplified
two-term display holds without its additional range assumptions.

### Ninth-row entry and exact remaining work

`bourgain_ninth_row_local_height_margin` proves that
chi=max(0,4sigma+4tau/3-5) is nonnegative and tau-chi>1 from sigma>3/4,
16sigma-11<=tau and 20sigma+tau/3<=16.
`bourgain_ninth_row_physical_comparison` actually instantiates the linked
source consumer at that choice. This closes that row's interior local-height
entry, not the row's large-values conclusion.

Next remove the finite/logarithmic losses with correctly ordered constants:
bound gamma and beta below by the required small-power expressions, use
the proved m bound, transfer the retained union back to total cardinality,
control the slice-cardinality exponent, and pass the actual comparison to
the frozen logarithmic dichotomy. Then discharge
`bourgain_ninth_row_of_log_dichotomy` and finish Add-est (ix).

The unrestricted printed-(4.7) range and other classical/source obligations
remain open. The printed logarithmic-window (4.48) is still not claimed:
the comparison uses the already proved power-window route.
EPZAE-19/36/37, Add-est (ix), and the full EPZAE-00--41 goal remain open.

The root imports, exact target BAT inventory, explicit audit and semantic
regressions include all ten modules: 31 public theorem audits and 45 regression
examples. Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, including coverage, dependency, integrity and
zero-warning gates. No frozen source or dependency pin changed.

### Verification status for this checkpoint

Both mandatory BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-172415-5a54834a.log`.
  All 511 package Lean files are covered, 522 Lean files scanned, and
  9366 build jobs pass. The exhaustive audit checks 4645 discovered target
  theorems and five imported boundary declarations: all 4650 pass.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_172230.log`
  and its matching JSON manifest. All six stages pass, with 301 root
  modules, two explicit regressions and no excluded/unclassified files.
  The 8857-job build, 7636 explicit public declarations, exhaustive
  14290-theorem audit and declaration linters pass.

All 31 new explicit audits report only `propext`, `Classical.choice`
and `Quot.sound`; all 45 new semantic regressions pass.
Both complete logs contain zero Lean errors, warnings or tactic suggestions.
Repository shortcut scans find no prohibited proof term or postulate;
broad text matches are existing prose and rational structure fields.
All 168 checkpoint source/integration/runner hashes are unchanged between
the pre-target-gate snapshot and post-gate check, including the counterexample.
The architecture has 177 distinct nodes and 444 resolved edges.
`git diff --check` passes; the 16 Git LF/CRLF normalization notices
are not Lean diagnostics.

Semantic green-node check: HBSET is
`bourgain_separated_self_moment`, applying the native moment to the
actual reflected arbitrary set and paying the closed-support endpoint.
SHCS is `bourgain_slice_mixed_integral_cauchySchwarz`, using the
proved exact twist, support-only coefficient bound and complete integer image.
MCOMP is `bourgain_subdivided_mixed_comparison`, composing the actual
selected-family lower bound with the proved upper estimate on its source union
and full slice. LELIM is `bourgain_subdivided_level_free_comparison`;
its first coefficient is derived from the real component product, its second
uses exact multiplicity cancellation, and its power-sum loss uses the actual
disjoint-union cardinality and bin count.
PSCALE is `bourgain_linked_subdivision_comparison` and
`bourgain_ninth_row_physical_comparison`, deriving local ranges and
the original-height enclosure from the literal subdivision and shrinking
the allowed delta explicitly. No desired analytic estimate is a premise.

These are finite source-comparison results. Finite-loss absorption, the
logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain
unfinished; dependency integrity is not a claim of those endpoints.

## Bourgain uniform finite power losses — historical checkpoint

The printed-Lemma-62 counterexample remains byte-for-byte unchanged
(SHA256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
The corrected independent cardinality and energy witnesses, Heath--Brown
energy relation and Add-est (i)--(viii) remain preserved. No false
s'/s fifth-coordinate scaling or third powering witness is introduced.

Five production modules now express the actual comparison's finite losses
as explicit powers, with constants chosen before the physical pattern:

- `BourgainCoefficientIdentity` proves beta^2=gamma exactly, including
  the zero fourth-moment-constant boundary, and beta=sqrt(gamma).
- `BourgainComparisonLogLoss` bounds the literal difference logarithm
  and amplitude count jointly by an arbitrary positive power.
- `BourgainCoefficientLosses` derives the ceiling-window product,
  enlarged local-height power and both coefficient lower bounds.
- `BourgainComparisonPowerBudget` bounds the square-root bin factor
  and original-height integration factor, and proves explicit slack control.
- `BourgainLinkedPowerLoss` consumes the actual constructed family,
  retained original-source union and complete integer slice.

### Exact finite consumer and parameter order

`bourgain_linked_power_loss_comparison` fixes
sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta,
and 0<epsilon<=8 before its constants B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta). Alpha is a permitted constant dependency;
this theorem does not assert uniformity in alpha. The earlier stronger
family-before-alpha construction is unchanged.

For the actual pattern, N>=max(C,N0), L=T/N^chi,
N^(tau-delta)<=T<=N^(tau+delta), and N^(sigma-delta)<=P.V,
the theorem derives L>0 and N<=L<=T. All local grids use lambda;
the Heath--Brown budgets retain the original T.

Write R=|S|, h=N^(epsilon/8), U=L+h+1, x=|Z(u)|, and

```text
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
F = C [N^(2-2sigma+epsilon)
       + N^(2lambda+4-8sigma+epsilon)
       + N^(-2alpha+lambda+12-16sigma+epsilon)],
HB(N,T,y) = y^2 N + y N^2 + y^(5/4) T^(1/2) N.
```

The real selected set S is a one-separated subset of the original ordinates,
with the original polynomial large at every member. Its packing inequality is

```text
|P.ordinates| <= 2 N^chi F + C H N^(epsilon+kappa) R.
```

Either |P.ordinates|<=2 N^chi F, or S is nonempty and a genuine grid level q
and u in (-h,h] give a nonempty complete integer slice with

```text
N^(2sigma-2delta) [
  N^(-2alpha-E)/G * x R
  + N^(-alpha-E/2-chi/2)/sqrt(2G) * sqrt(x) R^(3/2)]
< K N^(2eta+(tau+delta)theta)
    sqrt(HB(N,T,R)) sqrt(HB(N,T,x)).
```

The coefficient bounds come from the actual denominators, not assumed
certificates. The joint J Q Kc bound is applied to the actual localized
pattern; the bin factor comes from floor(T/L)+1<=2N^chi. The source comparison
at its original delta is specialized using monotonicity to the smaller
requested tolerance, while the new loss estimates use the smaller delta.
No caller supplies an analytic bound, desired correlation, or slice witness.

### Remaining acceptance work

This proves the finite power-loss reduction, not the logarithmic dichotomy.
Choose the small parameters in the required order, absorb the remaining fixed
constants in the limiting argument, control/extract the nonempty slice's
logarithmic cardinality, and use the actual packing inequality to relate R
to the original count. Discharge `bourgain_ninth_row_of_log_dichotomy`,
then the ninth energy projection and Add-est (ix).

The unrestricted printed-(4.7) source range, printed logarithmic-window
(4.48), other open classical/density/exponent-pair work, EPZAE-19/36/37,
and the full EPZAE-00--41 goal remain open. The power-window route is retained;
no public contract, source pin or dependency pin changes.

The root import graph, exact BAT production inventory, explicit axiom audit
and semantic regressions include these five modules and all 11 public theorems.
There are 20 new regressions: 11 exact signatures and nine boundary/slack cases.
Maintain both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat`, with complete coverage and unchanged integrity,
dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-175120-bcf6f466.log`.
  All 516 package Lean files are covered, 527 Lean files scanned, and
  9371 build jobs pass. All 4657 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4662-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_175131.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 11 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 20 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The first foundation attempt, `foundation_freeze_20260921_175009.log`,
failed its text scan on a prose-comment line beginning "constant boundary".
The comment was clarified; no proof or scan gate was weakened. That failed log
is retained as failed historical evidence, not substituted for the current PASS.

All 173 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 178 distinct nodes and 448 resolved edges.
Repository shortcut scans find no prohibited proof term or postulate;
remaining broad text matches are existing prose and rational structure fields.

Semantic green-node check: FPOWER is exactly
`bourgain_linked_power_loss_comparison`. Its proof unpacks
`bourgain_linked_subdivision_comparison`, applies the uniform coefficient
bounds to the derived local physical scale, applies the actual selection-count
bound to `P.localized L hL 0`, and uses the genuine bin count and original T.
It retains the source small alternative and the original polynomial, and
constructs the same complete zeta slice rather than assuming one.
The arbitrarily small tolerance is derived by shrinking the source delta.
No desired analytic estimate or limiting dichotomy is a premise.

This verifies finite power-loss reduction and dependency integrity only.
The logarithmic dichotomy, Add-est (ix), and the whole-proof contract remain open.

## Bourgain finite logarithms and slice compactness — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The independent corrected cardinality/energy witnesses, Heath--Brown relation,
and Add-est (i)--(viii) remain preserved. The false fifth-coordinate scaling
and third witness remain excluded.

Seven new production modules continue from the actual finite power-loss
comparison. They prove the physical slice-cardinality bound, translate both
comparison terms and the original-source packing inequality into logarithms,
and extract both real cardinality coordinates along one common subsequence.

### Actual finite logarithmic alternative

`bourgain_linked_logarithmic_comparison` consumes
`bourgain_linked_power_loss_comparison` on the original pattern, with the
same parameter order and an explicit nonempty-original-set restriction.
This restriction is needed because Mathlib gives log(0)=0; the theorem never
treats that convention as a logarithmic exponent for an empty set.

Fix sigma>3/4, chi>=0, lambda=tau-chi>1, alpha, positive eta/theta/kappa/zeta
and 0<epsilon<=8. Uniform B,C,K,G,H,N0 and
0<delta<=min(1,(lambda-1)/2,zeta) precede the physical pattern. For the same
literal subdivision L=T/N^chi and original-height/amplitude hypotheses,
write

```text
rho = log_N |P.ordinates|, r = log_N |S|, x = log_N |Z(u)|,
E = epsilon/4 + kappa + delta + (lambda+delta) epsilon,
Bsmall = max(chi+2-2sigma, -chi+2tau+4-8sigma,
             -2alpha+tau+12-16sigma),
HBexp(t,y) = max(2y+1, y+2, 5y/4+t/2+1).
```

Either rho<=Bsmall+epsilon+log_N(6C), or the actual nonempty retained subset
S and actual nonempty complete integer slice satisfy

```text
0 <= r <= tau+delta+log_N(2),
0 <= x <= lambda+delta+log_N(9),
rho <= log_N(6C+CH) + max(Bsmall+epsilon, epsilon+kappa+r),

max(-2alpha+2sigma+x+r-E-2delta-log_N(G),
    -alpha-chi/2+2sigma+x/2+3r/2-E/2-2delta-log_N(2G)/2)
< log_N(3K)+2eta+(tau+delta)theta
    + HBexp(tau+delta,r)/2 + HBexp(tau+delta,x)/2.
```

The source set remains one-separated and the original polynomial is large
at its members. The common grid level q and shift u remain genuine witnesses,
not separately supplied scalar cardinalities. All three Heath--Brown terms
are retained.

### Geometry, compactness and supporting limit algebra

`BourgainLogCardinality` proves the full slice has at most 2(U+h)+1
integers using its actual translated band, hence at most 9 N^(lambda+delta)
on the physical local scale. Positivity and logarithmic bounds are derived
from actual nonemptiness.

`BourgainBudgetLogarithm` proves the literal three-term budget is at most
3 N^HBexp at an actual cardinality, and proves joint continuity of HBexp and
its delta/2 height-slack bound. `BourgainComparisonLogarithm` takes logarithms
of both positive finite summands. `BourgainLogPacking` recovers exactly the
frozen first-branch maximum from the three small-component powers and keeps
the retained-to-original count loss explicit.

`bourgain_source_slice_log_subsequence` in `BourgainSliceCompactness`
derives a fixed box from actual pattern/subset/slice geometry and returns
one strictly increasing subsequence for both coordinates:
0<=r<=tau+2 and 0<=x<=lambda+5. No bounded-log-coordinate certificate is an
input. The harmless box constants do not replace the sharper finite bounds.

`BourgainComparisonLimits` proves fixed log_N multipliers tend to zero
when N tends to infinity. Its `bourgain_fixed_logarithmic_limit` passes an
explicit eventual finite logarithmic comparison and supplied coordinate
limits to the corresponding fixed-accuracy inequality. This is supporting
conditional limit algebra, not an assembled source-family dichotomy.

### Remaining source assembly

Construct the actual realizing family and select the small/large branch on
an appropriate subsequence. Apply the common compactness and limit results
to that selected family, use the original-count packing to identify the
retained exponent with the source exponent as the accuracy parameters
vanish, and remove epsilon/eta/theta/kappa/delta in their allowed order.
Then prove the frozen logarithmic dichotomy, discharge
`bourgain_ninth_row_of_log_dichotomy`, and assemble Add-est (ix).

The finite logarithmic alternative is not the zero-loss source theorem.
EPZAE-19/36/37, the ninth projection and clause (ix), all other unfinished
exponent-pair/density/public/release obligations, and the full EPZAE-00--41
goal remain open. The printed logarithmic-window (4.48) and unrestricted
printed-(4.7) range are not claimed.

All seven modules are in the root imports and exact BAT inventory, with
explicit audits for 21 public theorems and 31 new semantic regressions
(21 exact types plus ten boundary/source-form checks). Maintain
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
including full coverage, integrity, dependency and zero-warning gates.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-182850-36f5160d.log`.
  All 523 package Lean files are covered, 534 Lean files scanned, and
  9378 build jobs pass. All 4683 discovered target theorems and five
  imported boundary declarations pass the exhaustive 4688-declaration audit.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_182901.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  the exhaustive 14290-theorem audit and all declaration linters.

All 21 new explicit theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`; all 31 new semantic regressions pass.
Both complete current logs have zero Lean errors, warnings and tactic suggestions.
The earlier foundation run at 182402 also passed but preceded the last source
edit; the 182901 run above supplies the final-source evidence.

All 180 checkpoint source/integration/runner hashes are unchanged between
the pre-gate snapshot and post-gate check, including the counterexample.
The architecture has 180 distinct nodes and 455 resolved edges.
The runner inventory grew by exactly seven modules; source/dependency pins,
permitted axioms, foundation verification gates and both BAT launchers are
unchanged. No proof shortcut, postulate or warning suppression was introduced.

Semantic green-node checks:

- BLOG is `bourgain_linked_logarithmic_comparison`. It consumes the
  actual `bourgain_linked_power_loss_comparison`, derives the local scales
  from the original T and L=T/N^chi, and takes logarithms of the actual
  original/retained counts and complete integer slice. Nonemptiness,
  geometry, original-source packing, and both comparison terms are retained.
  The caller supplies no desired comparison or independent scalar witness.
- BSCOMP is `bourgain_source_slice_log_subsequence`. It derives a common
  compact box from the physical height and subset/slice hypotheses and
  returns one strictly increasing subsequence for both actual coordinates.
  It does not itself choose a realizing family or select the source branch.
- `bourgain_fixed_logarithmic_limit` is explicitly conditional supporting
  algebra: the eventual finite comparison and coordinate limits are inputs.
  It is not used to mark the full analytic source dichotomy green.

This verifies the finite logarithmic alternative, geometric compactness and
fixed-constant limit algebra only. Source branch selection, zero-loss limiting
assembly, Add-est (ix), and the unchanged whole-proof contract remain open.

## Bourgain source dichotomy and optimized region rows — historical checkpoint

The printed-Lemma-62 counterexample remains unchanged, SHA256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The corrected independent cardinality/energy witnesses, the Heath--Brown
relation and Add-est (i)--(viii) are preserved. No fifth-coordinate scaling
or third powering witness has been restored.

### Actual source-family construction and zero-loss limit

`exists_bourgain_region_family` chooses actual patterns from
`InCardinalityEnergyRegion` after arbitrary positive physical tolerances
and arbitrary scale thresholds. Its cardinality logarithms converge to the
source rho by the region's power sandwiches.

`exists_bourgain_diagonal_family` applies the proved finite logarithmic
alternative at accuracy `poweringAccuracy n`, choosing all analytic constants
before the patterns. One finite sum of exponential thresholds absorbs the
five varying factors G, 2G, 3K, 6C and 6C+CH. If rho>Bsmall, the source count
limit rules out the small branch on a tail. The retained source subsets,
original polynomial values and complete integer slices are actual witnesses,
not independent scalar inputs.

The resulting family has source packing

```text
rho_n <= epsilon_n + max(Bsmall+epsilon_n, 2epsilon_n+r_n)
```

and, for the same actual retained/slice cardinalities,

```text
max(-2alpha+2sigma+x_n+r_n,
    -alpha-chi/2+2sigma+x_n/2+3r_n/2)
<= (2tau-chi+12)epsilon_n
   + HBexp(tau,r_n)/2 + HBexp(tau,x_n)/2.
```

The explicit diagonal loss tends to zero. Joint geometric compactness
extracts r and x along one common subsequence. Subset monotonicity gives
r<=rho; the original-source packing and rho>Bsmall give rho<=r.
Thus r=rho, and continuity gives the exact zero-loss comparison.

The public consumer
`InCardinalityEnergyRegion.bourgain_log_dichotomy` now proves

```text
rho <= Bsmall
or exists x>=0,
  max(-2alpha+2sigma+x+rho,
      -alpha-chi/2+2sigma+x/2+3rho/2)
  <= HBexp(tau,rho)/2 + HBexp(tau,x)/2,
```

from actual region membership, sigma>3/4, chi>=0 and tau-chi>1.
It takes no source family, branch-stability assertion, coordinate-limit
certificate or analytic dichotomy as a premise. This closes the formerly
open source branch selection and zero-loss assembly in that physical range.

### Optimized region rows

Classical cardinality bounds discharge rho<=1 for tau<=3/2.
`InCardinalityEnergyRegion.bourgain_ninth_row` consumes the actual
dichotomy and the existing exact scalar certificate; its powered version
uses the corrected cardinality-preserving witness.

Three additional optimized rows follow from the same actual dichotomy.
For all rows below, sigma>3/4 and 1<=tau<=3/2; the listed additional cell
conditions are retained exactly.

| Row | Cardinality bound | Additional cell conditions |
|---|---|---|
| First affine | rho <= (16-20sigma+tau)/3 | 14sigma-10<=tau<=16sigma-11; 5tau<=4+4sigma |
| Mixed affine | rho <= 5-7sigma+3tau/4 | 4+4sigma<=5tau; 48-60sigma<=tau<=8-8sigma |
| Diagonal | rho <= 2-2sigma | tau<=14sigma-10; tau<=3sigma-1 |
| Ninth row | rho <= 9-12sigma+2tau/3 | 16sigma-11<=tau; 20sigma+tau/3<=16 |

The first-affine and diagonal height-one boundaries use the classical
estimate, not a weakened strict-margin hypothesis. The mixed cell itself
forces tau>1. Exact regressions include the common affine corner
(sigma,tau,rho-bound)=(59/76,27/19,12/19), the original 84/109 endpoint,
the height-one boundary and the actual power-two consumer.

### Remaining acceptance work

Add-est (ix) is still open. The frozen ANTEDB
`prove_zero_density_energy_7()` recipe uses tau0=8sigma-4, Bourgain and
Jutila-k=5 cardinality inputs, powers 2 through 5, the zeta moment and
Heath--Brown energy. Continue with actual corrected witnesses and exact
general/zeta energy projection over the entire interval [84/109,5/6].
Do not treat the proved cardinality row as the final energy bound.

The complete unrestricted Bourgain source range, its uniform LV-facing
assembly, any additional optimized cells required by that projection,
EPZAE-19/36/37, the other unfinished exponent-pair/density/public/release
obligations and the full EPZAE-00--41 goal remain open. Neither the printed
logarithmic-window (4.48) nor the unrestricted printed-(4.7) range is claimed.

Six new modules are root-imported and included in the exact BAT inventory.
All 15 public theorems have explicit audits and 24 new semantic regressions
(15 exact signatures and nine endpoint/object checks). The old
`NewAdditiveEnergy` module comment was corrected to say (i)--(viii), matching
its already proved theorem surface. Maintain both
`run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`,
with no exclusions, weakened scans, changed dependency pins or warning suppression.

### Verification and semantic status

Both required BAT gates passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-190824-8fa4580d.log`.
  All 529 package files are covered, 540 Lean files scanned and 9384
  build jobs pass. The exhaustive audit passes 4723 discovered target
  theorems plus five imported boundary declarations, 4728 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_190824.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and all declaration linters.

All 15 new public audits report only `propext`, `Classical.choice`
and `Quot.sound`. All 24 new regressions pass. Both complete final logs
contain zero Lean errors, warnings or tactic suggestions. Repository-wide
shortcut scans have no prohibited proof-term match; the broad declaration
search matches only existing prose and the two genuine rational structure
fields, also accepted by the contract-aware scanners.

All 186 checkpoint source/integration/runner hashes match the snapshot
taken before the final BAT runs. The counterexample and both BAT launchers
are unchanged. Only five existing integration/status files changed; the
remaining new Lean work is in the six named modules. No source/dependency
pin, permitted-axiom policy or verification gate was weakened.

The architecture has 183 distinct nodes and 464 resolved edges.
Semantic green-node checks:

- BDFAM is `exists_bourgain_diagonal_family`: it consumes actual region
  realizations and the finite analytic alternative, absorbs constants by
  its chosen physical scales, and derives branch selection on a tail.
- BDICH is `InCardinalityEnergyRegion.bourgain_log_dichotomy`: it invokes
  that constructor and `BourgainDiagonalFamily.source_witness`; the latter
  consumes actual geometric compactness and original-source packing to
  prove r=rho before taking the zero-loss limit.
- BROWS consists of the four stated actual-region row theorems and
  `bourgain_ninth_row_powered`. They consume the proved dichotomy,
  classical side-condition bridge, exact scalar algebra and corrected
  cardinality witness. The height-one cases are handled explicitly.

These passes verify the installed region dichotomy and specified cardinality
cells, not the full Bourgain source range, Add-est (ix), or whole-proof
completion. The energy projection and all other open goal obligations remain open.

## All nine Add-est clauses recovered by corrected powering — historical checkpoint

### Result and preserved obstruction

The authorized repair now recovers every printed Add-est clause (i)--(ix).
The original singleton counterexample in `EnergyPoweringObstruction.lean`
is unchanged (SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`).
Printed Lemma 62 remains false as printed: its fifth-coordinate scaling
has not been restored or assumed. The archived source and public output
statements have not been changed.

`correctedCardinalityEnergyPowering` supplies separate cardinality- and
energy-preserving witnesses. Their fifth exponents remain independently
existential. The actual Heath--Brown consumer uses the appropriate witness,
and cardinality monotonicity supplies the other coordinate's upper bound.
This is not a claim that an arbitrary four-coordinate polytope is preserved.

### Exact final-clause consumer

On the entire closed interval `84/109 <= sigma <= 5/6`, write

```text
B(sigma) = max((18-19sigma)/(9(3sigma-2)),
               4(10-9sigma)/(5(4sigma-1))).
```

The new public declarations are:

- `add_est_ix_bound`: `IsZeroDensityEnergyBound sigma (B(sigma)/(1-sigma))`.
- `add_est_ix`: the literal printed extended-real inequality
  `A*(sigma)(1-sigma) <= B(sigma)`.
- `add_est_ix_zero_energy`: for every positive epsilon, one constant and
  one positive sigma-shift bound the actual multiplicity-aware zero energy
  by `C T^(B(sigma)+epsilon)` for every sufficiently large T.
- `energyClauseNine_blueprint`: the exact divided blueprint normalization.

These theorems have only the stated sigma interval hypotheses. They do not
accept an energy estimate, cardinality theorem, source dichotomy, moment,
or optimization result as an analytic theorem premise.

The full general range `8sigma-4 <= tau <= 2(8sigma-4)` is derived by
`InCardinalityEnergyRegion.energyClauseNine_general`. Below sigma=4/5,
the exact power cover chooses q=2 or 3. Independent cardinality witnesses
at q and q+1 give rho/q<=3-3sigma. At t=tau/q<=6/5, Jutila k=5 and the
energy witness at q-1 feed all nine Heath--Brown branches. For
6/5<=t<=3/2, the actual corrected cardinality witness consumes the proved
Bourgain first-affine, mixed-affine or ninth row, while the independent
q-energy witness supplies the two energy branches. Above 3/2, all six
q-energy branches use the cardinality cap. For sigma>=4/5, the already
proved clause-(i) general rate is compared exactly with B.

The middle-height cover is exact, not sampled. Its sigma split is 17/22;
its switching lines are (81-96sigma)/5, (13-8sigma)/5, 16sigma-11,
(4+4sigma)/5, 48-60sigma, (27sigma-18)/2 and (16sigma-8)/3.
All overlaps and boundary cases are included. The proof needs no additional
high-height Bourgain row or unrestricted Bourgain theorem.

`energyClauseNine_zeta_bound` derives the complete interval
`1 <= tau <= 8sigma-4`: actual emptiness below 3/2, the proved twelfth
moment with cubic energy on [3/2,2], and the actual clause-(i) zeta
Heath--Brown consumer above 2. `energyClauseNine` then invokes the proved
endpoint-one bounded-range transfer with the source cutoff tau0=8sigma-4.
No endpoint-two source corollary is assumed.

### Coverage, source fidelity and remaining goal

Nine new modules are installed: `EnergyClauseNineRates`,
`EnergyClauseNineShortCertificates`, `EnergyClauseNineMiddleCertificates`,
`EnergyClauseNineTallCertificates`, `EnergyClauseNineBranches`,
`EnergyClauseNineRegion`, `EnergyClauseNineGeneral`,
`EnergyClauseNineZeta` and `EnergyClauseNine`.
There are 42 new closed-range branch certificates, 71 explicitly audited
public theorems including the three new `NewAdditiveEnergy` exports, and
85 new semantic regressions (71 exact signatures and 14 endpoint/object
checks). Every module is root-imported and listed in the exact BAT inventory.

The literal rate and domain were checked against frozen TeX label
`Add-est`, clause (ix), and the paper-time ANTEDB
`prove_zero_density_energy_7()` recipe with tau0=8sigma-4. Numerical
exploration was used only for discovery. Lean checks every certificate
and every actual-region consumer. The repaired proof is not a claim to
replay the archived Python's false five-coordinate powering transformation.

EPZAE-36 and EPZAE-37 now meet their mathematical acceptance tests: all
nine clause projections feed actual general/zeta consumers, and every
printed interval has an audited source-facing theorem and actual-zero
epsilon--delta consequence. EPZAE-06 remains open for deterministic
projection-recipe reproduction, rather than missing energy mathematics.
EPZAE-19's unrestricted Bourgain source range and uniform LV assembly,
EPZAE-33's separate source endpoint-two corollary, the other exponent-pair,
density, public-assembly and release obligations, and the full EPZAE-00--41
goal remain open.

Both `run_tao_trudgian_yang_build.bat` and foundation `run_lake_build.bat`
remain required acceptance interfaces. Maintain their exact inventory and
explicit audits whenever modules change; no exclusion, dependency-pin
change, relaxed warning rule or fifth-coordinate shortcut is permitted.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-194712-b1ebacdc.log`.
  All 538 package files are covered, 549 Lean files scanned and 9393
  build jobs pass. The exhaustive audit passes all 4809 discovered target
  theorems plus five imported boundary declarations: 4814 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_194607.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  all 14290 discovered project theorems and the declaration-linter gate.

Every one of the 71 new explicit public audits was found in the final
target log and has only permitted standard logical dependencies
(`propext`, `Classical.choice`, `Quot.sound`, or subsets). All 85 new
semantic regressions pass. The complete final logs contain zero Lean
warnings, errors or tactic suggestions. The repository shortcut scans
have no prohibited proof-term match; broad declaration matches are
existing prose and the two genuine rational structure fields.

All 195 checkpoint source/integration/runner hashes match the snapshot
taken before the final target BAT run. The counterexample, both BAT
launchers, frozen sources and dependency pins are unchanged. Relative to
the preceding checkpoint, exactly five existing integration/status files
and the nine new Lean modules carry the implementation. All 186 dirty
worktree entries remain within node 63; unrelated work was not changed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 187 distinct nodes and 481 resolved edges.
The semantic green-node checks are:

- EC9C: the 42 explicit short/middle/tall branch inequalities, together
  with the rate/sign lemmas, are exact on their complete stated ranges.
  `energyClauseNine_short_branch`, the middle consumers and
  `energyClauseNine_tall_branch` apply them to the actual branch outputs.
- EC9G: `InCardinalityEnergyRegion.energyClauseNine_general` consumes
  genuine region membership, derives the power cover and cardinality caps,
  unpacks the corrected cardinality witness, and invokes the independent
  Heath--Brown energy witness. `energyClauseNine_general_bound` supplies
  the uniform epsilon-loss estimate by the proved region realization.
- EC9Z: `energyClauseNine_zeta_bound` consumes actual short-pattern
  emptiness, the proved twelfth moment and the actual zeta-region
  Heath--Brown consumer. No zeta-energy estimate is assumed.
- EC9/NAE: `energyClauseNine` consumes both full uniform ranges at
  tau0=8sigma-4. The three `add_est_ix` exports preserve the literal
  paper maximum, its full closed sigma interval, the real shifted zero
  multiset and analytic multiplicities. Alongside the already audited
  (i)--(viii) exports, this completes the nine-clause Add-est acceptance
  test, not the other public theorem families or the whole goal.

The mathematical completion of EPZAE-36/37 and the integrity-gate PASS
are separate conclusions; neither is inferred merely from audit counts.

## Closed beta duality from actual model-phase sums — historical checkpoint

### Exact mathematical result

`exponentPair_iff_beta_bound` proves frozen TeX label `beta-duality`
with its full closed range: for every candidate in the source triangle,
the actual analytic `ExponentPair k l` predicate is equivalent to
`beta(alpha) <= k + (l-k)*alpha` for every `0 <= alpha <= 1`.
This is not polygon membership or an assumed exponent-pair estimate.

The converse, `isExponentPairEstimateNonAsymptotic_of_beta_bound`,
takes a finite subcover of the compact alpha interval. Minimum phase
tolerance, maximum derivative order and maximum threshold supply one
uniform set of constants for every physical pair `1 <= N <= T`.
The proof links alpha to `log_T N` and proves the exact real-power
identity with the original epsilon losses.

For the forward endpoint, the actual approximate-model condition gives
`c_sigma <= -F'' <= sigma+1` on the interior, with
`c_sigma = sigma*2^(-sigma-1)/2 > 0`.
`betaModelSample_secondDifference_bounds` transports this curvature
to the physical samples `-2*pi*T*F((A+n)/N)`.
`norm_exponentialSumAt_le_secondDerivative` consumes that result,
the native Guth--Maynard finite second-difference estimate, the proved
complex-conjugation/radians bridge, and all three boundary terms. It yields

```text
||sum_{a <= n <= b} e(T F(n/N))||
  <= K_sigma (sqrt(T) + N/sqrt(T))
```

for `T,N >= 1`, `T <= N^2`, the original dyadic endpoints, and
the stated approximate-model tolerance. The estimate is not a premise.
The non-asymptotic ANTEDB interface then gives
`exponentSumGrowthExponent_one_le_half`.
Together with the existing forward theorem on alpha<1, this proves
`exponentSumGrowthExponent_le_exponentPairLine_closed`.
`exponentSumGrowthExponent_zero` also proves beta(0)=0.

### Semantic status and remaining obligations

EPZAE-09's convex closure and exact closed-interval two-way duality are
proved. EPZAE-09 remains OPEN: the source reflection identity
`beta(1-alpha)=1/2-alpha+beta(alpha)` and the lower endpoint bound
`1/2 <= beta(1)` are not claimed here. The finite second-derivative
estimate is not the source dual-phase B transformation, and does not
complete EPZAE-10's B-process, the A/C/D processes, the derivative inputs,
the beta table, or any of the four new exponent-pair outputs.

Seven modules are installed: `BetaUniformity`, `BetaSecondDerivative`,
`BetaDiscreteCurvature`, `BetaBProcessMajorant`, `BetaFiniteSum`,
`BetaModelSumBound` and `BetaClosedDuality`.
Their 21 public theorems have explicit dependency audits and exact-type
regressions; six additional checks cover the closed endpoints, the uniform
physical estimate and an actual closed-interval model sum at T=N.
All seven modules are root-imported and listed in the exact principal BAT
inventory.

The permanent singleton counterexample to printed Lemma 62 is unchanged.
The corrected independent rho/k and rho*/k witnesses, Heath--Brown
consumers, and all nine proved Add-est clauses remain intact.
No fifth-coordinate scaling or third witness has been restored.
EPZAE-36/37 remain DONE; the whole EPZAE-00--41 objective and its other
open acceptance tests remain unchanged.

`run_tao_trudgian_yang_build.bat` remains the target's principal
acceptance interface, alongside foundation `run_lake_build.bat`.
Maintain their exact module inventory, explicit audits, warning gate and
source-integrity checks as work continues. This checkpoint is concrete
progress toward the original whole-proof goal, not a replacement goal.

### Current-checkout verification and semantic audit

Both mandatory commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-202605-c2073498.log`.
  All 545 package files are covered, 556 Lean files scanned and 9400
  build jobs pass. The exhaustive audit passes 4840 discovered target
  theorems plus five imported boundary declarations: 4845 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_202606.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

All 21 new explicit public audits were found in the final target log;
each has only `propext`, `Classical.choice` and `Quot.sound`.
All 27 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 204 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. The 195-file preceding snapshot has
only the four expected integration/runner changes; coverage also adds
seven new Lean modules and the two existing module headers corrected
to describe the now-proved equivalences. The permanent counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, frozen archives and dependency pins are unchanged.
All 195 dirty worktree entries remain within node 63. No unrelated
user changes were reverted, staged, committed or pushed.
`git diff --check` passes; Git's CRLF-conversion notices are not Lean
diagnostics.

The architecture has 193 distinct nodes and 496 resolved edges.
Its new green-node checks are:

- DUC: `ExponentPair.convexCombination` is the previously proved
  analytic convex-closure theorem, not just triangle closure.
- DUU: `isExponentPairEstimateNonAsymptotic_of_beta_bound` consumes
  actual ANTEDB beta bounds at every alpha and derives uniform physical
  constants through a finite subcover; N and T are linked by log_T N.
- DUS: `norm_exponentialSumAt_le_secondDerivative` consumes the
  actual approximate-model phase, derived curvature, physical discrete
  differences, conjugation identity and three boundary terms.
- DUE: `exponentSumGrowthExponent_zero` proves beta(0)=0, and
  `exponentSumGrowthExponent_one_le_half` consumes the complete
  finite estimate through the genuine non-asymptotic beta definition.
- DUF: `exponentPair_iff_beta_bound` assembles both directions for
  the exact source triangle and every alpha in the closed unit interval.
  It does not assume an exponent-pair estimate in the converse or a
  beta reflection theorem in the endpoint proof.

DUR and aggregate EPZAE-09 remain open for the exact reflection identity
and beta(1)>=1/2. The named source `beta-duality` lemma is proved,
but this does not complete its broader Checklist item, the remaining
public-output families or the whole goal. Mathematical/source
completeness and dependency-integrity PASS are separate conclusions.

## Exact beta endpoints and classical second-derivative pair — historical checkpoint

### Exact mathematical results

`exponentSumGrowthExponent_endpoints` now proves the complete frozen
`beta-end` statement: beta(0)=0 and beta(1)=1/2.
`half_le_exponentSumGrowthExponent_one` supplies the missing lower bound
from the actual logarithmic model phase, without a mean-square estimate
as an assumption.

For every natural m, set N=T=16(m+1)^2 and use the closed integer interval
[N,N+m]. For each 0<=j<=m, the proved elementary logarithm inequalities give

```text
|N log((N+j)/N)-j| <= j^2/N <= 1/16.
```

Cosine periodicity removes the integer j in the real part of the original
oscillatory factor. The remaining angle has absolute value at most one,
so each term has real part at least 1/2.
`norm_logPhase_resonant_sum_lower` therefore proves, for this actual sum,

```text
||sum_{N <= n <= N+m} e(N log(n/N))|| >= sqrt(N)/8.
```

The scale is unbounded, both dyadic endpoints are derived, and N=T gives
the exact power-asymptotic exponent one. The audited ANTEDB logarithmic
lower-bound consumer yields beta(1)>=1/2. Together with the prior
second-derivative upper bound, this proves equality. This is an alternate
proof of the exact endpoint claim; it does not claim to formalize the
paper's separate L2 proof of beta(alpha)>=alpha/2 for every alpha.

`isExponentPairEstimateNonAsymptotic_half_half` also proves the genuine
uniform estimate for the classical pair (1/2,1/2).
For T<=N^2 it consumes the actual model-phase second-derivative estimate;
N<=T bounds N/sqrt(T) by sqrt(T). For T>N^2, the original finite sum is
bounded by 3sqrt(T) using its cardinality. The phase tolerance, derivative
order and constant depend only on the source parameters, and every
epsilon loss is retained.
`exponentPair_half_half` converts this to the original asymptotic
predicate. Closed duality then proves
`exponentSumGrowthExponent_le_half` and the combined bound
`exponentSumGrowthExponent_le_min_self_half` on 0<=alpha<=1.

### Coverage and remaining whole-proof obligations

Four new modules are installed: `BetaLogCoherence`, `BetaResonantSum`,
`BetaEndpoints` and `ClassicalSecondDerivativePair`.
Their 18 public theorems have explicit audits and exact-signature
regressions, plus six additional actual-sum, analytic-predicate and
endpoint checks. The root imports and the exact PowerShell inventory
behind `run_tao_trudgian_yang_build.bat` cover every module.

EPZAE-09 now has proved convex closure, full closed-interval two-way
duality, and both exact beta endpoints. Its sole remaining acceptance
obligation is the reflection identity on the whole unit interval.
The two endpoint reflection regressions do not establish the interior
identity. The classical seed is not the full B transformation; all
unproved A/B/C/D process, derivative, beta-table, advertised new-pair,
density, public-assembly and release obligations retain their status.
The whole EPZAE-00--41 goal remains active and unchanged.

The original Lemma 62 counterexample is preserved byte-for-byte.
Corrected independent rho/k and rho*/k powering, the Heath--Brown
consumers, and all nine Add-est clauses are unchanged; EPZAE-36/37
remain DONE. No scaled fifth coordinate or third witness is assumed.

Keep both `run_tao_trudgian_yang_build.bat` and foundation
`run_lake_build.bat` as mandatory acceptance gates. Continue updating
the exact module inventory, root imports, explicit audits and semantic
regressions whenever the proof graph changes; never bypass their
warning or proof-integrity checks.

### Current-checkout verification and semantic audit

Both required commands passed on 21 September 2026 at dirty HEAD
`e85f4145652f6f309da0554c3bc86ca5d4e8f9a4`, each with exit code 0:

- Target: `cmd /c run_tao_trudgian_yang_build.bat --no-pause`;
  log `logs/tao-trudgian-yang-build-20260921-204634-0b462a03.log`.
  All 549 package files are covered, 560 Lean files scanned and 9404
  build jobs pass. The exhaustive audit passes 4870 discovered target
  theorems plus five imported boundary declarations: 4875 in total.
- Foundation: `cmd /c run_lake_build.bat --no-pause`;
  log `Riemann Zeta/logs/foundation_freeze_20260921_204635.log`
  and its matching JSON manifest. All six stages pass: 301 root modules,
  two explicit regressions, 8857 build jobs, 7636 explicit declarations,
  14290 discovered project theorems and the declaration-linter gate.

Each of the 18 new explicit public audits was found in the final target
log with only `propext`, `Classical.choice` and `Quot.sound`.
All 24 new semantic regressions pass. The complete final logs contain
zero Lean warnings, errors or tactic suggestions. Repository-wide
shortcut scans contain no prohibited proof-term match; broad postulate
matches are existing prose and genuine rational structure fields.

All 208 checkpoint source/integration/runner hashes match the snapshot
taken before both final BAT runs. Relative to the preceding 204-file
checkpoint, only the four integration/runner files changed, and the four
new production modules extend the hash coverage. The counterexample
retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
Both BAT launchers, dependency pins, frozen sources and all existing
energy-proof modules are unchanged. All 199 dirty worktree entries
remain within node 63; no unrelated changes were reverted, staged,
committed or pushed. `git diff --check` passes; Git's CRLF-conversion
notices are not Lean diagnostics.

The architecture has 195 distinct nodes and 503 resolved edges.
Its changed green-node checks are:

- DUL: `norm_logPhase_resonant_sum_lower` derives the lower bound
  for the literal ANTEDB sum at the actual natural scale and endpoints.
  The logarithmic remainder, integer periodicity, real-part estimate,
  term count and square-root normalization are proved.
- DUE: `half_le_exponentSumGrowthExponent_one` supplies an unbounded
  logarithmic model family, proves its dyadic endpoints and N=T relation,
  and invokes the genuine beta lower-bound consumer.
  `exponentSumGrowthExponent_endpoints` combines it with the already
  proved zero endpoint and endpoint-one upper bound.
- CSP: `isExponentPairEstimateNonAsymptotic_half_half` derives one
  uniform model-phase estimate on the whole 1<=N<=T domain by the two
  complementary scale cases. `exponentPair_half_half` returns the
  actual analytic predicate, and the beta corollaries consume closed
  duality. No exponential-sum estimate is assumed as a terminal premise.

The existing closed-duality proof needs only the upper endpoint bound;
it does not rely on the new logarithmic lower-bound construction.
DUR and aggregate EPZAE-09 remain open solely for the full reflection
identity. The classical seed does not close EPZAE-10's general processes.
The other open Checklist items and the original whole-proof goal remain
open. These semantic conclusions are independent of the audit count.

## Actual inverse and Legendre phases — historical checkpoint

EPZAE-09 remains unchecked: convexity, closed duality and exact endpoints
are proved, but full reflection still needs DHC and DBT.
EPZAE-10 remains unchecked: the classical seed is proved, while the
general processes retain their original acceptance tests.

DSI, DLG, DIS and DSP are now green for actual inverse smoothness,
Legendre derivative/curvature calculus, first-order model stability and
physical stationary-point consumers, respectively. The exact theorem
names and unfolded semantic tests are in the latest Goal Prompt section.
DHC (all-order dual model control and canonical-domain normalization)
and DBT (actual sum transformation, amplitudes, endpoints and uniform
errors) are explicitly open nodes belonging to EPZAE-09/10.

No other checkbox was changed. In particular, EPZAE-36/37 remain DONE,
with the counterexample and authorized independent two-witness repair
preserved. The full EPZAE-00--41 objective is unchanged.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions. Target log:
`logs/tao-trudgian-yang-build-20260921-211419-4caca476.log`;
foundation log: `Riemann Zeta/logs/foundation_freeze_20260921_211419.log`.
The target covers 553 package files and audits 4929 declarations.
All 37 new public audits and 42 new regression examples pass.
Both BATs and the counterexample are unchanged. Exact hashes and
foundation stage evidence are in the latest Reproduction Manifest section.

## Uniform all-order Legendre model control — historical checkpoint

EPZAE-09 and EPZAE-10 remain unchecked under their unchanged acceptance
tests. The all-order compact phase-control component is now proved:
DHE covers the actual derivative recurrence, DHR the exact reference
model, DHU simultaneous derivative errors and common slope-image
inclusion, and DHA the anchored phase-value estimate.

DHC remains open only for the canonical-domain extension/normalization
part of that phase-side branch. DBT still requires the actual sum
transformation, amplitudes, endpoints and uniform error. Full reflection
and the general source processes remain open.

The exact consumer is
`modelPhaseLegendreDual_compact_anchored_uniformity`; the latest Goal
Prompt gives its quantifiers and green-node tests. No other checkbox
changed. EPZAE-36/37, all nine Add-est clauses and the authorized repair
remain DONE, and the permanent counterexample is unchanged.
The full EPZAE-00--41 objective remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-215130-00a61f53.log)
and [final foundation log](../../logs/foundation_freeze_20260921_215409.log).
The target covers 561 package files and audits 5026 declarations.
All 44 new public audits and 52 new regression examples pass.
All 220 checkpoint source/integration/runner hashes are stable across
both final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Canonical Legendre extension and finite model families — historical checkpoint

DHC is now DONE for canonical extension of retained compact slope
windows onto the full closed [1,2] source interval. DCF proves smooth
cutoff correction estimates; DCC proves fixed finite coverage with one
tolerance; DMF consumes actual ANTEDB model families on all charts.
The latest Goal Prompt records the exact public consumers and green-node tests.

EPZAE-09 and EPZAE-10 remain unchecked. DBT's actual transformed sum,
amplitudes, physical normalization, boundary bands and uniform errors
remain open, hence so do full reflection and the general B process.
A fixed compact cover is not a proof of untrimmed moving-boundary control.
No other checkbox changed. EPZAE-36/37, the permanent counterexample and
all nine corrected Add-est clauses retain their verified status.
The whole EPZAE-00--41 objective remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-222922-4233a5f3.log)
and [final foundation log](../../logs/foundation_freeze_20260921_222922.log).
The target covers 569 package files and audits 5058 declarations.
All 27 new public audits and 35 new regression examples pass.
All 228 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Exact Poisson source entry and physical dual sums — historical checkpoint

DXS, DXW, DXF, DXE and DXT are DONE only for the exact physical-scale,
weighted-Poisson, Fourier normalization/summability, original source-entry
and stationary-exponent sum consumers listed in the latest Goal Prompt.

EPZAE-09 and EPZAE-10 remain unchecked. DBT still requires uniform
general-model stationary integral estimates, amplitudes, lattice-margin
cutoff budgets, nonstationary tails and moving dual-boundary bands.
The source endpoint loss <=2 does not prove dual-boundary control.
No aggregate checkbox changed. The printed-Lemma-62 counterexample,
corrected two-witness powering and all nine Add-est clauses retain their
verified status; EPZAE-36/37 stay DONE. The whole goal remains active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 21 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260921-231301-8d992207.log)
and [final foundation log](../../logs/foundation_freeze_20260921_231301.log).
The target covers 575 package files and audits 5124 declarations.
All 32 new public audits and 40 new regression examples pass.
All 234 checkpoint source/integration/runner hashes are stable across
the final runs. The counterexample and both BAT launchers are unchanged.
Exact hashes and foundation stage evidence are in the latest
Reproduction Manifest section. The full goal remains active.

## Stationary amplitudes, source beta consumers and quadratic coordinates — historical checkpoint

DCA, DMA, DVA, DSB, DQD and DQJ are DONE for the exact amplitude,
monotonicity, sampled-variation/main-block, constructed-chart beta,
quadratic-normal-form and critical-derivative consumers listed in
the latest Goal Prompt. These are supporting EPZAE-09/10 results.

EPZAE-09 and EPZAE-10 remain unchecked. New node DQI owns the uniform
smooth inverse and transformed-weight estimates; DBT still owns the
complete uniform integral approximation, cutoff budgets, nonstationary
tails and moving dual-boundary bands. The physical alpha reflection
and full beta identity remain open under DUR. The reciprocal of the
coordinate derivative is not an inverse-function construction, and a
main-term estimate is not an integral error estimate.

No aggregate checkbox changed. The preserved printed-Lemma-62
counterexample, independent cardinality/energy witnesses and all nine
Add-est clauses retain their verified status. EPZAE-36/37 remain DONE.
The complete original goal, including both mandatory BAT gates, stays
active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-000055-22681e8e.log)
and [final foundation log](../../logs/foundation_freeze_20260922_000107.log).
The target covers 583 package files and audits 5203 declarations.
All 46 new public audits and 54 new regression examples pass.
All 242 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Smooth quadratic inverse and original-mode remainder — historical checkpoint

DTA, DQS, DMI, DJB, DQV, DMW, DQP and DQR are DONE for the exact
Taylor-average, smooth-coordinate, actual-inverse, first-derivative,
change-of-variables, transformed-cutoff, source-mode and remainder
normalization consumers listed in the latest Goal Prompt.

EPZAE-09 and EPZAE-10 remain unchecked under their original acceptance
tests. DQI now owns uniform HIGHER inverse/weight derivative bounds and
smooth zero-extension, not the already constructed pointwise smooth
inverse. DBT still owns the uniform stationary remainder, cutoff budgets,
nonstationary tails and moving dual-boundary bands. DUR remains open
for physical power-window/epsilon transport and full beta reflection.
The new remainder identity is not a bound, and chi(g(v)) remains in
the physical main term.

No aggregate checkbox changed. The original counterexample and
independent two-witness repair remain preserved; all nine Add-est
clauses and EPZAE-36/37 retain their verified status. Both mandatory
BAT gates and the complete original objective stay active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-010958-9aae1d59.log)
and [final foundation log](../../logs/foundation_freeze_20260922_010947.log).
The target covers 594 package files and audits 5272 declarations.
All 54 new public audits and 63 new regression examples pass.
All 253 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains active.

## Uniform smooth weights and stationary remainder bounds — historical checkpoint

DZW, DJC, DJI and DJW prove actual smooth zero-extension, uniform
all-order coordinate/inverse derivatives and global weight bounds with
explicit original-cutoff jet budgets. DQI is DONE for that fixed-cutoff
analytic branch. DRE proves a genuine C/T quadratic remainder; DSE
consumes it in the actual source Poisson series as a C*N/T stationary-mode
error. Exact theorem names and quantifier checks are in the latest Goal Prompt.

EPZAE-09 and EPZAE-10 remain unchecked under their unchanged acceptance
tests. DBT still owns uniform VARYING lattice-cutoff budgets,
nonstationary modes/tails, cutoff-weighted main-block assembly and moving
dual-boundary bands. DUR still owns physical power-window/epsilon
transport and full beta reflection. A fixed-cutoff estimate is not
uniform in the lattice parameters that may determine that cutoff.

No aggregate checkbox changed. The permanent counterexample, independent
rho/k and rho*/k witnesses and all nine Add-est clauses retain their
verified status; EPZAE-36/37 stay DONE. The whole goal and both BAT gates
remain mandatory and active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-021704-cf554732.log)
and [final foundation log](../../logs/foundation_freeze_20260922_021704.log).
The target covers 610 package files and audits 5402 declarations.
All 75 new public audits and 85 new regression examples pass.
All 269 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Controlled cutoff families and weighted Fourier bounds — historical checkpoint

Installed sub-obligations, each with a production consumer:

- DCB: controlled original cutoff, sharp finite-order jets and actual
  source-to-Poisson loss <=4*N*eta+2.
- DWB: actual global transformed-weight order-n bound C*eta^(-n).
- DSW: genuine varying-cutoff stationary mode error C*N/(T*eta^3),
  with its constant chosen before N,a,b,eta.
- DWM: actual original-cutoff-weighted main block, bounded using the
  physically linked unweighted source beta predicate.
- DNS: original-model nonstationary estimate, both slope signs,
  with cutoff C1 bound derived independently of width.
- DFG: original derivative envelope discharges the gap condition;
  the resulting physical mode bound is 4/(pi*d).

These are proved estimates, not supplied hypotheses matching their
conclusions. Exact green-node tests are recorded in the Goal Prompt.
No aggregate checkbox changed. EPZAE-09/10 remain OPEN: DBT owns
summed-error balance, quantitative far tails and moving boundary bands;
DUR owns physical power-window/epsilon transport and full reflection.
Absolute summability and a pointwise inverse-gap estimate do not
discharge those quantitative tasks.

EPZAE-36/37 stay DONE. The permanent counterexample, independent
rho/k and rho*/k witnesses and all nine Add-est clauses are preserved.
The full objective and both mandatory BAT gates remain active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-085137-4fb8b007.log)
and [final foundation log](../../logs/foundation_freeze_20260922_085138.log).
The target covers 625 package files and audits 5516 declarations.
All 50 new explicit public audits and 66 new regression examples pass.
All 284 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Quantitative Fourier tails and the actual core expansion — historical checkpoint

Six new DONE subnodes record exact consumers, not aggregate completion:

- DKE: actual normalized kernel's uniform order-two derivative budget.
- DFT: actual two-sided infinite tail with explicit inverse-radius decay.
- DNL: actual exterior integer blocks with width-independent harmonic/log cost.
- DCR: original source-to-core reduction with a derived sufficient radius.
- DCS: actual stationary subset, physical count and summed stationary error.
- DCX: original source expansion with the unestimated core residue retained.

The latest Goal Prompt records the six green-node semantic checks.
DBT still owns inner-core nonstationary/moving-band estimates, canonical
chart assembly and sufficiently strong stationary/source error balance.
DUR still owns physical power-window/epsilon transport and full reflection.
An expansion containing a literal residual sum is not an estimate for it.

No aggregate checkbox changed. EPZAE-09/10 remain OPEN; EPZAE-36/37
and all nine repaired Add-est clauses retain their verified status.
The full EPZAE-00--41 objective and both mandatory BAT gates stay active.

### Verification

Both mandatory BAT runners passed with exit code 0 on 22 September 2026,
with zero Lean warnings, errors or tactic suggestions:
[final target log](logs/tao-trudgian-yang-build-20260922-094603-f91c6946.log)
and [final foundation log](../../logs/foundation_freeze_20260922_094604.log).
The target covers 635 package files and audits 5587 declarations.
All 29 new explicit public audits and 41 new regression examples pass.
All 294 checkpoint source/integration/runner hashes match the
verification snapshot. The counterexample and both BAT launchers
are unchanged. Exact hashes and foundation stage evidence are in
the latest Reproduction Manifest section. The full goal remains unfinished.

## Width-independent curvature and the bounded inner core — historical checkpoint

Six exact supporting consumers are now green inside the still-open
EPZAE-09/10 aggregate contract:

- DCI: `norm_fourierCharIntegral_le_of_negative_curvature` derives
  the actual integral bound by selecting the two slope thresholds with
  the intermediate value theorem, bounding their separation by the
  negative curvature, and applying the first-derivative theorem on both
  exterior intervals. `IntervalC1Bound.fourierChar_of_negative_curvature`
  consumes that bound on every prefix in integration by parts.
- DMU: `modelPhaseBufferedFourierMode_uniform_curvature` consumes the
  ORIGINAL order-one model phase, its derived negative curvature, and
  the original cutoff's proved variation bound. Its positive constant
  precedes every endpoint, width, qualifying phase and physical scale.
  The normalized-to-physical N factor is retained; all real frequencies
  are covered, with no stationarity, slope-gap or eta<=1 hypothesis.
- DCE: `modelPhaseSlopeRange_eq_endpoint_Ioo` proves the original open
  derivative image is exactly the interval between the genuine one-sided
  endpoint slopes. The endpoint derivative is taken WITHIN [1,2], with
  an eventual equality to the ordinary derivative at every interior point.
  Continuity, quantitative decrease and the endpoint model error are
  derived from the original model; exterior smoothness is not assumed.
- DNP: `modelPhaseCoreStationarySet_eq_endpoint_Ioo` identifies the
  ACTUAL filtered core with the literal open integer interval (L,U).
  `modelPhaseCore_nonstationary_sum` partitions its actual complement
  into [A,L] and [U,B]. Core containment, strict L<U, integer rounding,
  inclusion of endpoint frequencies and disjointness are all proved.
- DNE: `modelPhaseBufferedCoreNonstationary_uniform` consumes DNP,
  uses DMU for L and U, and applies genuine endpoint-slope reciprocal
  bounds to every remaining integer. Exact reverse/forward enumeration
  and harmonic sums give the logarithmic term. Both block lengths are
  bounded by the original core count. No residual nonstationary mode or
  positive endpoint gap remains as an assumed input.
- DSX: `modelPhase_buffered_source_stationary_expansion` starts with
  the original closed natural-endpoint source sum, consumes the previous
  actual core expansion and DNE, and rewrites the actual stationary set
  using DNP. Its sole main expression is the literal cutoff-weighted
  stationary sum over (L,U); the original curvature amplitude and
  negative-curvature Fourier factor are unchanged. Every error below
  is paid, not silently omitted. This does not close the B process.

DBT/full beta reflection remain OPEN. The original source loss
4*N*eta+2 and stationary loss D*eta^(-3)*(1+N/T) still need a sharp
physical-scale balance. Actual stationary-frequency assembly through
the canonical dual charts, moving/reference endpoint conventions,
and alpha-to-1-alpha epsilon/power-window transport remain required.
No aggregate EPZAE checkbox or source theorem is marked complete here.

All 42 original aggregate checkbox entries are preserved. The new
supporting results add nine integrated production modules, 32 explicit
public audits and 42 regression examples; those counts are integrity
coverage, not proof that the full source B process is complete.

The permanent printed-Lemma-62 counterexample, independent rho/k and
rho*/k witnesses with unrelated fifth coordinates, Heath--Brown energy
relation, exact optimization and all nine Add-est clauses are unchanged.
No false s'/s scaling or third witness is restored. The full
EPZAE-00--41 objective remains active and unfinished.

### Verified build evidence

On 22 September 2026, after the final Lean and integration edits:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: PASS, exit 0;
  [complete target log](logs/tao-trudgian-yang-build-20260922-103135-cc078125.log). Coverage is 655 scanned Lean files,
  644 production package files and 9499 build jobs. The audit checks
  5649 discovered target theorems plus five imported declarations, 5654 total.
- `cmd /c run_lake_build.bat --no-pause` from the foundation root:
  PASS, exit 0; [complete foundation log](../../logs/foundation_freeze_20260922_103132.log) and
  [machine-readable manifest](../../logs/foundation_freeze_20260922_103132.json). All six stages pass;
  301 root modules plus two regressions, 8857 jobs, 7636 explicit
  declarations and 14290 discovered theorems retain their verified status.

Both complete physical logs contain zero Lean warnings, errors or tactic
suggestions. All 32 new explicit audits occur once, with permitted logical
axioms only. The final 9499-job focused regression build is warning-free;
all 42 new examples pass. The target also verifies all 20 pinned source
files, 12 frozen ANTEDB files and deterministic certificate regeneration.
No coverage, integrity, dependency, warning or output gate was weakened.
Runner PASS verifies the installed scope, not full beta reflection or
the unfinished whole-proof goal.

## Sharp stationary source expansion and interior logarithmic sums — previous checkpoint

The ORIGINAL source now has a sharp interior C_sigma*N/(T*d) error,
a logarithmic sum over the actual plateau integers, a proved transition
count, and support-exterior harmonic bounds. The assembled source theorem
chooses eta=T^(-1/2), giving nonlogarithmic error
(4+6*E)*N/sqrt(T)+3+2*E*(sigma+1), with every remaining logarithm and
the polynomial far-tail radius explicit. The actual short-interval source
branch is also proved. No eta^(-3) stationary loss is needed in this route.

Public consumers:
`modelPhaseBufferedFourierMode_interior_uniform`,
`modelPhaseBufferedInteriorBlock_error`,
`modelPhaseBufferedTransition_error`,
`modelPhaseBufferedSharpCore_error`,
`modelPhase_buffered_source_inverse_sqrt_expansion`, and
`norm_exponentialSumAt_le_buffered_short`.

Uniform logarithmic budgets, the actual moving canonical dual-chart
assembly, alpha-to-1-alpha power-window transport, full beta reflection,
and the general B process remain OPEN under EPZAE-09/10. No aggregate
checkbox changes. The full EPZAE-00--41 objective remains unfinished.
See the latest Goal Prompt for exact hypotheses, constants, formulas
and the six green-node semantic checks.

All 12 new modules enter the default imports and exact runner inventory;
44 public axioms audits and 49 regressions accompany them.
The counterexample and corrected powering/Heath--Brown/optimization/
nine-clause Add-est chain are preserved. Both build BATs remain mandatory.

### Verification

Both mandatory BAT runners passed on 22 September 2026 with exit code 0,
zero Lean warnings/errors/tactic suggestions, and passing integrity and
dependency gates. The target covers 656 production-package files,
scans 667 Lean files, and audits 5778 imported/target declarations.
All 44 new explicit audits and 49 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-113320-9230abb9.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_113331.log).
All 315 checkpoint source/integration/runner hashes agree before and
after the BATs. The graph has 258 nodes and 713 resolved, nonduplicate
edges; all 42 aggregate checklist checkboxes are unchanged.
The full goal remains unfinished.

## Uniform source power error and full moving-slope geometry — previous checkpoint

The original source now satisfies the uniform comparison
C_sigma,epsilon*(N/sqrt(T)+T^epsilon), with constants chosen before all
physical data. The actual retained plateau integers are used in the long
branch; the genuine source cardinality pays for the entire short branch.
Every retained frequency has a derived actual critical point and an
explicit positive endpoint margin.

The full actual slope image, under delta<=min(2^(-sigma)/2,1), lies in
[2^(-sigma)/2,2]. Inverse-point stability and every original derivative
comparison at the explicit reciprocal reference point now hold there,
including outside the strict reference interval. This does not assume
smoothness of the original phase outside [1,2].

Public consumers: `modelPhase_source_sharp_comparison`,
`modelPhaseSharpStationarySet_critical_geometry`, and
`modelPhaseInverse_iteratedDeriv_expanded_reference_error`.
See the latest Goal Prompt for exact signatures, bounds and green-node
checks. Higher inverse/Legendre errors on the expanded window, exact
moving canonical charts, physical power-window transport, full beta
reflection and the general B process remain OPEN under EPZAE-09/10.
All 42 aggregate checkboxes are unchanged.

Six new modules, 23 public audits and 27 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/nine-clause Add-est chain are unchanged.
Both build BATs remain mandatory and must track production coverage.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 662 package files, scans 673
Lean files and audits 5817 discovered target theorems plus 5 imported
anchors (5822 declarations). All 23 new explicit audits occur once and
use only permitted standard logical axioms; all 27 regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-120938-14509d95.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_120949.log).
All 321 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 262 nodes and 722 resolved,
nonduplicate edges; all 42 aggregate checkboxes are unchanged.
The counterexample and repaired energy chain remain unchanged.

## Moving canonical Taylor extensions and retained-frequency coverage — previous checkpoint

The actual Legendre error now has a globally smooth moving-endpoint
Taylor extension, exact on its retained plateau, with uniform finite
derivative bounds independent of the shrinking buffer width. Full-image
inverse/reference jet estimates and a five-region proof supply the bounds;
no exterior regularity of the original phase is assumed.

`modelPhase_source_canonicalTaylorPhase` chooses its model tolerance
before the source data, derives h=min(c_sigma,1)/(4*sqrt(T)) and the anchor
F'(3/2), proves the full closed-[1,2] canonical model condition, and proves
exact phase identities for EVERY retained stationary integer.
It does not assert that all integers belong to one multiplicative chart.

The finite positive-slope chart partition, whole stationary main-sum beta
bound, physical power-window transport, beta reflection and general
B process remain OPEN under EPZAE-09/10. All 42 aggregate checkboxes are
unchanged. See the latest Goal Prompt for the exact formulas, finite input
orders, constant dependencies and four green-node semantic checks.

Eighteen modules, 53 public audits and 60 regressions are integrated.
The permanent counterexample and corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain are preserved.
Both build BATs remain mandatory and must track production coverage.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 680 package files, scans 691
Lean files and audits 5904 discovered target theorems plus 5 imported
anchors (5909 declarations). All 53 new explicit audits occur once and
use only permitted standard logical axioms; all 60 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-130811-0ad529b7.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_130808.log).
All 339 checkpoint source/integration/runner hashes match before and after
the BATs. Eighteen source texts and four integration texts also match
their normalized snapshots. The graph has 266 nodes and 732 edges, with
no duplicate nodes or unresolved endpoints; all 42 aggregate checkboxes
are unchanged. The counterexample and repaired energy chain remain unchanged.

## Full source chart assembly and the analytic B-process — previous checkpoint

The exact finite positive-slope grid now partitions EVERY original
retained stationary integer into contiguous natural-number chart blocks.
The moving Taylor phases, actual amplitude variation and upstream beta
bounds are assembled, with physical dual windows derived from N,T.
`sourceExponentialSum_reflection_estimate` proves the complete original
sum bound, including C*(N/sqrt(T)+T^epsilon) source error.

The resulting nonasymptotic reflection bound has exponent
max(0,beta+1/2-alpha). Its max is removed only when the reflected exponent
is proved nonnegative. The full beta-reflection identity remains OPEN.

`ExponentPair.bProcess` now proves the paper's analytic transformation
(k,l)->(l-1/2,k+1/2); its target affine line is nonnegative by the triangle
conditions. It does not assume the still-open exact reflection identity.
The next reflection obligation is a genuine beta lower bound sufficient
to remove the zero envelope. A and C processes remain open, so EPZAE-10
is not crossed out. All 42 aggregate checkbox states are unchanged.

Eleven modules, 35 public audits and 41 regressions are integrated.
The printed counterexample, corrected independent powering witnesses,
Heath--Brown energy relation, exact optimization and all nine repaired
Add-est clauses are unchanged. BOTH build BATs remain mandatory and
their imports, inventory and audits must track production changes.
See the current Goal Prompt for quantifiers and all five green-node tests.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 691 package files, scans 702
Lean files and audits 5960 discovered target theorems plus 5 imported
anchors (5965 declarations). All 35 new explicit audits occur once and
use only permitted standard logical axioms; all 41 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-135040-f8df686c.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_135036.log).
All 350 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match
their normalized snapshots. The graph has 270 nodes and 740 edges, with
no duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain remain unchanged. These checks verify this recorded scope;
they do not assert whole-goal completion.

## Exact beta reflection from coherent source sums — previous checkpoint

`exponentSumGrowthExponent_reflection` now proves the exact printed
identity beta(1-alpha)=1/2-alpha+beta(alpha) for every 0<=alpha<=1,
including endpoints. Convex closure, closed two-way duality and the
endpoint values were already proved; all EPZAE-09 mathematical
acceptance clauses are now supplied.

The new lower-bound proof is independent of reflection and the B-process.
It constructs actual phases log(u)+c*(u-1) with integral linear
oscillation at integer N, controls every finite model jet, and sums
a genuine closed coherent block. Beyond every threshold it produces
T^alpha=N and norm(original sum)>=T^(alpha-1/2)/8, proving
beta(alpha)>=alpha-1/2. This removes the zero envelope from the
previous complete original-source estimate; the two reflected
inequalities then give equality. No stronger alpha/2 bound is claimed.

Six modules, 18 public audits and 24 regressions are integrated.
EPZAE-10 remains OPEN: its general B-process is proved, A and C are not.
Continue with those analytic processes and the remaining whole-proof
obligations; this checkpoint does not complete the full goal.

The printed counterexample, corrected independent powering witnesses,
Heath--Brown relation, exact energy optimization and all nine repaired
Add-est clauses remain unchanged. BOTH build BATs remain mandatory,
and production imports, inventory and audits must track source changes.
See the current Goal Prompt for quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 697 package files, scans 708
Lean files and audits 5990 discovered target theorems plus 5 imported
anchors (5995 declarations). All 18 new explicit audits occur once and
use only permitted standard logical axioms; all 24 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-141433-3e901ee8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_141443.log).
All 356 checkpoint source/integration/runner hashes match before and after
the BATs. Six source texts and four integration texts also match their
normalized snapshots. The graph has 274 nodes and 748 edges, with no
duplicate nodes or edges and no unresolved endpoints. There are still
42 aggregate checkboxes: only EPZAE-09 changes to complete; all others
retain their status. The counterexample and completed repaired energy
chain are unchanged. These checks verify this recorded scope, not
whole-goal completion.

## Domain-preserving A-process models and source differencing — previous checkpoint

The A-process now has a domain-preserving shifted-model constructor,
exact original-source correlation identities, and a summed-correlation
Weyl inequality on the literal source exponential sum.

The constructed phase uses affine compression inside [1,2] and has
model parameter sigma+1, with every requested finite derivative and
both endpoints controlled by one tolerance chosen before the source.
Its physical parameters are exactly N'=N-r and T'=sigma*T*r/N;
the reindexed integers and conjugation are proved, including empty
overlaps. The analytic exponent-pair consumer derives its model and
endpoint conditions but explicitly retains C<=T' and N'<=T'.

`source_exponentialSum_weyl` constructs the actual padded source
sequence and keeps 2*H times the SUM of nonzero correlations. It has
no assumed analytic estimate. The small-dual-parameter branch and
integer shift optimization remain OPEN; A is not yet proved.
EPZAE-09 and the B-process remain complete. C remains open.
All 42 aggregate checkbox states are unchanged.

Eleven modules, 32 public audits and 39 regressions are integrated.
The printed counterexample and the corrected powering/Heath--Brown/
optimization/all-nine-Add-est chain remain unchanged. BOTH build BATs
remain mandatory and must track production imports, inventory and audits.
See the current Goal Prompt for exact quantifiers and semantic checks.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 708 package files, scans 719
Lean files and audits 6069 discovered target theorems plus 5 imported
anchors (6074 declarations). All 32 new explicit audits occur once and
use only permitted standard logical axioms; all 39 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-150004-71e72f6e.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_150014.log).
All 367 checkpoint source/integration/runner hashes match before and after
the BATs. Eleven source texts and four integration texts also match their
normalized snapshots. The graph has 280 nodes and 760 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. The counterexample and completed repaired
energy chain are unchanged. These checks verify this recorded scope,
not the still-open A-process or whole-goal completion.

## General analytic A-process from original source sums — previous checkpoint

The classical A-process is now proved for the paper's actual analytic
exponent-pair predicate:

    ExponentPair k l
      ==> ExponentPair (k/(2*k+2)) (l/(2*k+2)+1/2).

The public consumer is `ExponentPair.aProcess`. Its proof derives the
closed shifted model, source reindexing and conjugation, all positive
dual-height estimates, summed correlations, the original-source Weyl
bound, a genuine natural-number shift and the full epsilon budget.
It does not assume a transformed-phase estimate, a dual-height window,
an optimization certificate, or the output exponent-pair estimate.

The formerly open small-height branch is proved by the full closed-source
`norm_exponentialSumAt_le_firstDerivative`; curvature handles transition
heights, and `ExponentPair.allPositiveHeight_bound` combines every positive
height with the actual input pair. `sourceShiftCorrelation_normalized_bound`
links the result back to N,T,r, including the N^2/(T*r) term.
`sum_sourceShiftCorrelation_le` retains its harmonic sum.
`source_exponentialSum_differencing_bound` consumes the literal source sum.

`integer_shift_optimization` uses an actual floor-comparable natural H;
when that scale is too small, the original sum's cardinality supplies
the separate branch. `aProcessOptimizationScale_balance` and
`aProcessOptimizationScale_cost` link the optimum exactly to N,T.
The logarithmic loss is absorbed by `aProcess_power_budget`.
`source_exponentialSum_aProcess_bound` and
`isExponentPairEstimateNonAsymptotic_aProcess` assemble every source
interval, empty interval and bounded-N case with constants chosen first.

Fifteen production modules, 33 explicit public-theorem audits and 40
regressions are integrated. The extra fixtures include actual A/A/B
compositions yielding (1/6,2/3), (1/14,11/14), and (2/7,4/7), the H=0/H=1
harmonic endpoints, and two optimization-scale checks.

EPZAE-09 and both A/B processes are complete; C remains OPEN, so EPZAE-10
remains unchecked. D, Heath--Brown derivative inputs, certified beta
tables, the four advertised pairs and the remaining density/public
release obligations remain in the whole-proof goal. All 42 aggregate
checkbox states are unchanged.

The printed counterexample, corrected independent rho/k and rho*/k
witnesses, unrestricted fifth coordinates, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
preserved. BOTH build BATs remain mandatory; keep their production
imports, PowerShell inventory, audits and regression coverage synchronized.

### Verification

Both mandatory BATs passed on 22 September 2026, exit code 0, with zero
Lean warnings, errors, tactic suggestions or linter failures in their
complete physical logs. The target covers 723 package files, scans 734
Lean files and audits 6118 discovered target theorems plus 5 imported
anchors (6123 declarations). All 33 new explicit audits occur once and
use only permitted standard logical axioms; all 40 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-155044-98a95e32.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_155054.log).
All 382 checkpoint source/integration/runner hashes match before and after
the BATs. Fifteen source texts and four integration texts also match their
normalized snapshots. The graph has 281 nodes and 762 edges, with no
duplicate nodes or edges and no unresolved endpoints. All 42 aggregate
checkbox states are unchanged. This verifies the exact analytic A-process,
not C or whole-goal completion. The counterexample and the completed
repaired energy chain remain unchanged.

## Native Heath–Brown derivative input and exact source beta bound — previous checkpoint

The source `heath-brown-2017` conclusion is proved by
`exponentSumGrowthExponent_le_heathBrown` for every natural k >= 3
and every real alpha > 0, with the exact displayed three-branch formula.
Its public signature has no derivative theorem or beta bound parameter.
The native input is `GafniTao.heathBrownKthDerivativeTheorem_native`.

The nine-module bridge derives signed model-jet bounds, the physical
scale lambda = c*T/N^k, smoothness on the actual closed interval, exact
translation and conjugation of the tail sum, and restoration of the
first endpoint. It includes singleton and empty intervals. Constants,
model accuracy and derivative order precede all actual phases, heights,
scales and source endpoints. The source window and epsilon budget give
the non-asymptotic beta predicate, then the exact ANTEDB growth exponent.

The pinned dependency contains 460 unchanged mathematical source modules
with documented import-path adaptations and two proved PNT prefixes.
It inherits the canonical foundation and its existing pins, without a
second or shadow foundation. Its ledger verifies 469 files and its root
reaches all 463 Lean modules. The audit also checks every nonprivate
theorem defined in those pinned modules, including the global PNT names.
The first compatibility build that exposed unrelated admitted Wiener
preliminaries is not accepted evidence; the proved prefixes avoid that
monolithic import without editing the canonical external checkout.

All ten new production modules, 42 named public audits, four explicit native/PNT
boundary audits and 51 semantic regressions are integrated. The fixtures
include the actual beta bounds beta(1/2) <= 5/12 and beta(1/3) <= 11/36,
plus exact formula, source-table endpoints and closed-singleton checks.

`HeathBrownBetaTable` proves the first two source beta-table rows from
this analytic bound, including alpha zero and both joining endpoints.
The second affine segment is proved on the larger closed interval
[1/4,2/5], then restricted to the printed endpoint 890/3277. These are
proved analytic rows, not a claim that the full beta table is complete.

EPZAE-12 is complete. EPZAE-09 and A/B remain complete; C and D remain
open, so EPZAE-10 and EPZAE-11 stay unchecked. Certified beta-table
assembly, the four advertised exponent pairs, density and release
obligations remain in the unchanged whole-proof contract. Only the
EPZAE-12 checkbox changes among the 42 aggregate items.

The permanent printed Lemma 62 counterexample and completed corrected
cardinality/energy powering, Heath--Brown energy relation, exact energy
optimization and all nine Add-est clauses are unchanged. The two powering
witnesses still have independent, unrestricted fifth coordinates.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
source verifiers, root imports, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, import,
dependency, audit or runner changes. A passing build does not complete
the remaining whole-proof outputs.

Scoped `.gitattributes` rules preserve the exact bytes of pinned Sources,
ANTEDB/native dependency files, the generated certificate and the permanent
counterexample across Git checkouts. The runner requires this policy file.
No repository Git configuration was changed. A read-only comparison of
509 protected files against HEAD found 507 byte-identical; the only two
differences are the documented native README correction and its ledger.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), each
with exit code 0. Their complete physical logs contain no Lean warnings,
errors, tactic suggestions or linter failures. The target covers 733
package files and scans 1,207 Lean files; its default build checks 10,065
jobs. The audit checks 6,191 discovered target theorems, 6,240 pinned
source theorems and 5 imported anchors: 12,436 declarations in total.
All 42 new named public audits and all four native/PNT boundary audits
occur exactly once and use only permitted standard logical axioms.
All 51 new semantic regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-174454-55b1abae.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_174825.log).
The foundation's six stages pass with zero diagnostics: 301 root modules,
two retained regressions, 8,857 build jobs, 7,636 explicit public declarations
and 14,290 discovered theorem dependencies.

All 1,228 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Ten source modules and five integration/verifier files match
their normalized snapshots. The complete [source checkpoint record](logs/tao-trudgian-yang-heath-brown-20260922-174454-55b1abae.json)
records these hashes and the exact new public signatures. The synchronized
graph has 286 nodes and 772 edges, with no duplicate or unresolved links.
Only EPZAE-12 changes among the 42 aggregate checkbox states. The permanent
counterexample and completed repaired energy branch are unchanged.
This verifies the recorded scope, not whole-goal completion.

## Robert–Sargos fourth-power near-count — previous checkpoint

`card_sargosFourthNearSolutions_le_log` proves, for every natural N >= 1,

    card {q in (N,2N]^4 :
      |q0²+q1²-q2²-q3²| <= N,
      |q0⁴+q1⁴-q2⁴-q3⁴| <= N³}
      <= 4096 N² (1+log N).

The finite set contains actual integer quadruples. No counting bound,
moment estimate or exponent-pair conclusion is a theorem parameter.
The geometric calculation derives |q0*q1-q2*q3| <= 5N and a bounded
sum displacement, then injects the quadruples into four integer linear
coordinates. The two difference coordinates satisfy |u*v| <= 11N.
The signed hyperbola count is proved via an injective sign/absolute-value
encoding, actual natural-number fibers, division bounds and the harmonic
sum. Zero fibers and all signs are included.

Four production modules contain 17 public theorems. All have explicit
audits and exact-signature regressions; nine additional fixtures check
N=0/1/2 counts, zero fibers, both signs and coordinate encoding.
This proves the counting assertion in Robert–Sargos section 5
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)),
with an explicit constant and a stronger N >= 1 domain.
It does not yet prove the fourth-moment integral, the sixth-moment
bootstrap or the analytic C-process. Those remain under EPZAE-10.
D, remaining beta rows/pairs, density and public-release obligations
also remain open. All 42 aggregate checkbox states are unchanged.

The counterexample, independent corrected powering witnesses and
completed Heath--Brown energy/optimization/all-nine-Add-est chain
are unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic
beta-table rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Both it and the foundation `run_lake_build.bat` remain mandatory after
proof/integration/runner changes. Retain the scoped byte-preservation
rules for the pinned inputs, generated certificate and counterexample.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 737 package files, scans
1,211 Lean files and completes 10,069 default-build jobs. Its audit checks
6,232 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,477 declarations. The 17 new explicit public audits occur once
with only permitted standard logical axioms; all 26 new regressions pass.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-181839-3e1844f8.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_182203.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,232 recorded proof/configuration/tooling hashes are unchanged across
both BATs. Four source texts and four integration texts match normalized
snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-count-20260922-181839-3e1844f8.json)
contains the hashes, exact theorem signatures and both evaluation results.
The synchronized graph has 290 nodes and 779 edges, with no duplicates,
unresolved endpoints or unclassified nodes. All 42 aggregate checkbox
states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos rectangular windows and fixed-sum fourth moment — previous checkpoint

`sargosQuartic_fourth_moment` proves, for every natural N >= 1,
every fixed complex coefficient sequence with |z_n| <= 1 on (N,2N],
and every real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      |sum_{N<n<=2N} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|^4
      <= 131072 Delta/N (1+log N).

The sum, both physical windows and the four-variable count are literal.
No counting bound, moment estimate, kernel identity or exponent-pair
conclusion is assumed. The fixed coefficients may be arbitrary on the
source interval but do not depend on the integration parameters.

Fourteen new production modules prove whole-line sinc-square
integrability, its real-frequency tent Fourier transform, shifted-window
normalization, exact two-dimensional finite Gram integration, cutoff to
actual near pairs, and the source ordered-pair square. The rectangular
mean-square factor is exactly 16*delta*lambda. The source fourth moment
then consumes the proved 4096 N^2(1+log N) quadruple count, with
lambda=2/N^3. Both translated centers and non-integral frequencies are
included. No pinned native source was modified.

All 68 new public boundaries have explicit axiom audits and exact-signature
regressions. Fourteen additional fixtures cover tent/kernel normalization,
cutoff endpoints, a non-integral shifted frequency, N=1/2 source intervals
and sums, zero coefficients, and a concrete fourth-moment specialization.

This is the fixed-sum part of the Robert–Sargos section 4--5 analytic
transfer ([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
It does not yet prove the maximum over prefixes in source Lemma 2,
the slowly varying phase extension, the sixth-moment bootstrap, or the
analytic C-process. EPZAE-10 stays open. D, the remaining beta rows,
the four advertised pairs, density and release obligations remain open.
All 42 aggregate checkbox states are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy witnesses, Heath--Brown energy relation, exact energy
optimization and all nine repaired Add-est clauses are unchanged.
EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Retain the scoped byte-preservation rules
for pinned inputs, the generated certificate and the counterexample.

### Verification

Both mandatory BATs passed on 22 September 2026 (Pacific time), exit code 0,
with zero Lean warnings, errors, tactic suggestions or linter failures in
their complete physical logs. The target covers 751 package files, scans
1,225 Lean files and completes 10,083 default-build jobs. Its audit checks
6,330 discovered target theorems, 6,240 pinned source theorems and 5 imported
anchors: 12,575 declarations. All 68 new explicit public audits occur once
with permitted standard logical axioms only; all 82 new regressions pass.
The intermediate fixture warning and conversion error were fixed before
these accepted full runs; they are not acceptance evidence.

Target: [verified build log](logs/tao-trudgian-yang-build-20260922-191919-9f77a11b.log).
Foundation: [verified foundation log](../../logs/foundation_freeze_20260922_192240.log).
The foundation passes all six stages: 301 root modules plus two retained
regressions, 8,857 build jobs, 7,636 explicit public declarations and
14,290 discovered theorems.

All 1,246 recorded proof/configuration/tooling hashes are unchanged across
both serialized BATs. Fourteen source texts and four integration texts
match their normalized snapshots. The [source checkpoint record](logs/tao-trudgian-yang-sargos-moment-20260922-191919-9f77a11b.json)
contains the hashes, all exact new public signatures and both evaluation
results. The synchronized graph has 293 nodes and 784 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged. The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos maximal-prefix fourth moment — previous checkpoint

`sargosQuartic_maximal_fourth_moment` proves, for every natural N >= 1,
fixed coefficients |z_n| <= 1 on (N,2N], and real Delta >= 1/N,

    integral_{alpha=0}^{Delta} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} z_n exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^4
      <= 10616832 Delta/N (1+log N)^5.

H is an integer, every source prefix is present, and the maximum is
attained. The extra H=0 prefix is the proved zero sum. This bounds the
pointwise maximum before integration, not merely each fixed-prefix
integral. Empty and zero-coefficient cases are retained and tested;
the estimate itself requires N >= 1.

Thirteen production modules prove exact finite Fourier inversion on
ZMod N, the geometric kernel and unit-circle gap, and a prefix-independent
nonnegative coefficient majorant with total mass at most 3(1+log N).
Two finite Cauchy--Schwarz inequalities give the fourth-power bound.
A proved residue bijection identifies the literal integer interval.
Every completed mode is the original sum with unit-modulus coefficient
twists independent of alpha and gamma. Maximum continuity, rectangle
integrability and finite integral interchanges are proved. The final
estimate consumes the earlier fixed-sum theorem and its literal
four-variable count, without assuming any count or moment estimate.

All 61 new public boundaries have explicit audits and exact-signature
regressions. Fifteen further fixtures cover zero-frequency kernels,
N=1/2/3 majorant masses, residue endpoints, proper/full/empty prefixes,
zero coefficients and a concrete maximal-moment specialization.

This establishes the weighted maximal fourth-moment assertion of
Robert–Sargos section 5 for natural N, with an explicit constant and
1+log N normalization
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S5)).
The parameter-dependent slow-phase extension, higher-moment window
transfer, sixth-moment bootstrap and analytic C-process remain open.
EPZAE-10 stays unchecked. D, remaining beta rows/pairs, density and
release obligations remain open. All 42 aggregate checkbox states
are unchanged.

The permanent printed Lemma 62 counterexample, independent corrected
cardinality/energy powering witnesses, Heath--Brown energy relation,
exact energy optimization and all nine repaired Add-est clauses are
unchanged. EPZAE-09, A/B, EPZAE-12 and the first two analytic beta rows
are preserved.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, source verifiers, audits and regressions synchronized.
Run it and the foundation `run_lake_build.bat` after proof, integration,
dependency or runner changes. Keep byte-preservation rules for the
pinned inputs, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0 with no Lean errors, warnings, tactic
suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [complete target log](logs/tao-trudgian-yang-build-20260922-220844-6863d940.log);
  764 production modules, 1238 scanned Lean files, 10096 build jobs,
  6425 target plus 6240 pinned theorems and five imported boundaries
  audited (12670 total). Each of the 61 new public audits appears once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_221514.log)
  and [manifest](../../logs/foundation_freeze_20260922_221514.json);
  all six stages pass, 8857 build jobs, 301 root modules and two
  retained regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-maximal-20260922-220844-6863d940.json) records
1259 physical source/configuration/tooling hashes, unchanged across
both runs, plus 17 normalized module/integration hashes. The 469-file
native pin and its 463-module closure pass. No earlier proof file was
changed: only the root, audit, regressions and runner inventory were
extended. The synchronized graph has 295 nodes and 787 edges, with no
duplicates, unresolved endpoints or unclassified nodes. All 42 aggregate
checkbox states are unchanged (22 checked). The counterexample SHA-256
remains `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos parameter-dependent slow phase — previous checkpoint

The literal quartic prefixes now admit the actual phase
alpha*n^2+gamma*n^4+phi(alpha,gamma,n), with fixed source coefficients.
For N >= 1, K >= 0 and Delta >= 1/N, assume only the genuine local
derivative data on x in [N,2N] and on the integration rectangle:

    |d phi(alpha,gamma,x)/dx| <= K/N.

`sargosSlowQuarticMaximum_le` derives the pointwise bound by
(1+2*pi*K) times the unperturbed prefix maximum. The proof uses the
global character Lipschitz bound, exact integer-interval reindexing,
and finite Abel summation. Its adjacent variation is at most 2*pi*K;
no moment estimate or conclusion-equivalent variation bound is assumed.

`sargosSlowQuartic_upper_fourth_moment` then proves

    upper integral over [0,Delta] x [-N^-3,N^-3]
      (max_{0<=H<=N} |sum_{N<n<=N+H}
        z_n exp(2*pi*i*(alpha*n^2+gamma*n^4+phi(alpha,gamma,n)))|)^4
      <= (1+2*pi*K)^4 * 10616832 Delta/N (1+log N)^5.

There is no measurability hypothesis on the phase family here.
`sargosUpperIntegral` is the infimum of nonnegative integrals of
almost-everywhere measurable majorants. Its monotonicity and equality
with the ordinary nonnegative integral on measurable integrands are
proved. The result therefore does not exploit the default value of an
undefined Bochner integral.

For an almost-everywhere strongly measurable actual fourth-power
integrand, `integrable_sargosSlowQuarticFourth` proves integrability
from the existing majorant, and `sargosSlowQuartic_fourth_moment`
proves the ordinary iterated-integral estimate via Fubini. Continuity
of the actual maximum follows from continuity of each sampled phase.
The linear-phase consumers derive the derivative data for
phi(alpha,gamma,x)=u(alpha,gamma)*x/N; the upper-integral consumer
allows an arbitrary bounded, possibly nonmeasurable u.

Seven production modules contain 29 explicitly audited public theorems.
There are 29 exact-signature regressions and nine additional fixtures,
including a sin(alpha)-dependent phase, a bounded family without a
measurability assumption, Dirac upper integration, zero phase,
zero coefficients, the empty prefix and N=0 definitions.

This realizes the slow-phase removal used in Robert–Sargos section 4,
and composes it with the proved section 5 fourth moment
([author-uploaded paper](https://arxiv.org/html/2307.03554v1#S4)).
The printed variation sentence has an extra 1/N: a derivative of size
K/N over an interval of length N gives variation of size K. The proof
uses the correct explicit constant. The arbitrary higher-moment and
two-window comparison in Lemma 1, the sixth-moment argument and the
analytic C-process remain open. EPZAE-10 remains unchecked.

The permanent printed Lemma 62 counterexample and the completed
corrected powering -> Heath--Brown energy -> exact optimization ->
all nine repaired Add-est clauses are unchanged. A/B, EPZAE-09,
EPZAE-12 and the first two analytic beta rows are preserved.
All 42 aggregate checkbox states are unchanged.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell module inventory,
root imports, explicit audits, regressions and source verifiers
synchronized. Run it and the foundation `run_lake_build.bat` after
proof, integration, dependency or runner changes; preserve the pinned
bytes, generated certificates and permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-223544-52ff7f68.log); 771 production modules,
  1245 scanned Lean files, 10103 build jobs; 6474 target and 6240 pinned
  theorems plus five imported boundaries audited (12719 total).
  All 29 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_223848.log) and
  [manifest](../../logs/foundation_freeze_20260922_223848.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-slowphase-20260922-223544-52ff7f68.json) records
1266 physical source/configuration/tooling hashes, unchanged across
both runs, and 11 normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, every earlier proof file is unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 297 nodes and 790 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos small-alpha sixth moment — previous checkpoint

`sargosQuartic_small_sixth_moment` proves, for every natural N >= 1,

    integral_{alpha=0}^{1/sqrt(N)} integral_{gamma=-N^-3}^{N^-3}
      (max_{0<=H<=N}
        |sum_{N<n<=N+H} exp(2*pi*i*(alpha*n^2+gamma*n^4))|)^6
      <= 44845498368 (1+log N)^5.

This is the literal unweighted sum and its actual attained prefix
maximum, not a bound for arbitrary bounded coefficients. Every
integration and interval comparison has a proved integrability argument.
There is no sixth-moment, counting or cancellation hypothesis.

The quartic second difference is computed exactly. Its fourth-degree
coefficient is at most 110 N^2 on the actual sample range. With
|gamma| <= N^-3 and alpha >= 128/N, this gives positive curvature
between alpha and 3 alpha before conversion to radians.
The existing local discrete second-derivative theorem is applied to
the exact prefix and gives |S| <= 64 N sqrt(alpha), for alpha <= 1.
The conversion from the additive character to radians is proved.

A two-window split suffices. On [0,128/N], the trivial |S|^2 <= N^2
multiplies the proved maximal fourth moment. On [128/N,1/sqrt(N)],
the curvature bound gives |S|^2 <= 4096 N^2/sqrt(N), and the fourth
moment is bounded on the larger [0,1/sqrt(N)] window. The exact scale
identity N*(1/sqrt(N))^2=1 removes N. This yields log^5 directly,
without the extra logarithm from counting dyadic windows.

`sargosQuartic_small_sixth_moment_log_six` gives the (1+log N)^6
version. `sargosQuartic_small_sixth_moment_source` proves the literal
logarithm convention for N >= 2, with absolute constant

    44845498368 (1+1/log 2)^6

multiplying (log N)^6. Thus the exact source small-alpha assertion
is a proved consumer, including the logarithmic normalization bridge
([Robert–Sargos, section 5, Lemma 3](https://arxiv.org/html/2307.03554v1#S5)).
The cutoff 128/N is deliberately verified; the printed 16/N does not
uniformly guarantee positive quartic curvature. Changing this internal
cutoff changes only the absolute constant, not the public source result.

Six production modules contain 22 public theorem boundaries, each with
an explicit audit and exact-signature regression. Nine additional
fixtures test the sign issue, exact quartic difference, verified cutoff,
empty intervals, N=0 definitions, a literal full prefix, and the N=1/2
moment and source-normalization specializations.

The full higher-moment/window comparison, global sixth-moment bootstrap,
quartic B/Legendre transfer and analytic C-process remain open.
EPZAE-10 stays unchecked; this is the section 5 input, not the full
sixth-moment theorem or C-process. All 42 aggregate checkbox states
remain unchanged.

The maximal fourth moment and parameter-dependent slow-phase upper
and ordinary integral theorems are preserved. The permanent printed
Lemma 62 counterexample and completed corrected powering ->
Heath--Brown energy -> exact optimization -> all nine repaired Add-est
clauses remain unchanged, as do A/B, EPZAE-09, EPZAE-12 and the first
two analytic beta rows.

Keep `run_tao_trudgian_yang_build.bat`, its PowerShell inventory,
root imports, explicit audits, semantic regressions and source
verifiers synchronized. Run it and the foundation
`run_lake_build.bat` after proof, integration, dependency or runner
changes. Preserve pinned bytes and the permanent counterexample.

### Verification and preservation

Both required commands exited 0, with zero Lean errors, warnings,
tactic suggestions or linter failures:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`:
  [target log](logs/tao-trudgian-yang-build-20260922-230214-7730af3c.log); 777 production modules,
  1251 scanned Lean files, 10109 build jobs; 6516 target and 6240 pinned
  theorems plus five imported boundaries audited (12761 total).
  All 22 new explicit public audits occur exactly once.
- `cmd /c run_lake_build.bat --no-pause`:
  [foundation log](../../logs/foundation_freeze_20260922_230522.log) and
  [manifest](../../logs/foundation_freeze_20260922_230522.json); all six
  stages pass, 8857 build jobs, 301 root modules and two retained
  regressions, 7636 explicit and 14290 discovered declarations.

The [source checkpoint](logs/tao-trudgian-yang-sargos-sixth-20260922-230214-7730af3c.json) records
1272 physical source/configuration/tooling hashes, unchanged across
both runs, and ten normalized new-module/integration hashes. The 469-file
native pin and 463-module closure pass. Relative to the previous
checkpoint, all earlier proof files are unchanged; only root imports,
audits, regressions and the runner inventory were extended.

The graph has 299 nodes and 795 edges, without duplicates, missing
endpoints or unclassified nodes. All 42 aggregate checkbox states
remain unchanged (22 checked). The counterexample SHA-256 remains
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The completed repaired energy branch is unchanged; the whole goal remains open.

## Robert–Sargos full window comparison — previous checkpoint

The full higher-moment window comparison in Robert–Sargos Lemma 1 is now
kernel-checked for every natural N >= 2 and p >= 1. The public consumers are
`sargos_lemma_one_upper` and `sargos_lemma_one`; the latter derives
integrability from measurability and the proved majorant. No count,
cancellation estimate, window comparison, or moment bound is assumed.

Write B for the literal number of ordered pairs of p-tuples of integers
in (N,2N] satisfying the source quadratic and quartic tolerances
1/delta and 1/lambda. Let J be the unweighted fixed-sum 2p moment on
[-Delta/2,Delta/2] x [-mu/2,mu/2]. With derivative bound K/N on the actual
source interval and parameter rectangle, set

```text
C(p,K) = 16 [3 (1 + 2 pi K) (1 + 1/log 2)]^(2p).
U <= C(p,K) delta lambda (log N)^(2p) B,
B <= 64/(Delta mu) J,
0 < Delta <= delta, 0 < mu <= lambda.
```

Here U is the genuine upper integral of the actual slow-phase prefix
maximum; arbitrary, even nonmeasurable parameter dependence is allowed.
For an AEStronglyMeasurable integrand the ordinary iterated integral is
proved to agree, and the source-normalized inequality
U / [(log N)^(2p) delta lambda] <= C(p,K) B is exposed.
The result even permits delta > 1. The finite maximum includes the empty
prefix, whose norm is zero; the estimate therefore covers all source
nonempty prefixes as well. The coefficient family is fixed in the two
parameters and has norm at most one on the actual source interval.

The dependency chain is substantive:

- The p-th power is expanded exactly over `Fin p -> (N,2N]`.
- The physical tolerance identities retain both N^2 and N^4.
- The upper sinc-kernel window bound yields 16 delta lambda times the count.
- A dual tent Gram identity bounds that count by the central integral.
  Its compact support and weight at most one are proved, and every counted
  pair contributes at least Delta mu/64; all remaining weights are nonnegative.
- Finite weighted Jensen and actual Fourier completion work for every
  positive integer power. The common prefix kernel has mass at most
  3(1+log N); each completed mode has fixed unit-modulus-twisted coefficients.
- Actual Abel removal supplies the factor (1+2 pi K)^(2p), and a proved
  log-normalization inequality recovers the literal source log.

The 13 modules are `SargosWeightedPowers`, `SargosMomentTuples`,
`SargosMomentCount`, `SargosDualTentKernel`, `SargosDualTentGram`,
`SargosDualTentWindow`, `SargosMomentCentral`, `SargosPowerRegularity`,
`SargosPowerCompletion`, `SargosMaximalWindow`, `SargosSlowPowerWindow`,
`SargosLemmaOne`, and `SargosLemmaOneMeasurable`.
All 57 public theorems are explicitly audited. The 66 new regressions
comprise 57 exact signatures and nine additional fixtures, including
N=1 count scaling, delta > 1, sixth/tenth moments, both tent-support
directions, a smooth sine phase, and an arbitrary bounded linear-phase family.

Source: [Robert–Sargos, section 4, Lemma 1](https://arxiv.org/html/2307.03554v1#S4).
The explicit derivative loss uses the correct O(K) variation over an
interval of length N, not the printed O(1/N) variation sentence.

This closes the higher-moment window-comparison subbranch of EPZAE-10.
The global sixth-moment bootstrap, real dual-scale interval handling,
quartic B/Legendre and sextic slow-error calculation, and C-process are
still open. The previous small-alpha sixth moment remains available
with its verified log^5 estimate and exact source log^6 corollary.
No aggregate task is newly marked complete.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 790 production modules, 1264 scanned Lean files,
  10122 Lake jobs, 6607 target + 6240 pinned + 5 boundary declarations
  audited (12852 total). All 57 public declarations appear exactly once
  in the explicit audit and use only permitted logical axioms.
  [Full extension log](logs/tao-trudgian-yang-build-20260922-234413-dcbd04c1.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, with 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260922_234712.log) and
  [manifest](../../logs/foundation_freeze_20260922_234712.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. The production inventory, root imports, explicit audit and
  semantic regressions were updated together.
- All 1285 source/config/tooling files were byte-identical across the
  BAT pair; the 17 normalized source/integration hashes are recorded in
  the [checkpoint JSON](logs/tao-trudgian-yang-sargos-windows-20260922-234413-dcbd04c1.json).
  Of the previous 1272 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the 13 new modules were added.

The evaluated foundation HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`
with a dirty worktree. An owner Progress Update advanced the previous
HEAD during ongoing work; no agent commit or push was performed.
All 509 protected tracked files are unchanged against this HEAD.
The permanent counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 301 nodes and 801 edges, with no missing endpoints,
duplicates or unclassified nodes. All 42 aggregate checkbox states are
unchanged (22 checked). The repaired energy branch and all nine Add-est
clauses remain intact; the whole-proof goal is still open.

## Robert–Sargos sixth-moment base and strip reduction — previous checkpoint

The actual base integral `sargosSixthBaseMoment N` is defined by the
unweighted fixed sum on alpha in [0,1] and gamma in [-N^-3,N^-3].
Its kernel-checked bounds are

```text
1/64 <= I(N) <= 2 N^3                     (natural N >= 1).
```

The lower bound is derived from the literal diagonal tuple injection:
there are N^p source p-tuples, and each pair (t,t) satisfies both
nonnegative tolerances. The dual-tent count-to-central integral theorem
is then consumed. Exact complex conjugation under
(alpha,gamma) -> (-alpha,-gamma), actual integral reflection and
rectangle inclusion relate the central integral to I(N). No positive
lower bound, diagonal count or base-moment estimate is a parameter.

The same sign/window bridge consumes the previously proved small-alpha
maximal estimate and yields the fixed-sum central sixth moment on
[-1/sqrt N,1/sqrt N] x [-N^-3,N^-3] bounded by

```text
89690996736 (1+log N)^5.
```

For N >= 2, the literal source log^6 corollary has absolute constant
89690996736 (1+1/log 2)^6.

The completed Lemma 1 now has a further actual consumer:
`sargosQuartic_maximal_sixth_strip_reduction` bounds the weighted prefix
maximum on any translated unit-width alpha strip and any positive
height width lambda by

```text
128 C(3,0) (1 + lambda N^3) (log N)^6 I(N).
```

The ordinary and upper-integral slow-phase consumers replace C(3,0)
by C(3,K), for the proved derivative bound K/N. C is the explicit
constant from the preceding full-window checkpoint. The upper-integral
version allows arbitrary nonmeasurable parameter dependence; the
ordinary version derives integrability from measurability. The width
choice min(lambda,2/N^3), its positivity, physical count monotonicity,
central window inclusion and factor 1+lambda N^3 are all proved.

The six new modules are `SargosDiagonalMoment`, `SargosSymmetricWindow`,
`SargosCentralSixthMoment`, `SargosSixthBaseMoment`,
`SargosSixthStripCount`, and `SargosSixthStripTransfer`. Their 24 public
theorems are explicitly audited. The 34 new regressions comprise all
24 exact signatures and ten additional fixtures, including empty-tuple
counting, N=1 bounds, a concrete translated strip, the scale boundary,
a smooth sine phase and arbitrary bounded nonmeasurable linear phases.

These are the actual initial beta=3 estimate, nonvanishing base bound
and height-strip reduction used around
[Robert–Sargos, section 7](https://arxiv.org/html/2307.03554v1#S7).
They do not establish I(N) << N^epsilon. The exponent-improving recurrence,
quartic B/Legendre expansion, real dual-scale interval conversion and
C-process remain open. No aggregate checklist status changes.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  LEAN VERIFICATION PASS; 796 production modules, 1270 scanned Lean files,
  10128 Lake jobs, and 6640 target + 6240 pinned + 5 boundary declarations
  audited (12885 total). All 24 public theorems appear exactly once in the
  explicit audit with only permitted logical axioms.
  [Extension log](logs/tao-trudgian-yang-build-20260923-001009-8680cd0c.log).
- `cmd /c run_lake_build.bat --no-pause`: exit 0, PASS; all six stages
  passed, 8857 root jobs, 301 root modules, two retained regressions,
  7636 explicit public declarations and 14290 discovered foundation
  theorems audited. [Foundation log](../../logs/foundation_freeze_20260923_001404.log) and
  [manifest](../../logs/foundation_freeze_20260923_001404.json).
- Both logs have zero errors, warnings, tactic suggestions and linter
  failures. Root imports, runner inventory, audit and regressions are
  synchronized. All 1291 source/config/tooling files were byte-identical
  across the BAT pair; ten normalized source/integration hashes and all
  physical hashes appear in the [checkpoint JSON](logs/tao-trudgian-yang-sargos-base-20260923-001009-8680cd0c.json).
  Of the preceding 1285 files, only the root import, audit, regression and
  PowerShell runner inventory changed; the six new modules were added.

HEAD remains `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78` with a dirty worktree.
No agent commit or push was performed. All 509 protected tracked files
remain unchanged against that HEAD. The permanent counterexample retains
SHA-256 `76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 303 nodes and 805 edges, without duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The repaired energy branch and all nine Add-est clauses
remain intact; the whole-proof goal is still open.

## Robert–Sargos actual quartic Legendre expansion — previous checkpoint

The actual source phase g(x)=alpha*x^2+gamma*x^4 now has a kernel-checked
inverse slope on [N,2N]. Under N>0, alpha>0 and
|gamma| <= alpha/(96*N^2), its curvature lies between 3*alpha/2 and
5*alpha/2. The chosen inverse is proved to invert the real polynomial;
it is smooth on the open slope image. The signed phase
g*(y)=g(w(y))-y*w(y) has derivative -w(y).

For this actual phase, the residual v is defined by the exact identity

```text
g*(y) = -y^2/(4*alpha) + gamma*y^4/(16*alpha^4)
        - gamma^2*y^6/(16*alpha^7) + v(y).
|v(y)|  <= 10240*|gamma|^3*N^8/alpha^2.
|v'(y)| <= 16384*|gamma|^3*N^7/alpha^3.
```

Both bounds are proved by exact rational polynomial identities, not
assumed asymptotic expansions. With x=w(y), u=2*gamma*x^2/alpha,
the residual polynomials have absolute bounds 5 and 16 for |u|<=1/12.
The derivative is that of the same residual used in the phase identity.

For N>=9216, alpha>=1/sqrt(N), and |gamma|<=N^-3, the scale
hypotheses are derived, giving |v|<=10240 and |v'|<=16384/(alpha*N).
The actual slope image equals the open interval between the endpoint
slopes and is convex. Consequently the residual has the corresponding
Lipschitz bound on that image. For alpha in [Delta,2*Delta], the image
is contained in (2*Delta*N-4,8*Delta*N+32).

This is the quartic specialization of
[Robert–Sargos (6.7), with the large-scale threshold and dual interval in section 7](https://arxiv.org/html/2307.03554v1#S6).
It does not prove the generic perturbation Lemma 4 or the oscillatory
B-transform. The source display (6.2) omits a square root in the
stationary amplitude; (7.5) has the required inverse square root.
The remaining transform must use that correct amplitude, with a
proved full error bound. This discrepancy does not change any frozen
Tao–Trudgian–Yang public output.

The seven modules are `SargosQuarticPhase`, `SargosQuarticInverse`,
`SargosQuarticLegendreAlgebra`, `SargosQuarticLegendreRemainder`,
`SargosQuarticLegendreBounds`, `SargosQuarticLegendreScale`,
and `SargosQuarticDualRange`. Their 44 public theorems are explicitly
audited. The 59 regressions comprise all exact signatures and 15 fixtures,
including both signs of a nonzero quartic coefficient, the Legendre
sign, inverse endpoints, the exact quadratic residual, both polynomial
boundaries, N=9216, and a physical dyadic dual interval.

Still open: the actual oscillatory B-transform, curvature-amplitude
and residual removal from its integer sum, real dual-scale/integer-block
conversion, the parameter Jacobian and covering, the bounded N range,
the exponent-improving sixth-moment recurrence, and the C-process.
The previous base-moment and all-height strip bounds remain available.
No aggregate checklist status changes; the permanent printed-Lemma-62
counterexample, corrected powering, and all nine Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 803 production files, 1,277 scanned Lean
  files and 10,135 build jobs. The audit covers 6,731 target theorems,
  6,240 pinned-source theorems and five boundary anchors (12,976 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-004528-1a1e7f39.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_004918.log)
  and [manifest](../../logs/foundation_freeze_20260923_004918.json).
- All 1,298 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-legendre-20260923-004528-1a1e7f39.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 305 nodes and 809 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos quartic stationary coordinate and Poisson entry — previous checkpoint

The normalized quartic phase F(u)=u^2+epsilon*u^4 now has an explicit
positive quadratic coordinate about the actual stationary point:

```text
L(epsilon,r,u) = 1 + epsilon*(u^2 + 2*u*r + 3*r^2),
z(epsilon,r,u) = (u-r)*sqrt(2*L(epsilon,r,u)).
F(u)-F(r)-F'(r)*(u-r) = z(epsilon,r,u)^2/2.
```

For |epsilon|<=1/96 and r,u in [0,3], the proved coefficient bounds are
7/16<=L<=25/16. The exact coordinate derivative is

```text
(2+4*epsilon*(u^2+u*r+r^2))/sqrt(2*L),
```

and lies in [7/16,25/4]. The coordinate is smooth wherever L>0 and
strictly increasing on the closed extended interval. Its actual chosen
inverse is proved smooth on the open image, with derivative in
[4/25,16/7]. The inverse maps zero to r, and its derivative there is
1/sqrt(2+12*epsilon*r^2).

The physical consumer uses epsilon=gamma*N^2/alpha, T=alpha*N^2,
and r=w(y)/N, where w is the already proved inverse quartic slope.
All range and coefficient hypotheses are derived from the source
curvature assumptions. It proves the exact original-variable identity

```text
g(x)-y*x = g*(y) + (T/2)*z(epsilon,r,x/N)^2.
```

The physical stationary Jacobian is also proved exactly:
(N/sqrt(T))*(inverse-coordinate)'(0)=1/sqrt(g''(w(y))).
Thus the required square-root curvature amplitude is derived from
the actual coordinate, not supplied as an input.

A separate actual-source entry constructs a smooth compact cutoff
chi with 0<=chi<=1 from the literal source lattice. For every natural
N>=1, one cutoff works for all real alpha,gamma. The theorem
`sargosQuartic_source_poisson` proves absolute summability of the
original Fourier integrals

```text
Integral chi(x/N)*e(alpha*x^2+gamma*x^4-m*x) dx
```

over all integer m, and bounds the difference between their full
Poisson series and the unweighted source sum on (N,2N] by 2.
The endpoint count, cutoff values, real/complex character convention,
Schwartz decay and Poisson equality are all derived. No
approximate-model-phase or oscillatory-transform hypothesis is used.

The four modules are `SargosQuarticMorse`,
`SargosQuarticMorseInverse`, `SargosQuarticMorsePhysical`, and
`SargosQuarticPoisson`. Their 40 public theorems are explicitly audited.
The 52 regressions comprise every exact signature and 12 fixtures,
covering both signs at the coefficient bounds, the actual inverse
and critical derivative, physical scaling/amplitude, and N=1 source
and endpoint behavior.

This supplies the actual-coordinate and Poisson-entry obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
It does not yet estimate the individual Fourier modes or prove the
B-transform. The exact lattice cutoff carries no claimed uniform derivative
budget; the quantitative step must choose controlled cutoffs and pay their
source-endpoint loss. Remaining: uniform higher inverse/weight derivatives,
actual integral substitution and cutoff transport, complete
stationary/nonstationary mode errors and lattice summation, the
curvature-amplitude/residual Abel steps, dual block conversion,
parameter Jacobian/covering, bounded N range, the sixth-moment
recurrence, and the C-process. No aggregate checklist status changes.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 807 production files, 1,281 scanned Lean
  files and 10,139 build jobs. The audit covers 6,818 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,063 total).
  All 40 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-011542-75b94f86.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_011847.log)
  and [manifest](../../logs/foundation_freeze_20260923_011847.json).
- All 1,302 physical proof/configuration/tooling hashes are identical
  before and after both runners. The four modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-20260923-011542-75b94f86.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 307 nodes and 816 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos uniform quartic jets and cutoff transport — previous checkpoint

The actual positive quadratic coordinate and its inverse now have
all-order derivative bounds uniform in |epsilon|<=1/96 and r in [0,3].
The coordinate bounds hold on u in (0,3); inverse bounds hold on the
actual moving open image. Constants depend only on the derivative
order, not on epsilon, r or the individual phase.

The polynomial A=2*(1+epsilon*(u^2+2*u*r+3*r^2)) has exact derivatives
A'=4*epsilon*(u+r), A''=4*epsilon and A^(j)=0 for j>=3.
Every atom in the coordinate's proved finite derivative expression
has absolute value at most 3. Explicit finite expression magnitudes
give the coordinate bounds; explicit finite sums of those bounds give
the inverse bounds. The formulas are proved against the actual
coordinate/inverse, not a model-phase surrogate.

The positive inverse Jacobian now transports both the complex
Bochner integral and integrability between (0,3) and the actual
coordinate image. The transported source cutoff is exactly

```text
W(z) = chi(inverse(z))*inverse'(z) on the actual open image,
W(z) = 0 outside that image.
W(0) = chi(r)/sqrt(2+12*epsilon*r^2).
```

For smooth chi with closed support contained in (0,3), W is globally
smooth and compactly supported, including across the moving image
boundary. Its closed support lies in the actual coordinate image of
the closed support of chi, and uniformly in [-6,6]. Every derivative
is integrable and supported in that same compact image. The whole-line
identity holds for arbitrary complex g:

```text
Integral chi(u)*g(u) du = Integral W(z)*g(inverse(z)) dz.
```

Global all-order weight estimates retain an explicit finite cutoff
jet budget M. Their constants depend only on M and the output order,
not on the phase parameters. No derivative budget uniform in a
varying cutoff family is inferred from compactness.

Eleven modules are installed: `SargosQuarticMorseCurvature`,
`SargosQuarticMorseJets`, `SargosQuarticMorseJetBounds`,
`SargosQuarticMorseInverseJets`, `SargosQuarticMorseInverseJetBounds`,
`SargosQuarticMorseChangeVariables`, `SargosQuarticMorseAmplitude`,
`SargosQuarticMorseSupport`, `SargosQuarticMorseGlobalIntegral`,
`SargosQuarticMorseWeightJets`, and `SargosQuarticMorseWeightBounds`.
All 50 public theorems have exact-signature regressions and explicit
axiom audits; 12 additional fixtures cover signed boundary coefficients,
high-order vanishing, arbitrary derivative orders, cutoff retention,
moving-image exterior behavior and global cutoff budgets.

These results discharge further actual-coordinate analytic obligations
behind [Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
They do not yet prove a Fourier-mode remainder or the B-transform.
Remaining are the physical positive-quadratic Fourier identity and
Fresnel remainder, controlled cutoff family and source loss, complete
stationary/nonstationary mode errors and lattice sums, curvature and
Legendre-residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 818 production files, 1,292 scanned Lean
  files and 10,150 build jobs. The audit covers 6,891 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,136 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-014238-0efee296.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_014551.log)
  and [manifest](../../logs/foundation_freeze_20260923_014551.json).
- All 1,313 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-morse-jets-20260923-014238-0efee296.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 309 nodes and 822 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos physical stationary estimates and controlled source entry — previous checkpoint

The actual physical quartic Fourier integral is now proved equal to
its positive-quadratic representation. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open quartic slope image,
put epsilon=gamma*N^2/alpha, T=alpha*N^2 and r=w(y)/N. Then

```text
Integral chi(x/N)*e(g(x)-y*x) dx
  = N*e(g*(y))*Integral W(z)*e((T/2)*z^2) dz,
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

The original cutoff has closed support in (1,2), and W is its actual
smooth transported weight from the preceding checkpoint. The physical
factor N, actual stationary point, signed Legendre phase, positive
Fresnel sign and square-root curvature amplitude are all proved.
The leading coefficient is chi(r)*main(y); the cutoff is not dropped.

Exact complex conjugation transfers the already proved negative
quadratic Fresnel remainder to positive curvature. With the finite
original-cutoff derivative budget M visible, the theorem
`sargosQuarticFourierMode_stationary_bound` bounds the difference
from chi(r)*main(y) by C(M)/(alpha*N). Its constants do not depend
on N, alpha, gamma or y.

A separate varying-cutoff theorem chooses constants before both
endpoints, the width eta, and the quartic parameters. Its actual
transformed nth derivative costs at most C_n*eta^(-n), for 0<eta<=1.
This yields

```text
|physical mode - chi(r)*main(y)| <= C*eta^(-3)/(alpha*N).
```

The exponent -3 is explicitly retained. This estimate alone is not
the sharp summed B-transform error; a local plateau argument and
complete mode/lattice analysis are still required.

The source-facing controlled cutoff is now constructed explicitly:
chi(u)=bufferedCutoff((N+1)/N,2,eta)(u), for natural N>=1 and eta>0.
`sargosQuartic_buffered_poisson` proves absolute summability of the
original physical Fourier modes and

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4) - Sum_(m in Z) mode(m)|
  <= 4*N*eta+2.
```

Its endpoint count, literal source interval, source phase and
normalizations are derived. No model-phase approximation, Poisson
error certificate, or stationary-phase estimate is an input.

Seven modules are installed: `SargosQuarticMorseFourier`,
`SargosPositiveQuadraticRemainder`, `SargosQuarticMorseRemainder`,
`SargosQuarticStationaryEstimate`, `SargosQuarticBufferedJets`,
`SargosQuarticBufferedStationary`, and `SargosQuarticBufferedPoisson`.
All 17 public theorems have exact-signature regressions and explicit
axiom audits. Twelve additional fixtures test the Fresnel sign,
physical normalization and amplitude, arbitrary derivative order,
explicit width powers, and N=1,2 source support/endpoint behavior.

These are supporting steps toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
The sharp interior, near-edge, exterior and infinite-tail estimates,
their integer sums, curvature/residual Abel steps, integer dual-block
conversion, parameter Jacobian/covering, bounded N, sixth-moment
recurrence and C-process remain open. No aggregate checklist status
changes. The permanent counterexample, corrected powering and all
nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 825 production files, 1,299 scanned Lean
  files and 10,157 build jobs. The audit covers 6,930 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,175 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-020618-a3f2de7d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_020944.log)
  and [manifest](../../logs/foundation_freeze_20260923_020944.json).
- All 1,320 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-stationary-20260923-020618-a3f2de7d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 312 nodes and 833 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos sharp quartic interior stationary error — previous checkpoint

The actual positive-curvature quartic Fourier mode now has a sharp
interior error with no inverse cutoff-width loss. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and y in the actual open slope image, write
r=w(y)/N for its actual normalized stationary point. For the controlled
cutoff chi=bufferedCutoff(l,b,eta), assume 1<=l, b<=2, eta>0, d>0,
l+2*eta+d<=r and r+d<=b-2*eta. Then

```text
|mode(y) - e(g*(y)+1/8)/sqrt(g''(w(y)))| <= C/(alpha*N*d).
```

The constant is chosen before l, b, eta, d and all physical parameters.
The cutoff coefficient is one because the actual stationary point
lies inside its proved plateau; it is not discarded by assumption.
The source mode, inverse, signed Legendre phase, positive Fresnel sign,
physical N factor and square-root amplitude are the original objects.

The proof derives an actual quadratic-coordinate window |z|<=H.
Uniform coordinate distances and slope gaps locate its inverse images.
On that window the transported cutoff's derivatives are actual inverse
derivatives, so their constants do not grow as eta tends to zero.
The local positive-quadratic remainder is bounded by C_local/(T*H).

An exact positive-Jacobian change of variables identifies the central
original-integral piece. The two omitted original-integral tails
are bounded together by 128/(7*pi*T*H), using actual slope gaps and
the proved width-independent cutoff variation. Choosing H=d/4 and
T=alpha*N^2 gives the displayed physical estimate. All hypotheses
for the window, tails, plateau and normalization are derived.

Nine modules are installed: `SargosQuarticMorseGeometry`,
`SargosQuarticMorseWindow`, `SargosPositiveQuadraticLocal`,
`SargosQuarticLocalRemainder`, `SargosQuarticCenteredPhase`,
`SargosQuarticWindowIntegral`, `SargosQuarticLocalNonstationary`,
`SargosQuarticWindowTails`, and `SargosQuarticInteriorStationary`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Twelve further fixtures check both perturbation endpoints,
the quadratic specialization and derivative, actual inverse windows,
genuine integrability, positive central transport, varying widths,
and the quarter-distance physical bound.

This completes the sharp interior component, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Near-edge, exterior and infinite-tail bounds and their integer sums
remain open, followed by curvature/residual Abel steps, integer dual
blocks, parameter Jacobian/covering, bounded N, the sixth-moment
recurrence and C-process. Aggregate checklist states do not change.
The permanent counterexample, corrected powering and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 834 production files, 1,308 scanned Lean
  files and 10,166 build jobs. The audit covers 6,960 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,205 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-023612-86705e16.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_023922.log)
  and [manifest](../../logs/foundation_freeze_20260923_023922.json).
- All 1,329 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-interior-20260923-023612-86705e16.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 314 nodes and 840 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos sharp quartic support-frequency core — previous checkpoint

The original quartic Fourier modes now have uniform estimates at
every real frequency, including frequencies without a stationary
point and those at moving support endpoints. For N>0, alpha>0,
|gamma|<=alpha/(96*N^2), and the actual controlled cutoff
chi=bufferedCutoff(l,b,eta), with 1<=l, b<=2 and eta>0,

```text
|mode(y)| <= 4*(2/pi+2)/sqrt(alpha).
```

This follows from the actual quartic curvature and the proved cutoff
variation, by exact complex conjugation of the negative-curvature
integral theorem. No model-phase approximation is assumed. The actual
stationary main term has norm at most 1/sqrt(alpha).

Outside the support's actual slope interval, the original physical
mode has a reciprocal-gap bound 4/(pi*gap), where gap is the distance
from y to g'(N*(l+eta)) or g'(N*(b-eta)). The physical normalization
and the cutoff-empty case are proved. These are pointwise exterior
bounds; their integer sums are not yet included.

For the interior, the actual quartic curvature upper bound converts
frequency gaps to distances of the real inverse stationary point.
The preceding C/(alpha*N*d) estimate therefore becomes C'/gap.
Summing the two reciprocal edge distances gives a logarithmic error
over the literal integer interval; no stationary-image or per-mode
estimate is left as an input.

Support endpoints are rounded outwards, plateau endpoints inwards:

```text
L = floor g'(N*(l+eta)),     U = ceil g'(N*(b-eta)),
A = ceil  g'(N*(l+2*eta)),   B = floor g'(N*(b-2*eta)).
```

If l+4*eta<b, the transition complement Icc(L,U) minus Ioo(A,B)
has at most 5*alpha*N*eta+6 elements. Exactly resonant and nearest
endpoint frequencies are included. The public consumer
`sargosQuarticBufferedSupportCore_error` proves

```text
|Sum_(L<=y<=U) mode(y) - Sum_(A<y<B) main(y)|
 <= C*(1+log((B-A-1).toNat)) + (5*alpha*N*eta+6)*D/sqrt(alpha),
main(y) = e(g*(y)+1/8)/sqrt(g''(w(y))).
```

C>=1 and D>0 are chosen before all cutoff and physical parameters.
The source Fourier modes and actual signed stationary main terms are
used throughout. Empty integer interior blocks are handled explicitly.

Six modules are installed: `SargosQuarticFourierCurvature`,
`SargosQuarticExteriorModes`, `SargosQuarticInteriorFrequency`,
`SargosQuarticInteriorSum`, `SargosQuarticTransitionBands`, and
`SargosQuarticSharpCore`. All 18 public theorems have exact-signature
regressions and explicit axiom audits. Twelve further fixtures cover
all-frequency quadratic and extreme perturbation bounds, empty
cutoffs, physical stationary amplitude, both exterior gaps, exact
rounding at N=8, and the actual eleven-frequency interior block.

This is the sharp finite support-frequency core, not the full
[Robert–Sargos B-transform](https://arxiv.org/html/2307.03554v1#S6).
Exterior integer sums, quantitative infinite-tail bounds and full
source assembly remain open, followed by curvature/residual Abel
steps, integer dual blocks, parameter Jacobian/covering, bounded N,
the sixth-moment recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 840 production files, 1,314 scanned Lean
  files and 10,172 build jobs. The audit covers 7,000 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,245 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-025806-560f1b5d.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_030120.log)
  and [manifest](../../logs/foundation_freeze_20260923_030120.json).
- All 1,335 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-support-core-20260923-025806-560f1b5d.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 317 nodes and 849 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos complete explicit-parameter quartic source expansion — previous checkpoint

The literal quartic source sum is now connected to its actual signed
stationary main terms through every Fourier-mode class. Exterior
integer sums, quantitative two-sided infinite tails and source
assembly are proved. The cutoff width, truncation radius and
logarithmic lengths remain explicit; the final stationary-scale
error simplification is not yet claimed.

The original normalized quartic kernel has uniform second-derivative
bound C*eta^(-2)*(1+|T|)^2. Its actual phase has first two derivative
bounds proved from |epsilon|<=1/96 on [1,2]. Exact normalization links
T=alpha*N^2, epsilon=gamma*N^2/alpha and Fourier frequency y*N to the
original physical mode. Consequently,

```text
|mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*y^2), y != 0,
|Sum_(|y|>R) mode(y)| <= C*eta^(-2)*(1+alpha*N^2)^2/(N*R).
```

The omitted series is the actual two-sided integer tail. Both signs,
absolute convergence, zero-frequency exclusion and the physical N
factor are proved. A separate source consumer chooses an explicit
positive radius achieving any requested tail tolerance.

The left and right support-exterior blocks each have norm sums bounded
by (4/pi)*harmonic(length); both together have logarithmic loss.
They are exactly reindexed, with no omitted or duplicated nearest
exterior integer. Combining them with the preceding sharp support
core gives the complete finite Fourier-window expansion.

For the literal source Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4), take
natural N>=1, alpha>0, |gamma|<=alpha/(96*N^2), 0<eta<=1,
l=(N+1)/N, and l+4*eta<2. Let L,U be the outward-rounded support
slopes and A,B the inward-rounded plateau slopes. Then
`sargosQuartic_source_stationary_expansion` proves

```text
|source - Sum_(A<y<B) e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= 4*N*eta+2
  + C*eta^(-2)*(1+alpha*N^2)^2/(N*R)
  + D*(1+log((B-A-1).toNat))
  + (5*alpha*N*eta+6)*E/sqrt(alpha)
  + (4/pi)*(2+log((L+R).toNat)+log((R-U).toNat)).
```

Here R is a positive natural number whose symmetric interval contains
[L,U], and C>=1, D>=1, E>0 are chosen before all source parameters.
The precision consumer constructs
R=ceil(C*eta^(-2)*(1+alpha*N^2)^2/(N*tolerance))+|L|+|U|+1,
proves the required interval containment, and replaces the actual
tail term by tolerance. No Poisson, stationary or tail estimate is
left as an assumption.

Six modules are installed: `SargosQuarticExteriorSum`,
`SargosQuarticKernelJets`, `SargosQuarticFourierDecay`,
`SargosQuarticFourierTail`, `SargosQuarticFourierWindow`, and
`SargosQuarticSourceExpansion`. All 17 public theorems have exact
signature regressions and explicit axiom audits. Twelve further
fixtures check extreme perturbations, the actual kernel and carrier,
physical decay/tail constants, a concrete truncation tolerance,
empty exterior blocks, rounded finite windows, and the literal N=8
source's nine-frequency stationary block.

This assembles the explicit-parameter source chain toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the linked stationary-scale cutoff choice, polynomial
radius/logarithmic budgets and the final uniform B-transform error;
then curvature/residual Abel steps, integer dual blocks, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 846 production files, 1,320 scanned Lean
  files and 10,178 build jobs. The audit covers 7,026 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,271 total).
  All 17 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-032157-6b77f0c9.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_032511.log)
  and [manifest](../../logs/foundation_freeze_20260923_032511.json).
- All 1,341 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-expansion-20260923-032157-6b77f0c9.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 320 nodes and 860 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos large-source quartic B-transform — previous checkpoint

The literal quartic source now has a uniform B-transform into its full
closed stationary integer range. The actual cutoff choice, every
frequency logarithm, both infinite tails and the omitted endpoint
terms are consumed by one public theorem. This closes the large-source
oscillatory-transform step, not the sixth-moment recurrence.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_B_transform` proves, with one constant M>=1
chosen before N, alpha and gamma,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)
 - Sum_(g'(N)<=y<=g'(2N), y integer)
     e(g*(y)+1/8)/sqrt(g''(w(y)))|
 <= M*(1/sqrt(alpha)+1+log(2+alpha*N)).
```

Here g(x)=alpha*x^2+gamma*x^4, w is its actual inverse slope on
[N,2N], and g*(y)=g(w(y))-y*w(y). Both integer endpoint resonances
are included with full weight; their possible boundary contributions
are covered by the proved error. The positive square-root amplitude
is retained, consistently with (7.5). The earlier documented
missing square root in displayed (6.2) is not imported as an identity.

The stationary cutoff is eta=1/sqrt(alpha*N^2)=1/(N*sqrt(alpha)).
Its positivity, eta<=1 and nonempty source plateau are derived from
the original source range. Smoothing contributes 4/sqrt(alpha);
the transition term simplifies with no surviving inverse-width loss.
Every actual rounded slope has absolute integer size at most
6*alpha*N^2+1. The prescribed positive radius is at most
(C+16)*(alpha*N^2+1)^3; all three logarithmic lengths are bounded
using (C+24)*(alpha*N^2+1)^3, including zero-length cases.

The intermediate uniform consumer retains the actual buffered main
range. A separate closed-range bridge proves inverse-slope and
amplitude bounds at the endpoints, plateau containment, and the
count of omitted terms:
```text
omitted cardinality <= 5*alpha/2+10*alpha*N*eta+4.
```
At the stationary width and alpha<=1 their total norm is at most
17*(1/sqrt(alpha)+1). The final consumer restores the full closed
stationary sum and derives its logarithmic error from linked source
scales; no cutoff, stationary estimate or endpoint certificate is
assumed.

Nine modules are installed: `SargosQuarticStationaryWidth`,
`SargosQuarticRoundedBounds`, `SargosQuarticRadiusBudget`,
`SargosQuarticLogBudget`, `SargosQuarticUniformSource`,
`SargosQuarticClosedRange`, `SargosQuarticEndpointBands`,
`SargosQuarticEndpointError`, and `SargosQuarticBTransform`.
All 25 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen further fixtures check the stationary width,
degenerate inverse-square identity, threshold plateau, smoothing,
transition algebra, prescribed radius, full closed range, both
resonant endpoints, exterior exclusion, boundary amplitude, omitted
cardinality and the assembled source estimate.

This realizes the large-integer-source B-transform needed toward
[Robert–Sargos section 6 and (7.5)](https://arxiv.org/html/2307.03554v1#S6).
Still open: the power-scale error corollary, actual curvature and
residual Abel steps, integer dual blocks and real-scale conventions,
parameter Jacobian/covering, bounded N, the sixth-moment recurrence
and C-process. It does not assert the general C4 version of (6.2).
No aggregate checklist status changes. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 855 production files, 1,329 scanned Lean
  files and 10,187 build jobs. The audit covers 7,076 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,321 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-035345-754b20b2.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_035655.log)
  and [manifest](../../logs/foundation_freeze_20260923_035655.json).
- All 1,350 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-b-transform-20260923-035345-754b20b2.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 322 nodes and 866 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos source power error and both Abel steps — previous checkpoint

The literal quartic source is now bounded by the actual degree-six
polynomial prefix maximum. The quarter-power error and both Abel
steps are proved, including the full closed stationary range and
its resonant endpoints. Neither amplitude variation nor residual
variation is an assumed analytic input.

For natural N>=9216, 1/sqrt(N)<=alpha<=1 and |gamma|<=N^(-3),
`sargosQuartic_source_le_polynomialPrefixMaximum` proves

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(alpha^(-1/2)*Pmax(N,alpha,gamma)+N^(1/4)).
```

The single constant C>=1 is chosen before N, alpha and gamma.
Pmax is the attained maximum over every prefix, including the empty
prefix, of the actual integer interval
[ceil(g'(N)), floor(g'(2N))], with phase

```text
p(y) = -y^2/(4*alpha)+gamma*y^4/(16*alpha^4)
       -gamma^2*y^6/(16*alpha^7).
```

The prefix definition uses the exact integer interval length and
works also for an empty interval. It is not a separately supplied
exponential-sum majorant. The source consumer links every parameter
to the original phase g(x)=alpha*x^2+gamma*x^4.

The preceding full B-transform now has error at most C*N^(1/4).
The proof derives alpha^(-1/2)<=N^(1/4) and
log(N+1)<=1+4*N^(1/4), then consumes the actual logarithmic error.

The actual amplitude 1/sqrt(g''(w(y))) is positive, bounded by
alpha^(-1/2), and monotone or antitone according to the sign of
gamma on the closed slope range. Its sampled finite variation is
at most alpha^(-1/2). Exact integer reindexing and Abel summation
bound the full stationary sum by twice this scale times the genuine
unweighted Legendre-prefix maximum. The unit phase e(1/8) is removed
by an exact identity and norm equality.

The literal Legendre residual v(y)=g*(y)-p(y) uses the existing
source derivative bound 16384/(alpha*N). Its character has interior
Lipschitz constant 32768*pi/(alpha*N), while the actual slope interval
has length at most 5*alpha*N/2. Interior sampled variation is therefore
at most 81920*pi. On the full closed range, the first and last possible
boundary jumps each cost at most 2 by unit modulus. This yields the
uniform finite-variation budget 5+81920*pi, without extending the
derivative theorem to an unproved endpoint domain. The residual Abel
consumer retains every endpoint and supplies the polynomial maximum
used by the final source theorem.

Eight modules are installed: `SargosQuarticPowerError`,
`SargosQuarticAmplitude`, `SargosQuarticAmplitudeVariation`,
`SargosIntegerPrefix`, `SargosQuarticAmplitudeAbel`,
`SargosQuarticResidualVariation`, `SargosQuarticResidualBoundary`,
and `SargosQuarticResidualAbel`. All 29 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures cover quarter powers, threshold source errors,
constant curvature, both monotonicity signs, inverse endpoints,
sampled amplitude variation, negative and empty integer prefixes,
the literal dual polynomial, closed residual boundary variation,
and the final source-to-polynomial bound.

This completes the power-scale and actual-weight/residual steps toward
[Robert–Sargos (7.5)–(7.8)](https://arxiv.org/html/2307.03554v1#S7).
Still open: dyadic integer block conversion and real-scale conventions,
the sign-conjugation bridge to the source parameter change, parameter
Jacobian/covering, bounded N, the sixth-moment recurrence and C-process.
No integral transfer or recurrence is claimed here. No aggregate
checklist status changes. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 863 production files, 1,337 scanned Lean
  files and 10,195 build jobs. The audit covers 7,128 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,373 total).
  All 29 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-042459-0f7675ca.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_042813.log)
  and [manifest](../../logs/foundation_freeze_20260923_042813.json).
- All 1,358 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-abel-20260923-042459-0f7675ca.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 324 nodes and 872 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos rounded dyadic blocks and exact conjugation — previous checkpoint

The actual closed stationary-prefix interval now reduces to two integer
dyadic blocks. Exact conjugation converts their phases to positive
quadratic phases while retaining the sextic correction.

For natural N>=9216, N^(-1/2)<=Delta<=1/2,
alpha in [Delta,2*Delta] and |gamma|<=N^(-3), let
m=floor(2*Delta*N). The source-facing theorem
`sargosQuartic_source_le_two_slow_blocks` proves, with one C>=1
chosen before every source parameter,

```text
|Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|
 <= C*(Delta^(-1/2)*(Smax(m)+Smax(2*m))+N^(1/4)),
Smax(h) = max_(0<=L<=h)
 |Sum_(h<n<=h+L) e(x*n^2+y*n^4+phi(n))|,
x=1/(4*alpha), y=-gamma/(16*alpha^4),
phi(t)=gamma^2*t^6/(16*alpha^7).
```

These are the actual slow quartic maxima, not assumed majorants.
The scale is linked to the source: m>=192 and
Delta*N<=m<=2*Delta*N<m+1. The integer stationary endpoints satisfy
ceil(g'(N))>=m-4 and floor(g'(2N))<=4*m+35.
At most 40 unit-modulus terms lie outside (m,4*m].
Each retained interval is the difference of two prefixes in
(m,2*m] or (2*m,4*m]. This yields the two genuine maxima
and a bounded loss absorbed in the existing quarter-power error.

The polynomial sign reversal, character conjugation, prefix conjugation
and maximum equality are exact. In particular, the correction
gamma^2*t^6/(16*alpha^7) is retained. The natural scale m is not
silently identified with the paper's real scale 2*Delta*N.

Six production modules are installed: `SargosIntegerBlock`,
`SargosIntegerTwoBlocks`, `SargosIntegerDyadicTrim`,
`SargosQuarticRoundedScale`, `SargosQuarticPrefixBlocks`,
and `SargosQuarticDualConjugation`. All 19 public theorems have
exact-signature regressions and explicit axiom audits. Thirteen
additional fixtures cover negative and empty intervals, the exact
40-term trimming bound, integral and nonintegral rounded scales,
both extreme perturbation signs, the actual sextic polynomial,
and the source bound at N=9216.

This is a pointwise source reduction toward
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Parameter change, Jacobian, rectangle covering, integrated transfer,
the real-scale convention, bounded N, recurrence and C-process remain
open. No integral estimate or recurrence is claimed. All 42 aggregate
checkbox states are unchanged. The permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 869 production files, 1,343 scanned Lean
  files and 10,201 build jobs. The audit covers 7,188 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,433 total).
  All 19 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-045149-2aa62e03.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_045504.log)
  and [manifest](../../logs/foundation_freeze_20260923_045504.json).
- All 1,364 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-dyadic-conjugation-20260923-045149-2aa62e03.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 326 nodes and 874 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos actual parameter change and sextic rectangle moment — previous checkpoint

The actual source parameter substitution and the moment bound on each
admissible parameter rectangle are now proved. No Jacobian formula,
inverse map, phase-variation bound or rectangle moment is assumed.

The map
`(alpha,gamma) -> (1/(4*alpha),-gamma/(16*alpha^4))`
is its own inverse when alpha is nonzero. Its exact scalar derivatives
give the inverse Jacobian weight 1/(64*x^6). Two genuine set-integral
substitutions prove the triangular change of variables, including
the variable vertical range [-16*H*x^4,16*H*x^4]. For Delta>0 and H>=0,
this yields the fixed-rectangle bound

```text
Integral_(Delta<=alpha<=2Delta, |gamma|<=H) F(map(alpha,gamma))
 <= 4096*Delta^6 *
    Integral_(1/(8Delta)<=x<=1/(4Delta), |y|<=H/(16Delta^4)) F(x,y).
```

This statement is for nonnegative extended-real iterated integrals,
and does not require an integrand-measurability hypothesis.
`sargosQuarticDual_sixth_parameter_transfer` consumes it for the
actual source-linked slow maxima. The exact sextic identity changes
gamma^2*t^6/(16*alpha^7) into 4*y^2*t^6/x.

On a unit-width rectangle [c,c+1] by [d,d+2/M^3], with
M>=2, 0<Delta<=1/2, c>=1/(8*Delta) and
|d|<=5/(Delta*M^3), the frozen coefficients are exactly
e(4*d^2*n^6/c), of modulus one. Their residual phase is
4*(y^2/x-d^2/c)*t^6. The proved coefficient bound is
2496/M^6 and the derivative bound is 1916928/M.
The actual prefix and maximum are unchanged by this freezing.

The completed Lemma 1 consumer then proves

```text
Integral_rectangle Smax(M,x,y,4*y^2*t^6/x)^6
 <= 384*Cwindow(3,1916928)*(log M)^6*I(M).
```

Both a genuine upper-integral theorem and the ordinary nonnegative
iterated-integral theorem are installed. Measurability of the actual
sextic maximum is proved, not assumed. These are estimates for each
admissible rectangle; the finite covering has not yet been assembled.

Eight modules are installed: `SargosQuarticParameterMap`,
`SargosQuarticParameterDomain`, `SargosQuarticParameterChange`,
`SargosQuarticParameterTransfer`, `SargosQuarticSexticFreeze`,
`SargosQuarticSexticBounds`, `SargosQuarticSexticRectangle`,
and `SargosQuarticMomentTransfer`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Fourteen
additional fixtures check reciprocal images, source-scale parameters,
the sextic identity, the extremal Jacobian bound, frozen unit modulus,
rectangle boundaries and the actual source-moment transfer.

This advances the source reduction in
[Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
Still open: finite rectangular covering and its count, assembled
large-source sixth-moment bound, rounded/real-scale conventions,
bounded N, recurrence and C-process. The original quartic pointwise
bound uses the linked integer scales m=floor(2*Delta*N) and 2*m;
this checkpoint does not silently replace them by real scales.
All aggregate checklist states, the permanent counterexample,
corrected powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 877 production files, 1,351 scanned Lean
  files and 10,209 build jobs. The audit covers 7,254 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13,499 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-051922-22d50561.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_052320.log)
  and [manifest](../../logs/foundation_freeze_20260923_052320.json).
- All 1,372 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-parameter-rectangle-20260923-051922-22d50561.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 328 nodes and 878 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos large-source sixth moment at rounded scales — previous checkpoint

The literal source sixth moment now satisfies the large-source
two-scale reduction. The public theorem
`sargosQuartic_large_source_sixth_moment` chooses one C>=1 before
all N and Delta, and proves for natural N>=9216 and
N^(-1/2)<=Delta<=1/4, with m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)),
R(N,Delta) =
 Integral_(Delta<=alpha<=2Delta, |gamma|<=N^(-3))
 |Sum_(N<n<=2N) e(alpha*n^2+gamma*n^4)|^6.
```

R and I are the actual Bochner integrals of the literal quartic sums.
No majorant, Jacobian, covering, slow-phase estimate or moment
inequality is supplied as an analytic premise.

The closed transformed rectangle has a finite grid cover retaining
all endpoints. Its horizontal count is at most 2/Delta and its
vertical count at most 5/Delta. Every corner satisfies the already
proved sextic rectangle theorem. A finite-cover integration inequality
allows overlapping boundaries; no disjointness or boundary omission
is assumed. Summing the actual rectangle moments and applying the
proved source parameter change gives, at either admissible integer
scale M,

```text
Integral_source DualMax(M)^6
 <= 15728640*Cwindow(3,1916928)*Delta^4*(log M)^6*I(M).
```

The source-facing sixth-power consumer uses both real dual maxima
and the original pointwise source bound. It bounds the sixth power
of the quarter-power error by N^3, whose integral over the source
rectangle is exactly 2*Delta. Measurability of the actual dual maxima
and the bridge from the original Bochner integral to nonnegative
iterated integrals are proved. The linked scales satisfy
m>=2, 2*m>=2, m<=N and 2*m<=N, so both logarithms transfer to log N.
The actual lower bound I(m)>=1/64 absorbs the error, without an
extra logarithmic loss.

Eleven modules are installed: `SargosIntervalGrid`,
`SargosFiniteCoverIntegral`, `SargosQuarticCoverGeometry`,
`SargosQuarticCoverMoment`, `SargosQuarticDualMoment`,
`SargosQuarticSixthPower`, `SargosQuarticMomentIntegration`,
`SargosRectangleLinearIntegral`, `SargosQuarticSourceMoment`,
`SargosQuarticMomentScale`, and `SargosQuarticLargeSourceMoment`.
All 24 public theorems have exact-signature regressions and explicit
axiom audits. Fifteen additional fixtures cover zero/nonintegral
grid lengths, closed right endpoints, negative grid origins, actual
source grid counts at both scales, boundary corners, sixth powers,
the integrated source error, and the final threshold, nonintegral
rounding and Delta=1/4 source estimates.

This is the natural-N, rounded-scale, large-source form of the
reduction in [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
It does not identify m with the real number 2*Delta*N.
Still open: the bounded source range, the source's real-scale
convention, global recurrence and C-process. No aggregate checklist
status changes. The permanent counterexample, corrected powering
and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 888 production files, 1,362 scanned Lean
  files and 10,220 build jobs. The audit covers 7338 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13583 total).
  All 24 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-054924-c8e7f79f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_055711.log)
  and [manifest](../../logs/foundation_freeze_20260923_055711.json).
- All 1,383 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-large-source-moment-20260923-054924-c8e7f79f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 330 nodes and 883 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos bounded reduction and finite-scale bootstrap — previous checkpoint

The rounded two-scale reduction now covers every natural N>=16.
The theorem `sargosQuartic_sixth_moment_reduction` chooses one C>=1
before N and Delta, and proves, for N^(-1/2)<=Delta<=1/4 and
m=floor(2*Delta*N),

```text
R(N,Delta) <= C*Delta*(log N)^6*(I(m)+I(2*m)).
```

The previously omitted range 16<=N<=9216 is discharged using the
actual source rectangle inclusion, I(N)<=2*N^3, I(m)>=1/64,
m>=8 and Delta>=1/96. No additional analytic premise is introduced.

The recurrence now has an actual finite-scale consumer.
For the literal full-sum moment, the near-count upper/lower bounds
and symmetry prove localization without a maximal-completion loss:

```text
I(N) <= (1024/A)*InitialMoment(N,A),       0<A<=1/2.
```

A finite dyadic split retains every interval endpoint. Its linked
scales delta_i start at N^(-1/2), satisfy delta_i<=A, cover [0,A]
together with the small-alpha interval, and obey sum(delta_i)<=2*A.
If A is below the first scale, direct integral monotonicity applies.
The integration theorem consumes the actual R(N,delta_i), not a
separately supplied surrogate integral.

`sargosSixthBaseMoment_power_bootstrap` chooses C>=1 before
beta and B. For beta,B>=0, a genuine upstream bound
I(M)<=B*M^beta for every natural M>=1 implies, for N>=16 and
0<A<=1/4,

```text
I(N) <= C*((1+log N)^5/A + B*(log N)^6*(4*A*N)^beta).
```

Both rounded moment scales are explicitly bounded by 4*A*N in this
consumer. The upstream power bound is an explicit, narrower input:
it is used at those smaller linked moments. It is not a premise
equivalent to the bootstrap conclusion.
`sargosSixthBaseMoment_cubic_bootstrap` discharges that input using
the proved trivial estimate. Separately,
`sargosSixthBaseMoment_sqrt_bound` consumes the actual small-alpha
estimate and localization to prove for natural N>=4

```text
I(N) <= (1024*44845498368)*sqrt(N)*(1+log N)^5.
```

Seven modules are installed: `SargosQuarticBoundedScale`,
`SargosQuarticBoundedMoment`, `SargosSixthLocalization`,
`SargosDyadicIntegral`, `SargosSixthDyadicBudget`,
`SargosSixthPowerBootstrap`, and `SargosSixthBootstrapInputs`.
All 18 public theorems have exact-signature regressions and explicit
axiom audits. Fourteen additional fixtures cover threshold scales,
the bounded-range constant, empty/nonempty dyadic sums, the source
scale budget, negative/zero integration cases, localization,
small-alpha and square-root estimates, and actual source consumers.

This advances [Robert–Sargos Section 7](https://arxiv.org/html/2307.03554v1#S7).
The finite-scale bootstrap is proved; the epsilon-quantified exponent
improvement and its iteration are not yet proved. The exact real-scale
convention and C-process also remain open. The integer m is not
identified with 2*Delta*N. Aggregate checklist states, the permanent
counterexample, corrected powering and all nine Add-est clauses
remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 895 production files, 1,369 scanned Lean
  files and 10,227 build jobs. The audit covers 7374 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13619 total).
  All 18 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-061935-4e284490.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_062253.log)
  and [manifest](../../logs/foundation_freeze_20260923_062253.json).
- All 1,390 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-bounded-bootstrap-20260923-061935-4e284490.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 335 nodes and 894 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos natural-scale maximal sixth moment — previous checkpoint

The global recurrence and its iteration are now proved for the actual
natural-scale quartic moment. The public source-facing consumer
`sargosQuartic_maximal_sixth_moment` proves:

```text
For every epsilon>0 there is C>=1, chosen before N,z,lambda,c,d,
such that for every natural N>=2, |z(n)|<=1 on N<n<=2N,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(0<=H<=N)|Sum_(N<n<=N+H) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The maximum, coefficients, integer prefixes and Bochner integrals
are the actual previously defined objects. No moment estimate,
recurrence, exponent iteration or epsilon-loss bound is assumed
in this final theorem.

The finite-scale bootstrap is optimized at
A=(1/4)*N^(-beta/(1+beta)). Its admissibility is proved uniformly,
including beta=0. Exact real-power identities give the improved
exponent beta/(1+beta). The global logarithm estimate

```text
(1+log x)^6 <= (1+6/epsilon)^6*x^epsilon,    x>=1, epsilon>0
```

discharges the loss without an eventual-threshold assumption.
`SargosSixthMomentExponent beta` records the actual
epsilon-quantified estimate, with the constant chosen before N.
`sargosSixthMomentExponent_step` proves the genuine implication
from beta to beta/(1+beta), and explicitly handles all small N.

The proved trivial exponent 3 initiates the sequence
beta_n=3/(1+3*n). Its exact recurrence and arbitrarily small values
yield `sargosSixthBaseMoment_subpolynomial`:
for every epsilon>0, I(N)<=C*N^epsilon for every natural N>=1.
The final weighted maximal theorem consumes this bound and the
completed source-height strip transfer, then absorbs its logarithm.
The stronger square-root initial estimate remains available.

Six modules are installed: `SargosSixthExponentAlgebra`,
`SargosSixthLogAbsorption`, `SargosSixthOptimizedBootstrap`,
`SargosSixthMomentExponents`, `SargosSixthMomentIteration`,
and `SargosSixthMomentTheorem`. All 15 public theorems have
exact-signature regressions and explicit axiom audits.
Fourteen additional fixtures check zero-exponent parameters,
exact successive exponents, logarithmic absorption at x=1,
iteration outputs, subpolynomial bounds and the actual weighted
maximal integral at the smallest permitted natural block N=2.

This is the natural-block form of the sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not yet replace natural block endpoints by arbitrary real
scales. That real-scale bridge, the exact real-scale Lemma 5
convention, and the C-process remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 901 production files, 1,375 scanned Lean
  files and 10,233 build jobs. The audit covers 7402 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13647 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-063351-3ad01f0f.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_063758.log)
  and [manifest](../../logs/foundation_freeze_20260923_063758.json).
- All 1,396 physical proof/configuration/tooling hashes are identical
  before and after both runners. The six modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-natural-sixth-theorem-20260923-063351-3ad01f0f.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 338 nodes and 897 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Robert–Sargos real-scale maximal sixth moment — previous checkpoint

The source-facing theorem `sargos_source_maximal_sixth_moment`
now proves the weighted maximal sixth-moment estimate at arbitrary
real scales, with the actual maximum over real endpoints:

```text
For every epsilon>0 there is C>=1, chosen before M,z,lambda,c,d,
such that for every real M>=2, |z(n)|<=1 on M<n<=2M,
lambda>0 and real c,d,

 Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
   Max_(M<X<=2M)|Sum_(M<n<=X) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*M^(3+epsilon)+M^epsilon).
```

The endpoint maximum is the supremum of the literal integer sums
over the real interval M<X<=2M. Its equality to a finite prefix
maximum and its attainment are proved, not assumed.
The coefficient condition is stated on the physical interval
M<n<=2M. The double integral is the actual Bochner integral.
No moment estimate or endpoint bridge is a hypothesis of the
final theorem.

With m=floor(M), the real block has m or m+1 terms. The literal
prefix comparison gives Max_real<=Max_natural+1, including the
possible extra upper-endpoint term. The sixth-power bound
Max_real^6<=32*(Max_natural^6+1) is integrated over the actual
rectangle; the constant contribution is exactly lambda.
Continuity and the needed product, inner and outer integrability
are proved. Monotonicity of real powers transfers the completed
natural-scale theorem from m to M and absorbs the extra lambda.
The final uniform constant is 32*(C_natural+1).

Seven modules are installed: `SargosRealQuarticBlock`,
`SargosRealQuarticPrefix`, `SargosRealQuarticRegularity`,
`SargosRealQuarticMomentTransfer`, `SargosRealSixthMomentTheorem`,
`SargosRealQuarticEndpoints`, and `SargosSourceSixthMoment`.
All 22 public theorems have exact-signature regressions and
explicit axiom audits. Fourteen additional fixtures check
integer and noninteger scales, the strict left and closed right
endpoints, both possible block lengths, zero prefixes, attained
real maxima, translated rectangles, zero-height integration and
the source theorem at M=5/2.

This realizes the source maximal sixth-moment theorem in
[Robert–Sargos Sections 3 and 7](https://arxiv.org/html/2307.03554v1#S7).
It does not claim the separate exact real-scale Lemma 5 convention,
nor Sargos's C-process. Those remain open. No aggregate checklist
item changes status. The permanent counterexample, corrected
powering and all nine repaired Add-est clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 908 production files, 1,382 scanned Lean
  files and 10,240 build jobs. The audit covers 7445 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13690 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-070029-00a8fc3c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_070350.log)
  and [manifest](../../logs/foundation_freeze_20260923_070350.json).
- All 1,403 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-sixth-theorem-20260923-070029-00a8fc3c.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 341 nodes and 901 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos initial-interval moments and uniform sextuple count — previous checkpoint

`sargos_initial_sextuple_count` proves the actual source count:

```text
For every epsilon>0 there is C>=1, chosen before N and c,
such that for every natural N>=1 and every real c,

 #{(n,n') in {1,...,N}^3 x {1,...,N}^3 :
     sum_i n_i^2 = sum_i n'_i^2,
     c <= sum_i n_i^4-sum_i n'_i^4 <= c+N^3}
 <= C*N^(3+epsilon).
```

Triples are literal functions from Fin 3 to the integer interval
1<=n<=N. Their square and fourth-power sums are integer sums;
ordered pairs retain all multiplicities. Both window endpoints
are closed. The theorem's constant is uniform in the real shift c.
This realizes [Sargos 2003, Lemma 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82873).

The stronger theorem `sargosInitialSextupleWindow_card_bound`
allows every positive width B and proves
card<=C*(N^3+B)*N^epsilon, uniformly in N,B,c.
No count estimate is assumed.

The initial-interval moment is also proved. The actual dyadic
decomposition separates {1,2} and the blocks (2^i,2^(i+1)].
A finite sixth-power inequality is integrated with all needed
integrability established. Literal zero-padding transfers an
arbitrary N to a power-of-two P with N<=P<=2N. The dyadic count's
sixth power is absorbed by a proved logarithmic/epsilon bound.
`sargosInitialQuartic_sixth_moment` gives, uniformly in bounded
coefficients and translated windows,

```text
Integral_(c<=alpha<=c+1, d<=gamma<=d+lambda)
 |Sum_(1<=n<=N) z(n)e(alpha*n^2+gamma*n^4)|^6
 <= C*(lambda*N^(3+epsilon)+N^epsilon).
```

The shift-uniform count does not assume a translation principle.
The shifted tent-kernel Gram identity is proved with its actual
character factor. Taking the norm of the integral bounds it by
the same central unshifted moment. The actual tuple-power
expansion and source-window inclusion then give the count.

Ten modules are installed: `SargosInitialInterval`,
`SargosInitialRegularity`, `SargosInitialMomentTransfer`,
`SargosInitialDyadicMoment`, `SargosInitialTruncation`,
`SargosInitialSixthMoment`, `SargosShiftedTentGram`,
`SargosShiftedNearCount`, `SargosInitialMomentTuples`,
and `SargosInitialSextupleCount`. All 33 public theorems have
exact-signature regressions and explicit axiom audits.
Eighteen additional fixtures cover empty and non-dyadic intervals,
zero-padding at and beyond the endpoint, dyadic decomposition,
zero-height integration, exact tuple multiplicities, empty and
closed-endpoint shifted windows, arbitrary real shifts, and
the actual N=1 and N=3 moment/count consumers.

The real-scale maximal moment remains complete. Sargos's
symmetric differencing inequality, Taylor-remainder assembly,
A-bar-four inequality and C-process remain open. The separate
exact real-scale Robert–Sargos Lemma 5 convention also remains
open. No aggregate checklist item changes status. Preserve
the permanent counterexample, corrected powering and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 918 production files, 1,392 scanned Lean
  files and 10,250 build jobs. The audit covers 7506 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13751 total).
  All 33 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-072955-0a22d012.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_073326.log)
  and [manifest](../../logs/foundation_freeze_20260923_073326.json).
- All 1,413 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-initial-sextuple-20260923-072955-0a22d012.json).

The evaluated owner HEAD is `cc0a4c4e05ac16ce8a5eba174ce075725cd34a78`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 344 nodes and 906 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos finite symmetric differencing — previous checkpoint

`sargos_finite_sextuple_differencing` now proves the actual finite
polynomial estimate. For arbitrary complex coefficients a and natural
1<=H<=M, let Phi be a on the integer interval 0<=m<M and zero elsewhere.
Set S=sum Phi(m), E=sum |Phi(m)|^2 and

```text
Q = sum_(t,t' in {1,...,H}^3, s2(t)=s2(t'))
      |sum_(0<=m<M)
         product_i Phi(m+t_i)Phi(m-t_i)
         * conjugate(product_i Phi(m+t'_i)Phi(m-t'_i))|.

|S|^12 <= 1492992*(M/H)^6*E^6
           + 382205952*(M^11/H^4)*Q.
```

All tuples are literal ordered triples, their square frequencies are
integer sums, and Q retains every square-diagonal sextuple and its
multiplicity. The theorem assumes no differencing estimate, Gram identity,
moment bound or analytic certificate.

The proof starts with actual even shifts, finite Cauchy and exact
parity fibers. The square is nonconjugated at this stage. Negative
offsets pair with positive offsets, leaving the actual diagonal term.
Zero-padding support and center translation are proved. A finite maximum
selects an actual parity fiber. Cubing expands into literal triples;
Holder and the exact frequency Gram identity give the sixth-power bound.
Conjugation appears between the two triples in that Gram identity.
Finally, the parity indicators are removed by a proved termwise majorant,
so the public endpoint has no parity witness or restriction.

This is the polynomial finite input corresponding to
[Sargos 2003, Section 3.2](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The paper's one-based interval convention has not yet been bridged in
this consumer. The exact printed Lemma 1 maximum is not claimed: the
proved parity-fiber variant supplies the downstream finite inequality
directly. The source index bridge, Taylor-remainder assembly, derivative
bounds, phase/support identification, witness selection, A-bar-four
inequality and C-process remain open. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Eleven modules are installed: `SargosSymmetricAveraging`,
`SargosSymmetricFibers`, `SargosSymmetricPositive`,
`SargosSymmetricSupport`, `SargosSymmetricDifferencing`,
`SargosFiniteFrequencyGram`, `SargosGroupedSecondMoment`,
`SargosSymmetricTriples`, `SargosSymmetricSixth`,
`SargosSymmetricTwelfth` and `SargosSextupleMajorant`.
All 42 public theorems have exact-signature regressions and explicit
axiom audits. Eighteen additional fixtures cover support endpoints,
empty intervals, odd/even parity fibers, genuinely nonconjugated
squaring, Gram conjugation, empty tuple types, diagonal multiplicities
and the actual H=1 and (M,H)=(3,2) consumers.

The completed shift-uniform sextuple count and real-scale maximal
sixth moment are preserved. No aggregate checklist item changes
status. Preserve the permanent counterexample, corrected powering
and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 929 production files, 1,403 scanned Lean
  files and 10,261 build jobs. The audit covers 7596 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13841 total).
  All 42 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-080954-241e9fff.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_081351.log)
  and [manifest](../../logs/foundation_freeze_20260923_081351.json).
- All 1,424 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eleven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-symmetric-differencing-20260923-080954-241e9fff.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 346 nodes and 909 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos source Taylor and interior reduction — previous checkpoint

`sargos_character_interior_differencing` proves a source-indexed
estimate for the actual character sum. For every epsilon>0 there is
C>=1, chosen before natural H>=1, M>=H and the real phase f, such that

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qinterior
    + C*M^11*H^epsilon.
```

Qinterior is the actual sum over all ordered pairs of triples in
{1,...,H}^3 with equal integer square sums. Each term is the norm
of the character sum over the open integer interval
(radius+1, M-radius), where radius is the maximum of all six
offsets. Its phase is exactly

```text
(s4(t)-s4(t'))/12 * f^(4)(m) + u(t,t',m),
u(t,t',m) = sum_i v(t_i,m) - sum_i v(t'_i,m).
```

The one-based source bridge is proved: sums, zero-padding, triples
and full sextuple correlations are translated exactly from the
previous zero-based finite theorem. No source-index convention
remains assumed in this consumer.

The actual symmetric residual v is defined from f(m+n)+f(m-n)
minus its constant, quadratic and quartic terms. Its degree-five
Taylor cancellation and genuine integral representation are proved:

```text
v(n,m) = (1/120) * integral_0^n
           [f^(6)(m+t)+f^(6)(m-t)]*(n-t)^5 dt.
```

Under local smoothness of the original phase on the actual segment,
the proved bound is |v(n,m)|<=B*n^6/360 when |f^(6)|<=B there.
Iterated derivatives commute with this constructed remainder.
The literal six-term residual satisfies
|u^(j)(m)|<=B*H^6/60 when the original (j+6)-th derivative is bounded
by B on the sextuple's actual maximum-offset segment. The local
radius theorem is obtained by an exact retyping of the same
coordinates; it does not enlarge the required phase domain.
A source-interior consumer uses only smoothness and original
derivative bounds inside (1,M).

The actual padded products have precisely the closed support
[radius+1,M-radius]. Their character phase, including conjugation
between the two triples and cancellation of the quadratic term,
is proved. Removing its endpoints costs at most two unit terms,
including empty, reversed and singleton intervals. The full
square-diagonal cardinality bound is proved from the earlier
width-general sextuple count, giving O_epsilon(H^(4+epsilon)).
This controls the aggregate boundary error in the displayed
interior estimate. No boundary smoothness or global remainder
extension is assumed.

These are the source-indexed polynomial differencing input and
local Taylor/phase steps for
[Sargos 2003, Sections 3.2–3.3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The global remainder extension, quartic-window witness/prefix
selection, A-bar-four theorem and C-process remain open.
The Taylor lemmas use local C-infinity hypotheses, as available
for the intended model phases; the paper's separate finite-C^k
formulation is not claimed complete. The separate exact real-scale
Robert–Sargos Lemma 5 convention also remains open.

Thirteen modules are installed: `SargosSourceDifferencing`,
`SargosSymmetricTaylor`, `SargosSymmetricTaylorJets`,
`SargosTaylorIntegral`, `SargosSymmetricTaylorIntegral`,
`SargosSextupleRemainder`, `SargosSextuplePhase`,
`SargosTupleSupport`, `SargosSourceSextuplePhase`,
`SargosSextupleRadiusJets`, `SargosSquareDiagonalCount`,
`SargosSextupleEndpoints` and `SargosInteriorDifferencing`.
All 50 public theorems have exact-signature regressions and
explicit axiom audits. Twenty additional fixtures check source
endpoints and translation, zero/constant/quartic/sextic Taylor
cases, the zero-height integral, derivative order zero, diagonal
phase cancellation, actual singleton/empty supporting intervals,
coincident/reversed endpoints, the H=1 count, and the actual
(M,H)=(3,2) interior consumer.

The earlier sixth moments, shifted sextuple count and finite
symmetric differencing are preserved. No aggregate checklist
item changes status. Preserve the permanent counterexample,
corrected powering and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 942 production files, 1,416 scanned Lean
  files and 10,274 build jobs. The audit covers 7702 target theorems,
  6,240 pinned-source theorems and five boundary anchors (13947 total).
  All 50 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-084446-824cd661.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_084836.log)
  and [manifest](../../logs/foundation_freeze_20260923_084836.json).
- All 1,437 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-source-taylor-20260923-084446-824cd661.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 350 nodes and 914 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos smooth remainder extension — previous checkpoint

`sargos_smooth_extended_reduction` constructs the smooth remainder
family used in the actual source-indexed finite reduction. For each
finite order Q and epsilon>0, one C>=1 is chosen before H, M, the
phase f and the original-derivative bound B. For 1<=H<=M, B>=0,
local C-infinity regularity on (1,M), and

```text
|f^(j+6)(y)| <= B/M^j   (y in (1,M), 0<=j<=Q+1),
```

the constructed physical extension U_q satisfies, for every actual
ordered sextuple q,

```text
U_q is globally C-infinity;
U_q(m) = u_q(m) at every integer radius+1 < m < M-radius;
|U_q^(j)(x)| <= C*B*H^6/(60*M^j)  (0<=x<=M, 0<=j<=Q).
```

Here u_q is the actual six-term symmetric Taylor remainder, not a
freely supplied function. The construction normalizes it as
u_q(M*x), proves the local affine derivative identity, and derives
its jets from the original phase. With l=(radius+1)/M,
r=(M-radius)/M and h=1/(8M), the actual nonempty integer support
proves l+4h<r. Every retained integer m has m/M in the agreement
plateau [l+2h,r-2h]. Both Taylor anchors lie within distance one
of the observation interval [0,1]. The existing Taylor-pasted
construction therefore gives genuine global smoothness and
uniform finite-order bounds, even as the buffer shrinks.
The zero branch is tied to an empty actual integer support.

Exact phase and sum identities replace u_q by U_q inside every
retained character sum, with all ordered sextuple multiplicities
unchanged. The assembled theorem also proves

```text
|sum_(1<=m<=M) e(f(m))|^12
 <= 1492992*(M/H)^6*M^6
    + 382205952*(M^11/H^4)*Qextended
    + C*M^11*H^epsilon.
```

Qextended is defined using the actual interior character sums
with phase (s4(t)-s4(t'))*f^(4)(m)/12+U_q(m).
The common C controls both the extension and the boundary error.
The original phase bounds are explicit narrower analytic inputs;
no global remainder certificate, extension existence, agreement
condition or final sum estimate is assumed.

This closes the C-infinity, finite-order uniform-constant extension
consumer. It does **not** close the printed finite-C^k,
constant-one remainder statement or the A-bar-four witness theorem
in [Sargos 2003, Section 3](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The construction uses original jets through Q+7. The physical
model-phase input still needs its consumer, followed by signed
quartic-window counting, witness/prefix selection, optimization
and the C-process. The separate exact real-scale Robert–Sargos
Lemma 5 convention also remains open.

Eight modules are installed: `SargosLocalAffineJets`,
`SargosRemainderLocalSmooth`, `SargosNormalizedRemainder`,
`SargosRemainderGeometry`, `SargosRemainderExtension`,
`SargosPhysicalRemainderExtension`, `SargosExtendedSextuplePhase`
and `SargosSmoothExtendedReduction`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Sixteen
additional fixtures check zero/negative affine scaling, the
M=0/1 buffer conventions, empty and singleton integer interiors,
exact agreement, zeroth derivatives, a genuinely nonzero sextic
remainder (-15120), zero original-phase bounds and an empty
actual correlation.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 950 production files, 1,424 scanned Lean
  files and 10,282 build jobs. The audit covers 7755 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14000 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-091416-0a8b1879.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_091748.log)
  and [manifest](../../logs/foundation_freeze_20260923_091748.json).
- All 1,445 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-remainder-extension-20260923-091416-0a8b1879.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 353 nodes and 920 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos actual transformed model — previous checkpoint

The actual approximate model phase now supplies the remainder
extension's original-derivative hypotheses. The finite budget
D(sigma,Q)=1+sum_(p<Q+7) modelPhaseJetCoefficient(sigma,p)
depends only on the fixed model parameter and requested order.
For a source phase T*F((A+x)/N), N<=A and A+M<=2N imply M<=N.
Closed-interval model data through order Q+6, with delta<=1,
therefore gives

```text
|f^(j+6)(x)| <= (D(sigma,Q)*|T|/N^6)/M^j
  (1<x<M, 0<=j<=Q+1).
```

Local regularity is derived inside the physical interval; no
exterior smoothness of F is assumed. The theorem
`sargos_model_smooth_reduction` consumes this real-scale source
phase in the constructed extension and finite sum reduction.

The transformed-model branch is proved for the natural full
dyadic block, f(x)=T*F(1+x/M), M>=1. Put
D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0 and
T1=tau*T*D4/M^4. The normalized fourth derivative is defined
using **within-derivatives on the closed interval [1,2]**.
Its smoothness, derivative composition, falling-factorial identity
and exact model-error scaling are proved at both endpoints,
giving parameter sigma+4 and error delta/D4.

The actual globally smooth extension U_q is rescaled as
U_q(M*(u-1))/T1 and added to this fourth-derivative model.
`sargosTransformedModel_approximate` proves that, for each
sigma>0 and finite P, one C>=1 chosen before all physical data
gives the closed-interval model error

```text
(delta + C*H^6/(tau*M^2))/D4.
```

The source model order is P+7, the extension order is P+1,
and tau,T are positive. The correction estimate consumes the
constructed remainder's actual jets. No transformed-model
predicate or global remainder bound is assumed.

Exact physical entry is proved, not just an exponent inequality:

```text
T1*G(1+x/M) = tau*f^(4)(x)+U_q(x)  (0<x<M).
```

The source sextuple phase and its character sum are identified
with this expression at every actual interior integer.
`sargos_positive_sextuple_model` sets tau to the actual positive
quartic difference divided by 12 and returns both the approximate
model and the exact source-sum identity. A further proved
inequality gives H^6/(tau*M^2)<=eta from tau>=H^3 and
H^3/M^2<=eta.

This is the actual-model input for
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Signed quartic-window counting, the general subinterval/real-scale
transformed-model bridge, witness/prefix selection, optimization
and the C-process remain open. The natural full-block transformed
consumer is not claimed to cover arbitrary real-scale subintervals.
The printed finite-C^k constant-one A-bar-four formulation and
separate exact real-scale Robert–Sargos Lemma 5 convention
also remain open.

Eight modules are installed: `SargosModelRemainderJets`,
`SargosModelSmoothReduction`, `SargosWithinDerivativeCalculus`,
`SargosFourthDerivativeModel`, `SargosPhaseCorrection`,
`SargosTransformedModel`, `SargosTransformedSource` and
`SargosPositiveSextupleModel`. All 26 public theorems have
exact-signature regressions and explicit axiom audits. Eighteen
additional fixtures cover the fourth coefficient at sigma=0,1,2,
both closed endpoints, the exact reference primitive, derivative
order zero, zero/constant/quadratic corrections, physical time
normalization, zero frequency, a genuine square-diagonal sextuple
with quartic difference 144, the large-frequency threshold and
an actual transformed reference-model consumer.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected powering, Heath–Brown energy relation,
optimization certificates and all nine repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 958 production files, 1,432 scanned Lean
  files and 10,290 build jobs. The audit covers 7821 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14066 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-094310-2a298bd0.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_095000.log)
  and [manifest](../../logs/foundation_freeze_20260923_095000.json).
- All 1,453 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-transformed-model-20260923-094310-2a298bd0.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 356 nodes and 926 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos real-scale source consumer — previous checkpoint

The transformed model now covers arbitrary admissible real scales
N>=1 and natural source windows [a,a+M] inside [N,2N].
There is no assumption that M is comparable to N. The original
physical phase is f(x)=T*F((a+x)/N), and its actual derivative
bounds retain N in every denominator.

The six-term Taylor remainder is normalized by N, extended with
the existing Taylor-pasting construction, and pulled back to a
globally smooth U_q. It agrees at every actual interior integer.
The proved jets hold on the two-sided physical observation
interval [-N,N], which is essential because N*u-a can be negative
even when u belongs to the canonical closed interval [1,2].
For each fixed model parameter and finite order, one constant
is chosen before all source scales, phases and sextuples.

With D4=sigma*(sigma+1)*(sigma+2)*(sigma+3)>0,
the actual transformed time and model are

```text
T1 = tau*T*D4/N^4,
G(u) = F^(4)_within(u)/D4 + U_q(N*u-a)/T1,
model error <= (delta + C*H^6/(tau*N^2))/D4.
```

All derivatives and model bounds on [1,2] include both closed
endpoints. The original source order is P+7, and the constructed
extension uses order P+1. No regularity of F outside its source
interval is assumed.

Both signs of the actual quartic difference are handled by
swapping the two ordered triples when necessary. This preserves
the radius and exact integer support, negates the actual source
phase, and conjugates its character sum. Its norm is therefore
unchanged. The oriented frequency is exactly the absolute
integer quartic difference, and tau=abs(difference)/12.
Orientation is not used to collapse the counting set: all ordered
sextuple multiplicities remain available to subsequent estimates.

The source-entry bridges are now explicit kernel-checked identities.
The original closed natural interval sum is its one-based integer
source sum plus one endpoint character, with norm loss exactly 1.
For each nonempty actual inner support, translation by a gives
the exact natural closed interval with endpoints
a+R+2 and a+M-R-1. Its dyadic scale conditions are derived from
N<=a and a+M<=2N. Empty supports are treated as the actual empty
sum, not substituted for nonempty source objects.

The public consumer `sargos_large_frequency_exponentPair_bound`
uses an existing genuine exponent pair (k,l), sigma>0 and epsilon>0.
It chooses delta>0, source order P>=1, eta>0 and C>=1 before
all physical inputs. For the original phase model, 1<=H<=M,
N>=1, N<=a, a+M<=2N, T>0 and

```text
tau = abs(actual quartic difference)/12 >= H^3,
H^3/N^2 <= eta,
```

it proves the actual interior source-sum norm is at most

```text
C*((T1/N)^(k+epsilon)*N^(l+epsilon) + N/T1).
```

The proof derives the transformed model error, both-sign identity,
natural interval and scale conditions, then invokes the existing
all-positive-height exponent-pair theorem. None of those bridges,
nor the desired transformed-sum bound, is an assumed certificate.
This is a consumer of an upstream exponent pair, not yet a proof
of the new C-transformed exponent pair.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
Remaining EPZAE-10 work is actual signed-window aggregation,
including the reciprocal-frequency term, finite C-process
assembly and optimization. The printed A-bar-four witness/prefix
selection, finite-C^k constant-one formulation and separate exact
real-scale Robert–Sargos Lemma 5 convention remain open.

Thirteen production modules are installed: `SargosScaledRemainder`,
`SargosScaledRemainderGeometry`, `SargosScaledRemainderExtension`,
`SargosScaledPhysicalRemainder`, `SargosScaledModelRemainder`,
`SargosAffinePhaseCorrection`, `SargosScaledTransformedModel`,
`SargosScaledTransformedSource`, `SargosSourceModelEntry`,
`SargosSextupleOrientation`, `SargosOrientedModelSource`,
`SargosInnerModelEntry` and `SargosLargeFrequencyModelBound`.
All 46 public theorems have exact-signature regressions and explicit
axiom audits. Twenty-two further fixtures cover non-integer scales,
negative physical arguments, correction derivatives, time scaling,
zero frequency, source singleton/endpoint behavior, an actual
positive and negative quartic difference, square-diagonal membership,
conjugation, empty and singleton inner supports, the genuine empty
extension branch and large-frequency error thresholds.

No aggregate checklist item changes status. The permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 971 production files, 1,445 scanned Lean
  files and 10,303 build jobs. The audit covers 7938 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14183 total).
  All 46 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-101936-e5b0e215.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_102331.log)
  and [manifest](../../logs/foundation_freeze_20260923_102331.json).
- All 1,466 physical proof/configuration/tooling hashes are identical
  before and after both runners. The thirteen modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-real-scale-source-20260923-101936-e5b0e215.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 360 nodes and 935 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Sargos finite closed-source inequality — previous checkpoint

The actual signed-frequency aggregation and finite C-process
inequality are proved. All ordered sextuple multiplicities are
retained; orienting a phase never replaces the counting set by
its image.

The small-frequency set has absolute quartic difference at most
12*H^3. It lies in the actual signed window [-12*H^3,12*H^3],
so the proved shifted-window theorem gives cardinality at most
C_epsilon*H^(3+epsilon). Its actual inner character sum has norm
at most M, derived from the literal integer support.

For large frequencies, the absolute difference is at most 3*H^4.
Every such sextuple is covered by an actual window

```text
j*H^3 <= abs(difference) <= (j+1)*H^3,
1 <= j <= 3*H.
```

The index is the natural floor of abs(difference)/H^3.
Each absolute window is contained in two actual signed windows.
The proved finite cover inequality permits overlapping endpoints
only through nonnegative overcounting; no disjointness or omitted
multiplicity is assumed. Each window's reciprocal contribution is
controlled by its actual count and 12/(j*H^3).
The harmonic-sum estimate and an explicit logarithmic-loss bound
therefore give

```text
sum_(large ordered sextuples) 12/abs(difference)
  <= C_epsilon * H^epsilon.
```

This avoids the extra factor H produced by using only the full
diagonal count and the lower frequency threshold.

The actual all-positive-height exponent-pair consumer is summed
over this set. The quartic frequency is explicitly linked to both
terms: tau<=H^4 controls the main term, while the exact identity
N/T1=(N^5/(D4*T))*(12/abs(difference)) supplies the secondary term.
The small and large sets form a proved disjoint partition of the
original square-diagonal set.

The public theorem `sargos_finite_closed_model_process` consumes
an actual exponent pair (k,l), sigma>0 and epsilon>0. It chooses
delta>0, P>=1, eta>0 and C>=1 before all physical inputs.
For the original model F, real N>=1, T>0, N<=a, a+M<=2N,
1<=H<=M and H^3/N^2<=eta, it proves

```text
norm(exponentialSumAt F T N a (a+M))^12
 <= C * H^epsilon *
    [ N^12/H
      + N^11*(D4*T*H^4/N^5)^(k+epsilon)*N^(l+epsilon)
      + N^16/(D4*T*H^4) ],
D4 = sigma*(sigma+1)*(sigma+2)*(sigma+3).
```

This is the exact original closed natural sum, not a generic
majorant or a separately assumed transformed estimate.
The proof consumes the actual full correlation bound and
twelfth-power differencing theorem, derives M<=N, and absorbs
the single endpoint character with a proved twelfth-power bound.

The source is
[Sargos 2003, Sections 3 and 6](https://www.impan.pl/shop/publication/transaction/download/product/82873).
The finite inequality is not yet the C-transformed exponent pair.
Actual integer-H selection, short-window and low-height branches,
epsilon bookkeeping and final exponent-pair assembly remain open.
The printed A-bar-four witness/prefix selection, finite-C^k
constant-one formulation and separate exact real-scale
Robert–Sargos Lemma 5 convention remain distinct open obligations.

Ten production modules are installed: `SargosFrequencyWindows`,
`SargosFrequencyWindowCover`, `SargosReciprocalFrequency`,
`SargosSmallFrequencyContribution`, `SargosFrequencyScaleBounds`,
`SargosLargeFrequencyContribution`, `SargosModelCorrelationBound`,
`SargosFiniteProcessAlgebra`, `SargosFiniteModelProcess` and
`SargosFiniteClosedProcess`.
All 26 public theorems have exact-signature regressions and explicit
axiom audits. Twenty additional fixtures cover zero/positive/negative
frequencies, actual large square-diagonal sextuples with quartic
difference plus or minus 2,108,304, their distinct ordered identities,
the correct width-H^3 bin and excluded adjacent bin, exact tau,
empty source support, zero weights and finite-scale arithmetic.

No aggregate checklist item changes status. Preserve the permanent
counterexample, corrected two-witness powering, Heath–Brown energy
relation, optimization certificates and all nine repaired Add-est
clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 981 production files, 1,455 scanned Lean
  files and 10,313 build jobs. The audit covers 7992 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14237 total).
  All 26 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-105350-e615b783.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_105812.log)
  and [manifest](../../logs/foundation_freeze_20260923_105812.json).
- All 1,476 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-sargos-finite-closed-process-20260923-105350-e615b783.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 363 nodes and 941 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(22 checked). The whole-proof goal remains open.

## Exact analytic C-process — previous checkpoint

EPZAE-10 is complete: the genuine analytic exponent-pair predicate is
preserved by all three exact A/B/C formulas. The new public theorem is

```text
ExponentPair.cProcess :
  ExponentPair k l ->
  ExponentPair (k/(12*(1+4*k)))
               ((11*(1+4*k)+l)/(12*(1+4*k))).
```

Its only mathematical input is the original exponent pair. It does not
assume a transformed estimate, optimized majorant or desired output pair.
The source formula is the C-process in the frozen paper's
`exp-process` lemma, citing
[Sargos 2003, Theorem 5](https://www.impan.pl/shop/publication/transaction/download/product/82873).

The proof now links every optimization variable to the original physical
parameters. With

```text
t0 = (5+15*k+5*l)/(2+3*k),
R = (T/N)^(-k/(1+4*k)) * N^((1+4*k-l)/(1+4*k)),
(Kc,Lc) = C(k,l),
```

Lean proves the exact balance identity and
`N^12/R = ((T/N)^Kc*N^Lc)^12`. In the high-height range
`N^t0 <= T`, the actual optimum satisfies
`R <= N^(2/3-1/100)` and `N^(13/3) <= T*R^3`.
A derived initial threshold makes the finite-process smallness and
secondary-term conditions hold. When `2 <= R <= M`, the proof selects
the actual natural integer `H = floor(R)`, proves `R/2 <= H <= R`,
and consumes `sargos_finite_closed_model_process` with every condition
discharged. The main and secondary terms, rounding loss and all epsilon
powers are bounded by the target twelfth power.

When `M < R` or `R < 2`, the literal closed source sum is controlled
by its actual `M+1` terms. For low heights `N <= T <= N^t0`,
three applications of the proved A-process to the genuine classical
pair `(1/2,1/2)` yield `(1/30,26/30)`; an exact threshold identity
compares its bound to the C-process target. Small N is absorbed into
a uniform constant, and reversed or singleton natural intervals are
handled with their actual source semantics.

`isExponentPairEstimateNonAsymptotic_cProcess` assembles all branches.
For every epsilon>0 and sigma>0, it chooses delta>0, derivative order
P>=1 and C>=1 before the phase, real scales and natural endpoints.
The existing non-asymptotic equivalence then gives
`ExponentPair.cProcess`. Neither a comparable-length source interval
nor a lower bound on k is imposed; k=0 remains included.

The printed A-bar-four witness/prefix-selection statement, its
constant-one finite-C^k formulation, and the separate exact real-scale
Robert–Sargos Lemma 5 convention are **not claimed as proved**.
They were previously listed as possible intermediate routes. The
implemented route instead uses the proved summed finite inequality and
the natural-rounded moment reduction. These unused stronger or
different-convention intermediates are not additional requirements of
EPZAE-10's unchanged acceptance test: the exact analytic C transformation
itself is now proved.

Fourteen production modules carry this final assembly:
`SargosCProcessParameters`, `SargosClassicalLowHeight`,
`SargosCProcessScale`, `SargosCProcessHighScale`,
`SargosCProcessLowComparison`, `SargosCProcessThresholds`,
`SargosCProcessIntegerChoice`, `SargosCProcessMainBalance`,
`SargosCProcessTrivialBranches`, `SargosCProcessMainError`,
`SargosCProcessBoundBudget`, `SargosCProcessTargetBudget`,
`SargosCProcessHighSource` and `ExponentPairCProcess`.
All 44 public theorems have exact-signature regressions and explicit
axiom audits. Another 22 fixtures check actual analytic output pairs
`(1/72,67/72)` and `(1/408,50/51)`, triangle boundaries, exact height
thresholds, zero-k scales, nonintegral rounding, empty/singleton source
intervals, zero epsilon and the low-height comparison.

Only EPZAE-10 changes aggregate status. EPZAE-11's D-process, remaining
beta-table rows, four advertised new pairs, zeta-growth/density bridges
and whole-project release remain open. These two auxiliary C-images
are not the four advertised `new-exp-pair` outputs.

Preserve the permanent counterexample, corrected two-witness powering,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 995 production files, 1,469 scanned Lean
  files and 10,327 build jobs. The audit covers 8,051 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,296 total).
  All 44 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-112323-d2b42d66.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_112654.log)
  and [manifest](../../logs/foundation_freeze_20260923_112654.json).
- All 1,490 physical proof/configuration/tooling hashes are identical
  before and after both runners. The fourteen modules and four
  integration files also have recorded normalized hashes. Full evidence
  is in the [checkpoint JSON](logs/tao-trudgian-yang-exact-c-process-20260923-112323-d2b42d66.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 365 nodes and 945 edges, with no duplicate/missing endpoints
or unclassified nodes. Of 42 aggregate checkbox states, only EPZAE-10
changes to checked (23 checked). Every other state is preserved.
The whole-proof goal remains open.

## Native Heath-Brown exponent-pair family — previous checkpoint

The complete native Heath–Brown family is now proved for every integer
k>=3, with the exact source formula:

```text
exponentPair_heathBrown :
  3 <= k ->
  ExponentPair (2/((k-1)^2*(k+2)))
               (1-(3*k-2)/(k*(k-1)*(k+2))).
```

The input is the natural derivative order, not an assumed exponent pair,
derivative theorem or optimization certificate. The proof consumes the
already kernel-checked native kth-derivative theorem through
`isExponentSumBoundNonAsymptotic_heathBrown`.
The source is Heath–Brown,
[A new k-th derivative estimate for exponential sums via Vinogradov's mean value](https://arxiv.org/abs/1601.04493),
Theorem 2 and its proof, as frozen locally at v3. The arbitrary source
epsilon is already represented in the actual beta/exponent-pair
definitions; no fixed positive epsilon is left in the public pair.

For alpha in (0,1/2], set tau=1/alpha. The proof constructs an actual
natural j>=3 satisfying

```text
((j-1)^2+1)/j <= tau <= (j^2+1)/(j+1).
```

The construction uses the least natural index with a sufficient upper
endpoint and proves the lower endpoint from minimality. It does not
assume a cover or an order-selection oracle. Exact adjacent identities
and decreasing secant slopes prove that the selected local secant lies
below every fixed family secant. All three actual derivative-error
exponents are bounded on the selected interval. The reciprocal-scale
identity links these exponents to the native beta bound.

At alpha=0, the proved beta endpoint supplies the result. The new
`exponentPair_of_beta_bound_half` uses the already-proved exact
reflection identity and the candidate slope condition l-k>=1/2 to
supply the other half of the closed unit interval. The family satisfies
the entire exponent-pair triangle, including all boundary requirements.
The existing closed duality theorem then gives the actual analytic
exponent pair.

The separate D-transform work is deliberately narrower:
`SargosDProcessGeometry` proves denominator positivity, triangle and
slope, exact zero/half endpoint gaps, and the secondary-line comparison.
`sargosDProcess_pair_of_beta_bound` is **conditional** on its explicitly
displayed source beta estimate. It derives an exponent pair using
half-interval duality when 5*k-3*l+2>=0 and k+3*l>=2.
It is not a proof of the analytic D-process, nor of the Bourgain input
pair. In particular, the source's maximum cannot be dropped without
checking the comparison conditions. The original D-process theorem
remains EPZAE-11 OPEN. Its cited primary paper,
[Sargos 1995, Theorem 7.1](https://doi.org/10.1112/plms/s3-70.2.285),
has not yet been obtained in full; publisher pages restrict access,
and the available database statement does not supply its analytic proof.

Seven production modules are installed: `BetaHalfDuality`,
`SargosDProcessGeometry`, `HeathBrownPairParameters`,
`HeathBrownPairSecants`, `HeathBrownPairTriangle`,
`HeathBrownPairLocalBound` and `HeathBrownExponentPairs`.
All 41 public theorems have explicit axiom audits and exact-signature
regressions. Another 24 fixtures exercise actual family pairs for
k=3,4,5,6,10; genuine A/B/C images; D's exact rational formula and
negative endpoint gaps; joined interval endpoints; both directions of
global secant comparison; the actual order-selection theorem; and beta
at zero and one half. These fixtures do not assert the missing
D-process estimate.

EPZAE-10 remains complete with exact A/B/C transformations. No aggregate
checkbox changes in this checkpoint. The remaining beta rows, four
advertised new pairs, zeta-growth/density outputs and final reproduction
remain open. The new family is an analytic input, not a claim that
`new-exp-pair` has been completed.

The permanent powering counterexample, corrected two-witness theorem,
Heath–Brown energy relation, optimization certificates and all nine
repaired Add-est clauses remain preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,002 production files, 1,476 scanned Lean
  files and 10,334 build jobs. The audit covers 8,108 target theorems,
  6,240 pinned-source theorems and five boundary anchors (14,353 total).
  All 41 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The full physical
  [extension log](logs/tao-trudgian-yang-build-20260923-114934-4d93bc9c.log) has zero errors,
  warnings, tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  The foundation covers 301 root-graph modules and two retained
  regression modules, with 7,636 explicit and 14,290 discovered
  theorem audits. See the [foundation log](../../logs/foundation_freeze_20260923_115307.log)
  and [manifest](../../logs/foundation_freeze_20260923_115307.json).
- All 1,497 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have recorded normalized hashes. Full evidence is in the
  [checkpoint JSON](logs/tao-trudgian-yang-heath-brown-family-20260923-114934-4d93bc9c.json).

The evaluated owner HEAD is `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 369 nodes and 955 edges, with no duplicate/missing endpoints
or unclassified nodes. All 42 aggregate checkbox states are unchanged
(23 checked). The whole-proof goal remains open.

## Large-value powering and subdivision — previous checkpoint

The source cardinality powering inequality is now proved by
`largeValueExponent_powering` for every natural k, including zero:

```text
1/2 <= sigma <= 1, tau >= 0
  -> LV(sigma,k*tau) <= k*LV(sigma,tau).
```

It consumes the actual cardinality witness of the corrected Lemma 62.
Neither fifth coordinate is constrained or scaled. The preserved singleton
pattern proves nonnegativity and the exact height-zero endpoint. A failed
uniform cardinality bound now yields genuine source patterns at unbounded
scales; their common compactness subsequence gives an actual energy-region
point with cardinality exponent above the failed candidate.
`isLargeValueBound_iff_region_cardinality` proves the full converse to the
existing region consumer. Infimum closure then supplies the exact
epsilon-loss boundary, not merely a strictly larger exponent.

`largeValueExponent_subdivision` proves both printed Huxley subdivision
inequalities for 0 <= tau <= tau'. Height enlargement preserves the actual
coefficients and ordinates. Subdivision sums actual localized patterns and
bounds the literal floor-bin count, with constants and radii selected
before the input pattern. Equal heights and height zero are included.
`isLargeValueBound_of_bounded_power_range` transfers a uniform bound from
the closed factor-two interval to every larger height.

`huxley_largeValueBound` and `largeValueExponent_le_huxley` now provide
the standalone uniform source bound
`LV(sigma,tau) <= max(2-2*sigma,4+tau-6*sigma)` on the full stated domain.
Their proof consumes `InCardinalityEnergyRegion.huxley_cardinality` through
the new actual-region converse. The powered Huxley estimate consumes the
corrected powering theorem. The mean-square exponent API and its short-height
and sigma=1 endpoint consequences consume the already-proved finite estimate.

Seven production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`LargeValueBoundClosure`, `LargeValueNonnegative`,
`LargeValueRegionWitness`, `LargeValuePowering`,
`LargeValueSubdivisionBounds`, `LargeValueElementaryBounds` and
`LargeValueHuxleyBound`. All 22 public theorem signatures have regressions;
16 further fixtures cover zero height/power, equal-height subdivision,
actual unchanged coefficients/ordinates, concrete mean-square/Huxley bounds
and an improved bound from the powered Huxley consumer.

EPZAE-18 remains OPEN: the random-sign/block lower bound and the resulting
exact sigma=1/2 identity still need their actual-pattern construction.
The standalone Huxley sub-obligation of EPZAE-19 is complete; the other
listed classical inputs remain open. No aggregate checkbox is changed.
The analytic D-process, remaining beta rows, four advertised new pairs,
zeta-growth/density outputs and whole-proof release obligations remain open.

The original Lemma 62 counterexample, corrected two-witness theorem,
Heath–Brown energy relation, exact optimization and all nine repaired
Add-est clauses remain unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,009 production files, 1,483 scanned Lean
  files and 10,341 build jobs. The audit covers 8,145 target theorems,
  6,240 pinned-source theorems and five anchors (14,390 total).
  All 22 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-121240-f22694a3.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_121607.log) and
  [manifest](../../logs/foundation_freeze_20260923_121607.json).
- All 1,504 physical proof/configuration/tooling hashes are identical
  before and after both runners. The seven modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-large-value-powering-20260923-121240-f22694a3.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 373 nodes and 967 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

## Exact square-root large-value exponent — previous checkpoint

`largeValueExponent_half` now proves the exact source endpoint
`LV(1/2,tau) = tau` for every tau>=0. It constructs genuine normalized
Dirichlet polynomials and one-separated ordinate sets; neither the desired
large-value bound nor an extremal-pattern family is an assumption.

The finite sign samples are a literal recursively enumerated list.
Multiplicities are retained even when different sign choices produce the
same value. Their second moment is exactly the sum of squared block
weights times the number of samples. Their fourth moment is at most
three times the squared variance times that number. Finite Cauchy–Schwarz
gives the explicit one-twelfth lower-tail count. Double counting selects
one common sample with many large evaluations, rather than a different
coefficient sequence at every ordinate.

The input coefficient vectors are actual singleton indicators on the
closed dyadic integer interval. The proof establishes their pointwise
normalization and the actual additive evaluation map, so the selected
sample supplies one coefficient function with norm at most one at every
integer. Unit modulus of the true negative-sign Dirichlet phases gives
the exact variance. The lattice consists of natural integers between zero
and floor(T); its one-separation, interval membership and cardinality are
proved explicitly.

`exists_half_largeValuePattern` constructs, for every integer N>=2 and
every real T>0, a full source pattern with scale N, physical height T,
threshold sqrt((N+1)/2), and T<=12*card(W).
Taking N=n+2 and T=N^tau gives actual unbounded-scale patterns.
Constant-factor logarithmic sandwiches prove the value exponent 1/2 and
cardinality exponent tau. The already-proved common compactness subsequence
then yields `exists_half_largeValueEnergyRegion`, with its cardinality
coordinate exactly tau. Every uniform candidate is at least tau, and the
existing separation upper bound supplies the reverse inequality.

Twelve production modules are root-imported, explicitly audited and
included in the PowerShell inventory behind
`run_tao_trudgian_yang_build.bat`:
`FiniteSignSamples`, `FiniteSignMoments`, `FiniteMomentSelection`,
`FiniteSignLargeValues`, `FiniteSignCoefficients`,
`FiniteIncidenceSelection`, `FiniteSignEvaluationMoments`,
`FiniteSignSelection`, `FiniteRandomCoefficients`,
`LargeValueRandomLattice`, `LargeValueRandomPattern` and
`LargeValueHalfExponent`.
All 28 public theorem signatures have regressions. Sixteen additional
fixtures cover empty and repeated sign samples, concrete moment estimates,
coefficient normalization, lattice endpoint counts, the nonnegative-height
guard, a genuine N=2/T=1/2 pattern, and the exact exponent/region statements
at zero, fractional and large heights.

EPZAE-18 remains OPEN only for the remaining general lower-bound
construction: for 1/2<sigma<=1 prove
`min(2-2*sigma,tau) <= LV(sigma,tau)`.
The sigma=1 and tau=0 endpoints already follow from nonnegativity; the
remaining substantive step is the coherent finite-block construction for
1/2<sigma<1. Full subdivision, corrected cardinality powering, zero-height
and upper-bound APIs stay proved. No aggregate checkbox changes here.

The analytic D-process, remaining beta rows, advertised new pairs,
remaining classical/zeta/density interfaces and final release obligations
remain open. The original counterexample and all nine repaired Add-est
clauses are preserved.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,021 production files, 1,495 scanned Lean
  files and 10,353 build jobs. The audit covers 8,193 target theorems,
  6,240 pinned-source theorems and five anchors (14,438 total).
  All 28 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-123925-4025ec63.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_124307.log) and
  [manifest](../../logs/foundation_freeze_20260923_124307.json).
- All 1,516 physical proof/configuration/tooling hashes are identical
  before and after both runners. The twelve modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-random-sign-half-exponent-20260923-123925-4025ec63.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 376 nodes and 973 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (23 checked). The whole-proof goal remains open.

## Complete elementary large-value calculus — previous checkpoint

EPZAE-18 is now complete. Its original acceptance test is unchanged:
subdivision, lower/L2 bounds, obvious bounds and raising to a power all
have actual uniform source-pattern proofs with coefficient normalization.
The full source labels are `hux-sub`, `lv-lower`, `l2-mvt` and
`power-lemma`.

The remaining general lower bound is now proved by
`largeValueExponent_lower`:

```text
1/2 <= sigma <= 1, tau >= 0
  -> min(2-2*sigma,tau) <= LV(sigma,tau).
```

This includes all closed endpoints and is stronger in domain than the
printed lower-bound clause for sigma>1/2. The separate sharp endpoint
`largeValueExponent_half` remains LV(1/2,tau)=tau for every tau>=0.
No Montgomery equality is asserted beyond the proved ranges.

The new proof uses q=floor(N/L) actual disjoint natural blocks
[N+j*L,N+(j+1)*L), all contained in the closed source support [N,2N].
Each block has exactly L indices, and q*L>=N/2.
The coefficient vectors are their actual indicators, with pointwise sum of
norms at most one. The unused remainder and the right endpoint may carry
zero coefficients; the source support and its closed convention are unchanged.

`dirichletPhase_block_variation` proves the actual negative-sign phase bound
from the exact complex exponential identity and log(n/a)<=n/a-1.
For 0<=t<=N/(2L), `largeValueBlock_sum_lower` gives norm(block sum)>=L/2.
Thus the literal block-family variance is at least N*L/8.
The finite common-sign selection theorem consumes this variance and proves
one normalized coefficient sequence, shared by all selected ordinates.

`exists_block_largeValuePattern` constructs a full source pattern for
every N>=2, 1<=L<=N and T>0, with

```text
V = sqrt(N*L/16);
min(T,N/(2L)) <= 12*card(W).
```

The choice L=floor(N^(2*sigma-1)) is justified by exact real/natural
inequalities, including its positive lower bound. It gives
N^sigma/8<=V<=N^sigma and
N^min(tau,2-2*sigma)<=24*card(W) when T=N^tau.
These constants are uniform and derived before choosing the physical
pattern. Along N=n+2 the time/value logarithmic exponents converge to
tau/sigma. An actual common energy-region subsequence supplies a cardinality
coordinate rho>=min(2-2*sigma,tau). The existing uniform-bound consumer
forces every candidate B to be at least this lower bound, and the exact
least-exponent definition supplies the public statement.

The source-completion map is:

| EPZAE-18 clause | Public consumer |
| --- | --- |
| Both subdivision inequalities | `largeValueExponent_subdivision` |
| General lower bound | `largeValueExponent_lower` |
| Sharp sigma=1/2 endpoint | `largeValueExponent_half` |
| L2 mean-square upper bound | `largeValueExponent_le_meanSquare` |
| Obvious upper bound | `largeValueExponent_le_tau` |
| Every natural power, including zero | `largeValueExponent_powering` |

Powering still consumes the corrected cardinality witness, including its
actual convolution, divisor normalization and dyadic selection chain.
It does not use a scaled fifth coordinate. Subdivision still uses actual
localized patterns and its literal floor-bin count.

`LargeValueElementaryCalculus` additionally assembles the exact known
equality ranges: tau<=2-2*sigma, the mean-square range tau<=1, and the
Huxley range tau<=4*sigma-2. `largeValueExponent_one` proves
LV(1,tau)=0 for every tau>=0 by the proved bounded-range powering consumer.

Ten production modules are root-imported and included in the PowerShell
inventory behind `run_tao_trudgian_yang_build.bat`:
`DirichletBlockPhase`, `FiniteBlockCoefficients`,
`LargeValueBlockGeometry`, `LargeValueBlockCoherence`,
`LargeValueBlockVariance`, `LargeValueBlockPattern`,
`LargeValueBlockExponents`, `LargeValueLowerPatterns`,
`LargeValueLowerBound` and `LargeValueElementaryCalculus`.
All 25 public theorem signatures have explicit audits and regressions.
Twenty additional fixtures exercise zero-length empty blocks, closed
support, uncovered remainders, exact floor endpoints, phase coherence at
the height boundary, actual region witnesses, lower-bound and equality
crossovers, sigma=1 at arbitrary height, and the distinct sharp
sigma=1/2 behavior.

EPZAE-18 is the only newly checked aggregate item.
EPZAE-19 remains OPEN for its other classical inputs; the architecture
now separates that obligation from the completed elementary calculus.
The analytic D-process, remaining beta rows, advertised new pairs,
remaining zeta/density interfaces and final release obligations stay open.
The permanent counterexample and all nine repaired Add-est clauses remain
unchanged.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,031 production files, 1,505 scanned Lean
  files and 10,363 build jobs. The audit covers 8,245 target theorems,
  6,240 pinned-source theorems and five anchors (14,490 total).
  All 25 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-130446-48e1dea6.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_131219.log) and
  [manifest](../../logs/foundation_freeze_20260923_131219.json).
- All 1,526 physical proof/configuration/tooling hashes are identical
  before and after both runners. The ten modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-elementary-large-values-20260923-130446-48e1dea6.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 381 nodes and 986 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. Only EPZAE-18 changes among the 42 aggregate
checkboxes (24 checked). The whole-proof goal remains open.

## Actual Type-I cardinality transfer — previous checkpoint

The cardinality side of `zero-from-large` now has a complete uniform
Type-I source consumer. This is a proved transfer from explicit upstream
`IsZetaLargeValueBound` hypotheses, not an unconditional zero-density
theorem. EPZAE-24 remains OPEN.

`cardinality_eq_sum_color_fibers` counts every fiber of the original finite
index type. `cardinality_le_color_count_mul` sums the corresponding bounds.
Equal ordinate values are never collapsed here. The two exact pattern
conversion theorems use proved one-separation to show that the finite
ordinate image has exactly the original index cardinality. Thus analytic
multiplicity is retained in the zero-copy domain until separation justifies
passing to an image.

`LargeValueUniformity` proves general and zeta compact-range uniformity.
A genuine finite open subcover chooses one constant and one positive
threshold window before the pattern. It includes finite-scale excursions
past both interval endpoints and lowers the actual threshold without
changing any coefficient or ordinate. The resulting bound is
`card(W) <= C*T^B*N^epsilon`.

The Type-I expanded slab [T/2,4T] is covered by three actual positive zeta
slabs. No ordinate translation or coefficient twist is used. Every color
fiber is counted, giving the literal factor 3. Actual Fourier deweighting
then supplies a bounded shifted ordinate for each original index.
The proved unit-bin occupancy estimate and parity/rank coloring separate
every shifted fiber.

The complete cardinality loss is

```text
K(d) = 3 * card(ZMod 2 x Fin(ceil(2d+2)+1))
     <= 24*(1+d).
```

It is linear in the displacement. If 0<=theta<eta and
d<=2*pi*T^theta, then eventually K(d)<=T^eta.
No energy upper bound, square/cube conversion or selection of only four
energy classes substitutes for counting all original indices.

`classicalTypeI_uniform_source_cardinality_bound` consumes the actual
sharp cutoff polynomial. Its positive threshold forces N<=6T;
the Fourier order, normalized threshold and all loss absorption are proved.
The zeta hypotheses select delta before the slightly shifted source line s
and threshold exponent D. The resulting bound is
`card(index type) <= C*T^(B+epsilon)`.

`classicalTypeI_uniform_source_class_cardinality_bound` applies this to a
literal Type-I branch/scale fiber of the shifted zero multiset. Its natural
scale is `2^r*floor(T^a)`, with the floor loss proved. Largeness and
one-separation follow from the genuine branch label and refined color.
No detached source-polynomial family or final class-count estimate is
assumed.

Nine production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`CardinalityPartition`, `ClassicalPatternCardinality`,
`LargeValueUniformity`, `ClassicalTypeICardinalityTransfer`,
`ClassicalTypeIFourierCardinality`, `ClassicalTypeICardinalityLoss`,
`ClassicalTypeICardinalityUniformity`, `ClassicalTypeISourceCardinality`
and `ClassicalTypeISourceClasses`.
All 15 public theorem signatures have regressions. Eighteen additional
fixtures cover empty/constant color fibers, analytic-copy multiplicity,
coincident-ordinate exclusion, all positive-slab boundaries, exact rounded
coloring costs and strict subpower absorption.

The source-cardinality theorem uses zeta hypotheses on [1,1/a] (or
[1,2/a] after the natural floor loss). It does not silently replace the
paper's final tau>=2 contract. Remaining: actual Type-II cardinality,
multiplicity-preserving slab/global assembly, the exact endpoint-two
reflection bridge and the sup/limsup density statement and corollaries.
No aggregate checkbox changes at this checkpoint.

EPZAE-18, the corrected cardinality/energy powering, the independent rho/k
and rho-star/k witnesses, the Heath--Brown energy relation, all nine repaired
Add-est clauses and the permanent singleton counterexample remain proved
and unchanged. Other classical, exponent-pair, zeta/density and release
obligations remain open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,040 production files, 1,514 scanned Lean
  files and 10,372 build jobs. The audit covers 8,269 target theorems,
  6,240 pinned-source theorems and five anchors (14,514 total).
  All 15 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-132951-4bd2396c.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_133317.log) and
  [manifest](../../logs/foundation_freeze_20260923_133317.json).
- All 1,535 physical proof/configuration/tooling hashes are identical
  before and after both runners. The nine modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-type-i-cardinality-20260923-132951-4bd2396c.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 386 nodes and 997 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.

## Actual endpoint-one cardinality-to-density transfer — current checkpoint

`isZeroDensityBound_of_uniform_largeValue_bounds` now proves the complete
intermediate cardinality transfer:

```text
1/2 < sigma < 1, B >= 0, tau0 > 0;
LV_zeta bound B*tau for every tau >= 1;
LV bound B*tau for every tau >= tau0
  -> IsZeroDensityBound sigma (B/(1-sigma)).
```

The conclusion uses the actual multiplicity-weighted symmetric zero
rectangle and the original epsilon--delta quantifier order. The large-value
predicates are explicit, genuinely upstream inputs, not assumed zero-count
or detector-family estimates. The source statement's stronger lower zeta
endpoint 2 remains an independent obligation. EPZAE-24 is still OPEN.

`ClassicalTypeIICardinalityPatterns` packages the actual sharp mollifier,
with its divisor majorant and exact normalized threshold. It proves that the
pattern ordinate count equals the complete original zero-copy class count.
The native factory discharges the coefficient majorant. The uniform
Type-II consumer chooses its threshold window before the source real-part
line and consumes the literal dyadic cutoffs, scale label, expanded height
and one-separation.

`ClassicalSlabCardinalityClasses` extracts the genuine shifted source
branch/scale for every zero. It refines this by all parity/rank colors.
The zero count is exactly the sum of the cardinalities of these fibers;
no selected four-class energy witness replaces this partition.
The outer cardinality cost obeys `K*T^(3*theta)`, with the actual local
analytic-multiplicity cap and both logarithmic dyadic counts accounted for.

`classicalSlabZeroCount_bound_of_uniform_largeValue_bounds` assembles the
Type-I and Type-II cardinality consumers. The source cutoff exponents,
real-part shift, Fourier displacement and threshold losses are selected in
the required dependency order. Empty branch labels have empty fibers.
The conclusion is an actual positive-slab estimate for
`zeroCountRect (sigma-delta) 1 T (2*T)`.

`ZeroCardinalityRestrictions` injects indexed subfamilies into containing
weighted zero sets without discarding copy numbers. Negative ordinates are
transported through the proved zero-copy conjugation equivalence, including
equality of analytic vanishing orders. The symmetric assembly counts every
signed dyadic color, retains the terminal partially occupied slab, and
absorbs the actual finite low-height zero count. The logarithmic number of
colors is bounded by any positive height power.

The final predicate follows by splitting the arbitrary epsilon loss between
the positive-slab estimate and symmetric assembly, then choosing one global
constant and a positive real-part shift. No root of an energy estimate, zero
count oracle or unproved polynomial family is used.

Eight production modules are root-imported, explicitly audited and included
in the PowerShell inventory behind `run_tao_trudgian_yang_build.bat`:
`ClassicalTypeIICardinalityPatterns`, `ClassicalTypeIICardinalityTransfer`,
`ClassicalSlabCardinalityClasses`, `ClassicalSlabCardinalityLoss`,
`ClassicalSlabCardinalityTransfer`, `ZeroCardinalityRestrictions`,
`ZeroCardinalityAssembly` and `ZeroCardinalityTransfer`.
All 14 public theorem signatures have regressions. Sixteen additional
fixtures check analytic-copy counts, empty weighted sets, both signed slab
boundaries and excluded exterior points, strict subpower losses, and actual
unconditional density consequences obtained by supplying the proved obvious
large-value bounds.

Remaining within EPZAE-24: the exact sup/limsup exponent formulation,
the source's zeta endpoint-two reflection reduction, and all source
corollaries. The current endpoint-one predicate is not a substitute for
that unchanged aggregate acceptance contract. No aggregate checkbox changes.

The permanent counterexample, corrected independent cardinality/energy
powering witnesses, Heath--Brown energy relation, all nine repaired Add-est
clauses and complete EPZAE-18 elementary calculus remain intact.
Other classical, exponent-pair, zeta/density and release obligations stay open.

Verification for this checkpoint:

- `cmd /c run_tao_trudgian_yang_build.bat --no-pause`: exit 0,
  `LEAN VERIFICATION PASS`; 1,048 production files, 1,522 scanned Lean
  files and 10,380 build jobs. The audit covers 8,286 target theorems,
  6,240 pinned-source theorems and five anchors (14,531 total).
  All 14 new public theorems occur exactly once in the explicit audit,
  with only permitted standard logical axioms. The complete
  [extension log](logs/tao-trudgian-yang-build-20260923-134332-f1498f0d.log) has zero errors, warnings,
  tactic suggestions and linter failures.
- `cmd /c run_lake_build.bat --no-pause`: exit 0, `PASS`;
  all six stages pass, with zero diagnostics and 8,857 build jobs.
  It covers 301 root modules and two retained regression modules,
  7,636 explicit and 14,290 discovered theorem audits.
  See the [foundation log](../../logs/foundation_freeze_20260923_134658.log) and
  [manifest](../../logs/foundation_freeze_20260923_134658.json).
- All 1,543 physical proof/configuration/tooling hashes are identical
  before and after both runners. The eight modules and four integration
  files also have normalized hashes in the
  [checkpoint evidence](logs/tao-trudgian-yang-endpoint-one-density-20260923-134332-f1498f0d.json).

Owner HEAD remains `f722da69a38a665f220a9e092b5d1f49460c7bd8`.
No agent commit or push was performed. All 509 protected tracked files
are byte-identical to HEAD. The counterexample retains SHA-256
`76301acb24e912c76557d9b02dce8a3f50cbb2c953d5578743a069d70949a487`.
The graph has 392 nodes and 1,011 edges with no duplicate or missing endpoints,
class conflicts or unclassified nodes. All 42 aggregate checkbox states
are unchanged (24 checked). The whole-proof goal remains open.
