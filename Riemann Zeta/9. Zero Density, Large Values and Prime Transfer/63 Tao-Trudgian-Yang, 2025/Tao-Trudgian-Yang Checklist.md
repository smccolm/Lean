# Tao--Trudgian--Yang 2025 checklist

Current analytic progress: [Uniform smooth weights and stationary remainder bounds](#uniform-smooth-weights-and-stationary-remainder-bounds--current-checkpoint).
The actual transformed weight now has a smooth compactly supported zero-extension and uniform all-order derivative bounds for each fixed original cutoff. A proved quadratic remainder estimate gives O(N/T) physical stationary-mode errors, retaining the cutoff value and phase. Uniform lattice-dependent cutoff budgets, nonstationary modes and moving boundary bands remain open. The counterexample, corrected powering and all nine Add-est clauses are preserved; the full EPZAE-00--41 goal remains active.

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
- [ ] **EPZAE-09 -- Convexity and duality.** Convex closure and both directions of
  beta/exponent-pair duality are kernel-checked, including endpoints and beta
  reflection.
  Convex closure and exact two-way duality on the closed unit interval are now
  proved by `ExponentPair.convexCombination` and `exponentPair_iff_beta_bound`.
  Both exact endpoints beta(0)=0 and beta(1)=1/2 are now proved by
  `exponentSumGrowthExponent_endpoints`; the lower bound uses an actual
  coherent logarithmic sum. Only the full reflection identity remains open.
  Smooth inverse/Legendre phases, all-order compact model errors, common
  slope-image inclusion, anchored values and physical critical points are proved.
  DHC is now proved for canonical [1,2] extensions of retained compact
  windows, including finite charts and actual source model families.
  DBT (actual sum transformation, amplitudes and boundary control) remains
  an explicit open EPZAE-09/10 node.
- [ ] **EPZAE-10 -- A/B/C processes.** The three source transformations preserve
  exponent pairs with exact formulas.
  The classical analytic seed (1/2,1/2) is proved by `exponentPair_half_half`.
  This seed and its uniform estimate do not prove the general B transformation
  or close this process item.
- [ ] **EPZAE-11 -- Sargos D-process.** The beta bound is proved from the cited
  analytic theorem, then duality yields every D-derived exponent pair actually
  used downstream.
- [ ] **EPZAE-12 -- Heath--Brown derivative input.** The source kth-derivative
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
- [ ] **EPZAE-18 -- Elementary LV calculus.** Subdivision, lower/L2 bounds,
  obvious bounds, and raising-to-a-power are proved with uniform coefficient
  normalization. Actual-pattern subdivision and the uniform L2 upper
  bound are now proved in `LargeValueSubdivision` and `ClassicalMeanSquareBound`;
  the whole elementary-calculus acceptance test remains open.
- [ ] **EPZAE-19 -- Classical LV inputs.** Exact consumed Huxley, Jutila,
  Heath--Brown, twelfth-moment, and Bourgain interfaces are proved/imported.
  The native MHH finite estimate and Huxley cardinality constraints on actual
  energy regions are now proved in `ClassicalLargeValueRegions`, including
  full-domain height-padding removal and corrected cardinality powering.
  The genuine dyadic twelfth moment is now proved by `zeta_twelfth_dyadic`.
  The exact full-domain Jutila input is now proved by `jutila_largeValueBound`
  and `largeValueExponent_le_jutila`, with actual corrected-powering region
  consumers in `JutilaEnergyRegions`. The standalone uniform Huxley `LV`
  API and other listed inputs remain open; EPZAE-19 is not checked off.
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

## Uniform smooth weights and stationary remainder bounds — current checkpoint

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
