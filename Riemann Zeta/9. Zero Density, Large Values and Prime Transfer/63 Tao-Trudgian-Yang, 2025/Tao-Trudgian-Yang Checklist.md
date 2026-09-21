# Tao--Trudgian--Yang 2025 checklist

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
  nine public energy-clause tables from the frozen blueprint. The underlying
  energy projection witnesses and pinned execution of the archived Python
  stack remain open, so this item is not complete.

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
- [ ] **EPZAE-10 -- A/B/C processes.** The three source transformations preserve
  exponent pairs with exact formulas.
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
  normalization.
- [ ] **EPZAE-19 -- Classical LV inputs.** Exact consumed Huxley, Jutila,
  Heath--Brown, twelfth-moment, and Bourgain interfaces are proved/imported.
  The native MHH finite estimate and Huxley cardinality constraints on actual
  energy regions are now proved in `ClassicalLargeValueRegions`, including
  full-domain height-padding removal and corrected cardinality powering.
  The standalone uniform Huxley `LV` API and the other listed inputs remain open.
- [x] **EPZAE-20 -- Guth--Maynard bridge.** The completed local theorem proves the
  exact `guth-maynard-lvt` interface after all convention conversions; no
  generic restatement is accepted as a bridge.
- [ ] **EPZAE-21 -- Zeta LV inputs.** Reflection, moment, and
  `LV_zeta = -infinity`/nonexistence statements used by density are proved.
  The clause-(i) energy consumer now accepts the exact uniform twelfth-moment
  LV predicate and proves all downstream rational and uniform-energy steps.
  The moment theorem remains open; the nearby
  Gafni--Tao twelfth-moment proposition is not a proved instance.
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
  That moment is unproved; other source parameters
  and zeta-LV inputs remain open, so EPZAE-21 is not closed.

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
- [ ] **EPZAE-36 -- Energy optimization certificates.** Every projection and
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
  Its actual-region/uniform consumers use the twelfth-moment cardinality
  bound, now derived from the dyadic critical-line moment hypothesis.
  `energyClauseOne_short_cubic_bound` now certifies the remaining short
  height comparison on the exact closed interval `0 ≤ τ ≤ 2`.
  The moment itself, the other eight clauses' projections,
  and the general reproduction gate remain open.
- [ ] **EPZAE-37 -- Nine new energy estimates.** Every clause of `Add-est` is
  proved on its exact interval and audited.
  Clause (i)'s general intermediate `imphb-lver-ineq` is proved on the exact
  two-piece sigma range and compact height interval, with a uniform extension.
  `energyClauseOne_of_dyadic_moment` now derives the complete short-zeta
  input from the genuine dyadic critical-line twelfth moment: proved
  cancellation below `3/2`, and short Perron entry plus cubic energy on
  `[3/2,2]`. This composes the corrected witnesses, Heath--Brown relation,
  exact general/zeta optimizations, and actual endpoint-one zero transfer.
  The moment is the sole analytic theorem parameter for clause (i).
  It remains unproved, so clause (i) is still incomplete. EPZAE-33's
  independent source endpoint-two theorem and the other eight clauses
  remain in the full completion contract.

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

Global dyadic assembly is now proved. The maximal phase-sum/Gram
estimate, the source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.
