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
  hypothesis alone. That moment is unproved; other source parameters
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
  The moment itself, the other eight clauses' projections,
  and the general reproduction gate remain open.
- [ ] **EPZAE-37 -- Nine new energy estimates.** Every clause of `Add-est` is
  proved on its exact interval and audited.
  Clause (i)'s general intermediate `imphb-lver-ineq` is proved on the exact
  two-piece sigma range and compact height interval, with a uniform extension.
  `energyClauseOne_of_dyadic_moment_and_short_zeta` now separates the two
  remaining analytic inputs: short zeta energy on `[1,2)` and the genuine
  dyadic critical-line twelfth moment. The zeta cardinality bound, uniform
  conversion, and energy deductions are proved from the latter; the
  general side is proved.
  Neither analytic input nor the endpoint-two reduction is discharged,
  so even clause (i) remains incomplete.

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
