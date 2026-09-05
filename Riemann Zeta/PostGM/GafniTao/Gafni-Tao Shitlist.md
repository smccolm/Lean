# Gafni-Tao Shitlist

Status: implementation in progress.

This list is the exhaustive completion contract for the isolated Gafni-Tao program.

## Status rule

An item is crossed out only when its completion contract is satisfied at the release-package level.

For theorem items, that normally requires:

1. the exact intended public theorem exists;
2. its immediate mathematical source/dependency edge is demonstrated;
3. the theorem is imported through the intended release root;
4. the source-sensitive endpoint is represented in the central audit;
5. the isolated package build and audit pass;
6. the actual axiom output has been inspected.

Therefore:

- `[x]` means release-complete under the current contract.
- `[ ] WORKBENCH PROVED` means the mathematics exists in Lean but release-root promotion or central audit is still pending.
- `[ ] OPEN` means a mathematical source theorem or required consumer remains unproved.
- `[ ] PARTIAL` means substantial release-integrated infrastructure exists but the stated completion test has not yet been fully met.

---

- [x] **GT-00 - Isolation and source freeze.**  
  Separate Lake package exists under `PostGM/GafniTao/Extension`; the frozen Guth-Maynard foundation is pinned and consumed read-only; the Gafni-Tao source snapshot and source hashes are maintained separately.

- [ ] **GT-01 - Exact source crosswalk.** `SYNC IN PROGRESS`  
  Maintain exact mappings for Definition 1.1, `mu_delta`, `mu`, `A`, `N*`, `A*`, Theorems 1.1-1.3, Section 2 local entry, equations (2.3)-(2.7), Lemmas 2.1-2.4, the two Section 3 samples, and all source inputs actually consumed.  
  Current state: the Crosswalk has been substantially synchronized with the present theorem state.  
  Completion test: perform the final source-to-Lean review after native-core promotion and Section 3 closure.

- [ ] **GT-02 - Asymptotic/exponent language.** `PARTIAL, RELEASE-INTEGRATED`  
  Implement source-faithful `EReal` least/supremum exponents plus usable envelope predicates:
  - fixed-power eventual bounds for `mu_delta`;
  - epsilon-power bounds for `A`;
  - epsilon-power bounds for `A*`;
  - empty-supremum behavior;
  - positive-threshold countable diagonalization;
  - limiting lemmas used by the source theorem.
  
  Current state:
  - `leastFixedPowerExponent` infrastructure is audited;
  - epsilon-exponent interfaces are audited;
  - `exceptionalExponent_eq_countable` is audited;
  - `refinedExceptionalUpperExponent_eq_source_formula` is audited;
  - the exact finite-strip-to-source limit is audited.
  
  Completion test still requires a final review that every intended converse/interface in the public contract is present and no unused gap remains.

- [x] **GT-03 - Exceptional set.**  
  Exact Mangoldt discrepancy on `(x,x+x^theta]`, subset of `[X,2X]`, Lebesgue measurability, finite measure, `mu_delta`, and `mu` are implemented.  
  The public definition is not a sampled/cardinality proxy.

- [x] **GT-04 - Multiplicity-weighted zero model.**  
  The frozen zero-count model is bridged to finite zero sums weighted by `analyticVanishingOrder`.  
  Strip localization, symmetry, boundary conventions, and physical zero-sum consumers are integrated and centrally audited.

- [x] **GT-05 - Exact `N*` and `A*`.**  
  The tolerance-one four-zero additive energy is defined with ordered zero occurrences and product analytic multiplicity.  
  `zeroAdditiveEnergyOccurrenceCount_eq` provides the occurrence-count bridge.  
  `ZeroAdditiveEnergyEnvelope` and `zeroAdditiveEnergyExponent` provide the exponent interface.  
  No distinct-ordinate surrogate or unrelated additive-energy object replaces the source quantity.

- [x] **GT-06 - Chebyshev interval bridge.**  
  The real-endpoint von Mangoldt interval sum is connected exactly to the difference of `Chebyshev.psi`, including endpoint convention and prime powers.  
  Central audit includes `mangoldtIntervalSum_eq_psi_sub`.

- [x] **GT-07 - Local cover and Brun-Titchmarsh replacement.**  
  The finite multiplicative cover of `[X,2X]`, local scale, replacement of `x^theta` by `x/tau`, and the required error ledger are implemented.  
  Central audit includes the local cover, replacement bounds, and global exceptional-set union.

- [x] **GT-08 - Sharp truncated explicit formula.**  
  The paper's required sharp formula is proved natively, including:
  - nontrivial-zero multiplicities;
  - sign convention;
  - pole and residue terms;
  - horizontal and vertical contour edges;
  - selected heights;
  - boundary transition;
  - arbitrary real endpoints;
  - physical range `2 <= T <= x`.
  
  Public native endpoints include:
  ```lean
  GafniTao.sharpPsiTruncationBound_native
  GafniTao.sharpTruncatedExplicitFormulaBound_native
  ```

- [ ] **GT-09 - Vinogradov-Korobov zero-free region.** `WORKBENCH PROVED`  
  The release root contains and audits the complete consumer bridge from a pointwise/rectangle zero-free theorem to count vanishing.  
  The workbench now contains:
  ```lean
  GafniTao.ford_asymptotic_zero_free_native :
    FordAsymptoticZeroFree
  ```
  derived from the qualitative global zeta-growth theorem and the five-frequency detector.
  
  Remaining completion step:
  - import the native source theorem through `GafniTao.lean`;
  - add it to central `Audit.lean`;
  - run and inspect the release audit.

- [ ] **GT-10 - Near-one logarithmic zero density.** `WORKBENCH PROVED FOR THE CORE GT ROUTE`  
  The workbench contains:
  ```lean
  GafniTao.exists_pintz_nearOne_log_density_native
  ```
  which supplies a logarithmic near-one density theorem sufficient for the right-edge argument, together with native VK count vanishing.
  
  The native route uses a larger coefficient/logarithmic power than the older optimized Ford `58.05/log^16` objective but is sufficient for exact Theorems 1.3 and 1.2.
  
  Remaining completion step:
  - promote the native sufficient package into the release root and central audit.
  
  Separate source-fidelity objective:
  - the optimized `FordNearOneDensityEstimate` remains open and is no longer a blocker to the core Gafni-Tao theorem.

- [x] **GT-11 - Lemma 2.1.**  
  The release-integrated right-edge machinery assembles logarithmic density and Vinogradov-Korobov count vanishing into the physical stretched-exponential right-edge decay.  
  Central audit covers the cumulative-count integral, VK decay, physical cutoff, and final right-edge zero-sum estimates.
  
  The consumer theorem is complete.  
  Native discharge of its analytic input hypotheses is tracked separately under GT-09 and GT-10.

- [x] **GT-12 - Lemma 2.2.**  
  The exact physical `L-infinity` strip estimate is implemented using the actual zero count and physical `X`, `T`, and `tau` relations.  
  Central audit includes:
  ```lean
  GafniTao.zeroStripPhysicalMajorant_epsilonBound
  GafniTao.zeroStripPhysicalSup_le_majorant
  GafniTao.zeroStripPhysicalSup_epsilonBound
  ```

- [x] **GT-13 - Fourier-bump infrastructure.**  
  Fixed bump, complexification, compact support, polynomial/Fourier decay, and the required zero-coefficient estimates are implemented and audited.

- [x] **GT-14 - Lemma 2.3.**  
  The normalized `L2` integral estimate is proved using the actual multiplicity-weighted zero count and the source density exponent.

- [x] **GT-15 - Smoothed quadruple-to-energy bridge.**  
  Pair-count identities and the Schur/decay estimate are proved against the actual GT `N*` object with multiplicity.

- [x] **GT-16 - Lemma 2.4.**  
  The normalized `L4` integral estimate is proved using the actual `A*` exponent.

- [x] **GT-17 - Equation (2.7).**  
  The exact finite-strip argument is implemented:
  - half-open strips;
  - upper-boundary accounting;
  - no zero on `Re s=1`;
  - small-density eventually-empty branch;
  - right-edge branch;
  - second-moment Markov branch;
  - fourth-moment Markov branch;
  - strip union and measure sum.
  
  Central audit includes:
  ```lean
  GafniTao.sum_halfOpenStripIncrementSum_eq_full
  GafniTao.equation27StripMeasure_epsilonBound_of_second_or_fourth
  GafniTao.equation27StripMeasure_epsilonBound_of_exponent_upper_bounds
  GafniTao.equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
  ```

- [x] **GT-18 - Limit assembly.**  
  The full exponent ledger and finite-strip limit are implemented without assuming continuity of `A`.
  
  Central audit includes:
  ```lean
  GafniTao.refinedExceptionalUpperExponent_eq_source_formula
  GafniTao.exists_refined_limit_witness
  GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
  GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
  GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
  ```

- [ ] **GT-19 - Gafni-Tao Theorem 1.3.** `WORKBENCH PROVED`  
  The workbench now contains:
  ```lean
  GafniTao.gafniTaoTheorem13_native
  ```
  with:
  ```lean
  exceptionalExponent theta ≤ refinedExceptionalUpperExponent theta
  ```
  for `0 < theta < 1`.
  
  It supplies internally:
  - the frozen GM smooth cutoff;
  - `sharpTruncatedExplicitFormulaBound_native`;
  - the native Pintz near-one density package;
  - the native VK zero-free input.
  
  The workbench also contains:
  ```lean
  GafniTao.gafniTaoTheorem13_max_native
  ```
  
  Remaining completion step:
  - import `NativeTheorems.lean` through the release root;
  - add native endpoints to central `Audit.lean`;
  - build and inspect the release dependency output.

- [ ] **GT-20 - Theorems 1.2 and 1.1.** `WORKBENCH PROVED`  
  Exact native Theorem 1.2 exists:
  ```lean
  GafniTao.gafniTaoTheorem12_native
  ```
  
  The alternate upper-half form exists:
  ```lean
  GafniTao.gafniTaoTheorem12_max_native
  ```
  
  The complete native Guth-Maynard specialization of Theorem 1.1 exists:
  ```lean
  GafniTao.gafniTaoTheorem11_guthMaynard_native
  ```
  
  Its conclusion includes:
  - all intervals above `17/30`;
  - almost all intervals above `2/15`;
  - one measurable exceptional set of ordinary natural density zero.
  
  Remaining completion step:
  - promote `NativeTheorems.lean`, `Theorem11.lean`, and their dependencies into the release root and central audit.

- [ ] **GT-21 - Native GM consumer.** `WORKBENCH PROVED, RELEASE PROMOTION PENDING`  
  The release root already audits:
  ```lean
  GafniTao.guthMaynard_zeroDensityEnvelope
  GafniTao.zeroDensityExponent_le_guthMaynard
  GafniTao.frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
  GafniTao.zeroDensityExponent_le_thirty_thirteenths
  GafniTao.seventeen_thirtieths_eq_uniform_all_threshold
  GafniTao.two_fifteenths_eq_uniform_almost_all_threshold
  ```
  
  The workbench native Theorem 1.1 consumes the actual frozen GM envelope at `A0=30/13`.
  
  Remaining completion step:
  - promote the public native Theorem 1.1 endpoint into the release root/audit.

- [ ] **GT-22 - Published exponent inputs.** `OPEN`  
  Source-facing predicates are defined:
  ```lean
  GafniTao.PintzFirstDensitySegment
  GafniTao.PintzTwentyThreeTwentyFourCutoff
  GafniTao.HeathBrownZeroEnergyBounds
  ```
  
  Remaining mathematical work:
  - prove the Pintz `23/24` cutoff from the pinned source;
  - prove the Heath-Brown three-cell multiplicity-weighted `A*` envelope;
  - if the full best-known curve is claimed, formalize every additional pinned source segment used by the optimizer.

- [ ] **GT-23 - Exact native sample bounds.** `CONDITIONAL ALGEBRA PROVED`  
  First sample target:
  ```math
  \mu\!\left(\frac{17}{30}\right)
  \le
  \frac{7}{12}
  ```
  
  The exact refined-exponent algebra is proved in:
  ```lean
  GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le
  ```
  conditional on:
  ```lean
  HeathBrownZeroEnergyBounds
  ```
  
  Second sample target:
  ```math
  \mu\!\left(\frac{2}{15}+\Delta\right)
  \le
  1-\frac{9\Delta}{13}
  ```
  
  The workbench proves the refined-exponent bound on the explicit range:
  ```math
  0<\Delta\le\frac{1}{100}
  ```
  through:
  ```lean
  GafniTao.refinedExceptionalUpperExponent_two_fifteenths_add_le
  ```
  conditional on:
  ```lean
  PintzTwentyThreeTwentyFourCutoff
  ```
  
  Completion requires GT-22 source closure plus composition with the native Theorem 1.3.

- [ ] **GT-24 - Section 3 certification.** `OPEN`  
  Pin the exact numerical/source-table inputs required by any claimed full curve.
  
  If publishing the full optimizer:
  - reproduce the relevant piecewise formulas;
  - reduce the optimization to exact finite cells;
  - kernel-check each cell;
  - treat floats and plots as display/checking tools only.

- [ ] **GT-25 - Integrity and coverage.** `ACTIVE`  
  Current release root:
  ```text
  Extension/GafniTao.lean
  ```
  still stops before the native core and Section 3 workbench.
  
  Required promotion includes, at minimum:
  ```text
  FordAsymptoticZeroFree
  PintzNearOneNative
  NativeTheorems
  Theorem11
  ```
  
  Section 3 modules should be promoted as their source inputs close.
  
  Completion requires:
  - every production module imported by the isolated root;
  - public/source-sensitive theorems in central `Audit.lean`;
  - full isolated build;
  - forbidden-token scan;
  - actual axiom-output inspection;
  - zero release-runner errors;
  - frozen GM boundary unchanged.

- [ ] **GT-26 - Documentation and reproduction.** `ACTIVE`  
  Synchronize:
  ```text
  README.md
  Gafni-Tao Architecture.md
  Gafni-Tao Research Agenda.md
  Gafni-Tao Crosswalk.md
  Gafni-Tao Shitlist.md
  Gafni-Tao Sources.md
  audit report
  command logs
  ```
  
  Current state:
  - README synchronized to the workbench/release distinction;
  - Architecture synchronized to the current frontier;
  - Crosswalk and Shitlist substantially synchronized by this revision;
  - Research Agenda still requires the same native-core/Section-3 phase update;
  - final reproduction logs remain pending.
  
  Do not run `push_to_github.bat` without explicit owner instruction.

---

# Optimized Ford source-fidelity objectives

The following remain worthwhile mathematical/source-fidelity objectives but are no longer blockers to the exact native core Gafni-Tao theorem:

- [ ] `FordTheorem2` with optimized constants `9.463` and `133.66`.
- [ ] `FordZetaGrowthBound` with optimized constants `76.2` and `4.45`.
- [ ] `FordNearOneDensityEstimate` with coefficient `58.05` and the optimized logarithmic factor.

The native Pintz/VK route now supplies sufficient source inputs for `gafniTaoTheorem13_native`.

These objectives should not be confused with GT-22, which contains the still-required Section 3 published inputs.

---

# Current completion picture

## Release-complete infrastructure

The following numbered stages are now crossed out:

```text
GT-00
GT-03
GT-04
GT-05
GT-06
GT-07
GT-08
GT-11
GT-12
GT-13
GT-14
GT-15
GT-16
GT-17
GT-18
```

## Mathematically proved in the workbench, release promotion pending

```text
GT-09
GT-10
GT-19
GT-20
GT-21
```

## Still mathematically open

```text
GT-22
GT-23
GT-24
```

## Project/release gates still active

```text
GT-01
GT-02
GT-25
GT-26
```

---

# Overall completion test

The project is complete only when the publication-facing theorem path is promoted through the isolated release root and central audit, and the required source-facing Section 3 conclusions are closed.

The final target remains:

```text
exact native Theorem 1.3
        |
        v
exact native Theorem 1.2
        |
        v
native Theorem 1.1
        |
        +-----------------------------+
        |                             |
        v                             v
mu(17/30) <= 7/12       small-positive-Delta sample
```

with:

```text
Heath-Brown source input
Pintz Section 3 cutoff
```

proved rather than assumed.

A workbench theorem, conditional wrapper, numerical plot, focused build, or locally audited module is not by itself the whole publication-facing release.