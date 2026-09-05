# Gafni-Tao v1 paper-to-Lean crosswalk

Authoritative target: `Exceptional_Intervals.tex` from arXiv:2505.24017v1.

The source hash is recorded in `Sources/SHA256SUMS.txt`.

This crosswalk distinguishes four states:

- `DONE`: implemented in the release-root dependency path and represented on the central audit surface where source-sensitive.
- `CONDITIONAL`: the paper-level consumer is implemented, but it accepts named analytic inputs.
- `WORKBENCH PROVED`: a native theorem exists in Lean, but its module has not yet been promoted into `Extension/GafniTao.lean` and the central `Audit.lean`.
- `OPEN`: the required mathematical source input or publication-facing theorem has not yet been proved.

A declaration with a similar name does not close a source item unless its statement and dependency path match the source contract.

| Source item | Exact convention in the paper | Isolated Lean object | Status |
|---|---|---|---|
| Definition 1.1, `E_delta(X,theta)` | Lebesgue-measurable real `x in [X,2X]`; literal `x<n<=x+x^theta`; `Lambda` includes prime powers; discrepancy threshold `>= delta*x^theta` | `shortIntervalExceptionalSet`, `mangoldtShortSum`, `shortIntervalDiscrepancy`, `measurableSet_shortIntervalExceptionalSet` | DONE |
| `mu_delta(theta)` | Infimum of fixed exponents `xi` for one eventual `O_{delta,theta}(X^xi)` bound; no epsilon in the definition; value `-infinity` if eventually empty | `FixedPowerBound`, `leastFixedPowerExponent`, `exceptionalExponentDelta`, `exceptionalExponentDelta_eq_bot_of_eventually_empty` | DONE for the release-used interfaces |
| `mu(theta)` | Supremum over all positive exceptional thresholds | `exceptionalExponent`, `countableExceptionalExponent`, `exceptionalExponent_eq_countable` | DONE |
| `A(sigma)` | Least ordinary zero-density exponent in the epsilon-loss sense, with zero multiplicity | `ZeroDensityEnvelope`, `zeroDensityExponent`, `zeroCount`, `zeroCount_eq_weighted_sum` | DONE for the release-used source interfaces |
| `N*(sigma,T)` | Ordered four-tuples of zero occurrences with product analytic multiplicity and tolerance `|gamma1+gamma2-gamma3-gamma4|<=1` | `zeroAdditiveEnergyCount`, `resonantZeroQuadruples`, `zeroQuadrupleWeight`, `zeroAdditiveEnergyOccurrenceCount_eq` | DONE |
| `A*(sigma)` | Least epsilon-loss exponent for the actual multiplicity-weighted `N*` | `ZeroAdditiveEnergyEnvelope`, `zeroAdditiveEnergyExponent`, `zeroAdditiveEnergyExponent_le`, `zeroAdditiveEnergyEnvelope_of_zeroAdditiveEnergyExponent_lt` | DONE for the release-used source interfaces |
| Theorem 1.1, folklore theorem | Uniform ordinary density coefficient `A0`; all intervals for `theta>1-1/A0`; almost all for `theta>1-2/A0` | `gafniTaoTheorem11`, `GafniTaoTheorem11Conclusion`; native GM specialization `gafniTaoTheorem11_guthMaynard_native` in `Theorem11.lean` | WORKBENCH PROVED; release integration pending |
| Theorem 1.1, all-interval GM specialization | `A0=30/13`, hence threshold `theta>17/30` | `gafniTaoTheorem11_guthMaynard_allIntervals_regression` | WORKBENCH PROVED; release integration pending |
| Theorem 1.1, almost-all GM specialization | `A0=30/13`, hence threshold `theta>2/15`; one measurable exceptional set of natural density zero | `gafniTaoTheorem11_almostAll_guthMaynard_singleSet_native`, `gafniTaoTheorem11_guthMaynard_almostAll_regression` | WORKBENCH PROVED; release integration pending |
| Theorem 1.2, equation `muth` | Mandatory `inf_{epsilon>0}` over the ordinary density constraint; empty supremum handled literally; no continuity assumption | `ordinaryExceptionalUpperExponent`; native theorem `gafniTaoTheorem12_native` | WORKBENCH PROVED; release integration pending |
| Alternate ordinary upper-half form | `max(1-theta,...)` with the inner optimization restricted to the strict upper half strip | `upperHalfOrdinaryExceptionalUpperExponent`, `gafniTaoTheorem12_max_native`; conditional release theorem `gafniTaoTheorem12_max_conditional` | WORKBENCH PROVED natively; conditional form DONE in release root |
| Theorem 1.3, refined bound | Mandatory epsilon infimum with `min(mu_2,mu_4)` using the actual `A` and `A*` | `refinedExceptionalUpperExponent`, `refinedExceptionalUpperExponent_eq_source_formula`; native theorem `gafniTaoTheorem13_native` | WORKBENCH PROVED; release integration pending |
| Alternate refined upper-half form | `max(1-theta,...)` with strict-upper-half refined optimization | `upperHalfRefinedExceptionalUpperExponent`, `gafniTaoTheorem13_max_native`; conditional release theorem `gafniTaoTheorem13_max_conditional` | WORKBENCH PROVED natively; conditional form DONE in release root |
| Section 2 local cover | Cover `[X,2X]` by finitely many multiplicative local intervals at scale `delta/J` | `exists_local_multiplicative_cover_Ico`, `shortIntervalExceptionalSet_subset_local_union` | DONE |
| Brun-Titchmarsh replacement | `tau=X^(1-theta)`; replace `x^theta` by `x/tau` while controlling both length and Mangoldt-sum errors at the required local scale | local-entry and replacement chain in `ExceptionalEntry.lean` / `LocalCover.lean`; `eventually_local_replacement_total_le_third` | DONE |
| Explicit formula before equation (2.3) | `T=J(log X)^2 tau`; conventional zero-sum sign is harmless after absolute values | `sharpPsiTruncationBound_native`, `sharpTruncatedExplicitFormulaBound_native` | DONE |
| Equation (2.3), `targ` | Local exceptional event implies a large full zero-sum event | `eventually_localExceptionalSet_subset_equation27`, `eventually_localExceptionalMeasure_le_equation27` | DONE |
| Equation (2.4), `six` | Zero increment sum with analytic multiplicity and exact endpoint convention | `fullZeroIncrementSum`, `zeroStripIncrementSum`, `truncatedPsiZeroSum_sub_eq_fullZeroIncrementSum` | DONE |
| Equation (2.6), `eta-vanish` | Vinogradov-Korobov zero-free region at the physical height | Consumer bridge `vinogradovKorobovCountVanishing_of_rectangleZeroFree`; native source theorem `ford_asymptotic_zero_free_native` | WORKBENCH PROVED; release integration pending |
| Lemma 2.1 | Exponential right-edge decay using a logarithmic near-one density estimate and VK zero-free region | integrated `RightEdge.lean`, `RightEdgePhysical.lean`, `RightEdgeStrip.lean`; native near-one package in `PintzNearOneNative.lean` | CONDITIONAL consumer DONE; native inputs WORKBENCH PROVED |
| Lemma 2.2 | Exact physical `L-infinity` strip exponent using the actual zero count | `zeroStripPhysicalMajorant_epsilonBound`, `zeroStripPhysicalSup_le_majorant`, `zeroStripPhysicalSup_epsilonBound` | DONE |
| Lemma 2.3 | Smoothed logarithmic-variable second moment with complex Fourier transform and exact zero coefficients | `exists_complexifiedLogScaleBumpFourier_tenfold_decay`, `logarithmicZeroStripSecondMoment_eq_pair_sum`, `zeroStripPhysicalSecondMoment_epsilonBound` | DONE |
| Lemma 2.4 | Smoothed fourth moment using pair counting, Schur-type control, and the actual multiplicity-weighted `N*` | `zeroPairBinKernelSum_eq_differenceSum`, `zeroPairPairDecaySum_le_zeroAdditiveEnergyCount`, `logarithmicZeroStripFourthMoment_eq_pair_sum`, `zeroStripPhysicalFourthMoment_epsilonBound` | DONE |
| Equation (2.7), `targ-2` | Half-open strips; no zero on `Re rho=1`; right-edge, small-density, second-moment, and fourth-moment branches | `sum_halfOpenStripIncrementSum_eq_full`, `equation27StripMeasure_epsilonBound_of_second_or_fourth`, `equation27StripMeasure_epsilonBound_of_exponent_upper_bounds`, `equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs` | DONE as conditional release machinery |
| Section 2 epsilon/J limit | Remove finite-strip resolution and epsilon in the correct order; no continuity shortcut | `refinedExceptionalUpperExponent_eq_source_formula`, `exists_refined_limit_witness`, `equation27FullZeroMeasure_fixedPowerBound_of_refined_lt` | DONE |
| Section 2 local-to-global exceptional cover | Promote the local source-interval estimate to the actual exceptional set on `[X,2X]` | `localExceptionalMeasure_fixedPowerBound_of_source_inputs`, `exceptionalMeasure_le_sum_local`, `exceptionalMeasure_fixedPowerBound_of_source_inputs` | DONE |
| Frozen Guth-Maynard ordinary density input | Published exponent `15/(3+5 sigma)` and uniform coefficient `30/13` | `frozen_guthMaynard_zero_density`, `guthMaynard_zeroDensityEnvelope`, `frozen_uniform_thirty_thirteenths_zeroDensityEnvelope`, `zeroDensityExponent_le_thirty_thirteenths` | DONE |
| GM threshold arithmetic | `1-13/30=17/30` and `1-26/30=2/15` | `seventeen_thirtieths_eq_uniform_all_threshold`, `two_fifteenths_eq_uniform_almost_all_threshold` | DONE |
| Native VK source closure | Some positive Vinogradov-Korobov width is sufficient for the general GT theorem | `ford_asymptotic_zero_free_native : FordAsymptoticZeroFree` | WORKBENCH PROVED; release integration pending |
| Native sufficient near-one density | A logarithmic density theorem sufficient for the GT right-edge argument; exact optimized Ford `58.05/log^16` is not required for core closure | `exists_pintz_nearOne_log_density_native`; produces a native density package with log power `524` | WORKBENCH PROVED; release integration pending |
| Optimized Ford near-one density | Ford source-fidelity target with coefficient `58.05` and the older optimized logarithmic factor | `FordNearOneDensityEstimate` | OPEN as optimized/source-fidelity objective; no longer a blocker to native Theorem 1.3 |
| Optimized Ford zeta growth | Ford source theorem with constants `76.2`, `4.45`, and logarithmic exponent `2/3` | `FordZetaGrowthBound` | OPEN as optimized/source-fidelity objective |
| Optimized Ford Theorem 2 | Shifted exponential-sum theorem with constants `9.463` and `133.66` | `FordTheorem2` | OPEN as optimized/source-fidelity objective |
| Section 3 first source input | Heath-Brown three-cell four-zero energy envelope with exact endpoints | `HeathBrownZeroEnergyBounds` | OPEN |
| Section 3 first sample algebra | `theta=17/30`, critical `sigma=7/10`, Heath-Brown coefficient `235/39`, conclusion `7/12` | `heathBrown_second_at_seven_tenths`, `gafniTao_first_sample_arithmetic`, `refinedExceptionalUpperExponent_seventeen_thirtieths_le` | CONDITIONAL algebra PROVED; Heath-Brown source input OPEN |
| Section 3 second source input | Pintz cutoff forcing admissible `sigma<=23/24` in the sufficiently-small-Delta argument | `PintzTwentyThreeTwentyFourCutoff` | OPEN |
| Section 3 second sample algebra | Explicit sufficiently-small range and conclusion `mu(2/15+Delta)<=1-9Delta/13` | `second_sample_fixed_epsilon_bound`, `refinedExceptionalUpperExponent_two_fifteenths_add_le`; current explicit range `0<Delta<=1/100` | CONDITIONAL algebra PROVED; Pintz source cutoff OPEN |
| Full Section 3 best-known envelope | Exact source tables and finite optimization, if the full published curve is claimed | future certified optimizer and pinned source-table consumers | OPEN |

## Boundary and normalization ledger

- `zeroSet sigma T` is the frozen rectangle `zerosInRect sigma 1 (-T) T`.
- Distinct zero representatives are weighted by `analyticVanishingOrder`.
- Neither `N` nor `N*` is a distinct-zero count.
- The exceptional interval is closed at the global endpoints `X` and `2X`.
- The arithmetic interval is half-open: `x<n<=x+x^theta`.
- The local intervals introduced in Section 2 are derived localization objects and do not change Definition 1.1.
- `mu_delta` uses fixed-power eventual bounds.
- `A` and `A*` use epsilon-power bounds.
- These exponent notions remain deliberately distinct in Lean.
- Source exponent infima and suprema are represented in `EReal`, so an empty supremum is literally `bot`.
- No continuity assumption on `A` is used to remove the epsilon infimum.
- Analytic input status and release-integration status are separate.
- A theorem proved in a standalone workbench module is not described as release-complete until the module is imported through `GafniTao.lean` and represented in central `Audit.lean`.
- The optimized Ford contracts remain useful source-fidelity objectives, but the native Pintz/VK route now supplies sufficient inputs for the exact general Gafni-Tao theorem.
- The current publication-facing mathematical frontier is Section 3 source closure, principally `HeathBrownZeroEnergyBounds` and `PintzTwentyThreeTwentyFourCutoff`.