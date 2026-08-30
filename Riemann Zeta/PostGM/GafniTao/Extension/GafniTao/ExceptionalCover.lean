import GafniTao.LimitAssembly

/-!
# From one multiplicative interval back to `[X,2X]`

The Gafni--Tao source first proves a uniform estimate on intervals
`[Y,(1+delta/J)Y)` and then covers `[X,2X]` by finitely many such intervals.
This file performs that last measure-theoretic and fixed-power transfer with
the exact cover cardinality visible.
-/

open Filter Set
open scoped ENNReal BigOperators

namespace GafniTao

theorem tendsto_localCoverLeft_atTop
    {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun X : ℝ => localCoverLeft X u k) atTop atTop := by
  have hc : 0 < 1 + (k : ℝ) * u := by positivity
  have hmul : Tendsto (fun X : ℝ => (1 + (k : ℝ) * u) * X) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id
  apply hmul.congr'
  exact Eventually.of_forall fun X => by
    unfold localCoverLeft
    ring

/-- A fixed-power estimate remains fixed-power after evaluating it at one
of the finitely many multiplicative cover left endpoints. -/
theorem FixedPowerBound.comp_localCoverLeft
    {f : ℝ → ℝ} {xi u : ℝ} (h : FixedPowerBound f xi)
    (hu : 0 ≤ u) (k : ℕ) :
    FixedPowerBound (fun X => f (localCoverLeft X u k)) xi := by
  rcases h with ⟨C, hC, hBound⟩
  let c : ℝ := 1 + (k : ℝ) * u
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨C * c ^ xi, mul_pos hC (Real.rpow_pos_of_pos hc xi), ?_⟩
  have hAtTop := (tendsto_localCoverLeft_atTop hu k).eventually hBound
  filter_upwards [hAtTop, eventually_gt_atTop (0 : ℝ)] with X hBoundX hX
  calc
    |f (localCoverLeft X u k)| ≤
        C * (localCoverLeft X u k) ^ xi := hBoundX
    _ = (C * c ^ xi) * X ^ xi := by
      have hleft : localCoverLeft X u k = c * X := by
        dsimp [c]
        unfold localCoverLeft
        ring
      rw [hleft, Real.mul_rpow hc.le hX.le]
      ring

/-- Exact finite cover inclusion for the genuine exceptional set. -/
theorem shortIntervalExceptionalSet_subset_local_union
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hX : 0 < X) (hdelta : 0 < delta) :
    shortIntervalExceptionalSet delta X theta ⊆
      ⋃ k ∈ Finset.range (⌈1 / (delta / (J : ℝ))⌉₊ + 1),
        localShortIntervalExceptionalSet J theta delta
          (localCoverLeft X (delta / J) k) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hu : 0 < delta / (J : ℝ) := div_pos hdelta hJr
  intro x hx
  obtain ⟨k, hk, hxLower, hxUpper⟩ :=
    exists_local_multiplicative_cover_Ico hX hu hx.1
  rw [Set.mem_iUnion]
  refine ⟨k, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
  exact ⟨⟨hxLower, hxUpper⟩, hx.2⟩

theorem localShortIntervalExceptionalSet_subset_sourceInterval
    (J : ℕ) (theta delta X : ℝ) :
    localShortIntervalExceptionalSet J theta delta X ⊆
      Ico X ((1 + delta / J) * X) := by
  intro x hx
  exact hx.1

theorem measure_localShortIntervalExceptionalSet_ne_top
    (J : ℕ) (theta delta X : ℝ) :
    MeasureTheory.volume
        (localShortIntervalExceptionalSet J theta delta X) ≠ ∞ := by
  apply ne_of_lt
  calc
    MeasureTheory.volume (localShortIntervalExceptionalSet J theta delta X) ≤
        MeasureTheory.volume (Ico X ((1 + delta / J) * X)) :=
      MeasureTheory.measure_mono
        (localShortIntervalExceptionalSet_subset_sourceInterval
          J theta delta X)
    _ < ∞ := measure_Ico_lt_top

/-- Real-valued finite subadditivity for the exact multiplicative cover. -/
theorem exceptionalMeasure_le_sum_local
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hX : 0 < X) (hdelta : 0 < delta) :
    exceptionalMeasure delta X theta ≤
      ∑ k ∈ Finset.range (⌈1 / (delta / (J : ℝ))⌉₊ + 1),
        localShortIntervalExceptionalMeasure J theta delta
          (localCoverLeft X (delta / J) k) := by
  let s := Finset.range (⌈1 / (delta / (J : ℝ))⌉₊ + 1)
  have hMeasure :
      MeasureTheory.volume (shortIntervalExceptionalSet delta X theta) ≤
        ∑ k ∈ s, MeasureTheory.volume
          (localShortIntervalExceptionalSet J theta delta
            (localCoverLeft X (delta / J) k)) :=
    (MeasureTheory.measure_mono
      (shortIntervalExceptionalSet_subset_local_union hJ hX hdelta)).trans
      (MeasureTheory.measure_biUnion_finset_le s
        (fun k => localShortIntervalExceptionalSet J theta delta
          (localCoverLeft X (delta / J) k)))
  have hSumFinite :
      (∑ k ∈ s, MeasureTheory.volume
        (localShortIntervalExceptionalSet J theta delta
          (localCoverLeft X (delta / J) k))) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro k hk
    exact measure_localShortIntervalExceptionalSet_ne_top J theta delta _
  have hReal := ENNReal.toReal_mono hSumFinite hMeasure
  have hEach : ∀ k ∈ s,
      MeasureTheory.volume
        (localShortIntervalExceptionalSet J theta delta
          (localCoverLeft X (delta / J) k)) ≠ ∞ := by
    intro k hk
    exact measure_localShortIntervalExceptionalSet_ne_top J theta delta _
  rw [ENNReal.toReal_sum hEach] at hReal
  simpa [exceptionalMeasure, localShortIntervalExceptionalMeasure, s] using hReal

/-- A uniform local fixed-power estimate yields the exact global
`E_delta(X,theta)` fixed-power estimate. -/
theorem exceptionalMeasure_fixedPowerBound_of_local
    {J : ℕ} (hJ : 0 < J) {theta delta xi : ℝ}
    (hdelta : 0 < delta)
    (hLocal : FixedPowerBound
      (fun Y => localShortIntervalExceptionalMeasure J theta delta Y) xi) :
    FixedPowerBound (fun X => exceptionalMeasure delta X theta) xi := by
  let u : ℝ := delta / J
  let s := Finset.range (⌈1 / u⌉₊ + 1)
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hSum : FixedPowerBound
      (fun X => ∑ k ∈ s,
        localShortIntervalExceptionalMeasure J theta delta
          (localCoverLeft X u k)) xi := by
    apply FixedPowerBound.finset_sum
    intro k hk
    exact hLocal.comp_localCoverLeft hu k
  apply hSum.mono_eventually
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [abs_of_nonneg (show 0 ≤ exceptionalMeasure delta X theta from
    ENNReal.toReal_nonneg)]
  have hBound :=
    exceptionalMeasure_le_sum_local (theta := theta) hJ hX hdelta
  have hTermsNonneg : 0 ≤ ∑ k ∈ s,
      localShortIntervalExceptionalMeasure J theta delta
        (localCoverLeft X u k) := by
    apply Finset.sum_nonneg
    intro k hk
    exact ENNReal.toReal_nonneg
  rw [abs_of_nonneg hTermsNonneg]
  simpa [s, u] using hBound

/-- Full conditional exceptional-set bound: every downstream source step is
assembled, and the only remaining assumptions are the sharp explicit formula,
near-one logarithmic density, and Vinogradov--Korobov zero-free inputs. -/
theorem exceptionalMeasure_fixedPowerBound_of_source_inputs
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta xi : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsource :
      max (((1 - theta : ℝ) : EReal))
          (refinedExceptionalUpperExponent theta) < (xi : EReal)) :
    FixedPowerBound (fun X => exceptionalMeasure delta X theta) xi := by
  obtain ⟨J, hJ, hLocal⟩ :=
    localExceptionalMeasure_fixedPowerBound_of_source_inputs cutoff hFormula
      hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta hdeltaOne
        hsource
  exact exceptionalMeasure_fixedPowerBound_of_local hJ hdelta hLocal

end GafniTao
