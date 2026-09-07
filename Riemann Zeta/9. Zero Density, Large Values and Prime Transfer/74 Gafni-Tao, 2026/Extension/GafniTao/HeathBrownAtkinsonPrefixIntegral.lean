import GafniTao.HeathBrownAtkinsonPrefixLemma71
import Mathlib.MeasureTheory.Function.Floor

/-!
# Exact integration of the Atkinson prefix average

The cutoff in `S(x,K,t)` is `⌊x⌋`.  Hence its norm is constant on each unit
cell apart from the right endpoint, a null set.  The source integral over
`0 ≤ x ≤ K` is therefore exactly the sum of the `K` literal integer-prefix
norms.  This file proves that equality rather than replacing the integral by
an unrelated maximum or sampled surrogate.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- On the interior of the `j`th unit cell the Atkinson sum is the literal
`j`th prefix. -/
theorem heathBrownAtkinsonSum_eq_natCast_of_mem_Ico
    {x : ℝ} {j K : ℕ} (hx : x ∈ Set.Ico (j : ℝ) (j + 1 : ℝ)) (t : ℝ) :
    heathBrownAtkinsonSum x K t =
      heathBrownAtkinsonSum (j : ℝ) K t := by
  rw [heathBrownAtkinsonSum_eq_floor]
  rw [Nat.floor_eq_on_Ico j x hx]

/-- The norm of the source prefix sum is interval integrable on every unit
cell. -/
theorem intervalIntegrable_norm_heathBrownAtkinsonSum_natCell
    (j K : ℕ) (t : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖heathBrownAtkinsonSum x K t‖)
      volume (j : ℝ) (j + 1 : ℝ) := by
  have hconst : IntervalIntegrable
      (fun _x : ℝ => ‖heathBrownAtkinsonSum (j : ℝ) K t‖)
      volume (j : ℝ) (j + 1 : ℝ) := intervalIntegrable_const
  apply hconst.congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ (j + 1 : ℝ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx hmem
  rw [uIoc_of_le (by norm_num : (j : ℝ) ≤ (j + 1 : ℝ))] at hmem
  have hxIco : x ∈ Set.Ico (j : ℝ) (j + 1 : ℝ) := by
    refine ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ?_⟩
    exact fun h => hx h
  exact congrArg norm (heathBrownAtkinsonSum_eq_natCast_of_mem_Ico hxIco t).symm

/-- Exact value of the source norm integral on one unit prefix cell. -/
theorem intervalIntegral_norm_heathBrownAtkinsonSum_natCell
    (j K : ℕ) (t : ℝ) :
    (∫ x in (j : ℝ)..(j + 1 : ℝ),
        ‖heathBrownAtkinsonSum x K t‖) =
      ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
  calc
    (∫ x in (j : ℝ)..(j + 1 : ℝ),
        ‖heathBrownAtkinsonSum x K t‖) =
        ∫ _x in (j : ℝ)..(j + 1 : ℝ),
          ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
      apply intervalIntegral.integral_congr_ae'
      · have hne : ∀ᵐ x : ℝ ∂volume, x ≠ (j + 1 : ℝ) := by
          simp [ae_iff, measure_singleton]
        filter_upwards [hne] with x hx hmem
        have hxIco : x ∈ Set.Ico (j : ℝ) (j + 1 : ℝ) := by
          refine ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ?_⟩
          exact fun h => hx h
        exact congrArg norm
          (heathBrownAtkinsonSum_eq_natCast_of_mem_Ico hxIco t)
      · filter_upwards [] with x hmem
        exfalso
        exact (not_lt_of_ge (hmem.2.trans (by norm_num))) hmem.1
    _ = ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by simp

/-- The prefix-norm integrand is interval integrable over the complete
source range `[0,K]`. -/
theorem intervalIntegrable_norm_heathBrownAtkinsonSum
    (R K : ℕ) (t : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖heathBrownAtkinsonSum x K t‖)
      volume 0 (R : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
      simpa [Nat.cast_add, Nat.cast_one] using
        ih.trans (intervalIntegrable_norm_heathBrownAtkinsonSum_natCell R K t)

/-- The integral in Heath--Brown's Lemma 1 is exactly a finite sum of all
integer-prefix norms. -/
theorem intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixSum_aux
    (R K : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..(R : ℝ), ‖heathBrownAtkinsonSum x K t‖) =
      ∑ j ∈ Finset.range R,
        ‖heathBrownAtkinsonSum (j : ℝ) K t‖ := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ← ih,
        ← intervalIntegral_norm_heathBrownAtkinsonSum_natCell R K t]
      symm
      simpa [Nat.cast_add, Nat.cast_one] using
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_norm_heathBrownAtkinsonSum R K t)
          (intervalIntegrable_norm_heathBrownAtkinsonSum_natCell R K t)

/-- The complete source-range specialization. -/
theorem intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixSum
    (K : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..(K : ℝ), ‖heathBrownAtkinsonSum x K t‖) =
      ∑ j ∈ Finset.range K,
        ‖heathBrownAtkinsonSum (j : ℝ) K t‖ :=
  intervalIntegral_norm_heathBrownAtkinsonSum_eq_prefixSum_aux K K t


end

end GafniTao
