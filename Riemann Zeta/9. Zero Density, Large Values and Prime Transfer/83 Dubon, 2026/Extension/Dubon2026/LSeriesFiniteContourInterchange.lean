import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Justified finite-contour interchange for genuine convergent Dirichlet series -/

namespace Dubon2026

open Complex Set Filter MeasureTheory

noncomputable section

/-- An actually convergent Dirichlet series may be integrated termwise along a compact constant-real-part contour with a continuous weight. -/
theorem hasSum_intervalIntegral_mul_LSeries {a : ℕ → ℂ} {σ u v : ℝ}
    (ha : LSeriesSummable a (σ : ℂ)) {z : ℝ → ℂ} (hz : ContinuousOn z (uIcc u v))
    (hre : ∀ t ∈ uIcc u v, (z t).re = σ) {F : ℝ → ℂ} (hF : ContinuousOn F (uIcc u v)) :
    HasSum (fun n : ℕ => ∫ t in u..v, F t * LSeries.term a (z t) n)
      (∫ t in u..v, F t * LSeries a (z t)) := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hF
  let B : ℝ := |C| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : ∀ t ∈ uIcc u v, ‖F t‖ ≤ B := by
    intro t ht
    exact (hC t ht).trans (by dsimp [B]; linarith [le_abs_self C])
  have hs : Summable (fun n : ℕ => B * ‖LSeries.term a (σ : ℂ) n‖) := ha.norm.mul_left B
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => B * ‖LSeries.term a (σ : ℂ) n‖)
  · intro n
    have hc : Continuous (fun s : ℂ => LSeries.term a s n) :=
      continuous_iff_continuousAt.mpr (fun s => (LSeries.hasDerivAt_term a n s).continuousAt)
    exact ((hF.mul (hc.comp_continuousOn hz)).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · intro n
    filter_upwards [] with t ht
    have htu := uIoc_subset_uIcc ht
    rw [norm_mul]
    exact mul_le_mul (hb t htu)
      (LSeries.norm_term_le_of_re_le_re a (s := (σ : ℂ)) (by rw [hre t htu]; rfl) n)
      (norm_nonneg _) hB
  · exact Eventually.of_forall (fun _ _ => hs)
  · exact continuous_const.intervalIntegrable _ _
  · filter_upwards [] with t ht
    have hsum : LSeriesSummable a (z t) := ha.of_re_le_re (by rw [hre t (uIoc_subset_uIcc ht)]; rfl)
    exact hsum.hasSum.mul_left (F t)

end
end Dubon2026
