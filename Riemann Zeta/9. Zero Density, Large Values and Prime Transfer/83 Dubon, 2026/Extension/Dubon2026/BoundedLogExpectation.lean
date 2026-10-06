import Dubon2026.SmallBallLog

/-! # Full logarithmic integrability and expectation for bounded random variables -/

namespace Dubon2026

open MeasureTheory

noncomputable section

theorem log_norm_eq_positive_sub_negative (z : ℂ) :
    Real.log ‖z‖ = max 0 (Real.log ‖z‖) - negativeLogNorm z := by
  unfold negativeLogNorm
  by_cases h : 0 ≤ Real.log ‖z‖
  · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h), sub_zero]
  · have h' : Real.log ‖z‖ ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left h', max_eq_right (neg_nonneg.mpr h')]
    ring

theorem integrable_log_norm_of_bounded_smallBall {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℂ} (hf : Measurable f)
    {B C : ℝ} (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) (hC : 0 ≤ C)
    (hball : ∀ r : ℝ, 0 < r → μ {x | ‖f x‖ ≤ r} ≤ ENNReal.ofReal (C * r ^ 2)) :
    Integrable (fun x => Real.log ‖f x‖) μ ∧
      -C ≤ ∫ x, Real.log ‖f x‖ ∂μ := by
  obtain ⟨hneg, hnegBound⟩ := integrable_negativeLogNorm_of_smallBall hf hC hball
  have hpos : Integrable (fun x => max 0 (Real.log ‖f x‖)) μ := by
    apply (integrable_const B).mono'
    · exact (measurable_const.max (Real.measurable_log.comp hf.norm)).aestronglyMeasurable
    · filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le ((norm_nonneg _).trans hx) ((Real.log_le_self (norm_nonneg _)).trans hx)
  have he : (fun x => Real.log ‖f x‖) =
      fun x => max 0 (Real.log ‖f x‖) - negativeLogNorm (f x) :=
    funext (fun x => log_norm_eq_positive_sub_negative (f x))
  refine ⟨by rw [he]; exact hpos.sub hneg, ?_⟩
  rw [he, integral_sub hpos hneg]
  have hp : 0 ≤ ∫ x, max 0 (Real.log ‖f x‖) ∂μ := integral_nonneg (fun _ => le_max_left _ _)
  linarith

end

end Dubon2026
