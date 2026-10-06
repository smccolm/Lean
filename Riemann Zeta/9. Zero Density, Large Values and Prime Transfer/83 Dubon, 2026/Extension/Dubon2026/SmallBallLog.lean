import Dubon2026.ExponentialTailIntegral

/-! # Integrability of the negative logarithm from a genuine small-ball bound -/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

theorem integrable_of_exponential_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f)
    {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * Real.exp (-t))) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ C := by
  have hl : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    rw [lintegral_eq_lintegral_meas_lt μ hfn hf.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-t)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        exact fun t ht => htail t ht
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), C * Real.exp (-t)) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg_Ioi 0).const_mul C)
          (Filter.Eventually.of_forall (fun t => mul_nonneg hC (Real.exp_pos _).le))).symm
      _ = ENNReal.ofReal C := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  have hi : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf hfn).mp
      (ne_of_lt (lt_of_le_of_lt hl ENNReal.ofReal_lt_top))
  exact ⟨hi, integral_le_of_exponential_tail hi hfn hC htail⟩

/-- Positive part of the negative logarithm, with the library's null-point convention. -/
def negativeLogNorm (z : ℂ) : ℝ := max 0 (-Real.log ‖z‖)

theorem measurable_negativeLogNorm : Measurable negativeLogNorm :=
  measurable_const.max (Real.measurable_log.comp measurable_norm).neg

theorem negativeLogNorm_level_subset {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : t < negativeLogNorm z) : ‖z‖ ≤ Real.exp (-t) := by
  by_cases hz0 : z = 0
  · simp only [hz0, norm_zero]
    exact (Real.exp_pos _).le
  have hl : t < -Real.log ‖z‖ :=
    (lt_max_iff.mp hz).resolve_left (not_lt_of_ge ht.le)
  apply (Real.log_le_log_iff (norm_pos_iff.mpr hz0) (Real.exp_pos _)).mp
  rw [Real.log_exp]
  linarith

theorem integrable_negativeLogNorm_of_smallBall {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ r : ℝ, 0 < r → μ {x | ‖f x‖ ≤ r} ≤ ENNReal.ofReal (C * r ^ 2)) :
    Integrable (fun x => negativeLogNorm (f x)) μ ∧
      (∫ x, negativeLogNorm (f x) ∂μ) ≤ C := by
  apply integrable_of_exponential_tail (measurable_negativeLogNorm.comp hf).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => le_max_left _ _)) hC
  intro t ht
  calc
    μ {x | t < negativeLogNorm (f x)} ≤ μ {x | ‖f x‖ ≤ Real.exp (-t)} :=
      measure_mono (fun x hx => negativeLogNorm_level_subset ht hx)
    _ ≤ ENNReal.ofReal (C * Real.exp (-t) ^ 2) := hball _ (Real.exp_pos _)
    _ ≤ ENNReal.ofReal (C * Real.exp (-t)) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC
      have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.exp_pos (-t)]

end

end Dubon2026
