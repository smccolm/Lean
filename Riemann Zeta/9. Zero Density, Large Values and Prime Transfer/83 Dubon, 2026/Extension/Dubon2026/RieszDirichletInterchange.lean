import Dubon2026.RieszInverseKernel

/-! # The absolutely justified inverse Mellin formula for a genuine Dirichlet series -/

namespace Dubon2026

open Complex MeasureTheory

noncomputable section

/-- Each actual Dirichlet term times the inverse kernel is integrable by exact dilation. -/
theorem integrable_rieszInverseKernel_mul_term {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    (a : ℕ → ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp_rw [rieszInverseKernel_mul_term hx σ _ a hn]
    exact (integrable_rieszInverseKernel hσ
      (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)).const_mul (a n)

/-- Absolute Dirichlet convergence supplies the complete Tonelli majorant for the inverse integral. -/
theorem summable_integral_norm_riesz_terms (σ x : ℝ)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    Summable (fun n : ℕ => ∫ t : ℝ,
      ‖rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n‖) := by
  simp_rw [norm_rieszInverseKernel_mul_term, integral_const_mul]
  exact ha.norm.mul_right _

/-- The actual inverse integral with the full Dirichlet series is absolutely convergent. -/
theorem integrable_rieszInverseKernel_LSeries {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    Integrable (fun t : ℝ => rieszInverseKernel σ x t * LSeries a (σ + t * I)) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n
  have hm : AEStronglyMeasurable (fun t => ∑' n, F n t) :=
    AEStronglyMeasurable.tsum (fun n =>
      (integrable_rieszInverseKernel_mul_term hσ hx a n).aestronglyMeasurable)
  have he (t : ℝ) : (∑' n, F n t) = rieszInverseKernel σ x t * LSeries a (σ + t * I) := by
    simp only [F, tsum_mul_left, LSeries]
  have hh : Integrable (fun t => ∑' n, F n t) := by
    apply ((integrable_rieszInverseKernel hσ hx).norm.const_mul (∑' n, ‖LSeries.term a σ n‖)).mono' hm
    apply Filter.Eventually.of_forall
    intro t
    have hn : Summable (fun n => ‖F n t‖) := by
      simpa only [F, norm_rieszInverseKernel_mul_term] using ha.norm.mul_right ‖rieszInverseKernel σ x t‖
    calc
      _ ≤ ∑' n, ‖F n t‖ := norm_tsum_le_tsum_norm hn
      _ = _ := by simp only [F, norm_rieszInverseKernel_mul_term, tsum_mul_right]
  simpa only [he] using hh

/-- The genuine inverse Mellin transform of a convergent Dirichlet series times the Riesz symbol
is its actual, compactly supported cutoff series. -/
theorem mellinInv_LSeries_riesz {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    mellinInv σ (fun s => LSeries a s * rieszMellinSymbol s) x =
      ∑' n : ℕ, a n * rieszMellinCutoff ((n : ℝ) * x) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n
  have hi := hasSum_integral_of_summable_integral_norm
    (integrable_rieszInverseKernel_mul_term hσ hx a)
    (summable_integral_norm_riesz_terms σ x ha)
  have he (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, F n t) =
      a n * rieszMellinCutoff ((n : ℝ) * x) := by
    by_cases hn : n = 0
    · simp [F, hn, rieszMellinCutoff]
    · simp_rw [F, rieszInverseKernel_mul_term hx σ _ a hn]
      rw [integral_const_mul, ← mul_smul_comm, integral_rieszInverseKernel hσ
        (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)]
  have hs := hi.const_smul (1 / (2 * Real.pi) : ℝ)
  change HasSum (fun n => (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, F n t)
    ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, ∑' n, F n t) at hs
  simp_rw [he] at hs
  rw [hs.tsum_eq]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [F, rieszInverseKernel, tsum_mul_left, LSeries, smul_eq_mul]
  ring

end
end Dubon2026
