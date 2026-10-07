import Dubon2026.RieszSecondSum

/-! # Exact transfer from second Riesz differences to the unsmoothed summatory error -/

namespace Dubon2026

noncomputable section

/-- The actual second Riesz sum with its cubic main term subtracted. -/
def rieszSecondError (a : ℕ → ℝ) (c x : ℝ) : ℝ := rieszSecondSum a x - c * x ^ 3 / 6

/-- The second difference separates the genuine cubic main term and actual Riesz error exactly. -/
theorem rieszSecondSum_difference_main (a : ℕ → ℝ) (c x h : ℝ) :
    rieszSecondDifference (rieszSecondSum a) x h =
      c * h ^ 2 * (x + h) + rieszSecondDifference (rieszSecondError a c) x h := by
  have hm := rieszSecondDifference_cubic c x h
  simp only [rieszSecondDifference, rieszSecondError] at hm ⊢
  linarith

/-- Dividing by the true smoothing scale preserves the exact main-term separation. -/
theorem rieszSecondSum_difference_div (a : ℕ → ℝ) (c x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    rieszSecondDifference (rieszSecondSum a) x h / h ^ 2 =
      c * (x + h) + rieszSecondDifference (rieszSecondError a c) x h / h ^ 2 := by
  rw [rieszSecondSum_difference_main a c x h]
  field_simp

/-- Positivity transfers actual forward and backward Riesz-error differences to the literal unsmoothed error. -/
theorem realCoefficientSummatory_error_le_riesz {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (c x : ℝ) {h : ℝ} (hh : 0 < h) :
    |realCoefficientSummatory a x - c * x| ≤ c * h +
      max |rieszSecondDifference (rieszSecondError a c) x h|
        |rieszSecondDifference (rieszSecondError a c) (x - 2 * h) h| / h ^ 2 := by
  obtain ⟨hminus, hplus⟩ := realCoefficientSummatory_riesz_bounds ha x hh
  rw [rieszSecondSum_difference_div a c x hh.ne'] at hplus
  rw [rieszSecondSum_difference_div a c (x - 2 * h) hh.ne'] at hminus
  let M := max |rieszSecondDifference (rieszSecondError a c) x h|
    |rieszSecondDifference (rieszSecondError a c) (x - 2 * h) h|
  have hp : rieszSecondDifference (rieszSecondError a c) x h / h ^ 2 ≤ M / h ^ 2 :=
    div_le_div_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (sq_nonneg h)
  have hm : -(rieszSecondDifference (rieszSecondError a c) (x - 2 * h) h) / h ^ 2 ≤ M / h ^ 2 :=
    div_le_div_of_nonneg_right ((neg_le_abs _).trans (le_max_right _ _)) (sq_nonneg h)
  rw [neg_div] at hm
  change |realCoefficientSummatory a x - c * x| ≤ c * h + M / h ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith

end
end Dubon2026
