import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

/-! # A second finite-difference bound from actual derivatives -/

namespace Dubon2026

open Set

/-- Two applications of the mean-value inequality bound the actual complex second difference. -/
theorem norm_secondDifference_le_of_hasDerivAt {F F₁ F₂ : ℝ → ℂ} {x h C : ℝ}
    (hh : 0 ≤ h)
    (hF : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt F (F₁ y) y)
    (hF₁ : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt F₁ (F₂ y) y)
    (hF₂ : ∀ y ∈ Icc x (x + 2 * h), ‖F₂ y‖ ≤ C) :
    ‖F (x + 2 * h) - 2 * F (x + h) + F x‖ ≤ C * h ^ 2 := by
  have hd (y : ℝ) (hy : y ∈ Icc x (x + h)) :
      HasDerivAt (fun z => F (z + h) - F z) (F₁ (y + h) - F₁ y) y := by
    have h₁ := (hF (y + h) ⟨by linarith [hy.1], by linarith [hy.2]⟩).scomp y
      ((hasDerivAt_id y).add_const h)
    simpa only [one_smul] using h₁.sub (hF y ⟨hy.1, by linarith [hy.2]⟩)
  have hb (y : ℝ) (hy : y ∈ Ico x (x + h)) : ‖F₁ (y + h) - F₁ y‖ ≤ C * h := by
    have hm := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun z (hz : z ∈ Icc y (y + h)) =>
        (hF₁ z ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩).hasDerivWithinAt)
      (fun z (hz : z ∈ Ico y (y + h)) =>
        hF₂ z ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩)
      (y + h) ⟨by linarith, le_rfl⟩
    simpa only [add_sub_cancel_left] using hm
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => (hd y hy).hasDerivWithinAt) hb (x + h) ⟨by linarith, le_rfl⟩
  have he : F (x + 2 * h) - 2 * F (x + h) + F x =
      F (x + h + h) - F (x + h) - (F (x + h) - F x) := by
    rw [show x + h + h = x + 2 * h by ring]
    ring
  rw [he]
  convert hm using 1
  ring

end Dubon2026
