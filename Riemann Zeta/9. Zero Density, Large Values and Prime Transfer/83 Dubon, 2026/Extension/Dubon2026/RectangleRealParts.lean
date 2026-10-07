import Dubon2026.RectangleZeroCount

/-! # Real components of the normalized rectangle argument integral -/

namespace Dubon2026

open Complex MeasureTheory Set

theorem rectangleIntegral_scaled_real (f : ℂ → ℂ) (l u b t : ℝ) :
    (2 * Real.pi) * (RectangleIntegral' f (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ)).re =
      (HIntegral f l u b).im - (HIntegral f l u t).im +
        (∫ y in b..t, f ((u : ℂ) + y * I)).re -
          (∫ y in b..t, f ((l : ℂ) + y * I)).re := by
  have hn : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have he : (2 * (Real.pi : ℂ) * I) *
      RectangleIntegral' f (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) =
        RectangleIntegral f (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) := by
    rw [RectangleIntegral', smul_eq_mul, one_div, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have hi := congrArg Complex.im he
  simpa [RectangleIntegral, VIntegral, smul_eq_mul, mul_im, mul_re] using hi

theorem horizontal_bottom_mem_rectangleBorder {l u b t x : ℝ}
    (hlu : l ≤ u) (hx : x ∈ Icc l u) :
    (x : ℂ) + I * b ∈ RectangleBorder (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) := by
  simp [RectangleBorder, mem_reProdIm, uIcc_of_le hlu, hx.1, hx.2]

theorem horizontal_top_mem_rectangleBorder {l u b t x : ℝ}
    (hlu : l ≤ u) (hx : x ∈ Icc l u) :
    (x : ℂ) + I * t ∈ RectangleBorder (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) := by
  simp [RectangleBorder, mem_reProdIm, uIcc_of_le hlu, hx.1, hx.2]

theorem vertical_left_mem_rectangleBorder {l u b t y : ℝ}
    (hbt : b ≤ t) (hy : y ∈ Icc b t) :
    (l : ℂ) + I * y ∈ RectangleBorder (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) := by
  simp [RectangleBorder, mem_reProdIm, uIcc_of_le hbt, hy.1, hy.2]

theorem vertical_right_mem_rectangleBorder {l u b t y : ℝ}
    (hbt : b ≤ t) (hy : y ∈ Icc b t) :
    (u : ℂ) + I * y ∈ RectangleBorder (⟨l, b⟩ : ℂ) (⟨u, t⟩ : ℂ) := by
  simp [RectangleBorder, mem_reProdIm, uIcc_of_le hbt, hy.1, hy.2]

end Dubon2026
