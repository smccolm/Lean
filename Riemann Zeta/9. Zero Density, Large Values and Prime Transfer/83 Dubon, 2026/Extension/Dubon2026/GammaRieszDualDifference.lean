import Dubon2026.GammaRieszDualSeries

/-! # Both sharp coefficient powers in the actual dual Riesz second difference -/

namespace Dubon2026

open Complex

noncomputable section

/-- The actual reciprocal coefficient times the kernel difference has both exact low/high coefficient powers. -/
theorem exists_gammaRieszDualDifference_term_bounds {k A : ℝ} (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧
      ∀ (a : ℕ → ℝ) (x h : ℝ) (n : ℕ), 0 ≤ a n → 0 < x → 0 ≤ h → h ≤ x → 1 ≤ n →
        ‖((a n / (n : ℝ) : ℝ) : ℂ) * gammaRieszSecondDifference k (A * n) x h‖ ≤
          C₀ * h ^ 2 * x ^ (3 / 8 : ℝ) * (a n * (n : ℝ) ^ (-(5 / 8 : ℝ))) ∧
        ‖((a n / (n : ℝ) : ℝ) : ℂ) * gammaRieszSecondDifference k (A * n) x h‖ ≤
          C₂ * x ^ (15 / 8 : ℝ) * (a n * (n : ℝ) ^ (-(9 / 8 : ℝ))) := by
  obtain ⟨L, hL, hl⟩ := exists_gammaRieszSecondDifference_low_bound hk
  obtain ⟨H, hH, hh⟩ := exists_gammaRieszSecondDifference_high_bound hk
  refine ⟨L * A ^ (3 / 8 : ℝ), H * A ^ (-(1 / 8 : ℝ)), by positivity, by positivity, ?_⟩
  intro a x h n ha hx h0 h1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have han : 0 ≤ a n / (n : ℝ) := div_nonneg ha hn0.le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg han]
  constructor
  · calc
      _ ≤ (a n / n) * (L * h ^ 2 * (A * n * x) ^ (3 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hl (A * n) x h (mul_pos hA hn0) hx h0 h1) han
      _ = L * h ^ 2 * (a n / n * (A * n * x) ^ (3 / 8 : ℝ)) := by ring
      _ = _ := by
        rw [weighted_mellin_power_factor _ _ hA hn0 hx]
        norm_num only [show (3 / 8 : ℝ) - 1 = -(5 / 8 : ℝ) by norm_num]
        ring
  · have hnPow : (n : ℝ) ^ (-(1 / 8 : ℝ)) / (n : ℝ) = (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
      rw [← Real.rpow_sub_one hn0.ne']
      norm_num
    calc
      _ ≤ (a n / n) * (H * (A * n) ^ (-(1 / 8 : ℝ)) * x ^ (15 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hh (A * n) x h (mul_pos hA hn0) hx h0 h1) han
      _ = (H * A ^ (-(1 / 8 : ℝ))) * x ^ (15 / 8 : ℝ) *
          (a n * ((n : ℝ) ^ (-(1 / 8 : ℝ)) / (n : ℝ))) := by
        rw [Real.mul_rpow hA.le hn0.le]
        ring
      _ = _ := by rw [hnPow]

end
end Dubon2026
