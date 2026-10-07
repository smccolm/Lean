import Dubon2026.ConvolutionRealCutoff
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Exact power remainders preserved by genuinely convergent Dirichlet convolution -/

namespace Dubon2026

open Complex

noncomputable section

/-- A sublinear summatory error valid above one extends to every nonnegative cutoff by the actual empty initial sum. -/
theorem complexCoefficientSummatory_bound_nonneg {b : ℕ → ℂ} {c : ℂ} {C θ : ℝ}
    (hC : 0 ≤ C) (hθ : θ ≤ 1)
    (hb : ∀ y : ℝ, 1 ≤ y → ‖complexCoefficientSummatory b y - c * y‖ ≤ C * y ^ θ) :
    ∀ y : ℝ, 0 ≤ y → ‖complexCoefficientSummatory b y - c * y‖ ≤ (C + ‖c‖) * y ^ θ := by
  intro y hy
  by_cases hy1 : 1 ≤ y
  · exact (hb y hy1).trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg c]) (Real.rpow_nonneg hy _))
  · have hylt : y < 1 := lt_of_not_ge hy1
    have he : complexCoefficientSummatory b y = 0 := by
      simp [complexCoefficientSummatory, Nat.floor_eq_zero.mpr hylt]
    rw [he, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
    calc
      _ ≤ ‖c‖ * y ^ θ := mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hy hylt.le hθ) (norm_nonneg c)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hy _)

/-- A genuine coefficient Dirichlet series converging at theta preserves the exact x^theta error under convolution, with its actual value at one as main-term multiplier. -/
theorem complexCoefficientSummatory_convolution_power_bound {a b : ℕ → ℂ} {c : ℂ} {C θ : ℝ}
    (hθ : θ ≤ 1) (ha : LSeriesSummable a (θ : ℂ))
    (hb : ∀ y : ℝ, 0 ≤ y → ‖complexCoefficientSummatory b y - c * y‖ ≤ C * y ^ θ)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖complexCoefficientSummatory (LSeries.convolution a b) x - c * (x : ℂ) * LSeries a 1‖ ≤
      C * x ^ θ * ∑' n : ℕ, ‖LSeries.term a (θ : ℂ) n‖ := by
  have ha1 : LSeriesSummable a 1 := ha.of_re_le_re (by simpa only [Complex.ofReal_re, Complex.one_re] using hθ)
  have he := (hasSum_complexCoefficientSummatory_convolution a b x).sub (hasSum_convolution_linear ha1 c x)
  rw [← he.tsum_eq]
  apply tsum_of_norm_bounded (ha.norm.hasSum.mul_left (C * x ^ θ))
  intro n
  by_cases hn : n = 0
  · simp [hn, complexCoefficientSummatory]
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← mul_sub, norm_mul, LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re]
    calc
      _ ≤ ‖a n‖ * (C * (x / (n : ℝ)) ^ θ) :=
        mul_le_mul_of_nonneg_left (hb _ (div_nonneg hx hnR.le)) (norm_nonneg _)
      _ = _ := by rw [Real.div_rpow hx hnR.le]; ring

end
end Dubon2026
