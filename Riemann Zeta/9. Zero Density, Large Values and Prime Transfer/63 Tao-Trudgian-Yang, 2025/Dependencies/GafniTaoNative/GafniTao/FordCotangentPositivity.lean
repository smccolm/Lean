import GafniTao.FordZeroDetectorResidues

/-!
# Positivity of the cotangent weight

Ford discards zeta zeros only after proving that the real part of his
cotangent weight is nonnegative on the relevant half strip.  We keep this
sign calculation as a separate theorem.
-/

open Complex Set

namespace GafniTao

theorem ford_re_cot_formula (x y : ℝ) :
    (Complex.cot ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      Real.sin (2 * x) /
        (Real.cosh (2 * y) - Real.cos (2 * x)) := by
  rw [Complex.cot, Complex.div_re, Complex.sin_add_mul_I,
    Complex.cos_add_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one,
    Complex.normSq_apply]
  simp only [sub_zero, zero_sub, zero_add, add_zero, zero_mul]
  rw [← add_div]
  have hnum :
      Real.cos x * Real.cosh y * (Real.sin x * Real.cosh y) +
          -(Real.sin x * Real.sinh y) * (Real.cos x * Real.sinh y) =
        Real.sin x * Real.cos x := by
    calc
      _ = Real.sin x * Real.cos x *
          (Real.cosh y ^ 2 - Real.sinh y ^ 2) := by ring
      _ = Real.sin x * Real.cos x := by
        rw [Real.cosh_sq_sub_sinh_sq, mul_one]
  rw [hnum, Real.sin_two_mul]
  have hden :
      Real.cosh (2 * y) - Real.cos (2 * x) =
        2 * (Real.sin x * Real.cosh y * (Real.sin x * Real.cosh y) +
          Real.cos x * Real.sinh y * (Real.cos x * Real.sinh y)) := by
    rw [Real.cos_two_mul, Real.cosh_two_mul]
    have hsin : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hcosh : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq y]
    calc
      _ = 2 * (Real.cosh y ^ 2 - Real.cos x ^ 2) := by
        rw [hcosh]
        ring
      _ = 2 * (Real.sin x ^ 2 * Real.cosh y ^ 2 +
          Real.cos x ^ 2 * Real.sinh y ^ 2) := by
        rw [hsin, hcosh]
        ring
      _ = _ := by ring
  rw [hden]
  convert (mul_div_mul_left (Real.sin x * Real.cos x)
    (Real.sin x * Real.cosh y * (Real.sin x * Real.cosh y) +
      Real.cos x * Real.sinh y * (Real.cos x * Real.sinh y))
    (by norm_num : (2 : ℝ) ≠ 0)).symm using 1
  all_goals ring

theorem ford_re_cot_nonneg
    {x y : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    0 ≤ (Complex.cot ((x : ℂ) + (y : ℂ) * Complex.I)).re := by
  rw [ford_re_cot_formula]
  have hsin : 0 ≤ Real.sin (2 * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  have hden : 0 ≤ Real.cosh (2 * y) - Real.cos (2 * x) := by
    linarith [Real.one_le_cosh (2 * y), Real.cos_le_one (2 * x)]
  positivity

theorem fordCotKernel_re_nonneg
    {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hzeta : z.re ≤ eta) :
    0 ≤ (fordCotKernel eta z).re := by
  let c : ℝ := Real.pi / (2 * eta)
  have hc : 0 < c := div_pos Real.pi_pos (mul_pos two_pos heta)
  have hx0 : 0 ≤ c * z.re := mul_nonneg hc.le hz0
  have hxpi : c * z.re ≤ Real.pi / 2 := by
    calc
      c * z.re ≤ c * eta := mul_le_mul_of_nonneg_left hzeta hc.le
      _ = Real.pi / 2 := by
        dsimp [c]
        field_simp [heta.ne']
  have hcot := ford_re_cot_nonneg (y := c * z.im) hx0 hxpi
  have harg : ((c : ℂ) * z) =
      ((c * z.re : ℝ) : ℂ) + ((c * z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [c] <;> ring
  unfold fordCotKernel
  change 0 ≤ (((c : ℝ) : ℂ) * Complex.cot (((c : ℝ) : ℂ) * z)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, harg]
  exact mul_nonneg hc.le hcot

end GafniTao
