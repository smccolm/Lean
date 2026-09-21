import TaoTrudgianYang2025.ZetaGammaShiftAmplitude

/-!
# Gaussian reserves for the fourth-moment contour

Polynomial ordinate factors and the exact Gronwall error are absorbed
without changing the contour's height exponent.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

theorem abs_polynomial_mul_exp_le_gaussian
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (D : ℝ) (m : ℕ) (u : ℝ) :
    (a+b*|u|)^m * Real.exp (D*|u|) ≤
      Real.exp ((m:ℝ)*a+((m:ℝ)*b+D)^2/4) * Real.exp (u^2) := by
  have hx : 0 ≤ a+b*|u| := by positivity
  have he : a+b*|u| ≤ Real.exp (a+b*|u|) := by
    linarith [Real.add_one_le_exp (a+b*|u|)]
  calc
    _ ≤ (Real.exp (a+b*|u|))^m * Real.exp (D*|u|) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx he m) (by positivity)
    _ = Real.exp ((m:ℝ)*(a+b*|u|)+D*|u|) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (((m:ℝ)*a+((m:ℝ)*b+D)^2/4)+u^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (|u|-((m:ℝ)*b+D)/2), sq_abs u]
    _ = _ := Real.exp_add _ _

theorem zetaGammaShiftError_le_quadratic
    {t c : ℝ} (ht : 4 ≤ t) (hc : 0 ≤ c) {w : ℂ} (u : ℝ)
    (hw : ‖w‖ ≤ c+|u|) :
    zetaGammaShiftError t w ≤ 17*c/4+c^2+u^2+17*|u|/4 := by
  have hnum : 17*‖w‖+2*‖w‖^2 ≤ 17*(c+|u|)+2*(c+|u|)^2 := by
    gcongr
  calc
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/t :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (17*(c+|u|)+2*(c+|u|)^2)/4 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
    _ ≤ _ := by nlinarith [sq_nonneg (c-|u|), sq_abs u]

theorem norm_vertical_shift_le {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ‖(c:ℂ)+(u:ℂ)*I‖ ≤ c+|u| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc] using
      norm_add_le (c:ℂ) ((u:ℂ)*I)

theorem vertical_shift_re_le_norm {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    c ≤ ‖(c:ℂ)+(u:ℂ)*I‖ := by
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, abs_of_nonneg hc] using
      Complex.abs_re_le_norm ((c:ℂ)+(u:ℂ)*I)

end TaoTrudgianYang2025
