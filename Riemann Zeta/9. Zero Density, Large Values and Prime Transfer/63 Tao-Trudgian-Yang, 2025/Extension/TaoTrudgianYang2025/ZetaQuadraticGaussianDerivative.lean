import TaoTrudgianYang2025.ZetaLogGaussianVariation

/-!
# Derivative of the true quadratic Gaussian transform

The closed complex Gaussian is differentiated exactly. Its derivative
retains the proved frequency damping throughout the interval whose
length grows with the source width.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

theorem hasDerivAt_zetaGaussianQuadraticIntegral (T : ℝ) {G : ℝ} (hG : G ≠ 0) (v : ℝ) :
    HasDerivAt (zetaGaussianQuadraticIntegral T G)
      (-(v : ℂ) / (2 * zetaGaussianQuadraticCoefficient T G) *
        zetaGaussianQuadraticIntegral T G v) v := by
  have heq : zetaGaussianQuadraticIntegral T G = fun w : ℝ =>
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(w : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) :=
    funext (fun w => zetaGaussianQuadraticIntegral_eq T w hG)
  have hv := (hasDerivAt_id v).ofReal_comp
  have h := ((hv.pow 2).neg.div_const (4 * zetaGaussianQuadraticCoefficient T G)).cexp.const_mul
    (((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ))
  rw [heq]
  convert h using 1
  norm_num
  ring

theorem inverse_norm_zetaGaussianQuadraticCoefficient_le (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    1 / ‖zetaGaussianQuadraticCoefficient T G‖ ≤ G ^ 2 := by
  have hr := zetaGaussianQuadraticCoefficient_re_pos T hG
  have hle := (Complex.re_le_norm (zetaGaussianQuadraticCoefficient T G))
  have h := one_div_le_one_div_of_le hr hle
  simpa only [zetaGaussianQuadraticCoefficient_re, one_div_one_div] using h

theorem norm_deriv_zetaGaussianQuadraticIntegral_le {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖deriv (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (Real.sqrt Real.pi * G ^ 3 / 2) * |v| * Real.exp (-(G * v) ^ 2 / 8) := by
  rw [(hasDerivAt_zetaGaussianQuadraticIntegral T hG.ne' v).deriv, norm_mul,
    norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul]
  norm_num only [norm_ofNat]
  have hcoef : |v| / (2 * ‖zetaGaussianQuadraticCoefficient T G‖) ≤ |v| * G ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left (inverse_norm_zetaGaussianQuadraticCoefficient_le T hG.ne')
      (show 0 ≤ |v| / 2 by positivity)
    convert h using 1 <;> ring
  calc
    _ ≤ (|v| * G ^ 2 / 2) *
        (Real.sqrt Real.pi * G * Real.exp (-(G * v) ^ 2 / 8)) :=
      mul_le_mul hcoef (norm_zetaGaussianQuadraticIntegral_le hT hG hGT v)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
