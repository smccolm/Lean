import TaoTrudgianYang2025.ZetaSquareGaussianTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Quadratic Gaussian transform on the mean-square source scales

The exact transform and its frequency damping are proved here. Applying
this quadratic phase to the zeta-square contour still requires the
shifted-Gamma amplitude/source bridge. The later `ZetaSquareGamma*`
modules prove the actual unit-phase approximation and integrated error.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

def zetaGaussianQuadraticCoefficient (T G : ℝ) : ℂ :=
  ((1 / G ^ 2 : ℝ) : ℂ) + ((1 / (2 * T) : ℝ) : ℂ) * I

def zetaGaussianQuadraticIntegral (T G v : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * (v : ℂ) * x) *
    Complex.exp (-zetaGaussianQuadraticCoefficient T G * x ^ 2)

theorem zetaGaussianQuadraticCoefficient_re (T G : ℝ) :
    (zetaGaussianQuadraticCoefficient T G).re = 1 / G ^ 2 := by
  simp only [zetaGaussianQuadraticCoefficient, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero]

theorem zetaGaussianQuadraticCoefficient_im (T G : ℝ) :
    (zetaGaussianQuadraticCoefficient T G).im = 1 / (2 * T) := by
  simp only [zetaGaussianQuadraticCoefficient, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, zero_add]

theorem zetaGaussianQuadraticCoefficient_re_pos (T : ℝ) {G : ℝ} (hG : G ≠ 0) :
    0 < (zetaGaussianQuadraticCoefficient T G).re := by
  rw [zetaGaussianQuadraticCoefficient_re]
  positivity

theorem zetaGaussianQuadraticIntegral_eq (T v : ℝ) {G : ℝ} (hG : G ≠ 0) :
    zetaGaussianQuadraticIntegral T G v =
      ((Real.pi : ℂ) / zetaGaussianQuadraticCoefficient T G) ^ (1 / 2 : ℂ) *
        Complex.exp (-(v : ℂ) ^ 2 / (4 * zetaGaussianQuadraticCoefficient T G)) :=
  fourierIntegral_gaussian (zetaGaussianQuadraticCoefficient_re_pos T hG) v

theorem integrable_zetaGaussianQuadraticIntegrand (T v : ℝ) {G : ℝ} (hG : G ≠ 0) :
    Integrable (fun x : ℝ => Complex.exp (I * (v : ℂ) * x) *
      Complex.exp (-zetaGaussianQuadraticCoefficient T G * x ^ 2)) := by
  have h := integrable_cexp_quadratic (zetaGaussianQuadraticCoefficient_re_pos T hG)
    (I * (v : ℂ)) 0
  convert h using 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  ring

theorem inverse_re_lower_of_im_le_re {a : ℂ} (ha : 0 < a.re) (hi : |a.im| ≤ a.re) :
    1 / (2 * a.re) ≤ a⁻¹.re := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hi2 : a.im ^ 2 ≤ a.re ^ 2 := by
    calc
      _ = |a.im| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [Complex.inv_re]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * a.re) hn).mpr
  rw [Complex.normSq_apply]
  nlinarith

theorem norm_fourierGaussian_le_of_im_le_re {a : ℂ} (ha : 0 < a.re)
    (hi : |a.im| ≤ a.re) (v : ℝ) :
    ‖((Real.pi : ℂ) / a) ^ (1 / 2 : ℂ) * Complex.exp (-(v : ℂ) ^ 2 / (4 * a))‖ ≤
      Real.sqrt (Real.pi / a.re) * Real.exp (-v ^ 2 / (8 * a.re)) := by
  have haNorm : a.re ≤ ‖a‖ := (le_abs_self _).trans (Complex.abs_re_le_norm a)
  have hexp : (-(v : ℂ) ^ 2 / (4 * a)).re = -(v ^ 2 / 4) * a⁻¹.re := by
    have heq : -(v : ℂ) ^ 2 / (4 * a) = ((-(v ^ 2 / 4) : ℝ) : ℂ) * a⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      push_cast
      ring
    rw [heq, Complex.re_ofReal_mul]
  have hdecay : -(v ^ 2 / 4) * a⁻¹.re ≤ -v ^ 2 / (8 * a.re) := by
    have h := mul_le_mul_of_nonpos_left (inverse_re_lower_of_im_le_re ha hi)
      (show -(v ^ 2 / 4) ≤ 0 from neg_nonpos.mpr (by positivity))
    convert h using 1
    field_simp
    ring
  rw [norm_mul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, ← Real.sqrt_eq_rpow, Complex.norm_exp, hexp]
  exact mul_le_mul (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le ha haNorm))
    (Real.exp_le_exp.mpr hdecay) (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- Uniform frequency damping in the physical range `G^2 ≤ 2T`. -/
theorem norm_zetaGaussianQuadraticIntegral_le {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hscale : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-(G * v) ^ 2 / 8) := by
  have hi : |(zetaGaussianQuadraticCoefficient T G).im| ≤
      (zetaGaussianQuadraticCoefficient T G).re := by
    rw [zetaGaussianQuadraticCoefficient_im, zetaGaussianQuadraticCoefficient_re,
      abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    exact one_div_le_one_div_of_le (by positivity) hscale
  rw [zetaGaussianQuadraticIntegral_eq T v hG.ne']
  have h := norm_fourierGaussian_le_of_im_le_re
    (zetaGaussianQuadraticCoefficient_re_pos T hG.ne') hi v
  have hden : Real.pi / (1 / G ^ 2) = Real.pi * G ^ 2 := by field_simp
  rw [zetaGaussianQuadraticCoefficient_re, hden, Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_sq_eq_abs, abs_of_pos hG] at h
  convert h using 1
  congr 2
  field_simp

theorem norm_zetaGaussianQuadraticIntegral_tail {T G L v : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hscale : G ^ 2 ≤ 2 * T)
    (hL : 0 ≤ L) (hfrequency : L ≤ G * |v|) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤
      Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8) := by
  have hsq : L ^ 2 ≤ (G * v) ^ 2 := by
    calc
      _ ≤ (G * |v|) ^ 2 := pow_le_pow_left₀ hL hfrequency 2
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]
  apply (norm_zetaGaussianQuadraticIntegral_le hT hG hscale v).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith)

end TaoTrudgianYang2025
