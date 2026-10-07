import Dubon2026.GammaVerticalPhase
import Dubon2026.TrigammaAsymptotic

/-! # Quantitative curvature of the actual vertical Gamma phase -/

namespace Dubon2026

open Complex RiemannZeta.GuthMaynard

noncomputable section

/-- The derivative of the genuine phase frequency is twice the imaginary part of the actual trigamma function. -/
theorem hasDerivAt_gammaVerticalFrequency {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (gammaVerticalFrequency a) (2 * (deriv digamma (gammaVerticalPoint a t)).im) t := by
  have hp := (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one
    (z := gammaVerticalPoint a t) (by simpa only [gammaVerticalPoint_re] using ha)).differentiableAt.hasDerivAt
  have hi : HasDerivAt (fun z : ℂ => (a : ℂ) + z * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (a : ℂ)
  have hh := ((hp.comp (t : ℂ) hi).real_of_complex).const_mul (-2)
  convert hh using 1
  simp only [mul_re, I_re, I_im, mul_zero, mul_one, zero_sub]
  ring

/-- The actual imaginary trigamma value has its exact rational main term with uniform second-order error. -/
theorem abs_im_trigamma_vertical_add_le {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) :
    |(deriv digamma (gammaVerticalPoint a t)).im + t / (a ^ 2 + t ^ 2)| ≤ 32 / t ^ 2 := by
  have hb := (Complex.abs_im_le_norm (deriv digamma (gammaVerticalPoint a t) -
    (gammaVerticalPoint a t)⁻¹)).trans (norm_deriv_digamma_sub_inv_le
      (by simpa only [gammaVerticalPoint_re] using ha)
      (by simpa only [gammaVerticalPoint_im, abs_of_nonneg (by linarith : 0 ≤ t)] using ht))
  simpa [gammaVerticalPoint, Complex.inv_im, Complex.normSq_apply, pow_two, neg_div, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ t)] using hb

/-- At explicit large heights the true imaginary trigamma value is negative and has reciprocal size. -/
theorem im_trigamma_vertical_bounds {a t : ℝ} (ha : 0 < a) (ht : 128 ≤ t) (hat : a ≤ t) :
    -(2 * (1 / t)) ≤ (deriv digamma (gammaVerticalPoint a t)).im ∧
      (deriv digamma (gammaVerticalPoint a t)).im ≤ -(1 / t) / 4 := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < a ^ 2 + t ^ 2 := by positivity
  have hb := abs_le.mp (abs_im_trigamma_vertical_add_le ha (by linarith : 1 ≤ t))
  have hlo : (1 / t) / 2 ≤ t / (a ^ 2 + t ^ 2) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < t * 2) hd).mpr
    nlinarith [sq_le_sq₀ ha.le ht0.le |>.mpr hat]
  have hhi : t / (a ^ 2 + t ^ 2) ≤ 1 / t := by
    apply (div_le_div_iff₀ hd ht0).mpr
    nlinarith [sq_nonneg a]
  have he : 32 / t ^ 2 ≤ (1 / t) / 4 := by
    rw [div_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (by positivity : 0 < t * 4)).mpr
    nlinarith
  constructor <;> nlinarith

/-- The actual Gamma phase frequency is strictly decreasing at large height, with the precise reciprocal curvature scale. -/
theorem gammaVerticalFrequency_deriv_bounds {a t : ℝ} (ha : 0 < a) (ht : 128 ≤ t) (hat : a ≤ t) :
    -4 / t ≤ deriv (gammaVerticalFrequency a) t ∧
      deriv (gammaVerticalFrequency a) t ≤ -1 / (2 * t) := by
  rw [(hasDerivAt_gammaVerticalFrequency ha t).deriv]
  have hb := im_trigamma_vertical_bounds ha ht hat
  have h1 : -4 / t = -4 * (1 / t) := by ring
  have h2 : -1 / (2 * t) = -(1 / t) / 2 := by ring
  rw [h1, h2]
  constructor <;> nlinarith

end
end Dubon2026
