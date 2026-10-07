import Dubon2026.GammaRatioAmplitude
import Dubon2026.DoubleGammaOscillation

/-! # Sharp amplitude bounds for the actual product of two reflected Gamma ratios -/

namespace Dubon2026

open Complex RiemannZeta.GuthMaynard

noncomputable section

/-- The true modulus of the product of the two reflected Gamma ratios. -/
def doubleGammaAmplitude (a b c d t : ℝ) : ℝ :=
  ‖reflectedGammaRatio a b t‖ * ‖reflectedGammaRatio c d t‖

/-- An explicit constant depending only on the four fixed Gamma shifts. -/
def doubleGammaAmplitudeConstant (a b c d : ℝ) : ℝ :=
  Real.exp ((4 + max a b) * |a - b|) * Real.exp ((4 + max c d) * |c - d|)

/-- The explicit logarithmic derivative constant for the actual product modulus. -/
def doubleGammaVariationConstant (a b c d : ℝ) : ℝ :=
  33 * (|a - b| + |c - d|)

/-- The product modulus is positive when all Gamma shifts are positive. -/
theorem doubleGammaAmplitude_pos {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    0 < doubleGammaAmplitude a b c d t :=
  mul_pos (norm_pos_iff.mpr (reflectedGammaRatio_ne_zero ha hb t))
    (norm_pos_iff.mpr (reflectedGammaRatio_ne_zero hc hd t))

/-- The actual product has exactly the sum of the two sharp horizontal Gamma powers. -/
theorem doubleGammaAmplitude_le {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ht : 1 ≤ t) :
    doubleGammaAmplitude a b c d t ≤
      doubleGammaAmplitudeConstant a b c d * t ^ ((a - b) + (c - d)) := by
  have hh := mul_le_mul (norm_reflectedGammaRatio_le ha hb ht)
    (norm_reflectedGammaRatio_le hc hd ht) (norm_nonneg _) (by positivity)
  convert hh using 1
  rw [Real.rpow_add (by linarith : 0 < t)]
  unfold doubleGammaAmplitudeConstant
  ring

/-- The actual product amplitude is differentiable at every real height. -/
theorem differentiable_doubleGammaAmplitude {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Differentiable ℝ (doubleGammaAmplitude a b c d) := fun t =>
  ((hasDerivAt_norm_reflectedGammaRatio ha hb t).mul
    (hasDerivAt_norm_reflectedGammaRatio hc hd t)).differentiableAt

/-- Its genuine derivative is bounded by the amplitude times a fixed inverse-height constant. -/
theorem abs_deriv_doubleGammaAmplitude_le {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ht : 1 ≤ t) :
    |deriv (doubleGammaAmplitude a b c d) t| ≤
      doubleGammaVariationConstant a b c d / t * doubleGammaAmplitude a b c d t := by
  have he := ((hasDerivAt_norm_reflectedGammaRatio ha hb t).differentiableAt.hasDerivAt.mul
    (hasDerivAt_norm_reflectedGammaRatio hc hd t).differentiableAt.hasDerivAt).deriv
  change deriv (doubleGammaAmplitude a b c d) t = _ at he
  rw [he]
  calc
    _ ≤ |deriv (fun u => ‖reflectedGammaRatio a b u‖) t * ‖reflectedGammaRatio c d t‖| +
        |‖reflectedGammaRatio a b t‖ * deriv (fun u => ‖reflectedGammaRatio c d u‖) t| := abs_add_le _ _
    _ ≤ ((33 * |a - b| / t) * ‖reflectedGammaRatio a b t‖) * ‖reflectedGammaRatio c d t‖ +
        ‖reflectedGammaRatio a b t‖ * ((33 * |c - d| / t) * ‖reflectedGammaRatio c d t‖) := by
      simp only [abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (abs_deriv_norm_reflectedGammaRatio_le ha hb ht) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_deriv_norm_reflectedGammaRatio_le hc hd ht) (norm_nonneg _))
    _ = _ := by unfold doubleGammaVariationConstant doubleGammaAmplitude; ring

/-- The actual digamma function on a positive vertical line is continuous. -/
theorem continuous_digamma_vertical {a : ℝ} (ha : 0 < a) :
    Continuous (fun t => digamma (gammaVerticalPoint a t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one
    (z := gammaVerticalPoint a t) (by simpa only [gammaVerticalPoint_re] using ha)).continuousAt.comp
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt

/-- The genuine product amplitude has continuous derivative, allowing ordinary integration by parts. -/
theorem continuous_deriv_doubleGammaAmplitude {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Continuous (deriv (doubleGammaAmplitude a b c d)) := by
  have h1 : Continuous (fun t => ‖reflectedGammaRatio a b t‖) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_norm_reflectedGammaRatio ha hb t).continuousAt
  have h2 : Continuous (fun t => ‖reflectedGammaRatio c d t‖) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_norm_reflectedGammaRatio hc hd t).continuousAt
  have he (t : ℝ) := ((hasDerivAt_norm_reflectedGammaRatio ha hb t).mul
    (hasDerivAt_norm_reflectedGammaRatio hc hd t)).deriv
  change ∀ t, deriv (doubleGammaAmplitude a b c d) t = _ at he
  exact (((((Complex.continuous_im.comp (continuous_digamma_vertical hb)).sub (Complex.continuous_im.comp (continuous_digamma_vertical ha))).mul h1).mul h2).add
    (h1.mul (((Complex.continuous_im.comp (continuous_digamma_vertical hd)).sub (Complex.continuous_im.comp (continuous_digamma_vertical hc))).mul h2))).congr
      (fun t => (he t).symm)

/-- The literal modulated product is its genuine amplitude times the proved normalized phase. -/
theorem doubleGamma_product_eq_amplitude_mul_phase {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (v t : ℝ) :
    Complex.exp (I * ((v * t : ℝ) : ℂ)) * reflectedGammaRatio a b t * reflectedGammaRatio c d t =
      (doubleGammaAmplitude a b c d t : ℂ) * doubleGammaOscillatoryPhase a b c d v t := by
  rw [reflectedGammaRatio_eq_norm_mul_phase ha hb t, reflectedGammaRatio_eq_norm_mul_phase hc hd t]
  simp only [doubleGammaAmplitude, doubleGammaOscillatoryPhase, ofReal_mul]
  ring

end
end Dubon2026
