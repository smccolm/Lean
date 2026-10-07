import Dubon2026.GammaDyadicAmplitude
import Dubon2026.OscillatoryAmplitude

/-! # Weighted cancellation for the actual two-ratio Gamma product -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A genuine phase primitive bound transfers to the literal Gamma product using its proved variation. -/
theorem norm_doubleGamma_product_integral_le_of_primitive {a b c d T l r M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ)) (hT : 1 ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ)
    (hM : ∀ t ∈ Icc l r, ‖∫ u in l..t, doubleGammaOscillatoryPhase a b c d v u‖ ≤ M) :
    ‖∫ t in l..r, Complex.exp (I * ((v * t : ℝ) : ℂ)) *
      reflectedGammaRatio a b t * reflectedGammaRatio c d t‖ ≤
      M * (doubleGammaAmplitudeConstant a b c d *
        (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T) := by
  have hM0 : 0 ≤ M := by simpa using hM l ⟨le_rfl, hlr⟩
  have hz : Continuous (doubleGammaOscillatoryPhase a b c d v) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v t).continuousAt
  have hh := norm_integral_amplitude_mul_le (w := fun t => (doubleGammaAmplitude a b c d t : ℂ))
    (w' := fun t => ((deriv (doubleGammaAmplitude a b c d) t : ℝ) : ℂ)) hz hlr
    (fun t _ => ((differentiable_doubleGammaAmplitude ha hb hc hd t).hasDerivAt).ofReal_comp)
    ((Complex.continuous_ofReal.comp (continuous_deriv_doubleGammaAmplitude ha hb hc hd)).intervalIntegrable _ _) hM
  have he : (‖(doubleGammaAmplitude a b c d r : ℂ)‖ +
      ∫ t in l..r, ‖((deriv (doubleGammaAmplitude a b c d) t : ℝ) : ℂ)‖) ≤
      doubleGammaAmplitudeConstant a b c d * (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (doubleGammaAmplitude_pos ha hb hc hd r)] using
      doubleGammaAmplitude_variation_le ha hb hc hd hp hT hl hlr hr
  rw [intervalIntegral.integral_congr (fun t _ => doubleGamma_product_eq_amplitude_mul_phase ha hb hc hd v t)]
  exact hh.trans (mul_le_mul_of_nonneg_left he hM0)

/-- The full genuine Gamma product has uniform bounded integral on every high dyadic subinterval.
The square-root phase cancellation exactly cancels its inverse-square-root amplitude. -/
theorem norm_doubleGamma_product_integral_le {a b c d T l r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ))
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ) :
    ‖∫ t in l..r, Complex.exp (I * ((v * t : ℝ) : ℂ)) *
      reflectedGammaRatio a b t * reflectedGammaRatio c d t‖ ≤
      8 * doubleGammaAmplitudeConstant a b c d * (1 + doubleGammaVariationConstant a b c d) := by
  have hh := norm_doubleGamma_product_integral_le_of_primitive ha hb hc hd hp (by linarith : 1 ≤ T)
    hl hlr hr v (fun t ht => norm_doubleGammaOscillatoryPhase_integral_le ha hb hc hd hT haT hbT hcT hdT
      hl ht.1 (ht.2.trans hr) v)
  convert hh using 1
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr (by linarith : 0 < T)).ne'
  field_simp

end
end Dubon2026
