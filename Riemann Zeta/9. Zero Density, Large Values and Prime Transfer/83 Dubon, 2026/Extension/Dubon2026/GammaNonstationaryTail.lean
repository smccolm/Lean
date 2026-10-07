import Dubon2026.GammaTailVariation
import Dubon2026.GammaFrequencySeparation

/-! # Uniform genuine Gamma tail bounds beyond the stationary region -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- Genuine endpoint frequency separation controls any full finite interval at large height. -/
theorem norm_doubleGamma_product_interval_le_of_separation {a b c d T u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ))
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (hu : T ≤ u) (v : ℝ) (hfreq : doubleGammaFrequency a b c d v T ≤ -1 ∨ 1 ≤ doubleGammaFrequency a b c d v u) :
    ‖∫ t in T..u, Complex.exp (I * ((v * t : ℝ) : ℂ)) *
      reflectedGammaRatio a b t * reflectedGammaRatio c d t‖ ≤
      4 * doubleGammaAmplitudeConstant a b c d * (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T := by
  have hν : Differentiable ℝ (doubleGammaFrequency a b c d v) :=
    fun t => (hasDerivAt_doubleGammaFrequency ha hb hc hd v t).differentiableAt
  have hm := antitoneOn_doubleGammaFrequency ha hb hc hd hT haT hbT hcT hdT v
  have hz : Continuous (doubleGammaOscillatoryPhase a b c d v) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v t).continuousAt
  have hprimitive (t : ℝ) (ht : t ∈ Icc T u) :
      ‖∫ w in T..t, doubleGammaOscillatoryPhase a b c d v w‖ ≤ 2 := by
    rcases hfreq with hneg | hpos
    · apply (norm_phase_integral_le_of_negative_frequency hν.continuous
        (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v)
        (norm_doubleGammaOscillatoryPhase ha hb hc hd v 0) ht.1 (by norm_num : (0 : ℝ) < 1)
        (fun w hw => (hm (le_refl T) hw.1 hw.1).trans hneg)
        (fun w hw z hz hwz => hm hw.1 hz.1 hwz)).trans_eq
      norm_num
    · apply (norm_phase_integral_le_of_positive_frequency hν.continuous
        (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v)
        (norm_doubleGammaOscillatoryPhase ha hb hc hd v 0) ht.1 (by norm_num : (0 : ℝ) < 1)
        (fun w hw => hpos.trans (hm hw.1 hu (hw.2.trans ht.2)))
        (fun w hw z hz hwz => hm hw.1 hz.1 hwz)).trans_eq
      norm_num
  have hh := norm_integral_amplitude_mul_le (w := fun t => (doubleGammaAmplitude a b c d t : ℂ))
    (w' := fun t => ((deriv (doubleGammaAmplitude a b c d) t : ℝ) : ℂ)) hz hu
    (fun t _ => ((differentiable_doubleGammaAmplitude ha hb hc hd t).hasDerivAt).ofReal_comp)
    ((Complex.continuous_ofReal.comp (continuous_deriv_doubleGammaAmplitude ha hb hc hd)).intervalIntegrable _ _)
    hprimitive
  have he : (‖(doubleGammaAmplitude a b c d u : ℂ)‖ +
      ∫ t in T..u, ‖((deriv (doubleGammaAmplitude a b c d) t : ℝ) : ℂ)‖) ≤
      doubleGammaAmplitudeConstant a b c d * (1 + 2 * doubleGammaVariationConstant a b c d) / Real.sqrt T := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (doubleGammaAmplitude_pos ha hb hc hd u)] using
      doubleGammaAmplitude_tail_variation_le ha hb hc hd hp (by linarith : 1 ≤ T) hu
  rw [intervalIntegral.integral_congr (fun t _ => doubleGamma_product_eq_amplitude_mul_phase ha hb hc hd v t)]
  apply (hh.trans (mul_le_mul_of_nonneg_left he (by norm_num))).trans
  have hC : 0 ≤ doubleGammaAmplitudeConstant a b c d := by unfold doubleGammaAmplitudeConstant; positivity
  have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have heq : 2 * (doubleGammaAmplitudeConstant a b c d * (1 + 2 * doubleGammaVariationConstant a b c d) / Real.sqrt T) =
      (2 * doubleGammaAmplitudeConstant a b c d * (1 + 2 * doubleGammaVariationConstant a b c d)) / Real.sqrt T := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right (by nlinarith) hs

end
end Dubon2026
