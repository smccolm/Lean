import Dubon2026.GammaWeightedOscillation

/-! # Actual Gamma frequency separation and summable weighted block bounds -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The true two-ratio frequency differs from its logarithmic main term by an explicit inverse-height error. -/
theorem abs_doubleGammaFrequency_sub_log_le {a b c d t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ht : 1 ≤ t) (v : ℝ) :
    |doubleGammaFrequency a b c d v t - (v - 4 * Real.log t)| ≤ (16 + a + b + c + d) / t := by
  have ht' : 1 ≤ |t| := by rwa [abs_of_nonneg (by linarith : 0 ≤ t)]
  have h1 := abs_gammaRatioFrequency_add_log_le ha hb ht'
  have h2 := abs_gammaRatioFrequency_add_log_le hc hd ht'
  rw [abs_of_nonneg (by linarith : 0 ≤ t)] at h1 h2
  have he : doubleGammaFrequency a b c d v t - (v - 4 * Real.log t) =
      (gammaRatioFrequency a b t + 2 * Real.log t) + (gammaRatioFrequency c d t + 2 * Real.log t) := by
    unfold doubleGammaFrequency
    ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- At explicit height the genuine double Gamma frequency is decreasing on the whole upper ray. -/
theorem antitoneOn_doubleGammaFrequency {a b c d T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T) (v : ℝ) :
    AntitoneOn (doubleGammaFrequency a b c d v) (Ici T) := by
  have hν : Differentiable ℝ (doubleGammaFrequency a b c d v) :=
    fun t => (hasDerivAt_doubleGammaFrequency ha hb hc hd v t).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici T) hν.continuous.continuousOn hν.differentiableOn
  intro t ht
  have hTt : T ≤ t := interior_subset ht
  rw [(hasDerivAt_doubleGammaFrequency ha hb hc hd v t).deriv]
  have h1 := (gammaRatioFrequency_deriv_bounds ha hb (hT.trans hTt) (haT.trans hTt) (hbT.trans hTt)).2
  have h2 := (gammaRatioFrequency_deriv_bounds hc hd (hT.trans hTt) (hcT.trans hTt) (hdT.trans hTt)).2
  have hn : -1 / (2 * t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
  linarith

/-- Separation of the genuine endpoint frequency gives an inverse-square-root bound for the full weighted block. -/
theorem norm_doubleGamma_product_integral_le_of_frequency_separation {a b c d T l r lam : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ))
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ) (hlam : 0 < lam)
    (hsep : doubleGammaFrequency a b c d v l ≤ -lam ∨ lam ≤ doubleGammaFrequency a b c d v r) :
    ‖∫ t in l..r, Complex.exp (I * ((v * t : ℝ) : ℂ)) *
      reflectedGammaRatio a b t * reflectedGammaRatio c d t‖ ≤
      (2 / lam) * (doubleGammaAmplitudeConstant a b c d *
        (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T) := by
  have hν : Differentiable ℝ (doubleGammaFrequency a b c d v) :=
    fun t => (hasDerivAt_doubleGammaFrequency ha hb hc hd v t).differentiableAt
  have hm := antitoneOn_doubleGammaFrequency ha hb hc hd hT haT hbT hcT hdT v
  apply norm_doubleGamma_product_integral_le_of_primitive ha hb hc hd hp (by linarith) hl hlr hr v
  intro t ht
  have hmono : AntitoneOn (doubleGammaFrequency a b c d v) (Icc l t) :=
    fun u hu w hw huw => hm (hl.trans hu.1) (hl.trans hw.1) huw
  rcases hsep with hneg | hpos
  · apply norm_phase_integral_le_of_negative_frequency hν.continuous
      (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v)
      (norm_doubleGammaOscillatoryPhase ha hb hc hd v 0) ht.1 hlam _ hmono
    intro u hu
    exact (hm hl (hl.trans hu.1) hu.1).trans hneg
  · apply norm_phase_integral_le_of_positive_frequency hν.continuous
      (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v)
      (norm_doubleGammaOscillatoryPhase ha hb hc hd v 0) ht.1 hlam _ hmono
    intro u hu
    exact hpos.trans (hm (hl.trans hu.1) (hl.trans hlr) (hu.2.trans ht.2))

/-- Outside the explicit stationary logarithmic window all true frequency premises are discharged. -/
theorem norm_doubleGamma_product_integral_le_off_window {a b c d T l r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hp : (a - b) + (c - d) = -(1 / 2 : ℝ))
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (herror : 16 + a + b + c + d ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ)
    (hwindow : v - 4 * Real.log T ≤ -2 ∨ 2 ≤ v - 4 * Real.log (2 * T)) :
    ‖∫ t in l..r, Complex.exp (I * ((v * t : ℝ) : ℂ)) *
      reflectedGammaRatio a b t * reflectedGammaRatio c d t‖ ≤
      2 * (doubleGammaAmplitudeConstant a b c d *
        (1 + doubleGammaVariationConstant a b c d) / Real.sqrt T) := by
  have hm := antitoneOn_doubleGammaFrequency ha hb hc hd hT haT hbT hcT hdT v
  have hfreq (t : ℝ) (ht : T ≤ t) : |doubleGammaFrequency a b c d v t - (v - 4 * Real.log t)| ≤ 1 :=
    (abs_doubleGammaFrequency_sub_log_le ha hb hc hd (by linarith) v).trans
      ((div_le_one (by linarith : 0 < t)).mpr (herror.trans ht))
  have hsep : doubleGammaFrequency a b c d v l ≤ -(1 : ℝ) ∨ 1 ≤ doubleGammaFrequency a b c d v r := by
    rcases hwindow with hneg | hpos
    · left
      have hh := (abs_le.mp (hfreq T le_rfl)).2
      have hml := hm (le_refl T) hl hl
      linarith
    · right
      have hh := (abs_le.mp (hfreq (2 * T) (by linarith))).1
      have hmr := hm (hl.trans hlr) (show T ≤ 2 * T by linarith) hr
      linarith
  simpa only [div_one] using norm_doubleGamma_product_integral_le_of_frequency_separation
    ha hb hc hd hp hT haT hbT hcT hdT hl hlr hr v (by norm_num : (0 : ℝ) < 1) hsep

end
end Dubon2026
