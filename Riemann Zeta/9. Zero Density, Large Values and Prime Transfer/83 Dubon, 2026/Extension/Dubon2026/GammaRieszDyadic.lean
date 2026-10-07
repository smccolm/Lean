import Dubon2026.GammaRieszSymbol

/-! # Exact dyadic bounds for the genuine degree-four Riesz Gamma integrands -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The literal vertical Mellin integrand for the degree-four Riesz Gamma kernel. -/
def gammaRieszIntegrand (k r x t : ℝ) : ℂ :=
  (x : ℂ) ^ gammaVerticalPoint (gammaRieszLine r) t *
    gammaRieszSymbol k r (gammaVerticalPoint (gammaRieszLine r) t)

/-- The explicit fixed-weight and fixed-order amplitude-variation constant. -/
def gammaRieszConstant (k r : ℝ) : ℝ :=
  doubleGammaAmplitudeConstant (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
    (k - gammaRieszLine r) (gammaRieszLine r + k - 1) *
  (1 + doubleGammaVariationConstant (1 - gammaRieszLine r) (gammaRieszLine r + r + 1)
    (k - gammaRieszLine r) (gammaRieszLine r + k - 1))

/-- The Riesz constant is strictly positive, with no dependence on the Mellin argument or the height. -/
theorem gammaRieszConstant_pos (k r : ℝ) : 0 < gammaRieszConstant k r := by
  unfold gammaRieszConstant doubleGammaAmplitudeConstant doubleGammaVariationConstant
  positivity

/-- The actual Riesz integrand is its exact real power times the two reflected Gamma factors and linear phase. -/
theorem gammaRieszIntegrand_eq {x : ℝ} (hx : 0 < x) (k r t : ℝ) :
    gammaRieszIntegrand k r x t = (x ^ gammaRieszLine r : ℝ) *
      (Complex.exp (I * ((Real.log x * t : ℝ) : ℂ)) *
        reflectedGammaRatio (1 - gammaRieszLine r) (gammaRieszLine r + r + 1) t *
        reflectedGammaRatio (k - gammaRieszLine r) (gammaRieszLine r + k - 1) t) := by
  rw [gammaRieszIntegrand, positive_cpow_vertical_eq hx, gammaRieszSymbol_vertical_eq]
  ring

/-- The actual Riesz integrand is continuous in height, so every finite truncation is a genuine integral. -/
theorem continuous_gammaRieszIntegrand {k r x : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hx : 0 < x) : Continuous (gammaRieszIntegrand k r x) := by
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_shifts_pos hk hr0 hr2
  have h1 := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_reflectedGammaRatio ha hb t).continuousAt
  have h2 := continuous_iff_continuousAt.mpr fun t => (hasDerivAt_reflectedGammaRatio hc hd t).continuousAt
  have he : Continuous (fun t : ℝ => Complex.exp (I * ((Real.log x * t : ℝ) : ℂ))) := by fun_prop
  exact ((continuous_const.mul ((he.mul h1).mul h2))).congr (fun t => (gammaRieszIntegrand_eq hx k r t).symm)

/-- The complete literal Riesz Gamma integrand has its sharp uniform power bound on high dyadic subintervals. -/
theorem norm_gammaRieszIntegrand_integral_le {k r x T l u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : 128 ≤ T) (hkT : 21 + 2 * k ≤ T) (hl : T ≤ l) (hlu : l ≤ u) (hu : u ≤ 2 * T) :
    ‖∫ t in l..u, gammaRieszIntegrand k r x t‖ ≤ 8 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_shifts_pos hk hr0 hr2
  obtain ⟨haT, hbT, hcT, hdT, _⟩ := gammaRiesz_shifts_le hk hr0 hr2 hkT
  have hh := norm_doubleGamma_product_integral_le ha hb hc hd (gammaRiesz_power k r)
    hT haT hbT hcT hdT hl hlu hu (Real.log x)
  rw [intervalIntegral.integral_congr (fun t _ => gammaRieszIntegrand_eq hx k r t),
    intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le (gammaRieszLine r)) using 1
  unfold gammaRieszConstant
  ring

/-- Away from the stationary logarithmic window the literal Riesz Gamma blocks have summable inverse-square-root decay. -/
theorem norm_gammaRieszIntegrand_integral_le_off_window {k r x T l u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : 128 ≤ T) (hkT : 21 + 2 * k ≤ T) (hl : T ≤ l) (hlu : l ≤ u) (hu : u ≤ 2 * T)
    (hwindow : Real.log x - 4 * Real.log T ≤ -2 ∨ 2 ≤ Real.log x - 4 * Real.log (2 * T)) :
    ‖∫ t in l..u, gammaRieszIntegrand k r x t‖ ≤
      2 * gammaRieszConstant k r * x ^ gammaRieszLine r / Real.sqrt T := by
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_shifts_pos hk hr0 hr2
  obtain ⟨haT, hbT, hcT, hdT, herror⟩ := gammaRiesz_shifts_le hk hr0 hr2 hkT
  have hh := norm_doubleGamma_product_integral_le_off_window ha hb hc hd (gammaRiesz_power k r)
    hT haT hbT hcT hdT herror hl hlu hu (Real.log x) hwindow
  rw [intervalIntegral.integral_congr (fun t _ => gammaRieszIntegrand_eq hx k r t),
    intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  convert mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le (gammaRieszLine r)) using 1
  unfold gammaRieszConstant
  ring

end
end Dubon2026
