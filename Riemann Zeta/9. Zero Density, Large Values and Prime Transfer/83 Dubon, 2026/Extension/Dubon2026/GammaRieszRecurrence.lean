import Dubon2026.GammaRieszShiftUniform

/-! # The exact adjacent-order recurrence of the genuine Riesz Gamma symbol -/

namespace Dubon2026

open Complex

noncomputable section

/-- Gamma recurrence exactly removes the factor introduced by differentiating the Riesz weight. -/
theorem gammaRieszSymbol_order_sub_one (k r : ℝ) {s : ℂ} (hs : s + (r : ℂ) ≠ 0) :
    gammaRieszSymbol k (r - 1) s = (s + (r : ℂ)) * gammaRieszSymbol k r s := by
  have he : s + ((r + 1 : ℝ) : ℂ) = (s + (r : ℂ)) + 1 := by push_cast; ring
  have he' : s + (((r - 1) + 1 : ℝ) : ℂ) = s + (r : ℂ) := by congr 1; push_cast; ring
  rw [gammaRieszSymbol, gammaRieszSymbol, he, he', Gamma_add_one _ hs]
  symm
  calc
    _ = ((s + (r : ℂ)) * (Gamma (1 - s) * Gamma ((k : ℂ) - s))) /
        ((s + (r : ℂ)) * (Gamma (s + (r : ℂ)) * Gamma (s + ((k - 1 : ℝ) : ℂ)))) := by ring
    _ = _ := mul_div_mul_left _ _ hs

/-- The literal weighted Mellin integrand whose derivative passes between adjacent Riesz orders. -/
def gammaRieszWeightedIntegrand (k r c β t x : ℝ) : ℂ :=
  ((x ^ r : ℝ) : ℂ) * gammaRieszMellinFunction k r (c * x) (gammaVerticalPoint β t)

/-- Differentiating the actual weighted integrand on the common line lowers its Riesz order by one. -/
theorem hasDerivAt_gammaRieszWeightedIntegrand {r c x : ℝ} (hr : 1 ≤ r)
    (hc : 0 < c) (hx : 0 < x) (k t : ℝ) :
    HasDerivAt (gammaRieszWeightedIntegrand k r c (3 / 8) t)
      (gammaRieszWeightedIntegrand k (r - 1) c (3 / 8) t x) x := by
  let s := gammaVerticalPoint (3 / 8) t
  have hs : s ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [s, gammaVerticalPoint_re] at hh
  have hsr : s + (r : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re, s, gammaVerticalPoint_re] at hh
    linarith
  have hcx := mul_pos hc hx
  have hp := (hasDerivAt_ofReal_cpow_const hcx.ne' hs).scomp x ((hasDerivAt_id x).const_mul c)
  have hw := (Real.hasDerivAt_rpow_const (p := r) (Or.inl hx.ne')).ofReal_comp
  have hh := (hw.mul hp).mul_const (gammaRieszSymbol k r s)
  convert hh using 1
  · ext y
    unfold gammaRieszWeightedIntegrand gammaRieszMellinFunction
    change (y ^ r : ℝ) * (((c * y : ℝ) : ℂ) ^ s * gammaRieszSymbol k r s) =
      (((y ^ r : ℝ) : ℂ) * ((c * y : ℝ) : ℂ) ^ s) * gammaRieszSymbol k r s
    ring
  · have hpow : x ^ r = x ^ (r - 1) * x := by
      calc
        x ^ r = x ^ ((r - 1) + 1) := by congr 1; ring
        _ = x ^ (r - 1) * x := by rw [Real.rpow_add hx, Real.rpow_one]
    have hcpow : ((c * x : ℝ) : ℂ) ^ (s - 1) = ((c * x : ℝ) : ℂ) ^ s / ((c * x : ℝ) : ℂ) := by
      rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hcx.ne'), Complex.cpow_one]
    unfold gammaRieszWeightedIntegrand gammaRieszMellinFunction
    rw [gammaRieszSymbol_order_sub_one k r hsr, hpow, hcpow]
    simp only [Complex.ofReal_mul, Complex.real_smul, mul_one, Function.comp_apply]
    dsimp only [s] at *
    field_simp [Complex.ofReal_ne_zero.mpr hc.ne', Complex.ofReal_ne_zero.mpr hx.ne']
    ring

end
end Dubon2026
