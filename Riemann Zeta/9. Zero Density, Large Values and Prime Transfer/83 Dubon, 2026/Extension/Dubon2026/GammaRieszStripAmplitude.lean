import Dubon2026.GammaRieszHolomorphic
import Dubon2026.GammaRieszKernel

/-! # Uniform genuine Gamma bounds across the finite Riesz contour-shift strip -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- An explicit weight-only constant for the actual Gamma symbol throughout the contour-shift strip. -/
def gammaRieszStripConstant (k : ℝ) : ℝ := Real.exp (4 * (k + 6) * (k + 2))

/-- Throughout the shift strip all four true Gamma shifts lie in a fixed positive interval. -/
theorem gammaRiesz_strip_shifts {k r β : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) :
    1 - β ∈ Ioc 0 (k + 2) ∧ β + r + 1 ∈ Ioc 0 (k + 2) ∧
      k - β ∈ Ioc 0 (k + 2) ∧ β + k - 1 ∈ Ioc 0 (k + 2) := by
  unfold gammaRieszLine at hβ0
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- The actual fixed-shift amplitude constant is uniformly controlled by a single weight-only value. -/
theorem doubleGammaAmplitudeConstant_le_strip {k a b c d : ℝ} (hk : 2 ≤ k)
    (ha : a ∈ Ioc 0 (k + 2)) (hb : b ∈ Ioc 0 (k + 2))
    (hc : c ∈ Ioc 0 (k + 2)) (hd : d ∈ Ioc 0 (k + 2)) :
    doubleGammaAmplitudeConstant a b c d ≤ gammaRieszStripConstant k := by
  have hab : |a - b| ≤ 2 * (k + 2) := abs_le.mpr ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩
  have hcd : |c - d| ≤ 2 * (k + 2) := abs_le.mpr ⟨by linarith [hc.1, hc.2, hd.1, hd.2], by linarith [hc.1, hc.2, hd.1, hd.2]⟩
  have h1 : (4 + max a b) * |a - b| ≤ (k + 6) * (2 * (k + 2)) :=
    mul_le_mul (by linarith [max_le ha.2 hb.2]) hab (abs_nonneg _) (by linarith)
  have h2 : (4 + max c d) * |c - d| ≤ (k + 6) * (2 * (k + 2)) :=
    mul_le_mul (by linarith [max_le hc.2 hd.2]) hcd (abs_nonneg _) (by linarith)
  rw [doubleGammaAmplitudeConstant, gammaRieszStripConstant, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The actual Gamma symbol has uniform inverse-square-root decay on every contour between its critical line and three eighths. -/
theorem norm_gammaRieszSymbol_le_on_strip {k r β t : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) (ht : 1 ≤ t) :
    ‖gammaRieszSymbol k r (gammaVerticalPoint β t)‖ ≤ gammaRieszStripConstant k * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨ha, hb, hc, hd⟩ := gammaRiesz_strip_shifts hk hr0 hr2 hβ0 hβ1
  rw [gammaRieszSymbol_vertical_eq, norm_mul]
  apply (doubleGammaAmplitude_le ha.1 hb.1 hc.1 hd.1 ht).trans
  apply mul_le_mul (doubleGammaAmplitudeConstant_le_strip hk ha hb hc hd)
  · apply Real.rpow_le_rpow_of_exponent_le ht
    unfold gammaRieszLine at hβ0
    linarith
  · exact Real.rpow_nonneg (by linarith) _
  · exact (Real.exp_pos _).le

/-- The real Mellin power is uniformly controlled across the whole fixed shift strip. -/
theorem rpow_gammaRiesz_strip_le {r β x : ℝ} (hr2 : r ≤ 2)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) (hx : 0 < x) :
    x ^ β ≤ Real.exp |Real.log x| := by
  have hb : |β| ≤ 1 := by
    unfold gammaRieszLine at hβ0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |Real.log x * β| := le_abs_self _
    _ = |Real.log x| * |β| := abs_mul _ _
    _ ≤ |Real.log x| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := mul_one _

/-- The full genuine Mellin integrand has one uniform horizontal-contour majorant at positive height. -/
theorem norm_gammaRieszMellinFunction_le_on_strip {k r β x t : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) (ht : 1 ≤ t) :
    ‖gammaRieszMellinFunction k r x (gammaVerticalPoint β t)‖ ≤
      (Real.exp |Real.log x| * gammaRieszStripConstant k) * t ^ (-(1 / 2 : ℝ)) := by
  rw [gammaRieszMellinFunction, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, gammaVerticalPoint_re]
  have hh := mul_le_mul (rpow_gammaRiesz_strip_le hr2 hβ0 hβ1 hx)
    (norm_gammaRieszSymbol_le_on_strip hk hr0 hr2 hβ0 hβ1 ht)
    (norm_nonneg _) (Real.exp_pos _).le
  convert hh using 1
  ring

end
end Dubon2026
