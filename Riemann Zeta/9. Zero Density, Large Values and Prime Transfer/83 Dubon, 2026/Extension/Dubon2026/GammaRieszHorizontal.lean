import Dubon2026.GammaRieszStripAmplitude

/-! # Vanishing actual horizontal edges for the Riesz Gamma contour shift -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Reflection of height preserves the actual Mellin integrand's modulus. -/
theorem norm_gammaRieszMellinFunction_neg_height {x : ℝ} (hx : 0 < x) (k r β t : ℝ) :
    ‖gammaRieszMellinFunction k r x (gammaVerticalPoint β (-t))‖ =
      ‖gammaRieszMellinFunction k r x (gammaVerticalPoint β t)‖ := by
  unfold gammaRieszMellinFunction
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [gammaVerticalPoint_re, gammaRieszSymbol_vertical_eq, norm_mul,
    reflectedGammaRatio_neg_eq_conj, norm_conj]

/-- The actual horizontal majorant is valid at either sign of the height. -/
theorem norm_gammaRieszMellinFunction_le_abs_height {k r β x t : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) (ht : 1 ≤ |t|) :
    ‖gammaRieszMellinFunction k r x (gammaVerticalPoint β t)‖ ≤
      (Real.exp |Real.log x| * gammaRieszStripConstant k) * |t| ^ (-(1 / 2 : ℝ)) := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at ht ⊢
    exact norm_gammaRieszMellinFunction_le_on_strip hk hr0 hr2 hx hβ0 hβ1 ht
  · have hn : t < 0 := lt_of_not_ge ht0
    have hh := norm_gammaRieszMellinFunction_le_on_strip hk hr0 hr2 hx hβ0 hβ1
      (show 1 ≤ -t by simpa only [abs_of_neg hn] using ht)
    rw [norm_gammaRieszMellinFunction_neg_height hx] at hh
    simpa only [abs_of_neg hn] using hh

/-- Both actual horizontal edges have a uniform decaying bound across the full admissible contour interval. -/
theorem norm_gammaRiesz_horizontal_integral_le {k r x β₀ β₁ t : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hlo : gammaRieszLine r ≤ β₀) (hab : β₀ ≤ β₁) (hhi : β₁ ≤ 3 / 8) (ht : 1 ≤ |t|) :
    ‖HIntegral (gammaRieszMellinFunction k r x) β₀ β₁ t‖ ≤
      ((β₁ - β₀) * (Real.exp |Real.log x| * gammaRieszStripConstant k)) * |t| ^ (-(1 / 2 : ℝ)) := by
  have hg0 : -(1 / 4 : ℝ) < gammaRieszLine r := by unfold gammaRieszLine; linarith
  have hline : Continuous (fun β : ℝ => gammaVerticalPoint β t) := by unfold gammaVerticalPoint; fun_prop
  have hc : ContinuousOn (fun β : ℝ => gammaRieszMellinFunction k r x (gammaVerticalPoint β t)) (uIcc β₀ β₁) := by
    intro β hβ
    rw [uIcc_of_le hab] at hβ
    apply ContinuousAt.continuousWithinAt
    apply (differentiableAt_gammaRieszMellinFunction hk hr0 hx
      (by simpa only [gammaVerticalPoint_re] using hg0.trans_le (hlo.trans hβ.1))
      (by simp only [gammaVerticalPoint_re]; linarith [hβ.2])).continuousAt.comp
    exact hline.continuousAt
  change ‖∫ β in β₀..β₁, gammaRieszMellinFunction k r x (gammaVerticalPoint β t)‖ ≤ _
  calc
    _ ≤ ∫ β in β₀..β₁, ‖gammaRieszMellinFunction k r x (gammaVerticalPoint β t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _ in β₀..β₁, (Real.exp |Real.log x| * gammaRieszStripConstant k) * |t| ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_mono_on hab hc.norm.intervalIntegrable (continuous_const.intervalIntegrable _ _)
        (fun β hβ => norm_gammaRieszMellinFunction_le_abs_height hk hr0 hr2 hx (hlo.trans hβ.1) (hβ.2.trans hhi) ht)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- The genuine upper horizontal contour integral vanishes as its height tends to infinity. -/
theorem tendsto_gammaRiesz_horizontal_integral_zero {k r x β₀ β₁ : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hlo : gammaRieszLine r ≤ β₀) (hab : β₀ ≤ β₁) (hhi : β₁ ≤ 3 / 8) :
    Tendsto (fun T : ℝ => HIntegral (gammaRieszMellinFunction k r x) β₀ β₁ T) atTop (𝓝 0) := by
  have hz : Tendsto (fun T : ℝ => ((β₁ - β₀) * (Real.exp |Real.log x| * gammaRieszStripConstant k)) *
      T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      ((β₁ - β₀) * (Real.exp |Real.log x| * gammaRieszStripConstant k))
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using
    norm_gammaRiesz_horizontal_integral_le hk hr0 hr2 hx hlo hab hhi
      (by rw [abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT : 1 ≤ |T|)

end
end Dubon2026
