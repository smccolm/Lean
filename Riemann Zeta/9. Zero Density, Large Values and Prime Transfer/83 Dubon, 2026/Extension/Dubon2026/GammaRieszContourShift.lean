import Dubon2026.GammaRieszHorizontal
import Dubon2026.GammaRieszUniformConvergence

/-! # A genuine finite-rectangle contour shift for the improper Riesz Gamma kernel -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The literal normalized vertical cutoff on an arbitrary real line. -/
def gammaRieszVerticalCutoff (k r x β T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T,
    gammaRieszMellinFunction k r x (gammaVerticalPoint β t)

/-- The genuine lower horizontal edge also vanishes as the symmetric height tends to infinity. -/
theorem tendsto_gammaRiesz_lower_horizontal_integral_zero {k r x β₀ β₁ : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hlo : gammaRieszLine r ≤ β₀) (hab : β₀ ≤ β₁) (hhi : β₁ ≤ 3 / 8) :
    Tendsto (fun T : ℝ => HIntegral (gammaRieszMellinFunction k r x) β₀ β₁ (-T)) atTop (𝓝 0) := by
  have hz : Tendsto (fun T : ℝ => ((β₁ - β₀) * (Real.exp |Real.log x| * gammaRieszStripConstant k)) *
      T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      ((β₁ - β₀) * (Real.exp |Real.log x| * gammaRieszStripConstant k))
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using
    norm_gammaRiesz_horizontal_integral_le hk hr0 hr2 hx hlo hab hhi
      (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)]; exact hT : 1 ≤ |-T|)

/-- The difference of actual normalized vertical cutoffs equals the two actual horizontal edges. -/
theorem gammaRieszVerticalCutoff_sub_eq {k r x β₀ β₁ T : ℝ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hx : 0 < x)
    (hlo : -(1 / 4 : ℝ) < β₀) (hab : β₀ ≤ β₁) (hhi : β₁ < 1) (hT : 0 ≤ T) :
    gammaRieszVerticalCutoff k r x β₁ T - gammaRieszVerticalCutoff k r x β₀ T =
      (1 / (2 * Real.pi) : ℝ) • (I *
        (HIntegral (gammaRieszMellinFunction k r x) β₀ β₁ (-T) -
          HIntegral (gammaRieszMellinFunction k r x) β₀ β₁ T)) := by
  have hh := gammaRieszMellin_rectangle_eq_zero hk hr hx hlo hab hhi hT
  simp only [RectangleIntegral, gammaVerticalPoint_re, gammaVerticalPoint_im, VIntegral, smul_eq_mul] at hh
  have hi := congrArg (fun z : ℂ => I * z) hh
  simp only [mul_add, mul_sub, mul_zero, ← mul_assoc, I_mul_I, neg_one_mul] at hi
  rw [gammaRieszVerticalCutoff, gammaRieszVerticalCutoff, ← smul_sub]
  congr 1
  unfold gammaVerticalPoint
  linear_combination -hi

/-- Moving the actual improper Riesz Gamma integral to any admissible line preserves its proved kernel value. -/
theorem tendsto_gammaRieszVerticalCutoff {k r x β : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hβ0 : gammaRieszLine r ≤ β) (hβ1 : β ≤ 3 / 8) :
    Tendsto (gammaRieszVerticalCutoff k r x β) atTop (𝓝 (gammaRieszKernel k r x)) := by
  have hcrit : Tendsto (gammaRieszVerticalCutoff k r x (gammaRieszLine r)) atTop
      (𝓝 (gammaRieszKernel k r x)) := tendsto_gammaRieszKernel hk hr0 hr2 hx
  have hp := tendsto_gammaRiesz_horizontal_integral_zero hk hr0 hr2 hx (le_refl (gammaRieszLine r)) hβ0 hβ1
  have hn := tendsto_gammaRiesz_lower_horizontal_integral_zero hk hr0 hr2 hx (le_refl (gammaRieszLine r)) hβ0 hβ1
  have hc := ((hn.sub hp).const_mul I).const_smul (1 / (2 * Real.pi) : ℝ)
  simp only [sub_self, mul_zero, smul_zero] at hc
  have hs := hcrit.add hc
  simp only [add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have he := gammaRieszVerticalCutoff_sub_eq hk hr0 hx
    (by unfold gammaRieszLine; linarith : -(1 / 4 : ℝ) < gammaRieszLine r)
    hβ0 (by linarith : β < 1) hT
  linear_combination -he

end
end Dubon2026
