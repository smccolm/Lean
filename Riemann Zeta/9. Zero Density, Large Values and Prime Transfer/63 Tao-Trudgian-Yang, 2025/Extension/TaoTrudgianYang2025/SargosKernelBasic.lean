import GafniTao.FordTentSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Real tent and sinc-square kernels for Robert--Sargos windows

These are whole-line kernels, not the periodic tent from Ford.
The scaled sinc-square kernel is integrable. The real-frequency
Fourier identity is a subsequent proof obligation, not assumed here.
-/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

def sargosRealTent (w x : ℝ) : ℝ := max 0 (1-|x|/w)

def sargosSincKernel (w x : ℝ) : ℝ := w*Real.sinc (Real.pi*w*x)^2

theorem sargos_mul_sinc (x : ℝ) : x*Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

theorem sargos_sinc_sq_majorant (x : ℝ) :
    Real.sinc x^2 ≤ 2/(1+x^2) := by
  have hs : Real.sinc x^2 ≤ 1 := by
    have h := abs_le.mp (Real.abs_sinc_le_one x)
    nlinarith
  have ht : Real.sin x^2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin x,Real.sin_le_one x]
  have he := congrArg (fun y : ℝ => y^2) (sargos_mul_sinc x)
  apply (le_div_iff₀ (by positivity : 0 < 1+x^2)).mpr
  nlinarith only [hs,ht,he]

theorem integrable_sargos_sinc_sq :
    Integrable (fun x : ℝ => Real.sinc x^2) := by
  have hmajor : Integrable (fun x : ℝ => 2/(1+x^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul 2
  apply hmajor.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact sargos_sinc_sq_majorant x)

theorem sargosSincKernel_nonneg {w : ℝ} (hw : 0 ≤ w) (x : ℝ) :
    0 ≤ sargosSincKernel w x := by
  exact mul_nonneg hw (sq_nonneg _)

theorem continuous_sargosSincKernel (w : ℝ) : Continuous (sargosSincKernel w) := by
  unfold sargosSincKernel
  fun_prop

theorem integrable_sargosSincKernel {w : ℝ} (hw : 0 < w) :
    Integrable (sargosSincKernel w) := by
  have hs := integrable_sargos_sinc_sq.comp_mul_left'
    (show Real.pi*w ≠ 0 by positivity)
  exact hs.const_mul w

theorem sargosRealTent_nonneg (w x : ℝ) : 0 ≤ sargosRealTent w x := le_max_left _ _

theorem sargosRealTent_le_one {w : ℝ} (hw : 0 < w) (x : ℝ) :
    sargosRealTent w x ≤ 1 := by
  apply max_le (by norm_num)
  have h : 0 ≤ |x|/w := by positivity
  linarith

theorem sargosRealTent_zero_of_le_abs {w x : ℝ} (hw : 0 < w) (hx : w ≤ |x|) :
    sargosRealTent w x = 0 := by
  apply max_eq_left
  have h : 1 ≤ |x|/w := (le_div_iff₀ hw).mpr (by simpa using hx)
  linarith

theorem sargosRealTent_eq_of_abs_le {w x : ℝ} (hw : 0 < w) (hx : |x| ≤ w) :
    sargosRealTent w x = 1-|x|/w := by
  apply max_eq_right
  exact sub_nonneg.mpr ((div_le_one hw).mpr hx)

theorem continuous_sargosRealTent (w : ℝ) : Continuous (sargosRealTent w) := by
  unfold sargosRealTent
  fun_prop

theorem hasCompactSupport_sargosRealTent {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (sargosRealTent w) := by
  apply HasCompactSupport.intro (K := Icc (-w) w) isCompact_Icc
  intro x hx
  apply sargosRealTent_zero_of_le_abs hw
  by_contra h
  exact hx (abs_le.mp (le_of_lt (lt_of_not_ge h)))

theorem integrable_sargosRealTent {w : ℝ} (hw : 0 < w) :
    Integrable (sargosRealTent w) :=
  (continuous_sargosRealTent w).integrable_of_hasCompactSupport
    (hasCompactSupport_sargosRealTent hw)

end TaoTrudgianYang2025
