import TaoTrudgianYang2025.BetaTaylorGlobal
import TaoTrudgianYang2025.FresnelEvaluation
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The actual negative quadratic character and its Fresnel window

The Fourier convention is e(x)=exp(2*pi*i*x). The evaluated leading
coefficient is e(-1/8)/sqrt(T), with an explicit finite-window error.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def betaQuadraticKernel (T z : ℝ) : ℂ := (𝐞 (-(T/2)*z^2) : ℂ)

theorem continuous_betaQuadraticKernel (T : ℝ) : Continuous (betaQuadraticKernel T) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).comp (by fun_prop)

theorem norm_betaQuadraticKernel (T z : ℝ) : ‖betaQuadraticKernel T z‖ = 1 :=
  Circle.norm_coe _

theorem betaQuadraticKernel_neg (T z : ℝ) :
    betaQuadraticKernel T (-z) = betaQuadraticKernel T z := by
  simp only [betaQuadraticKernel,neg_sq]

theorem betaQuadraticKernel_hasDerivAt (T z : ℝ) :
    HasDerivAt (betaQuadraticKernel T)
      ((-2*Real.pi*T : ℂ)*Complex.I*(z : ℂ)*betaQuadraticKernel T z) z := by
  have hd := (Real.hasDerivAt_fourierChar (-(T/2)*z^2)).scomp z
    (((hasDerivAt_id z).pow 2).const_mul (-(T/2)))
  convert hd using 1
  simp only [betaQuadraticKernel,Complex.real_smul,id_eq]
  push_cast
  ring

theorem integral_betaQuadraticKernel_odd (T H : ℝ) :
    (∫ z in (-H)..H, (z : ℂ)*betaQuadraticKernel T z) = 0 := by
  let f : ℝ → ℂ := fun z => (z : ℂ)*betaQuadraticKernel T z
  have hodd : ∀ z, f (-z) = -f z := by
    intro z
    simp only [f,Complex.ofReal_neg,betaQuadraticKernel_neg,neg_mul]
  have h := intervalIntegral.integral_comp_neg f (a := -H) (b := H)
  simp_rw [hodd] at h
  rw [intervalIntegral.integral_neg,neg_neg] at h
  change (∫ z in (-H)..H, f z) = 0
  linear_combination -h/2

theorem integral_betaQuadraticKernel_eq_window (T H : ℝ) :
    (∫ z in (-H)..H, betaQuadraticKernel T z) = atkinsonQuadraticWindow (T/2) H := by
  apply intervalIntegral.integral_congr
  intro z _
  simp only [betaQuadraticKernel,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem norm_betaQuadraticWindow_sub_main {T H : ℝ} (hT : 0 < T) (hH : 0 < H) :
    ‖(∫ z in (-H)..H, betaQuadraticKernel T z) -
      (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)‖ ≤ 4/(T*H*Real.pi) := by
  have h := norm_atkinsonQuadraticWindow_sub_fresnel_le (by linarith : 0 < T/2) hH
  rw [integral_betaQuadraticKernel_eq_window]
  have he : (𝐞 (-(1 : ℝ)/8) : ℂ) = Complex.exp (((-Real.pi/4 : ℝ) : ℂ)*Complex.I) := by
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [he]
  rw [show 2*(T/2) = T by ring] at h
  convert h using 1
  ring

end TaoTrudgianYang2025
