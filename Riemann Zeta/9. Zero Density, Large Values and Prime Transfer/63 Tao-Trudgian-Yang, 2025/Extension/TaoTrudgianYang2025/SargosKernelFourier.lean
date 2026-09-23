import TaoTrudgianYang2025.SargosTentIntegral
import Mathlib.Analysis.Fourier.Inversion

/-!
# Whole-line Fourier pair for Robert--Sargos windows

The transforms use Mathlib's exp(-2*pi*i*x*frequency) convention.
Both whole-line integrability obligations are discharged before inversion.
-/

noncomputable section

open MeasureTheory Set GafniTao
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem sargos_fourier_eq_character (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, f x*fordAdditiveCharacter (-(ξ*x)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [smul_eq_mul]
    have he : Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) =
        fordAdditiveCharacter (-(ξ*x)) := by
      unfold fordAdditiveCharacter
      congr 1
      push_cast
      ring
    rw [he,mul_comm])

theorem fourier_sargosRealTent {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (sargosRealTent w x : ℂ)) ξ = (sargosSincKernel w ξ : ℂ) := by
  rw [sargos_fourier_eq_character]
  let f : ℝ → ℂ := fun x => (sargosRealTent w x : ℂ)*fordAdditiveCharacter (-(ξ*x))
  have hs : Function.support f ⊆ Ioc (-w) w := by
    intro x hx
    have ht : sargosRealTent w x ≠ 0 := by
      intro ht
      apply hx
      simp [f,ht]
    have hlt : |x| < w := by
      by_contra h
      exact ht (sargosRealTent_zero_of_le_abs hw (le_of_not_gt h))
    exact ⟨(abs_lt.mp hlt).1,(abs_lt.mp hlt).2.le⟩
  calc
    _ = ∫ x in -w..w, f x := (intervalIntegral.integral_eq_integral_of_support_subset hs).symm
    _ = ∫ x in -w..w, ((1-|x|/w : ℝ) : ℂ)*fordAdditiveCharacter (-(ξ*x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxabs : |x| ≤ w := by
        rcases Set.mem_uIcc.mp hx with h | h
        · exact abs_le.mpr h
        · linarith
      dsimp only [f]
      rw [sargosRealTent_eq_of_abs_le hw hxabs]
    _ = _ := sargos_integral_symmetric_tent_character_eq_kernel hw ξ

theorem fourier_sargosSincKernel {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (sargosSincKernel w x : ℂ)) ξ = (sargosRealTent w ξ : ℂ) := by
  have ht : Integrable (fun x : ℝ => (sargosRealTent w x : ℂ)) :=
    (integrable_sargosRealTent hw).ofReal
  have hk : Integrable (fun x : ℝ => (sargosSincKernel w x : ℂ)) :=
    (integrable_sargosSincKernel hw).ofReal
  have he : 𝓕 (fun x : ℝ => (sargosRealTent w x : ℂ)) =
      (fun x : ℝ => (sargosSincKernel w x : ℂ)) :=
    funext (fourier_sargosRealTent hw)
  have hft : Integrable (𝓕 (fun x : ℝ => (sargosRealTent w x : ℂ))) := by
    rwa [he]
  have hc : Continuous (fun x : ℝ => (sargosRealTent w x : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sargosRealTent w)
  have hi := congrFun (hc.fourierInv_fourier_eq ht hft) (-ξ)
  rw [he,Real.fourierInv_eq_fourier_neg,neg_neg] at hi
  simpa only [sargosRealTent,abs_neg] using hi

theorem integral_sargosSincKernel_character {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    (∫ x : ℝ, (sargosSincKernel w x : ℂ)*fordAdditiveCharacter (-(ξ*x))) =
      (sargosRealTent w ξ : ℂ) := by
  rw [← sargos_fourier_eq_character]
  exact fourier_sargosSincKernel hw ξ

theorem integral_sargosSincKernel_character_eq_zero {w ξ : ℝ}
    (hw : 0 < w) (hξ : w ≤ |ξ|) :
    (∫ x : ℝ, (sargosSincKernel w x : ℂ)*fordAdditiveCharacter (-(ξ*x))) = 0 := by
  rw [integral_sargosSincKernel_character hw ξ,sargosRealTent_zero_of_le_abs hw hξ]
  rfl

end TaoTrudgianYang2025
