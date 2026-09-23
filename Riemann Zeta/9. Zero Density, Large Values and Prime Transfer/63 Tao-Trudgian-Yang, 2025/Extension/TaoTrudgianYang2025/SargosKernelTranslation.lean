import TaoTrudgianYang2025.SargosKernelWindow
import GafniTao.FordLemma51Fibers

/-! Exact character normalization, integrability and Fourier phases after real translation. -/

noncomputable section

open MeasureTheory GafniTao

namespace TaoTrudgianYang2025

theorem sargos_character_norm (x : ℝ) : ‖fordAdditiveCharacter x‖ = 1 := by
  simp [fordAdditiveCharacter,Complex.norm_exp]

theorem integrable_sargosSincKernel_shift {w : ℝ} (hw : 0 < w) (c : ℝ) :
    Integrable (fun x : ℝ => sargosSincKernel w (x-c)) := by
  simpa only [sub_eq_add_neg] using (integrable_sargosSincKernel hw).comp_add_right (-c)

theorem integrable_sargosSincKernel_shift_character {w : ℝ}
    (hw : 0 < w) (c ξ : ℝ) :
    Integrable (fun x : ℝ =>
      (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))) := by
  have hc : Continuous (fun x : ℝ =>
      (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))) := by
    unfold sargosSincKernel fordAdditiveCharacter
    fun_prop
  apply (integrable_sargosSincKernel_shift hw c).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [norm_mul,sargos_character_norm,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (sargosSincKernel_nonneg hw.le (x-c))])

theorem integral_sargosSincKernel_shift_character {w : ℝ}
    (hw : 0 < w) (c ξ : ℝ) :
    (∫ x : ℝ, (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))) =
      fordAdditiveCharacter (-(ξ*c))*(sargosRealTent w ξ : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))
  have ht := integral_add_right_eq_self (μ := volume) f c
  calc
    _ = ∫ x : ℝ, f (x+c) := ht.symm
    _ = ∫ x : ℝ, fordAdditiveCharacter (-(ξ*c))*
        ((sargosSincKernel w x : ℂ)*fordAdditiveCharacter (-(ξ*x))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [f]
        rw [add_sub_cancel_right,
          show -(ξ*(x+c)) = -(ξ*c)+(-(ξ*x)) by ring,fordAdditiveCharacter_add]
        ring)
    _ = fordAdditiveCharacter (-(ξ*c))*
        ∫ x : ℝ, (sargosSincKernel w x : ℂ)*fordAdditiveCharacter (-(ξ*x)) :=
      integral_const_mul _ _
    _ = _ := by rw [integral_sargosSincKernel_character hw ξ]

theorem norm_integral_sargosSincKernel_shift_character_le_one {w : ℝ}
    (hw : 0 < w) (c ξ : ℝ) :
    ‖∫ x : ℝ, (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))‖ ≤ 1 := by
  rw [integral_sargosSincKernel_shift_character hw c ξ,norm_mul,sargos_character_norm,
    one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sargosRealTent_nonneg w ξ)]
  exact sargosRealTent_le_one hw ξ

theorem integral_sargosSincKernel_shift_character_eq_zero {w ξ : ℝ}
    (hw : 0 < w) (hξ : w ≤ |ξ|) (c : ℝ) :
    (∫ x : ℝ, (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (-(ξ*x))) = 0 := by
  rw [integral_sargosSincKernel_shift_character hw c ξ,sargosRealTent_zero_of_le_abs hw hξ]
  simp


theorem integral_sargosSincKernel_shift_character_positive {w : ℝ}
    (hw : 0 < w) (c ξ : ℝ) :
    (∫ x : ℝ, (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (ξ*x)) =
      fordAdditiveCharacter (ξ*c)*(sargosRealTent w ξ : ℂ) := by
  have h := integral_sargosSincKernel_shift_character hw c (-ξ)
  simpa only [neg_mul,neg_neg,sargosRealTent,abs_neg] using h

theorem integrable_sargosSincKernel_shift_character_positive {w : ℝ}
    (hw : 0 < w) (c ξ : ℝ) :
    Integrable (fun x : ℝ =>
      (sargosSincKernel w (x-c) : ℂ)*fordAdditiveCharacter (ξ*x)) := by
  simpa only [neg_mul,neg_neg] using integrable_sargosSincKernel_shift_character hw c (-ξ)

end TaoTrudgianYang2025
