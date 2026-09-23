import TaoTrudgianYang2025.SargosKernelTranslation

/-! The exact two-variable Fourier kernel used by the near-pair count. -/

noncomputable section

open MeasureTheory GafniTao

namespace TaoTrudgianYang2025

def sargosPlanarKernelTerm (a b c d ξ η α γ : ℝ) : ℂ :=
  (sargosSincKernel a (α-c) : ℂ)*(sargosSincKernel b (γ-d) : ℂ)*
    fordAdditiveCharacter (ξ*α+η*γ)

theorem integrable_sargosPlanarKernelTerm_inner {b : ℝ} (hb : 0 < b)
    (a c d ξ η α : ℝ) :
    Integrable (sargosPlanarKernelTerm a b c d ξ η α) := by
  have h := (integrable_sargosSincKernel_shift_character_positive hb d η).const_mul
    ((sargosSincKernel a (α-c) : ℂ)*fordAdditiveCharacter (ξ*α))
  apply h.congr
  exact Filter.Eventually.of_forall (fun γ => by
    dsimp only [sargosPlanarKernelTerm]
    rw [fordAdditiveCharacter_add]
    ring)

theorem integral_sargosPlanarKernelTerm_inner {b : ℝ} (hb : 0 < b)
    (a c d ξ η α : ℝ) :
    (∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ) =
      ((sargosSincKernel a (α-c) : ℂ)*fordAdditiveCharacter (ξ*α))*
        fordAdditiveCharacter (η*d)*(sargosRealTent b η : ℂ) := by
  calc
    _ = ∫ γ : ℝ, ((sargosSincKernel a (α-c) : ℂ)*fordAdditiveCharacter (ξ*α))*
        ((sargosSincKernel b (γ-d) : ℂ)*fordAdditiveCharacter (η*γ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun γ => by
        dsimp only [sargosPlanarKernelTerm]
        rw [fordAdditiveCharacter_add]
        ring)
    _ = _ := by
      rw [integral_const_mul,integral_sargosSincKernel_shift_character_positive hb d η]
      ring

theorem integrable_sargosPlanarKernelTerm_outer {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d ξ η : ℝ) :
    Integrable (fun α : ℝ => ∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ) := by
  simp_rw [integral_sargosPlanarKernelTerm_inner hb]
  exact ((integrable_sargosSincKernel_shift_character_positive ha c ξ).mul_const
    (fordAdditiveCharacter (η*d))).mul_const (sargosRealTent b η : ℂ)

theorem integral_sargosPlanarKernelTerm {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d ξ η : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ) =
      fordAdditiveCharacter (ξ*c+η*d)*(sargosRealTent a ξ : ℂ)*(sargosRealTent b η : ℂ) := by
  simp_rw [integral_sargosPlanarKernelTerm_inner hb]
  rw [integral_mul_const,integral_mul_const,
    integral_sargosSincKernel_shift_character_positive ha c ξ,fordAdditiveCharacter_add]
  ring

theorem norm_integral_sargosPlanarKernelTerm_le_one {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d ξ η : ℝ) :
    ‖∫ α : ℝ, ∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ‖ ≤ 1 := by
  rw [integral_sargosPlanarKernelTerm ha hb c d ξ η]
  simp only [norm_mul,sargos_character_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sargosRealTent_nonneg a ξ),abs_of_nonneg (sargosRealTent_nonneg b η),
    one_mul]
  exact (mul_le_mul (sargosRealTent_le_one ha ξ) (sargosRealTent_le_one hb η)
    (sargosRealTent_nonneg b η) (by norm_num)).trans_eq (by norm_num)

theorem integral_sargosPlanarKernelTerm_eq_zero {a b ξ η : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hcut : a ≤ |ξ| ∨ b ≤ |η|) (c d : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, sargosPlanarKernelTerm a b c d ξ η α γ) = 0 := by
  rw [integral_sargosPlanarKernelTerm ha hb c d ξ η]
  rcases hcut with h | h
  · rw [sargosRealTent_zero_of_le_abs ha h]
    simp
  · rw [sargosRealTent_zero_of_le_abs hb h]
    simp

end TaoTrudgianYang2025
