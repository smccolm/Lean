import Dubon2026.SourceGammaOneSignedParabolicCharacters
import Dubon2026.SourceManinCuspStabilizer

/-! DUB-17/18 -> original Gamma1 real period surjectivity -> real Manin
upper dimension bound. Adapt the already proved original complex
subgroup-character identities to real coefficients. These values feed
the actual rational cusp potential and preserve the original subgroup.
The finite relation-space dimension theorem is reused unchanged. -/
namespace Dubon2026.SourceFunctionField.GammaOne.RealManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint SourceManin
open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ))

open Classical in

/-- Extend an actual subgroup character by zero for evaluating chosen integral lifts. -/
noncomputable def Phi (φ : Additive Γ →+ ℝ) (g : SL(2, ℤ)) : ℝ :=
  if h : g ∈ Γ then φ (Additive.ofMul ⟨g, h⟩) else 0

theorem Phi_of_mem (φ : Additive Γ →+ ℝ) {g : SL(2, ℤ)} (h : g ∈ Γ) :
    Phi Γ φ g = φ (Additive.ofMul ⟨g, h⟩) := dif_pos h

theorem Phi_mul (φ : Additive Γ →+ ℝ) {g h : SL(2, ℤ)} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    Phi Γ φ (g * h) = Phi Γ φ g + Phi Γ φ h := by
  rw [Phi_of_mem Γ φ (mul_mem hg hh), Phi_of_mem Γ φ hg, Phi_of_mem Γ φ hh, ← map_add]
  rfl

theorem Phi_one (φ : Additive Γ →+ ℝ) : Phi Γ φ 1 = 0 := by
  rw [Phi_of_mem Γ φ (one_mem Γ)]
  exact map_zero φ

theorem Phi_inv (φ : Additive Γ →+ ℝ) {g : SL(2, ℤ)} (hg : g ∈ Γ) :
    Phi Γ φ g⁻¹ = -Phi Γ φ g := by
  have h := Phi_mul Γ φ (inv_mem hg) hg
  rw [inv_mul_cancel, Phi_one] at h
  linear_combination -h

theorem Phi_add (φ ψ : Additive Γ →+ ℝ) (g : SL(2, ℤ)) :
    Phi Γ (φ + ψ) g = Phi Γ φ g + Phi Γ ψ g := by
  unfold Phi
  split_ifs <;> simp

theorem Phi_smul (c : ℝ) (φ : Additive Γ →+ ℝ) (g : SL(2, ℤ)) :
    Phi Γ (c • φ) g = c * Phi Γ φ g := by
  unfold Phi
  split_ifs <;> simp

theorem Phi_parabolic {φ : Additive Γ →+ ℝ} (hφ : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0) {g : SL(2, ℤ)} (hg : g ∈ Γ)
    (htr : (g : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : Phi Γ φ g = 0 := by
  rw [Phi_of_mem Γ φ hg]
  exact hφ ⟨g, hg⟩ htr

end
end Dubon2026.SourceFunctionField.GammaOne.RealManin
