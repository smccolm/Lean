import Dubon2026.SourceFrickeHolomorphy
import Dubon2026.SourceWeierstrassTorsionFourierExpansion

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> Fricke generators.
The native torsion-index functions inherit the exact cyclotomic Fourier
coefficients and the cusp bounds derived from the actual series. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex PeriodPair
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

theorem wpNormZ_eq_wpNorm (N : ℕ) (a : Fin 2 → ZMod N) :
    wpNormZ N a = wpNorm N (a 0).val (a 1).val := rfl

theorem periodic_wpNormZ {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    Function.Periodic (wpNormZ N a ∘ ofComplex) N := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps a ha
  exact periodic_wpNorm h₁ h₂ h₀

theorem isBoundedAtImInfty_wpNormZ {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    IsBoundedAtImInfty (wpNormZ N a) := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps a ha
  exact isBoundedAtImInfty_wpNorm h₁ h₂ h₀

theorem qExpansion_wpNormZ_coeff {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) (n : ℕ) :
    (qExpansion N (wpNormZ N a)).coeff n = wpQCoeff N (a 0).val (a 1).val n := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps a ha
  exact qExpansion_wpNorm_coeff h₁ h₂ h₀ n

theorem qExpansion_wpNormZ_coeff_mem_kN {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) (n : ℕ) :
    (qExpansion N (wpNormZ N a)).coeff n ∈ kN N := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps a ha
  exact qExpansion_wpNorm_coeff_mem_kN h₁ h₂ h₀ n

theorem frickeF_mul_discriminant {N : ℕ} (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeF N a τ * ModularForm.discriminant τ =
      (-1 / 2592 : ℂ) * (ModularForm.E₄ τ * ModularForm.E₆ τ * wpNormZ N a τ) := by
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  dsimp only [frickeF]
  field_simp

theorem isBoundedAtImInfty_frickeF_mul_discriminant {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    IsBoundedAtImInfty (frickeF N a * ModularForm.discriminant) := by
  have hH := ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
    (ModularFormClass.bdd_at_infty ModularForm.E₆)).mul
      (isBoundedAtImInfty_wpNormZ a ha)
  have heq : (frickeF N a * ModularForm.discriminant : ℍ → ℂ) =
      fun τ => (-1 / 2592 : ℂ) *
        ((ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₆ : ℍ → ℂ) * wpNormZ N a) τ := by
    funext τ
    exact frickeF_mul_discriminant a τ
  rw [heq]
  exact hH.const_mul_left _

end
end Dubon2026.SourceFricke
