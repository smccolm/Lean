import Dubon2026.SourceFrickeTwistModularEquivariance

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> stability of the actual cusp-form image. Convert the proved modular
pullback and cusp-vanishing identities to the source's forward-translate
convention and preserve invariance under the actual subgroup, including
Gamma1. No subgroup-invariance or all-cusps conclusion is assumed of the
twisted function. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups

theorem frickeCoefficientTwist_preserves_all_cusps (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m : ℕ) (hF : ∀ A : SL(2, ℤ),
      IsZeroAtImInfty (((F : ℍ → ℂ) ∘ (A • ·)) * ⇑CuspForm.discriminant ^ m)) :
    ∀ A : SL(2, ℤ), IsZeroAtImInfty
      (((frickeCoefficientTwist N σ F : ℍ → ℂ) ∘ (A • ·)) * ⇑CuspForm.discriminant ^ m) := by
  intro A
  have hh : IsZeroAtImInfty ((A⁻¹ • (F : ℍ → ℂ)) * ⇑CuspForm.discriminant ^ m) := by
    simpa only [sl_smul_def, inv_inv, Function.comp_def] using hF A
  have ht := (frickeCoefficientTwist_isZeroAtImInfty_sl_mul_discriminant_iff N σ A⁻¹ F m).mpr hh
  simpa only [sl_smul_def, inv_inv, Function.comp_def] using ht

theorem frickeCoefficientTwist_preserves_subgroup_invariance (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (Γ : Subgroup SL(2, ℤ))
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, (F : ℍ → ℂ) (γ • τ) = (F : ℍ → ℂ) τ) :
    ∀ γ ∈ Γ, ∀ τ : ℍ, (frickeCoefficientTwist N σ F : ℍ → ℂ) (γ • τ) =
      (frickeCoefficientTwist N σ F : ℍ → ℂ) τ := by
  intro γ hγ τ
  have hi : frickeSpanPullback N γ⁻¹ F = F := by
    apply Subtype.ext
    funext z
    change (F : ℍ → ℂ) ((γ⁻¹)⁻¹ • z) = (F : ℍ → ℂ) z
    simpa only [inv_inv] using hF γ hγ z
  have ht := frickeCoefficientTwist_pullback N σ γ⁻¹ F
  rw [hi] at ht
  have he := congrFun (congrArg Subtype.val ht) τ
  change (frickeCoefficientTwist N σ F : ℍ → ℂ) τ =
    (frickeCoefficientTwist N σ F : ℍ → ℂ) ((γ⁻¹)⁻¹ • τ) at he
  simpa only [inv_inv] using he.symm

end
end Dubon2026.SourceFricke