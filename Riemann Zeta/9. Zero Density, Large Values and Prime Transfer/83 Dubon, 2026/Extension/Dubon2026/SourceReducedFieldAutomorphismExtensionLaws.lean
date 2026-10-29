import Dubon2026.SourceReducedFieldAutomorphismExtension

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue fiber bounds -> faithful extension of the actual diamond action.
The scalar extension is unique on the original coefficient images, preserves
composition and is injective. Thus the already proved action and its exact
kernel can be transported without a new assumed group-action certificate. -/
namespace Dubon2026.SourceFunctionField.ReducedDegreeTransport
noncomputable section
open IntermediateField GammaOne
open scoped MatrixGroups TensorProduct
attribute [local instance] originalFieldScalarAlgebra

theorem originalField_algHom_ext {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Γ : Subgroup SL(2, ℤ)) (f g : qExpFunctionFieldC L Γ →ₐ[L] qExpFunctionFieldC L Γ)
    (h : ∀ x : qExpFunctionFieldC K Γ,
      f (originalFieldCoefficientHom (K := K) (L := L) Γ x) = g (originalFieldCoefficientHom (K := K) (L := L) Γ x)) : f = g := by
  have ht : f.comp (originalFieldTensorEval (K := K) Γ) =
      g.comp (originalFieldTensorEval (K := K) Γ) := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change f (originalFieldTensorEval (K := K) (L := L) Γ (1 ⊗ₜ[K] x)) =
      g (originalFieldTensorEval (K := K) (L := L) Γ (1 ⊗ₜ[K] x))
    simpa only [originalFieldTensorEval_tmul, one_smul] using h x
  apply AlgHom.ext
  intro x
  obtain ⟨a, b, hx⟩ := originalField_exists_tensor_fraction (K := K) Γ x
  rw [hx, map_div₀, map_div₀]
  exact congrArg₂ (fun u v : qExpFunctionFieldC L Γ => u / v)
    (DFunLike.congr_fun ht a) (DFunLike.congr_fun ht b)

theorem originalFieldAutomorphismExtension_one {K L : Type*}
    [Field K] [Field L] [Algebra K L] (Γ : Subgroup SL(2, ℤ)) :
    originalFieldAutomorphismExtension (K := K) (L := L) Γ 1 = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply originalField_algHom_ext (K := K) Γ
  intro x
  exact originalFieldAutomorphismExtension_coeff Γ 1 x

theorem originalFieldAutomorphismExtension_mul {K L : Type*}
    [Field K] [Field L] [Algebra K L] (Γ : Subgroup SL(2, ℤ))
    (σ τ : qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ) :
    originalFieldAutomorphismExtension (L := L) Γ (σ * τ) =
      originalFieldAutomorphismExtension (K := K) (L := L) Γ σ * originalFieldAutomorphismExtension (K := K) (L := L) Γ τ := by
  apply AlgEquiv.coe_algHom_injective
  apply originalField_algHom_ext (K := K) Γ
  intro x
  change originalFieldAutomorphismExtension (K := K) (L := L) Γ (σ * τ) (originalFieldCoefficientHom (K := K) (L := L) Γ x) =
    originalFieldAutomorphismExtension (K := K) (L := L) Γ σ
      (originalFieldAutomorphismExtension (K := K) (L := L) Γ τ (originalFieldCoefficientHom (K := K) (L := L) Γ x))
  rw [originalFieldAutomorphismExtension_coeff, originalFieldAutomorphismExtension_coeff,
    originalFieldAutomorphismExtension_coeff]
  rfl

/-- The faithful scalar-extension homomorphism for original integral-ratio field automorphisms. -/
def originalFieldAutomorphismExtensionHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Γ : Subgroup SL(2, ℤ)) :
    (qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ) →*
      (qExpFunctionFieldC L Γ ≃ₐ[L] qExpFunctionFieldC L Γ) where
  toFun := originalFieldAutomorphismExtension (K := K) (L := L) Γ
  map_one' := originalFieldAutomorphismExtension_one Γ
  map_mul' := originalFieldAutomorphismExtension_mul Γ

theorem originalFieldAutomorphismExtensionHom_injective {K L : Type*}
    [Field K] [Field L] [Algebra K L] (Γ : Subgroup SL(2, ℤ)) :
    Function.Injective (originalFieldAutomorphismExtensionHom (K := K) (L := L) Γ) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun e : qExpFunctionFieldC L Γ ≃ₐ[L] qExpFunctionFieldC L Γ =>
    e (originalFieldCoefficientHom (K := K) (L := L) Γ x)) h
  change originalFieldAutomorphismExtension (K := K) (L := L) Γ σ (originalFieldCoefficientHom (K := K) (L := L) Γ x) =
    originalFieldAutomorphismExtension (K := K) (L := L) Γ τ (originalFieldCoefficientHom (K := K) (L := L) Γ x) at hx
  rw [originalFieldAutomorphismExtension_coeff, originalFieldAutomorphismExtension_coeff] at hx
  exact (originalFieldCoefficientHom (L := L) Γ).injective hx

end
end Dubon2026.SourceFunctionField.ReducedDegreeTransport
