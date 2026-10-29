import Dubon2026.SourceReducedFieldTensorEmbedding
import Mathlib.RingTheory.Localization.FractionRing

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue fiber bounds -> extension of the actual diamond action.
The actual larger original field is the fraction field of the faithful scalar
tensor. Native adjoin fractions give surjectivity; the proved tensor injection
supplies faithfulness. This is the exact localization needed to transport the
already proved prime-field automorphisms. -/
namespace Dubon2026.SourceFunctionField.ReducedDegreeTransport
noncomputable section
open IntermediateField GammaOne
open scoped MatrixGroups TensorProduct
attribute [local instance] originalFieldScalarAlgebra

theorem originalField_exists_tensor_fraction {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Γ : Subgroup SL(2, ℤ)) (x : qExpFunctionFieldC L Γ) :
    ∃ a b : L ⊗[K] qExpFunctionFieldC K Γ,
      x = originalFieldTensorEval (L := L) Γ a / originalFieldTensorEval (L := L) Γ b := by
  let e := (qExpFunctionFieldC L Γ).val.comp (originalFieldTensorEval (K := K) Γ)
  have hgen : Algebra.adjoin L
      (coeffMap (algebraMap K L) '' (qExpFunctionFieldC K Γ : Set (LaurentSeries K)))
      ≤ e.range := by
    apply Algebra.adjoin_le
    rintro y ⟨z, hz, rfl⟩
    refine ⟨1 ⊗ₜ[K] (⟨z, hz⟩ : qExpFunctionFieldC K Γ), ?_⟩
    change (originalFieldTensorEval (L := L) Γ (1 ⊗ₜ[K] (⟨z, hz⟩ : qExpFunctionFieldC K Γ)) :
      LaurentSeries L) = coeffMap (algebraMap K L) z
    rw [originalFieldTensorEval_tmul, one_smul, originalFieldCoefficientHom_coe]
  have hx := (originalField_eq_adjoin_coeffMap (algebraMap K L) Γ).le x.property
  obtain ⟨a, ha, b, hb, hx⟩ := mem_adjoin_iff_div.mp hx
  obtain ⟨u, hu⟩ := hgen ha
  obtain ⟨v, hv⟩ := hgen hb
  refine ⟨u, v, Subtype.ext ?_⟩
  change x.val = (e u) / (e v)
  change e u = a at hu
  change e v = b at hv
  rw [hu, hv]
  exact hx

/-- The faithful scalar tensor acts through its actual evaluation homomorphism. -/
abbrev originalFieldTensorAlgebra {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Γ : Subgroup SL(2, ℤ)) : Algebra (L ⊗[K] qExpFunctionFieldC K Γ) (qExpFunctionFieldC L Γ) :=
  (originalFieldTensorEval (L := L) Γ).toRingHom.toAlgebra

attribute [local instance] originalFieldTensorAlgebra

theorem originalField_isFractionRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Γ : Subgroup SL(2, ℤ)) :
    IsFractionRing (L ⊗[K] qExpFunctionFieldC K Γ) (qExpFunctionFieldC L Γ) := by
  letI : FaithfulSMul (L ⊗[K] qExpFunctionFieldC K Γ) (qExpFunctionFieldC L Γ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (originalFieldTensorEval_injective Γ)
  exact IsFractionRing.of_field _ _ (originalField_exists_tensor_fraction Γ)

end
end Dubon2026.SourceFunctionField.ReducedDegreeTransport
