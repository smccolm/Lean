import Dubon2026.SourceModularCoefficientCoordinateSpecialization

/-! Actual coefficient-field embeddings with a prescribed transcendental
j-value are exactly homomorphisms over its specialized coordinate field.
The equivalence preserves the underlying map pointwise. This is the
field-theoretic entry into the remaining finite-fiber orbit calculation. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField
open scoped IntermediateField
variable (N : ℕ) (K : Type*) [Field K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] {j₀ : Ω}

/-- The coordinate-field scalar action induced by the constructed specialization. -/
abbrev coordinateAlgebra (hj₀ : Transcendental K j₀) : Algebra K⟮jCoeff N K⟯ Ω :=
  (coordinateSpecialization N K hj₀).toRingHom.toAlgebra

theorem coordinateScalarTower (hj₀ : Transcendental K j₀) :
    letI := coordinateAlgebra N K hj₀
    IsScalarTower K K⟮jCoeff N K⟯ Ω := by
  letI := coordinateAlgebra N K hj₀
  exact IsScalarTower.of_algebraMap_eq fun c => (coordinateSpecialization N K hj₀).commutes c |>.symm

/-- Fixing the actual j-image is equivalent to linearity over the specialized j-field. -/
def embeddingsEquivCoordinateHom (hj₀ : Transcendental K j₀) :
    letI := coordinateAlgebra N K hj₀
    {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀} ≃
      (modularFunctionFieldCoeff N K →ₐ[K⟮jCoeff N K⟯] Ω) := by
  letI := coordinateAlgebra N K hj₀
  haveI := coordinateScalarTower N K hj₀
  letI : Algebra K (modularFunctionFieldCoeff N K) := inferInstance
  letI : Algebra K K⟮jCoeff N K⟯ := inferInstance
  refine
    { toFun := fun ψ =>
        { ψ.1.toRingHom with
          commutes' := fun z => ?_ }
      invFun := fun χ => ⟨χ.restrictScalars K, ?_⟩
      left_inv := fun ψ => by ext; rfl
      right_inv := fun χ => by ext; rfl }
  · have hr : ψ.1.comp (IsScalarTower.toAlgHom K K⟮jCoeff N K⟯
        (modularFunctionFieldCoeff N K)) = coordinateSpecialization N K hj₀ := by
      apply coordinate_algHom_ext N K
      change ψ.1 (jCoeff N K) = _
      rw [coordinateSpecialization_gen]
      exact ψ.2
    exact DFunLike.congr_fun hr z
  · change χ (jCoeff N K) = j₀
    have h := χ.commutes (AdjoinSimple.gen K (jCoeff N K))
    rw [AdjoinSimple.algebraMap_gen] at h
    exact h.trans (coordinateSpecialization_gen N K hj₀)

theorem embeddingsEquivCoordinateHom_apply (hj₀ : Transcendental K j₀)
    (ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] Ω // ψ (jCoeff N K) = j₀})
    (x : modularFunctionFieldCoeff N K) :
    embeddingsEquivCoordinateHom N K hj₀ ψ x = ψ.1 x := rfl

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
