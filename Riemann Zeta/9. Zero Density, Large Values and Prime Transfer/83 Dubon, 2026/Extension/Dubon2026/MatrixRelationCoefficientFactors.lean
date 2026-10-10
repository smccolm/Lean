import Dubon2026.MatrixRepresentationRelationIdeals

/-! # Actual coefficient maps factoring all original matrix relations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]

/-- An actual coefficient map whose original representation kills all relations factors through the literal relation ideal. -/
def matrixRelationCoefficientMap
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) (f : R →ₐ[O] A)
    (hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp ρ).ker) :
    (R ⧸ matrixRepresentationRelationIdeal ρ N) →ₐ[O] A :=
  Ideal.Quotient.liftₐ _ f (fun _ hx =>
    (matrixRepresentationRelationIdeal_le_kernel_iff ρ N f.toRingHom).mpr hf hx)

/-- The genuine coefficient factor retains every original coefficient value. -/
theorem matrixRelationCoefficientMap_mk
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) (f : R →ₐ[O] A)
    (hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp ρ).ker) (r : R) :
    matrixRelationCoefficientMap ρ N f hf
      (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N) r) = f r := rfl

/-- The actual coefficient factor is uniquely determined on the entire original relation quotient. -/
theorem matrixRelationCoefficientMap_unique
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) (f : R →ₐ[O] A)
    (hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp ρ).ker)
    (a : (R ⧸ matrixRepresentationRelationIdeal ρ N) →ₐ[O] A)
    (ha : ∀ r, a (Ideal.Quotient.mk (matrixRepresentationRelationIdeal ρ N) r) = f r) :
    a = matrixRelationCoefficientMap ρ N f hf := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ha r

/-- Evaluating the actual descended representation gives precisely the original coefficient-changed matrices. -/
theorem matrixRelationCoefficientMap_representation
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) [N.Normal] (f : R →ₐ[O] A)
    (hf : N ≤ ((GeneralLinearGroup.map (n := ι) f.toRingHom).comp ρ).ker) (g : G) :
    GeneralLinearGroup.map (n := ι) (matrixRelationCoefficientMap ρ N f hf).toRingHom
      (matrixRelationQuotientRepresentation ρ N (QuotientGroup.mk' N g)) =
        GeneralLinearGroup.map (n := ι) f.toRingHom (ρ g) := rfl

end
end Dubon2026
