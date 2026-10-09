import Dubon2026.GroupAlgebraMatrix

/-! # The genuine determinant of a group-algebra representation -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- The literal determinant of the original group-algebra matrix, with its proved multiplication law. -/
def matrixRepresentationDeterminant (ρ : G →* GeneralLinearGroup ι R) :
    MonoidAlgebra R G →* R :=
  Matrix.detMonoidHom.comp (groupAlgebraMatrix ρ).toMonoidHom

/-- Scalar multiplication has the actual dimension as its determinant degree. -/
theorem matrixRepresentationDeterminant_smul (ρ : G →* GeneralLinearGroup ι R)
    (a : R) (x : MonoidAlgebra R G) :
    matrixRepresentationDeterminant ρ (a • x) =
      a ^ Fintype.card ι * matrixRepresentationDeterminant ρ x := by
  change Matrix.det (groupAlgebraMatrix ρ (a • x)) = _
  rw [map_smul, Matrix.det_smul]
  rfl

/-- On an original group element the construction is exactly its usual matrix determinant. -/
theorem matrixRepresentationDeterminant_single (ρ : G →* GeneralLinearGroup ι R)
    (g : G) (a : R) :
    matrixRepresentationDeterminant ρ (MonoidAlgebra.single g a) =
      a ^ Fintype.card ι * (ρ g).val.det := by
  change Matrix.det (groupAlgebraMatrix ρ (MonoidAlgebra.single g a)) = _
  rw [groupAlgebraMatrix_single, Matrix.det_smul]

/-- Determinants of the original group-algebra action commute with arbitrary coefficient homomorphisms. -/
theorem matrixRepresentationDeterminant_map (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (x : MonoidAlgebra R G) :
    φ (matrixRepresentationDeterminant ρ x) =
      matrixRepresentationDeterminant ((GeneralLinearGroup.map φ).comp ρ)
        (MonoidAlgebra.mapRingHom G φ x) := by
  change φ (Matrix.det (groupAlgebraMatrix ρ x)) = _
  rw [φ.map_det, groupAlgebraMatrix_map]
  rfl

end
end Dubon2026
