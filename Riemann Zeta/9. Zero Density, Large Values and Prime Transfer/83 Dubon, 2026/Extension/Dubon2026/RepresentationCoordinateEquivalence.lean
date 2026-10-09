import Dubon2026.RepresentationCoordinateEvaluation

/-! # The actual universal property of the original matrix representation coordinate algebra -/

namespace Dubon2026

noncomputable section
open Matrix MvPolynomial

variable {G ι R S T : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- An actual algebra map evaluates the original universal matrices to a genuine original-group representation. -/
def representationFromCoordinates (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] S) :
    G →* GeneralLinearGroup ι S :=
  (GeneralLinearGroup.map f.toRingHom).comp (universalMatrixRepresentation G ι R)

/-- Reconstructing a representation from its actual coordinate evaluation recovers the entire original representation. -/
theorem representationFromCoordinates_evaluation (ρ : G →* GeneralLinearGroup ι S) :
    representationFromCoordinates (representationCoordinateEvaluation (R := R) ρ) = ρ :=
  universalMatrixRepresentation_evaluation ρ

/-- Original coordinate evaluation recovers the entire input algebra map, not only its values on a selected subset of group elements. -/
theorem representationCoordinateEvaluation_fromCoordinates
    (f : RepresentationCoordinateAlgebra G ι R →ₐ[R] S) :
    representationCoordinateEvaluation (representationFromCoordinates f) = f := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  rintro ⟨g, i, j⟩
  change representationCoordinateEvaluation (representationFromCoordinates f)
    (Ideal.Quotient.mk (representationCoordinateIdeal G ι R) (X (g, i, j))) = _
  rw [representationCoordinateEvaluation_entry]
  rfl

/-- The concrete coordinate algebra represents actual matrix representations of the original group over every original coefficient algebra. -/
def representationCoordinateEquiv :
    (RepresentationCoordinateAlgebra G ι R →ₐ[R] S) ≃ (G →* GeneralLinearGroup ι S) where
  toFun := representationFromCoordinates
  invFun := representationCoordinateEvaluation
  left_inv := representationCoordinateEvaluation_fromCoordinates
  right_inv := representationFromCoordinates_evaluation

/-- The actual coordinate evaluation is natural under the original coefficient-algebra map. -/
theorem representationCoordinateEvaluation_natural (ρ : G →* GeneralLinearGroup ι S)
    (ψ : S →ₐ[R] T) :
    representationCoordinateEvaluation ((GeneralLinearGroup.map ψ.toRingHom).comp ρ) =
      ψ.comp (representationCoordinateEvaluation (R := R) ρ) := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  rintro ⟨g, i, j⟩
  change representationCoordinateEvaluation ((GeneralLinearGroup.map ψ.toRingHom).comp ρ)
    (Ideal.Quotient.mk (representationCoordinateIdeal G ι R) (X (g, i, j))) =
      ψ (representationCoordinateEvaluation (R := R) ρ
        (Ideal.Quotient.mk (representationCoordinateIdeal G ι R) (X (g, i, j))))
  rw [representationCoordinateEvaluation_entry, representationCoordinateEvaluation_entry]
  rfl

end
end Dubon2026
