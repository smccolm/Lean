import Dubon2026.UniversalMatrixRepresentation

/-! # Actual evaluation of representation coordinates at an original representation -/

namespace Dubon2026

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing S] [Algebra R S]

/-- Actual evaluation of the coordinate polynomials at every original matrix entry. -/
def representationPolynomialEvaluation (ρ : G →* GeneralLinearGroup ι S) :
    MvPolynomial (G × ι × ι) R →ₐ[R] S :=
  MvPolynomial.aeval (fun t => (ρ t.1).val t.2.1 t.2.2)

/-- The actual identity relation vanishes on every original representation. -/
theorem representationPolynomialEvaluation_one (ρ : G →* GeneralLinearGroup ι S)
    (i j : ι) :
    representationPolynomialEvaluation (R := R) ρ
      (representationCoordinateOneRelation G ι R i j) = 0 := by
  unfold representationCoordinateOneRelation representationPolynomialEvaluation
  rw [map_sub, MvPolynomial.aeval_X, map_one]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- The actual multiplication relation vanishes on every original representation. -/
theorem representationPolynomialEvaluation_mul (ρ : G →* GeneralLinearGroup ι S)
    (g h : G) (i j : ι) :
    representationPolynomialEvaluation (R := R) ρ
      (representationCoordinateMulRelation G ι R g h i j) = 0 := by
  unfold representationCoordinateMulRelation representationPolynomialEvaluation
  simp only [map_sub, map_sum, map_mul, MvPolynomial.aeval_X,
    Units.val_mul, Matrix.mul_apply, sub_self]

/-- The entire original relation ideal is killed by evaluation at every original matrix representation. -/
theorem representationCoordinateIdeal_le_ker (ρ : G →* GeneralLinearGroup ι S) :
    representationCoordinateIdeal G ι R ≤
      RingHom.ker (representationPolynomialEvaluation (R := R) ρ).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with ⟨ij, rfl⟩ | ⟨t, rfl⟩
  · exact representationPolynomialEvaluation_one ρ ij.1 ij.2
  · exact representationPolynomialEvaluation_mul ρ t.1.1 t.1.2 t.2.1 t.2.2

/-- The original representation gives an actual algebra map out of the concrete coordinate quotient. -/
def representationCoordinateEvaluation (ρ : G →* GeneralLinearGroup ι S) :
    RepresentationCoordinateAlgebra G ι R →ₐ[R] S :=
  Ideal.Quotient.liftₐ (representationCoordinateIdeal G ι R)
    (representationPolynomialEvaluation ρ) (fun _ hp => representationCoordinateIdeal_le_ker ρ hp)

/-- Evaluation of the original coordinate class recovers the original matrix entry. -/
theorem representationCoordinateEvaluation_entry (ρ : G →* GeneralLinearGroup ι S)
    (g : G) (i j : ι) :
    representationCoordinateEvaluation (R := R) ρ
      (Ideal.Quotient.mk (representationCoordinateIdeal G ι R) (X (g, i, j))) =
        (ρ g).val i j := by
  change MvPolynomial.aeval (fun t : G × ι × ι => (ρ t.1).val t.2.1 t.2.2)
    (X (g, i, j) : MvPolynomial (G × ι × ι) R) = _
  exact MvPolynomial.aeval_X _ _

/-- Base change of the entire original universal representation by its actual coordinate evaluation recovers the entire original matrix representation. -/
theorem universalMatrixRepresentation_evaluation (ρ : G →* GeneralLinearGroup ι S) :
    (GeneralLinearGroup.map (representationCoordinateEvaluation (R := R) ρ).toRingHom).comp
      (universalMatrixRepresentation G ι R) = ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact representationCoordinateEvaluation_entry ρ g i j

end
end Dubon2026
