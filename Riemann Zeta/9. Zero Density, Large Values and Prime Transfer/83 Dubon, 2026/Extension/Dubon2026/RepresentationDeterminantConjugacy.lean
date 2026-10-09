import Dubon2026.DeterminantCoefficientLaw
import Dubon2026.SymmetricRepresentationReduction

/-! # Change-of-basis invariance of the genuine representation determinant family -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- An original intertwining change of basis conjugates the genuine action on every group-algebra element. -/
theorem groupAlgebraMatrix_conjugate (ρ σ : G →* GeneralLinearGroup ι R)
    (A : GeneralLinearGroup ι R) (h : ∀ g, σ g = A * ρ g * A⁻¹)
    (x : MonoidAlgebra R G) :
    groupAlgebraMatrix σ x = A.val * groupAlgebraMatrix ρ x * (A⁻¹).val := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
      change groupAlgebraMatrix σ (MonoidAlgebra.single g 1) =
        A.val * groupAlgebraMatrix ρ (MonoidAlgebra.single g 1) * (A⁻¹).val
      rw [groupAlgebraMatrix_single, groupAlgebraMatrix_single, one_smul, one_smul]
      exact congrArg Units.val (h g)
  | hadd x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]
  | hsmul a x hx => simp only [map_smul, hx, smul_mul_assoc, mul_smul_comm]

/-- The actual group-algebra determinant is independent of an original intertwining change of basis. -/
theorem matrixRepresentationDeterminant_conjugate (ρ σ : G →* GeneralLinearGroup ι R)
    (A : GeneralLinearGroup ι R) (h : ∀ g, σ g = A * ρ g * A⁻¹)
    (x : MonoidAlgebra R G) :
    matrixRepresentationDeterminant σ x = matrixRepresentationDeterminant ρ x := by
  change Matrix.det (groupAlgebraMatrix σ x) = Matrix.det (groupAlgebraMatrix ρ x)
  rw [groupAlgebraMatrix_conjugate ρ σ A h, Matrix.det_units_conj]

/-- The whole actual determinant family is unchanged by an original change of basis, over every coefficient extension. -/
theorem determinantCoefficientLaw_conjugate (ρ σ : G →* GeneralLinearGroup ι R)
    (A : GeneralLinearGroup ι R) (h : ∀ g, σ g = A * ρ g * A⁻¹)
    (φ : R →+* S) (x : MonoidAlgebra S G) :
    determinantCoefficientLaw σ φ x = determinantCoefficientLaw ρ φ x := by
  apply matrixRepresentationDeterminant_conjugate _ _ (GeneralLinearGroup.map φ A)
  intro g
  simpa only [map_mul, map_inv, MonoidHom.comp_apply] using
    congrArg (GeneralLinearGroup.map φ) (h g)

end
end Dubon2026
