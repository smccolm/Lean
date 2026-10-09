import Dubon2026.DeterminantCoefficientLaw
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Characteristic polynomials of the actual determinant family -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Evaluate the original determinant family on the genuine group-algebra polynomial X-g. -/
def determinantCharacteristicPolynomial (ρ : G →* GeneralLinearGroup ι R) (g : G) :
    Polynomial R :=
  determinantCoefficientLaw ρ Polynomial.C
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1)

/-- The determinant-law polynomial is the characteristic polynomial of the original group matrix. -/
theorem determinantCharacteristicPolynomial_eq (ρ : G →* GeneralLinearGroup ι R)
    (g : G) : determinantCharacteristicPolynomial ρ g = (ρ g).val.charpoly := by
  change Matrix.det (groupAlgebraMatrix ((GeneralLinearGroup.map Polynomial.C).comp ρ)
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single g 1)) = _
  rw [map_sub, groupAlgebraMatrix_single, groupAlgebraMatrix_single]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [Matrix.charmatrix, GeneralLinearGroup.map, Matrix.scalar, Matrix.diagonal,
      Matrix.smul_apply, h]

/-- The genuine determinant-law characteristic polynomial annihilates the original representation matrix. -/
theorem determinantCharacteristicPolynomial_annihilates
    (ρ : G →* GeneralLinearGroup ι R) (g : G) :
    Polynomial.aeval (ρ g).val (determinantCharacteristicPolynomial ρ g) = 0 := by
  rw [determinantCharacteristicPolynomial_eq]
  exact Matrix.aeval_self_charpoly _

end
end Dubon2026
