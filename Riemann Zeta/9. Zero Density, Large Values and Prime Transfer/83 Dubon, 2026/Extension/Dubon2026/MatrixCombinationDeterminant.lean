import Dubon2026.GroupAlgebraMatrix
import Mathlib.Algebra.MvPolynomial.Eval

/-! # The actual determinant polynomial of a finite linear combination of matrices -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped BigOperators

variable {σ ι R S : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- The genuine multivariable determinant of the original linear combination of matrices. -/
def matrixCombinationDeterminant (A : σ → Matrix ι ι R) : MvPolynomial σ R :=
  Matrix.det (∑ t, (MvPolynomial.X t : MvPolynomial σ R) •
    (MvPolynomial.C : R →+* MvPolynomial σ R).mapMatrix (A t))

/-- Changing the original coefficient ring commutes with the entire actual multivariable determinant polynomial. -/
theorem matrixCombinationDeterminant_map (φ : R →+* S) (A : σ → Matrix ι ι R) :
    MvPolynomial.map φ (matrixCombinationDeterminant A) =
      matrixCombinationDeterminant (fun t => (A t).map φ) := by
  unfold matrixCombinationDeterminant
  rw [(MvPolynomial.map φ).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.sum_apply, Matrix.smul_apply, RingHom.mapMatrix_apply]

/-- The original representation's determinant law on a genuine finite group-algebra combination is exactly the multivariable determinant of its original group matrices. -/
theorem matrixCombinationDeterminant_groupAlgebra {G : Type*} [Group G]
    (ρ : G →* GeneralLinearGroup ι R) (g : σ → G) :
    Matrix.det (groupAlgebraMatrix ((GeneralLinearGroup.map
      (MvPolynomial.C : R →+* MvPolynomial σ R)).comp ρ)
        (∑ t, MonoidAlgebra.single (g t) (MvPolynomial.X t))) =
      matrixCombinationDeterminant (fun t => (ρ (g t)).val) := by
  rw [map_sum]
  simp_rw [groupAlgebraMatrix_single]
  rfl

end
end Dubon2026
