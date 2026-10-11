import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases

/-! # A genuine primitive vector extends to an original two-dimensional matrix basis -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R]

/-- A two-dimensional vector with a unit coordinate is the first column of an actual invertible matrix over the same original coefficient ring. -/
theorem matrixTwo_exists_basis_column_of_unit (v : Fin 2 → R)
    (hv : ∃ i, IsUnit (v i)) :
    ∃ U : GeneralLinearGroup (Fin 2) R, ∀ i, U i 0 = v i := by
  obtain ⟨i, hi⟩ := hv
  fin_cases i
  · let A : Matrix (Fin 2) (Fin 2) R := !![v 0, 0; v 1, 1]
    have hA : IsUnit A.det := by
      simpa [A, Matrix.det_fin_two] using hi
    refine ⟨GeneralLinearGroup.mk'' A hA, ?_⟩
    intro j
    fin_cases j <;> rfl
  · let A : Matrix (Fin 2) (Fin 2) R := !![v 0, 1; v 1, 0]
    have hA : IsUnit A.det := by
      simpa [A, Matrix.det_fin_two] using hi.neg
    refine ⟨GeneralLinearGroup.mk'' A hA, ?_⟩
    intro j
    fin_cases j <;> rfl

end
end Dubon2026
