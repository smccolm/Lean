import Dubon2026.RationalAdeleRealFinite

/-! # Literal determinant and special-linear factors of actual invertible two-by-two matrices -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped MatrixGroups
variable {R : Type*} [CommRing R]

/-- The actual invertible diagonal matrix with a specified unit in its first position. -/
def gl2UnitFirstDiagonal (u : Rˣ) : Matrix.GeneralLinearGroup (Fin 2) R where
  val := !![↑u, 0; 0, 1]
  inv := !![↑u⁻¹, 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The first diagonal's genuine determinant is exactly the original unit. -/
theorem gl2UnitFirstDiagonal_det (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (gl2UnitFirstDiagonal u) = u := by
  apply Units.ext
  simp [gl2UnitFirstDiagonal, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]

/-- Its actual inverse is the diagonal of the inverse unit. -/
theorem gl2UnitFirstDiagonal_inv (u : Rˣ) :
    (gl2UnitFirstDiagonal u)⁻¹ = gl2UnitFirstDiagonal u⁻¹ := by
  apply Units.ext
  rfl

/-- Removing the determinant diagonal from an original invertible matrix gives an actual determinant-one matrix. -/
def gl2SpecialLinearFactor (g : Matrix.GeneralLinearGroup (Fin 2) R) : SL(2, R) :=
  ⟨((gl2UnitFirstDiagonal (Matrix.GeneralLinearGroup.det g))⁻¹ * g).val, by
    have h : Matrix.GeneralLinearGroup.det
        ((gl2UnitFirstDiagonal (Matrix.GeneralLinearGroup.det g))⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, gl2UnitFirstDiagonal_det, inv_mul_cancel]
    exact congrArg Units.val h⟩

/-- The special-linear factor embeds as precisely the original normalized invertible matrix. -/
theorem gl2SpecialLinearFactor_toGL (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.toGL (gl2SpecialLinearFactor g) =
      (gl2UnitFirstDiagonal (Matrix.GeneralLinearGroup.det g))⁻¹ * g := by
  apply Units.ext
  rfl

/-- Every original invertible matrix is exactly its determinant diagonal times its actual special-linear factor. -/
theorem gl2_eq_diagonal_mul_specialLinear (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    g = gl2UnitFirstDiagonal (Matrix.GeneralLinearGroup.det g) *
      Matrix.SpecialLinearGroup.toGL (gl2SpecialLinearFactor g) := by
  rw [gl2SpecialLinearFactor_toGL, mul_inv_cancel_left]

/-- Actual scalar-ring maps carry the determinant diagonal to the diagonal of the mapped unit. -/
theorem gl2UnitFirstDiagonal_map {S : Type*} [CommRing S] (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (gl2UnitFirstDiagonal u) =
      gl2UnitFirstDiagonal (Units.map f.toMonoidHom u) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2UnitFirstDiagonal, Matrix.GeneralLinearGroup.map]

/-- The original special-linear embedding commutes exactly with an actual scalar-ring map. -/
theorem generalLinear_map_toGL {S : Type*} [CommRing S] (f : R →+* S) (g : SL(2, R)) :
    Matrix.GeneralLinearGroup.map f (Matrix.SpecialLinearGroup.toGL g) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) := by
  apply Units.ext
  rfl

end
end Dubon2026
