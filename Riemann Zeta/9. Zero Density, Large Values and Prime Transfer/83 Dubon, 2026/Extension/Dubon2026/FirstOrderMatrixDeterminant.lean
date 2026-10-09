import Dubon2026.DualMatrixStrictUnits
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The actual first-order determinant and its trace term -/

namespace Dubon2026

noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The determinant of the original strict matrix has the actual trace as its epsilon coefficient. -/
theorem dualMatrixStrictUnit_det (X : Matrix ι ι R) :
    Matrix.det (dualMatrixStrictUnit X).val = (1, Matrix.trace X) := by
  have he : (dualMatrixStrictUnit X).val =
      1 + (DualNumber.eps : DualNumber R) • X.map (TrivSqZeroExt.inlHom R R) := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext <;> by_cases h : i = j <;>
      simp [dualMatrixStrictUnit, Matrix.dualNumberEquiv, Matrix.one_apply,
        Matrix.smul_apply, Matrix.map_apply, h]
  rw [he, Matrix.det_one_add_smul, DualNumber.eps_pow_two, mul_zero, add_zero,
    ← AddMonoidHom.map_trace]
  apply TrivSqZeroExt.ext <;> simp

/-- The original constant coefficient inclusion on invertible matrices. -/
def constantDualMatrixUnit (A : GeneralLinearGroup ι R) : GeneralLinearGroup ι (DualNumber R) :=
  GeneralLinearGroup.map (TrivSqZeroExt.inlHom R R) A

/-- The actual dual-number matrix factors into its strict infinitesimal matrix and its original constant reduction. -/
theorem dualMatrixUnit_factor (A : GeneralLinearGroup ι (DualNumber R)) :
    A = dualMatrixStrictUnit (dualMatrixInfinitesimal A) *
      constantDualMatrixUnit (dualMatrixReduction A) := by
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  rw [Units.val_mul, map_mul Matrix.dualNumberEquiv]
  change Matrix.dualNumberEquiv A.val =
    Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm
      ⟨1, dualMatrixInfinitesimal A⟩) * ⟨(dualMatrixReduction A).val, 0⟩
  rw [AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext
  · change dualMatrixFst A.val = 1 * (dualMatrixReduction A).val
    rw [one_mul, dualMatrixFst_val]
  · change dualMatrixSnd A.val =
      1 * 0 + dualMatrixInfinitesimal A * (dualMatrixReduction A).val
    rw [mul_zero, zero_add, dualMatrixInfinitesimal, mul_assoc, Units.inv_mul, mul_one]

/-- The determinant of the original invertible dual-number matrix has its original reduction determinant and its exact logarithmic trace correction. -/
theorem dualMatrixUnit_det (A : GeneralLinearGroup ι (DualNumber R)) :
    Matrix.det A.val = (Matrix.det (dualMatrixReduction A).val,
      Matrix.trace (dualMatrixInfinitesimal A) * Matrix.det (dualMatrixReduction A).val) := by
  have he := congrArg (fun B : GeneralLinearGroup ι (DualNumber R) => Matrix.det B.val)
    (dualMatrixUnit_factor A)
  change Matrix.det A.val = Matrix.det (dualMatrixStrictUnit (dualMatrixInfinitesimal A) *
    constantDualMatrixUnit (dualMatrixReduction A)).val at he
  rw [Units.val_mul, Matrix.det_mul, dualMatrixStrictUnit_det] at he
  have hc : Matrix.det (constantDualMatrixUnit (dualMatrixReduction A)).val =
      (TrivSqZeroExt.inlHom R R) (Matrix.det (dualMatrixReduction A).val) := by
    change Matrix.det ((dualMatrixReduction A).val.map (TrivSqZeroExt.inlHom R R)) = _
    exact (RingHom.map_det _ _).symm
  rw [hc] at he
  exact he.trans (by apply TrivSqZeroExt.ext <;> simp)

end
end Dubon2026
