import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Actual fixed vectors under an original invertible change of coordinates -/

namespace Dubon2026
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original invertible change of coordinates identifies the actual fixed vectors of a matrix and its genuine conjugate. -/
theorem matrix_conjugate_fixed_iff (A U : GeneralLinearGroup ι R) (v : ι → R) :
    (U⁻¹ * A * U).val *ᵥ (U⁻¹.val *ᵥ v) = U⁻¹.val *ᵥ v ↔ A.val *ᵥ v = v := by
  have hc : (U⁻¹ * A * U).val * U⁻¹.val = U⁻¹.val * A.val := by
    change ((U⁻¹ * A * U) * U⁻¹).val = (U⁻¹ * A).val
    congr 1
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  exact (Matrix.mulVec_injective_of_isUnit U⁻¹.isUnit).eq_iff

end Dubon2026
