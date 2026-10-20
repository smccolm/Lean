import Dubon2026.DualMatrixStrictUnits
import Dubon2026.PolarizedContragredient

/-! Exact algebra of the existing strict dual-number matrices, reused in
the fixed-similitude polarized tangent comparison for DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original strict matrices multiply by adding their actual infinitesimal matrices. -/
theorem dualMatrixStrictUnit_add (X Y : Matrix ι ι R) :
    dualMatrixStrictUnit (X + Y) = dualMatrixStrictUnit X * dualMatrixStrictUnit Y := by
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  change Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm ⟨1, X + Y⟩) =
    Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm ⟨1, X⟩ *
      Matrix.dualNumberEquiv.symm ⟨1, Y⟩)
  rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext <;> simp [add_comm]

/-- The original zero infinitesimal gives the identity matrix. -/
theorem dualMatrixStrictUnit_zero : dualMatrixStrictUnit (0 : Matrix ι ι R) = 1 := by
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  change Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm ⟨1, 0⟩) =
    Matrix.dualNumberEquiv 1
  rw [AlgEquiv.apply_symm_apply, map_one]
  rfl

/-- The original first-order matrix coordinates are faithful. -/
theorem dualMatrixStrictUnit_injective :
    Function.Injective (dualMatrixStrictUnit (ι := ι) (R := R)) := by
  intro X Y h
  have h' := congrArg dualMatrixInfinitesimal h
  simpa only [dualMatrixStrictUnit_infinitesimal] using h'

/-- The source contragredient acts on the strict kernel by negative transpose. -/
theorem dualMatrixStrictUnit_contragredient (X : Matrix ι ι R) :
    polarizedContragredient (ι := ι) (R := DualNumber R) (dualMatrixStrictUnit X) =
      dualMatrixStrictUnit (-X.transpose) := by
  apply Units.ext
  change (Matrix.dualNumberEquiv.symm ⟨1, -X⟩).transpose =
    Matrix.dualNumberEquiv.symm ⟨1, -X.transpose⟩
  apply Matrix.ext
  intro i j
  change (((1 : Matrix ι ι R) j i, -X j i) : DualNumber R) =
    ((1 : Matrix ι ι R) i j, -X j i)
  simp only [Matrix.one_apply, eq_comm]

/-- Conjugation by an original dual-number matrix acts on the strict kernel by its actual reduction. -/
theorem dualMatrixStrictUnit_conjugate (A : GeneralLinearGroup ι (DualNumber R))
    (X : Matrix ι ι R) :
    A * dualMatrixStrictUnit X * A⁻¹ =
      dualMatrixStrictUnit ((dualMatrixReduction A).val * X *
        (dualMatrixReduction A).inv) := by
  have hr : dualMatrixReduction (A * dualMatrixStrictUnit X * A⁻¹) = 1 := by
    rw [map_mul, map_mul, dualMatrixStrictUnit_reduction, map_inv, mul_one, mul_inv_cancel]
  rw [← dualMatrixStrictUnit_of_reduction _ hr]
  apply congrArg dualMatrixStrictUnit
  have hzero : dualMatrixInfinitesimal (A * A⁻¹) = 0 := by
    rw [mul_inv_cancel, ← dualMatrixStrictUnit_zero, dualMatrixStrictUnit_infinitesimal]
  rw [dualMatrixInfinitesimal_mul] at hzero
  rw [dualMatrixInfinitesimal_mul, dualMatrixInfinitesimal_mul,
    dualMatrixStrictUnit_infinitesimal, map_mul, dualMatrixStrictUnit_reduction, mul_one]
  change dualMatrixInfinitesimal A +
      (dualMatrixReduction A).val * X * (dualMatrixReduction A).inv +
      (dualMatrixReduction A).val * dualMatrixInfinitesimal A⁻¹ *
        (dualMatrixReduction A).inv = _
  change dualMatrixInfinitesimal A +
      (dualMatrixReduction A).val * dualMatrixInfinitesimal A⁻¹ *
        (dualMatrixReduction A).inv = 0 at hzero
  rw [add_right_comm, hzero, zero_add]

end
end Dubon2026
