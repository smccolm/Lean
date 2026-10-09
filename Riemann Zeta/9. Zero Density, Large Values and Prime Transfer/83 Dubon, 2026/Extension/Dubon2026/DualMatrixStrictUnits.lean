import Dubon2026.FirstOrderDeformationEquiv

/-! # Actual matrices congruent to the identity over the dual numbers -/

namespace Dubon2026

noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual invertible matrix `I + epsilon X`, with explicit inverse `I - epsilon X`. -/
def dualMatrixStrictUnit (X : Matrix ι ι R) : GeneralLinearGroup ι (DualNumber R) where
  val := Matrix.dualNumberEquiv.symm ⟨1, X⟩
  inv := Matrix.dualNumberEquiv.symm ⟨1, -X⟩
  val_inv := by
    apply Matrix.dualNumberEquiv.injective
    rw [map_mul Matrix.dualNumberEquiv, map_one Matrix.dualNumberEquiv]
    simp only [AlgEquiv.apply_symm_apply]
    apply TrivSqZeroExt.ext <;> simp
  inv_val := by
    apply Matrix.dualNumberEquiv.injective
    rw [map_mul Matrix.dualNumberEquiv, map_one Matrix.dualNumberEquiv]
    simp only [AlgEquiv.apply_symm_apply]
    apply TrivSqZeroExt.ext <;> simp

/-- The original strict unit reduces to the identity. -/
theorem dualMatrixStrictUnit_reduction (X : Matrix ι ι R) :
    dualMatrixReduction (dualMatrixStrictUnit X) = 1 := by
  apply Units.ext
  rfl

/-- The inverse of the original strict unit has the negated epsilon component. -/
theorem dualMatrixStrictUnit_inv (X : Matrix ι ι R) :
    (dualMatrixStrictUnit X)⁻¹ = dualMatrixStrictUnit (-X) := by
  apply Units.ext
  rfl

/-- The infinitesimal matrix of the actual strict unit is exactly its input matrix. -/
theorem dualMatrixStrictUnit_infinitesimal (X : Matrix ι ι R) :
    dualMatrixInfinitesimal (dualMatrixStrictUnit X) = X := by
  rw [dualMatrixInfinitesimal, dualMatrixStrictUnit_reduction]
  change X * (1 : Matrix ι ι R) = X
  exact mul_one X

/-- Every original invertible matrix reducing to the identity is the strict unit of its actual infinitesimal matrix. -/
theorem dualMatrixStrictUnit_of_reduction (U : GeneralLinearGroup ι (DualNumber R))
    (hU : dualMatrixReduction U = 1) :
    dualMatrixStrictUnit (dualMatrixInfinitesimal U) = U := by
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  change Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm
    ⟨1, dualMatrixInfinitesimal U⟩) = Matrix.dualNumberEquiv U.val
  rw [AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext
  · change (1 : Matrix ι ι R) = dualMatrixFst U.val
    rw [dualMatrixFst_val, hU]
    rfl
  · change dualMatrixInfinitesimal U = dualMatrixSnd U.val
    rw [dualMatrixInfinitesimal, hU]
    exact mul_one _

/-- Actual conjugation by the strict unit changes the first-order part by the original adjoint coboundary formula. -/
theorem dualMatrixInfinitesimal_strictConjugate (A : GeneralLinearGroup ι (DualNumber R))
    (X : Matrix ι ι R) :
    dualMatrixInfinitesimal (dualMatrixStrictUnit X * A * (dualMatrixStrictUnit X)⁻¹) =
      dualMatrixInfinitesimal A + X -
        (dualMatrixReduction A).val * X * ((dualMatrixReduction A)⁻¹).val := by
  rw [dualMatrixStrictUnit_inv, dualMatrixInfinitesimal_mul,
    dualMatrixInfinitesimal_mul, dualMatrixStrictUnit_infinitesimal,
    dualMatrixStrictUnit_infinitesimal, map_mul, dualMatrixStrictUnit_reduction]
  simp only [Units.val_one, one_mul, inv_one, mul_one]
  noncomm_ring

end
end Dubon2026
