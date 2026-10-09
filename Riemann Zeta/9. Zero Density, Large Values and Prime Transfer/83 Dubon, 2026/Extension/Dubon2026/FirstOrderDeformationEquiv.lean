import Dubon2026.CocycleFirstOrderLift

/-! # Exact equivalence between original first-order lifts and original adjoint cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Reconstructing a genuine original lift from its actual first-order cocycle recovers the entire original dual-number representation. -/
theorem firstOrderLiftFromCocycle_cocycle (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) :
    firstOrderLiftFromCocycle ρ (matrixFirstOrderCocycle ρ τ) = τ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  have hg : dualMatrixReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property g
  have hf : dualMatrixFst (τ.val g).val = (ρ g).val := by rw [dualMatrixFst_val, hg]
  change Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm
    ⟨(ρ g).val, matrixFirstOrderCocycle ρ τ g * (ρ g).val⟩) =
      Matrix.dualNumberEquiv (τ.val g).val
  rw [AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext
  · exact hf.symm
  · change dualMatrixInfinitesimal (τ.val g) * (ρ g).val = dualMatrixSnd (τ.val g).val
    rw [← hg, dualMatrixInfinitesimal, mul_assoc, Units.inv_mul, mul_one]

/-- The actual first-order representation fiber is equivalent to Mathlib's genuine adjoint cocycle module, with both inverse constructions proved on original matrices. -/
def matrixFirstOrderLiftEquiv (ρ : G →* GeneralLinearGroup ι R) :
    MatrixFirstOrderLift ρ ≃ groupCohomology.cocycles₁ (matrixAdjointRep ρ) where
  toFun := matrixFirstOrderCocycle ρ
  invFun := firstOrderLiftFromCocycle ρ
  left_inv := firstOrderLiftFromCocycle_cocycle ρ
  right_inv := matrixFirstOrderCocycle_fromCocycle ρ

end
end Dubon2026
