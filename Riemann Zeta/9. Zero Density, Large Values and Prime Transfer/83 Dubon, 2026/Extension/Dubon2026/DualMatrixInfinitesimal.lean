import Mathlib.Data.Matrix.DualNumber
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.NoncommRing

/-! # The actual first-order part of an invertible dual-number matrix -/

namespace Dubon2026

noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original first component of a matrix over the dual numbers. -/
def dualMatrixFst (A : Matrix ι ι (DualNumber R)) : Matrix ι ι R :=
  (Matrix.dualNumberEquiv A).fst

/-- The original epsilon component of a matrix over the dual numbers. -/
def dualMatrixSnd (A : Matrix ι ι (DualNumber R)) : Matrix ι ι R :=
  (Matrix.dualNumberEquiv A).snd

/-- The original epsilon components satisfy the exact first-order matrix product rule. -/
theorem dualMatrixSnd_mul (A B : Matrix ι ι (DualNumber R)) :
    dualMatrixSnd (A * B) = dualMatrixFst A * dualMatrixSnd B +
      dualMatrixSnd A * dualMatrixFst B := by
  change (Matrix.dualNumberEquiv (A * B)).snd = _
  rw [map_mul, DualNumber.snd_mul]
  rfl

/-- The actual reduction of an invertible dual-number matrix to its original coefficient ring. -/
def dualMatrixReduction : GeneralLinearGroup ι (DualNumber R) →* GeneralLinearGroup ι R :=
  GeneralLinearGroup.map (TrivSqZeroExt.fstHom R R R).toRingHom

/-- The first component of the original matrix is exactly its actual invertible reduction. -/
theorem dualMatrixFst_val (A : GeneralLinearGroup ι (DualNumber R)) :
    dualMatrixFst A.val = (dualMatrixReduction A).val := rfl

/-- The original right logarithmic first-order matrix, formed from the genuine epsilon part and inverse of the actual reduction. -/
def dualMatrixInfinitesimal (A : GeneralLinearGroup ι (DualNumber R)) : Matrix ι ι R :=
  dualMatrixSnd A.val * ((dualMatrixReduction A)⁻¹).val

/-- The actual infinitesimal part satisfies the adjoint cocycle identity on the original dual-number general-linear group. -/
theorem dualMatrixInfinitesimal_mul (A B : GeneralLinearGroup ι (DualNumber R)) :
    dualMatrixInfinitesimal (A * B) = dualMatrixInfinitesimal A +
      (dualMatrixReduction A).val * dualMatrixInfinitesimal B *
        ((dualMatrixReduction A)⁻¹).val := by
  let a := dualMatrixReduction A
  let b := dualMatrixReduction B
  have hb : b.val * (b⁻¹).val = 1 := b.mul_inv
  change dualMatrixSnd (A * B).val * ((dualMatrixReduction (A * B))⁻¹).val = _
  rw [Units.val_mul, dualMatrixSnd_mul, dualMatrixFst_val, dualMatrixFst_val, map_mul,
    _root_.mul_inv_rev, Units.val_mul]
  change (a.val * dualMatrixSnd B.val + dualMatrixSnd A.val * b.val) *
      ((b⁻¹).val * (a⁻¹).val) =
    dualMatrixSnd A.val * (a⁻¹).val +
      a.val * (dualMatrixSnd B.val * (b⁻¹).val) * (a⁻¹).val
  calc
    _ = a.val * (dualMatrixSnd B.val * (b⁻¹).val) * (a⁻¹).val +
        dualMatrixSnd A.val * (b.val * (b⁻¹).val) * (a⁻¹).val := by noncomm_ring
    _ = _ := by rw [hb, mul_one, add_comm]

end
end Dubon2026
