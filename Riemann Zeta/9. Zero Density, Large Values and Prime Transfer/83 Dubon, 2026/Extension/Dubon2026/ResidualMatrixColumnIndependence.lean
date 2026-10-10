import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The actual residue-identity column matrix and independence of original column lifts -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [IsLocalRing R]

/-- The genuine column matrix formed by evaluating each original lifted matrix on the selected standard vector. -/
def residualColumnMatrix (v : ι → Matrix ι ι R) (i₀ : ι) : Matrix ι ι R :=
  Matrix.of (fun i j => v j i i₀)

/-- Original lifts of residual column units produce a change-of-basis matrix whose true original reduction is exactly the identity. -/
theorem residualColumnMatrix_reduction (v : ι → Matrix ι ι R) (i₀ : ι)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i) =
      Matrix.single i i₀ 1) :
    (RingHom.mapMatrix (IsLocalRing.residue R)) (residualColumnMatrix v i₀) = 1 := by
  ext i j
  have h := congrArg (fun X : Matrix ι ι (IsLocalRing.ResidueField R) => X i i₀) (hv j)
  change IsLocalRing.residue R (v j i i₀) = (1 : Matrix ι ι (IsLocalRing.ResidueField R)) i j
  simpa [Matrix.single, Matrix.one_apply, eq_comm] using h

/-- The actual original column matrix is invertible over the original local ring, by its genuine residue-identity determinant. -/
theorem residualColumnMatrix_isUnit (v : ι → Matrix ι ι R) (i₀ : ι)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i) =
      Matrix.single i i₀ 1) : IsUnit (residualColumnMatrix v i₀) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_of_map_unit (IsLocalRing.residue R)
  rw [RingHom.map_det, residualColumnMatrix_reduction v i₀ hv, Matrix.det_one]
  exact isUnit_one

/-- The original matrices lifting the distinct residual column units are linearly independent over the original local coefficient ring, as witnessed by their actual invertible column matrix. -/
theorem residualMatrixColumns_linearIndependent (v : ι → Matrix ι ι R) (i₀ : ι)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i) =
      Matrix.single i i₀ 1) : LinearIndependent R v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let B := residualColumnMatrix v i₀
  have hmul : B.mulVec c = 0 := by
    ext i
    have h := congrArg (fun X : Matrix ι ι R => X i i₀) hc
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
    change (∑ k, v k i i₀ * c k) = 0
    simpa only [mul_comm] using h
  have hc0 : c = 0 := by
    apply Matrix.mulVec_injective_of_isUnit (residualColumnMatrix_isUnit v i₀ hv)
    simpa only [Matrix.mulVec_zero] using hmul
  exact congrFun hc0 j

end
end Dubon2026
