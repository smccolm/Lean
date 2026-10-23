import Dubon2026.SourceIntegralCoordinateBaseChange
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! DUB-17/18 -> primitive specialization -> the scalar-extended
integral Hecke algebra still acts faithfully by the original matrices.
The native tensor algebra map agrees entrywise with the proved faithful
extension of integral coordinates. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {A : Type*} [Ring A] {n : ℕ}
variable (M : A →+* Matrix (Fin n) (Fin n) ℤ)
variable (K : Type*) [Field K]

/-- The literal integral matrix entries as a finite coordinate map. -/
def integralMatrixCoordinates : A →ₗ[ℤ] (Fin n × Fin n → ℤ) where
  toFun a := fun ij => M a ij.1 ij.2
  map_add' a b := by ext ij; exact congrFun (congrFun (map_add M a b) ij.1) ij.2
  map_smul' z a := by
    ext ij
    exact congrFun (congrFun (map_zsmul M z a) ij.1) ij.2

/-- Scalar extension of the original integral matrix algebra action. -/
def integralMatrixBaseChange : K ⊗[ℤ] A →ₐ[K] Matrix (Fin n) (Fin n) K :=
  AlgHom.liftEquiv ℤ K A (Matrix (Fin n) (Fin n) K)
    (((Int.castRingHom K).mapMatrix).comp M).toIntAlgHom

theorem integralMatrixBaseChange_tmul (c : K) (a : A) :
    integralMatrixBaseChange M K (c ⊗ₜ[ℤ] a) = c • (M a).map (Int.cast : ℤ → K) := rfl

theorem integralMatrixBaseChange_coordinates (x : K ⊗[ℤ] A) (ij : Fin n × Fin n) :
    integralMatrixBaseChange M K x ij.1 ij.2 =
      integralCoordinateBaseChange (integralMatrixCoordinates M) K x ij := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Matrix.zero_apply, Pi.zero_apply]
  | tmul c a => rfl
  | add x y hx hy => simp only [map_add, Matrix.add_apply, Pi.add_apply, hx, hy]

theorem integralMatrixBaseChange_injective [CharZero K] (hM : Function.Injective M) :
    Function.Injective (integralMatrixBaseChange M K) := by
  have hi : Function.Injective (integralMatrixCoordinates M) := by
    intro a b h
    apply hM
    ext i j
    exact congrFun h (i, j)
  intro x y h
  apply integralCoordinateBaseChange_injective (integralMatrixCoordinates M) K hi
  ext ij
  exact (integralMatrixBaseChange_coordinates M K x ij).symm.trans
    ((congrArg (fun B : Matrix (Fin n) (Fin n) K => B ij.1 ij.2) h).trans
      (integralMatrixBaseChange_coordinates M K y ij))

end
end Dubon2026
