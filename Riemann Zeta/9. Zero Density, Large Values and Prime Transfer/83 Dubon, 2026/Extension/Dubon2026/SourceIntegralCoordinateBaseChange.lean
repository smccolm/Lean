import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.TorsionFree

/-! DUB-17/18 -> primitive coefficient specialization of the actual Tate
Hecke algebra -> faithful scalar extension of its integral matrices.
Native flatness over the integers and the finite-product tensor equivalence
preserve injectivity. This avoids a second determinant/descent argument. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {A : Type*} [AddCommGroup A] [Module ℤ A]
variable {ι : Type*}
variable (F : A →ₗ[ℤ] (ι → ℤ)) (K : Type*) [Field K]

/-- Scalar extension of the literal integral coordinates. -/
def integralCoordinateBaseChange : K ⊗[ℤ] A →ₗ[K] (ι → K) :=
  LinearMap.liftBaseChange K
    (((Int.castRingHom K).toIntAlgHom.toLinearMap.compLeft ι).comp F)

theorem integralCoordinateBaseChange_tmul (c : K) (a : A) (i : ι) :
    integralCoordinateBaseChange F K (c ⊗ₜ[ℤ] a) i = c * (F a i : K) := rfl

variable [Fintype ι] [DecidableEq ι]

theorem integralCoordinateBaseChange_factor (x : K ⊗[ℤ] A) :
    integralCoordinateBaseChange F K x =
      TensorProduct.piScalarRight ℤ K K ι (F.lTensor K x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    ext i
    simp only [integralCoordinateBaseChange_tmul, LinearMap.lTensor_tmul,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      zsmul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem integralCoordinateBaseChange_injective [CharZero K] (hF : Function.Injective F) :
    Function.Injective (integralCoordinateBaseChange F K) := by
  have ht := Module.Flat.lTensor_preserves_injective_linearMap (M := K) F hF
  intro x y h
  apply ht
  apply (TensorProduct.piScalarRight ℤ K K ι).injective
  exact (integralCoordinateBaseChange_factor F K x).symm.trans
    (h.trans (integralCoordinateBaseChange_factor F K y))

end
end Dubon2026
