import Dubon2026.AlgebraBaseChangePoints
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic

/-! # Genuine tensor-coordinate injection into the generic fiber -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R F A B K : Type*} [CommRing R] [CommRing F] [Algebra R F]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- The actual original tensor coordinates mapped into the two scalar-extended factors. -/
def genericFiberTensorCoordinates : A ⊗[R] B →ₗ[R] (F ⊗[R] A) ⊗[F] (F ⊗[R] B) :=
  ((TensorProduct.AlgebraTensorModule.distribBaseChange R F A B).toLinearMap.restrictScalars R).comp
    (TensorProduct.mk R F (A ⊗[R] B) 1)

/-- The generic-fiber tensor map preserves each original pair of pure coordinates. -/
theorem genericFiberTensorCoordinates_tmul (a : A) (b : B) :
    genericFiberTensorCoordinates (F := F) (a ⊗ₜ[R] b) =
      (1 ⊗ₜ[R] a) ⊗ₜ[F] (1 ⊗ₜ[R] b) := by
  rfl

/-- Finite-flat applications use the actual injectivity of original free tensor coordinates under faithful scalar extension. -/
theorem genericFiberTensorCoordinates_injective [FaithfulSMul R F]
    [Module.Free R A] [Module.Free R B] :
    Function.Injective (genericFiberTensorCoordinates (R := R) (F := F) (A := A) (B := B)) := by
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange R F A B).injective.comp
    (Module.Flat.tensorProduct_mk_injective (R := R) (S := F) (M := A ⊗[R] B))

/-- Evaluation on a pair of genuine generic-fiber points equals evaluation of the original tensor at their actual original restrictions. -/
theorem genericFiberTensorCoordinates_point_pair [CommRing K] [Algebra R K]
    [Algebra F K] [IsScalarTower R F K]
    (p : F ⊗[R] A →ₐ[F] K) (q : F ⊗[R] B →ₐ[F] K) (z : A ⊗[R] B) :
    Algebra.TensorProduct.productMap p q (genericFiberTensorCoordinates z) =
      Algebra.TensorProduct.productMap ((AlgHom.liftEquiv R F A K).symm p)
        ((AlgHom.liftEquiv R F B K).symm q) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

end
end Dubon2026
