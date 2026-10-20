import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Literal scalar extension of the finite source embedding tensor.
The original factor bases and native tensor bases give the comparison.
Its exact pure-tensor formula identifies it independently of the chosen
bases and is the formula required by the original arithmetic action.
-/

namespace Dubon2026
noncomputable section
open Module
open scoped TensorProduct

variable (R B : Type*) [CommSemiring R] [CommSemiring B] [Algebra R B]
variable {I : Type*} [Finite I] {M : I → Type*} {J : I → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The scalar extension of the actual finite tensor is equivalent to the tensor of the actual scalar-extended factors, through their original bases. -/
def sourcePiTensorBaseChangeEquiv (b : ∀ i, Basis (J i) R (M i)) :
    B ⊗[R] (⨂[R] i, M i) ≃ₗ[B] (⨂[B] i, B ⊗[R] M i) :=
  ((Basis.piTensorProduct b).baseChange B).equiv
    (Basis.piTensorProduct fun i => (b i).baseChange B) (Equiv.refl _)

/-- The actual tensor comparison preserves coordinates in the original tensor bases. -/
theorem sourcePiTensorBaseChangeEquiv_repr (b : ∀ i, Basis (J i) R (M i))
    (z : B ⊗[R] (⨂[R] i, M i)) :
    (Basis.piTensorProduct fun i => (b i).baseChange B).repr
      (sourcePiTensorBaseChangeEquiv R B b z) =
        ((Basis.piTensorProduct b).baseChange B).repr z := by
  simp [sourcePiTensorBaseChangeEquiv, Basis.equiv]

/-- The comparison sends the original integral pure tensor to the pure tensor of its original scalar-extended factors. -/
theorem sourcePiTensorBaseChangeEquiv_one_tprod
    (b : ∀ i, Basis (J i) R (M i)) (p : ∀ i, M i) :
    sourcePiTensorBaseChangeEquiv R B b ((1 : B) ⊗ₜ[R] PiTensorProduct.tprod R p) =
      PiTensorProduct.tprod B (fun i => (1 : B) ⊗ₜ[R] p i) := by
  letI := Fintype.ofFinite I
  apply (Basis.piTensorProduct fun i => (b i).baseChange B).repr.injective
  rw [sourcePiTensorBaseChangeEquiv_repr]
  ext j
  simp only [Basis.baseChange_repr_tmul, Basis.piTensorProduct_repr_tprod_apply,
    Algebra.smul_def, mul_one, map_prod]

/-- The literal tensor comparison retains the exact original scalar on every scalar times a pure tensor. -/
theorem sourcePiTensorBaseChangeEquiv_tprod
    (b : ∀ i, Basis (J i) R (M i)) (k : B) (p : ∀ i, M i) :
    sourcePiTensorBaseChangeEquiv R B b (k ⊗ₜ[R] PiTensorProduct.tprod R p) =
      k • PiTensorProduct.tprod B (fun i => (1 : B) ⊗ₜ[R] p i) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul,
    sourcePiTensorBaseChangeEquiv_one_tprod]

end
end Dubon2026
