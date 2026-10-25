import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Flat.Basic

/-! DUB-17/18 -> primitive determinant -> required primitive Tate pairing.
Finite-source Hom base change preserves injectivity of a bilinear pairing
over a field extension, retaining the literal tensor of its target. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- A finite-source injective bilinear map remains injective over a field extension. -/
theorem finite_bilinear_baseChange_injective
    {K E V W : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W]
    (B : V →ₗ[K] V →ₗ[K] W) (hB : Function.Injective B) :
    Function.Injective (LinearMap.BilinMap.baseChange E B) := by
  let ibc := (TensorProduct.isBaseChange K W E).linearMapRight V
  let A := B.baseChange E
  have hA : Function.Injective A :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := E) B hB
  have heval (x : E ⊗[K] V) (y : V) :
      ibc.equiv (A x) y =
        LinearMap.BilinMap.baseChange E B x ((1 : E) ⊗ₜ[K] y) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp [hx, hz]
    | tmul a x =>
      simp [A, LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul,
        LinearMap.BilinMap.baseChange_tmul, TensorProduct.smul_tmul']
  intro x z h
  apply hA
  apply ibc.equiv.injective
  apply LinearMap.ext
  intro y
  rw [heval, heval, h]

end
end Dubon2026
