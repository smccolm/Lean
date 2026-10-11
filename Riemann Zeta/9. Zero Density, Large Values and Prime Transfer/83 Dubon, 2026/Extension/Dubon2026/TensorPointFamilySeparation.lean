import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Algebra.Hom

/-! # Original finite point families detect actual tensors -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {K A B ι : Type*} [CommRing K] [AddCommGroup A] [Module K A]
  [Module.Flat K A] [CommRing B] [Algebra K B] [Finite ι]

/-- A genuine finite point family that separates the original coordinate algebra also separates tensors with the original flat module in the first factor. Flat tensor injection and the actual finite product tensor equivalence prove this assertion. -/
theorem tensorPointFamily_separates (p : ι → B →ₐ[K] K)
    (hp : Function.Injective (fun b : B => fun i : ι => p i b)) :
    Function.Injective (fun z : A ⊗[K] B => fun i : ι => (p i).toLinearMap.lTensor A z) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e : B →ₗ[K] (ι → K) := LinearMap.pi (fun i => (p i).toLinearMap)
  have he : Function.Injective e := hp
  have ht : Function.Injective (e.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A) e he
  let d := TensorProduct.piRight K K A (fun _ : ι => K)
  have hd (z : A ⊗[K] B) (i : ι) : d (e.lTensor A z) i = (p i).toLinearMap.lTensor A z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  intro x y hxy
  apply ht
  apply d.injective
  funext i
  rw [hd, hd]
  exact congrFun hxy i

end
end Dubon2026
