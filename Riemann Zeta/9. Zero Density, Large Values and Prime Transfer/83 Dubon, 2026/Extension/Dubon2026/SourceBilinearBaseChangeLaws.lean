import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! DUB-17/18 -> rational Weil pairing on the required Hecke component.
Transport precisely skew symmetry, Hecke adjointness and the cyclotomic
similitude law through the native bilinear scalar extension. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {R K M W : Type*} [CommRing R] [CommRing K] [Algebra R K]
variable [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]
variable (B : M →ₗ[R] M →ₗ[R] W)

theorem sourceBilinear_baseChange_skew (hB : ∀ x y, B x y = -B y x)
    (x y : K ⊗[R] M) :
    LinearMap.BilinMap.baseChange K B x y = -LinearMap.BilinMap.baseChange K B y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', neg_add_rev]
    exact add_comm _ _
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, LinearMap.add_apply, hy, hy', neg_add_rev]
      exact add_comm _ _
    | tmul b y =>
      simp only [LinearMap.BilinMap.baseChange_tmul]
      rw [hB x y, TensorProduct.tmul_neg, mul_comm a b]

theorem sourceBilinear_baseChange_adjoint (f : Module.End R M)
    (hf : ∀ x y, B (f x) y = B x (f y)) (x y : K ⊗[R] M) :
    LinearMap.BilinMap.baseChange K B (f.baseChange K x) y =
      LinearMap.BilinMap.baseChange K B x (f.baseChange K y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [map_add, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul, hf]

theorem sourceBilinear_baseChange_multiplier (f : Module.End R M) (c : R)
    (hf : ∀ x y, B (f x) (f y) = c • B x y) (x y : K ⊗[R] M) :
    LinearMap.BilinMap.baseChange K B (f.baseChange K x) (f.baseChange K y) =
      algebraMap R K c • LinearMap.BilinMap.baseChange K B x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [map_add, hx, hx', smul_add]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', smul_add]
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinMap.baseChange_tmul, hf]
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      exact congrArg (fun a : K => a ⊗ₜ[R] B x y) (Algebra.smul_def c (a * b))

end
end Dubon2026
