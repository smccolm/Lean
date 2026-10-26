import Mathlib.RingTheory.TensorProduct.Basic

/-! DUB-17/18 -> primitive determinant -> retain the existing spanning
specialization after coefficient extension, for both its original Hecke
operators and its original Galois matrices. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {K E V W : Type*} [Field K] [Field E] [Algebra K E]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module E W] [Module K W] [IsScalarTower K E W]

theorem liftBaseChange_intertwine (π : V →ₗ[K] W)
    (H : Module.End K V) (M : Module.End E W)
    (h : ∀ v, π (H v) = M (π v)) (x : E ⊗[K] V) :
    π.liftBaseChange E (H.baseChange E x) = M (π.liftBaseChange E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, h, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem liftBaseChange_scalar_intertwine (π : V →ₗ[K] W)
    (H : Module.End K V) (a : E)
    (h : ∀ v, π (H v) = a • π v) (x : E ⊗[K] V) :
    π.liftBaseChange E (H.baseChange E x) = a • π.liftBaseChange E x :=
  liftBaseChange_intertwine π H (a • (1 : Module.End E W)) h x

end
end Dubon2026
