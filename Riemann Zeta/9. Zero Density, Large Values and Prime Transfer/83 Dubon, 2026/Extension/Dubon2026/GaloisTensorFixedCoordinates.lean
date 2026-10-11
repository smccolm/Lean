import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Actual original coordinates recovered from genuine Galois-fixed scalar extensions -/

namespace Dubon2026
noncomputable section
open Module
open scoped TensorProduct

variable {F K M ι : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]
  [AddCommGroup M] [Module F M] [Finite ι]

omit [IsGalois F K] [Finite ι] in
/-- Actual coefficient action transforms each original extended-basis coefficient by the same field automorphism. -/
private theorem galoisTensor_basis_coordinate (b : Basis ι F M) (g : K ≃ₐ[F] K)
    (z : K ⊗[F] M) (i : ι) :
    (b.baseChange K).repr (TensorProduct.map g.toLinearMap (LinearMap.id : M →ₗ[F] M) z) i =
      g ((b.baseChange K).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k m => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A tensor in the actual scalar extension is fixed by every genuine Galois automorphism exactly when it is the image of an original coordinate. The original finite basis reduces invariance to the pinned infinite-Galois fixed-field theorem on its actual coefficients, then reconstructs an original vector. -/
theorem galoisTensor_fixed_iff_original (b : Basis ι F M) (z : K ⊗[F] M) :
    (∀ g : K ≃ₐ[F] K,
      TensorProduct.map g.toLinearMap (LinearMap.id : M →ₗ[F] M) z = z) ↔
      ∃ m : M, (1 : K) ⊗ₜ[F] m = z := by
  classical
  constructor
  · intro hz
    have hc (i : ι) : ∃ c : F, algebraMap F K c = (b.baseChange K).repr z i := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro g
      rw [← galoisTensor_basis_coordinate b g z i, hz g]
    choose c hc using hc
    refine ⟨b.equivFun.symm c, ?_⟩
    apply (b.baseChange K).repr.injective
    ext i
    rw [Basis.baseChange_repr_tmul]
    have hb : b.repr (b.equivFun.symm c) i = c i := by
      exact congrFun (b.equivFun.apply_symm_apply c) i
    rw [hb, Algebra.smul_def, mul_one, hc i]
  · rintro ⟨m, rfl⟩ g
    simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, map_one, LinearMap.id_apply]

end
end Dubon2026
