import Dubon2026.UniversalEnvelopingInduction
import Dubon2026.ComplexSl2Basis

/-! # Exact linear intertwiners of genuine enveloping-algebra actions -/

namespace Dubon2026

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Intertwining all actual Lie generators intertwines the full original enveloping algebra. -/
theorem universalEnveloping_intertwine
    (T : UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ] Module.End ℂ V)
    (S : UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ] Module.End ℂ W)
    (u : V →ₗ[ℂ] W)
    (h : ∀ x v, u (T (UniversalEnvelopingAlgebra.ι ℂ x) v) =
      S (UniversalEnvelopingAlgebra.ι ℂ x) (u v))
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (v : V) : u (T z v) = S z (u v) := by
  induction z using universalEnveloping_induction generalizing v with
  | hscalar c =>
      rw [AlgHom.commutes, AlgHom.commutes]
      change u (c • v) = c • u v
      exact map_smul _ _ _
  | hgenerator x => exact h x v
  | hadd x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | hmul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]

/-- A genuine nonzero image of an eigenvector forces exact equality of its two intertwined scalars. -/
theorem linearIntertwiner_eigenvalue (T : Module.End ℂ V) (S : Module.End ℂ W)
    (u : V →ₗ[ℂ] W) (v : V) (a b : ℂ) (hv : u v ≠ 0)
    (hi : u (T v) = S (u v)) (hT : T v = a • v) (hS : S (u v) = b • u v) : a = b := by
  rw [hT, map_smul, hS] at hi
  exact smul_left_injective ℂ hv hi

end
end Dubon2026
