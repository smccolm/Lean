import Dubon2026.SourceSL2CocycleExists

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual Galois association -> weight-two integral lifting.
The already proved modular-generator existence theorem avoids constructing
a separate PSL2 free-product model. Uniqueness is now needed to identify the
reduction of the lifted native cocycle with the original cocycle.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup groupCohomology

private theorem nativeCocycle_zero_on_closure
    {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (c : cocycles₁ A) (B : Set G) (hB : ∀ b ∈ B, c b = 0)
    (g : G) (hg : g ∈ Subgroup.closure B) : c g = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hB x hx
  | one => exact cocycles₁_map_one c
  | mul x y _ _ hx hy =>
    rw [(mem_cocycles₁_iff c).mp c.property, hx, hy, map_zero, add_zero]
  | inv x _ hx =>
    have h := cocycles₁_map_inv c x
    rw [hx, neg_zero] at h
    have h' := congrArg (A.ρ x⁻¹) h
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h'

/-- Native cocycles on the actual modular group are determined by S and S*T. -/
theorem sourceSL2Cocycle_ext {R : Type} [CommRing R] (A : Rep R SL(2, ℤ))
    (c d : cocycles₁ A) (hS : c S = d S) (hU : c (S * T) = d (S * T)) :
    c = d := by
  have hzS : (c - d) S = 0 := sub_eq_zero.mpr hS
  have hzU : (c - d) (S * T) = 0 := sub_eq_zero.mpr hU
  have hzT : (c - d) T = 0 := by
    have h := (mem_cocycles₁_iff (c - d)).mp (c - d).property S T
    rw [hzU, hzS, add_zero] at h
    have h' := congrArg (A.ρ S⁻¹) h
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h'.symm
  apply cocycles₁_ext
  intro g
  apply sub_eq_zero.mp
  exact nativeCocycle_zero_on_closure A (c - d) {S, T}
    (by intro b hb; rcases hb with rfl | rfl; exact hzS; exact hzT) g
    (by rw [SpecialLinearGroup.SL2Z_generators]; trivial)

end
end Dubon2026
