import Dubon2026.ContinuousRepresentationCocycles
import Mathlib.GroupTheory.Perm.Basic

/-! Encode the actual one-cocycle as its affine action on the original
coefficient module. A fixed point is exactly the local coboundary condition.
This permits DUB-17 prescribed Frobenius to retain dual-class detection in a
finite permutation factor, without rebuilding the existing cohomology theory. -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- The actual affine action associated to an original representation cocycle. -/
def cocycleAffinePermutation (c : groupCohomology.cocycles₁ A) : G →* Equiv.Perm A where
  toFun g := {
    toFun := fun x => A.ρ g x + c g
    invFun := fun x => A.ρ g⁻¹ (x - c g)
    left_inv := by
      intro x
      dsimp only
      rw [add_sub_cancel_right, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one]
      rfl
    right_inv := by
      intro x
      dsimp only
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      exact sub_add_cancel x (c g) }
  map_one' := by
    apply Equiv.ext
    intro x
    change A.ρ 1 x + c 1 = x
    rw [map_one, groupCohomology.cocycles₁_map_one, add_zero]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro x
    change A.ρ (g * h) x + c (g * h) = A.ρ g (A.ρ h x + c h) + c g
    have hc : c (g * h) = A.ρ g (c h) + c g :=
      (groupCohomology.mem_cocycles₁_iff _).mp c.property g h
    rw [map_mul, Module.End.mul_apply, map_add, hc, add_assoc]

/-- A fixed point of the original affine cocycle action is exactly a
coboundary value at the same original group element. -/
theorem cocycleAffinePermutation_exists_fixed_iff
    (c : groupCohomology.cocycles₁ A) (g : G) :
    (∃ x : A, cocycleAffinePermutation A c g x = x) ↔
      c g ∈ LinearMap.range (A.ρ g - 1) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    change A.ρ g (-x) - -x = c g
    change A.ρ g x + c g = x at hx
    rw [map_neg]
    calc
      -A.ρ g x - -x = x - A.ρ g x := by abel
      _ = c g := (eq_sub_of_add_eq' hx).symm
  · rintro ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    change A.ρ g (-x) + c g = -x
    change A.ρ g x - x = c g at hx
    rw [map_neg, ← hx]
    abel

/-- Conjugate permutation images have equivalent fixed-point existence.
Consequently the affine encoding retains the non-coboundary test under the
prescribed Frobenius conjugacy supplied by Chebotarev. -/
theorem permutation_isConj_exists_fixed_iff {V : Type*}
    {f g : Equiv.Perm V} (h : IsConj f g) :
    (∃ x, f x = x) ↔ ∃ x, g x = x := by
  obtain ⟨e, rfl⟩ := isConj_iff.mp h
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using congrArg e hx
  · rintro ⟨x, hx⟩
    refine ⟨e⁻¹ x, ?_⟩
    apply e.injective
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hx

end
end Dubon2026
