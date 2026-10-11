import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

/-! # Actual inverse closure of a compact submonoid in an original topological group -/

namespace Dubon2026

/-- A compact submonoid of the original Hausdorff topological group contains
the inverse of every original member. Apply the compact-semigroup idempotent result
to its left translate; the only original group idempotent is one. -/
theorem compactSubmonoid_inv_mem
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (M : Submonoid G) (hM : IsCompact (M : Set G)) {u : G} (hu : u ∈ M) :
    u⁻¹ ∈ M := by
  let s : Set G := (fun x => u * x) '' (M : Set G)
  have hs : IsCompact s := hM.image (continuous_const.mul continuous_id)
  have hne : s.Nonempty := ⟨u * 1, 1, M.one_mem, rfl⟩
  have hmul : ∀ᵉ (x ∈ s) (y ∈ s), x * y ∈ s := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨x * u * y, M.mul_mem (M.mul_mem hx hu) hy, ?_⟩
    simp only [mul_assoc]
  obtain ⟨z, hz, hid⟩ := exists_idempotent_in_compact_subsemigroup
    (fun r => continuous_id.mul_const r) s hne hs hmul
  have hz1 : z = 1 := mul_left_cancel (hid.trans (mul_one z).symm)
  obtain ⟨y, hy, hey⟩ := hz
  have he : u * y = 1 := hey.trans hz1
  have hyinv : y = u⁻¹ := by
    calc
      y = u⁻¹ * (u * y) := by simp
      _ = u⁻¹ := by rw [he, mul_one]
  exact hyinv ▸ hy

/-- The actual compact submonoid, with its original carrier and multiplication,
is a subgroup by its proved inverse closure. -/
def compactSubmonoidSubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (M : Submonoid G) (hM : IsCompact (M : Set G)) : Subgroup G where
  carrier := M
  one_mem' := M.one_mem
  mul_mem' := M.mul_mem
  inv_mem' := compactSubmonoid_inv_mem M hM

end Dubon2026
