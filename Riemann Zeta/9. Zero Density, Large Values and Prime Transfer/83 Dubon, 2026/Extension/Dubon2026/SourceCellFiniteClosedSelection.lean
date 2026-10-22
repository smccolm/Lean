import Mathlib.Topology.Connected.Basic

/-! DUB-17/18 -> original Abel-Jacobi -> actual arc pairing.
The constructed branch and pole carriers are compact and pairwise disjoint.
Finite closed separation selects the unique carrier containing a connected
lifted arc, without adding disjoint chart-neighborhood assumptions.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcSelection
open Set

theorem exists_subset_of_finite_closed {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {L : Set X} {C : ι → Set X} (hL : IsPreconnected L) (hne : L.Nonempty)
    (hclosed : ∀ i, IsClosed (C i)) (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : L ⊆ ⋃ i, C i) : ∃ i, L ⊆ C i := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let T : Set X := ⋃ j ∈ ({i}ᶜ : Set ι), C j
  have hT : IsClosed T := (Set.toFinite _).isClosed_biUnion fun j _ => hclosed j
  have hsub : L ⊆ C i ∪ T := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hj : j = i
    · exact Or.inl (hj ▸ hyj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, hj, hyj⟩)
  have hd : Disjoint (C i) T := by
    rw [Set.disjoint_left]
    intro y hyi hyT
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hyT
    exact Set.disjoint_left.mp (hdisj (Ne.symm hj)) hyi hyj
  refine ⟨i, fun y hy => ?_⟩
  by_contra hyi
  have hyT := (hsub hy).resolve_left hyi
  obtain ⟨z, _, hzi, hzT⟩ := isPreconnected_closed_iff.mp hL (C i) T
    (hclosed i) hT hsub ⟨x, hx, hxi⟩ ⟨y, hy, hyT⟩
  exact Set.disjoint_left.mp hd hzi hzT

theorem eq_of_image_subset_of_injOn {α β : Type*} {f : α → β} {L T : Set α}
    (hLT : L ⊆ T) (himage : f '' T ⊆ f '' L) (hinj : InjOn f T) : L = T := by
  refine Subset.antisymm hLT fun t ht => ?_
  obtain ⟨l, hl, hfl⟩ := himage ⟨t, ht, rfl⟩
  exact (hinj (hLT hl) ht hfl) ▸ hl

end Dubon2026.SourceFunctionField.CellGeometry.ArcSelection
