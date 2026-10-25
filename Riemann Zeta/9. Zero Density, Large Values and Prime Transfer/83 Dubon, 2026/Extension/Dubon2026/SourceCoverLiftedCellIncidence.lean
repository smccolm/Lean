import Dubon2026.SourceOriginalCellArcGeometry

/-! DUB-17/18 -> lifted intersection chains -> exact carrier/arc incidence.
Within one lifted cell, projection and injectivity of the original coordinate
identify membership in every original arc with membership in its actual lift.
Disjoint sheet domains give uniqueness at a fixed cover point. -/
namespace Dubon2026.SourceFunctionField.SheetCover
open Set CellGeometry

theorem lifted_carrier_projects {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (p : X → B) (e : OpenPartialHomeomorph B ℂ) (ζ : OpenPartialHomeomorph X ℂ)
    (R : RadialRegion) (hp : ∀ z ∈ R.K, p (ζ.symm z) = e.symm z)
    {w : X} (hw : w ∈ ζ.symm '' R.K) : p w ∈ e.symm '' R.K := by
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, hz, (hp z hz).symm⟩

theorem lifted_arc_iff_over_arc {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (p : X → B) (e : OpenPartialHomeomorph B ℂ) (ζ : OpenPartialHomeomorph X ℂ)
    (R : RadialRegion) (hK : R.K ⊆ e.target)
    (hp : ∀ z ∈ R.K, p (ζ.symm z) = e.symm z)
    {w : X} (hw : w ∈ ζ.symm '' R.K) (k : Fin R.N) :
    w ∈ ζ.symm '' R.arcSet k ↔ p w ∈ e.symm '' R.arcSet k := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hp z (R.arcSet_subset_K k hz)).symm⟩
  · rintro ⟨z, hz, he⟩
    obtain ⟨u, hu, rfl⟩ := hw
    have hzu : z = u := e.symm.injOn (hK (R.arcSet_subset_K k hz)) (hK hu)
      (he.trans (hp u hu))
    exact ⟨z, hz, congrArg ζ.symm hzu⟩

theorem lifted_carrier_unique {X : Type*} [TopologicalSpace X] {J : Type*}
    (ζ : J → OpenPartialHomeomorph X ℂ) (K : Set ℂ)
    (hK : ∀ j, K ⊆ (ζ j).target)
    (hd : Pairwise fun i j => Disjoint (ζ i).source (ζ j).source)
    {i j : J} {w : X} (hi : w ∈ (ζ i).symm '' K) (hj : w ∈ (ζ j).symm '' K) : i = j := by
  by_contra hne
  obtain ⟨z, hz, he⟩ := hi
  obtain ⟨u, hu, hf⟩ := hj
  exact Set.disjoint_left.mp (hd hne) (he ▸ (ζ i).map_target (hK i hz))
    (hf ▸ (ζ j).map_target (hK j hu))

end Dubon2026.SourceFunctionField.SheetCover
