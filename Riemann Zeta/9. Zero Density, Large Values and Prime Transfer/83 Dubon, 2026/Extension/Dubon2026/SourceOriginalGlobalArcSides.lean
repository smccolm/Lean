import Dubon2026.SourceOriginalGlobalArcIndex

/-! DUB-17/18 -> original Abel-Jacobi -> the pairing involution.
Every actual global boundary arc lies over a complete side of its assigned
planar region, and j is injective on it. No affine presentation is needed
for this stage; those presentations are reserved for the C1 reversal proof.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem arc_side (a : A.Arc) :
    (∃ Z : Set ℂ, A.Shares (A.regionOf a.1) Z ∧ LiesOver (A.arcPlaces a) Z) ∧
      InjOn (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) (A.arcPlaces a) := by
  obtain ⟨i, a⟩ := a
  cases i with
  | inl i =>
    cases i with
    | inl q =>
      obtain ⟨hr, k, he, hi⟩ := (A.G.ordinary q.1.1 q.1.2).arc_image q.2 a
      refine ⟨⟨_, ?_, LiesOver.of_image_eq hr he⟩, hi⟩
      exact ⟨A.regionOf_mem_window (.inl (.inl q)) rfl, k, rfl⟩
    | inr q =>
      have hq := A.branch_region_center (A.G.branchSquare q.1) q.1 (A.G.branch_cap q.1)
      obtain ⟨hr, k, he, hi⟩ :=
        (A.G.branch (A.G.branchSquare q.1) q.1 (A.G.branch_cap q.1)).arc_image hq q.2 a
      refine ⟨⟨_, ?_, LiesOver.of_image_eq hr he⟩, hi⟩
      exact ⟨A.regionOf_mem_window (.inl (.inr q)) rfl, k, rfl⟩
  | inr v =>
    obtain ⟨hr, k, he, hi⟩ := A.poles.arc_image v a
    exact ⟨⟨_, ⟨k, rfl⟩, LiesOver.of_image_eq hr he⟩, hi⟩

theorem arcPlaces_nonempty (a : A.Arc) : (A.arcPlaces a).Nonempty :=
  (A.cell a.1).arc_nonempty a.2

theorem arcPlaces_isPreconnected (a : A.Arc) : IsPreconnected (A.arcPlaces a) :=
  (A.cell a.1).arc_isPreconnected a.2

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
