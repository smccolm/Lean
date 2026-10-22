import Dubon2026.SourceOriginalExteriorArcIncidence

/-! DUB-17/18 -> original Abel-Jacobi -> lifting planar shared-side chains.
Every specified side through the value of a point in an actual carrier
has an actual arc through that point mapping onto the entire side.
Regularity of j is derived in the local families, not added as a premise.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_arc_through (i : A.Index) {P : Place ℂ (modularFunctionFieldOver N ℂ)}
    (hP : P ∈ (A.cell i).carrier) {Z : Set ℂ} (hsh : A.Shares (A.regionOf i) Z)
    (hv : originalPlaceEval N ℂ P (jOver N ℂ) ∈ Z) :
    ∃ a : Fin (A.cell i).R.N, P ∈ (A.cell i).arc a ∧ LiesOver (A.arcPlaces ⟨i, a⟩) Z := by
  rcases i with (⟨p, i⟩ | ⟨b, v⟩) | v
  · obtain ⟨_, k, rfl⟩ := hsh
    exact (A.G.ordinary p.1 p.2).arc_through i k hP hv
  · obtain ⟨_, k, rfl⟩ := hsh
    exact (A.G.branch (A.G.branchSquare b) b (A.G.branch_cap b)).arc_through
      (A.branch_region_center (A.G.branchSquare b) b (A.G.branch_cap b)) v k hP hv
  · obtain ⟨k, rfl⟩ := hsh
    exact A.poles.arc_through v k hP hv

theorem shares_pairArc (a : A.Arc) {Z : Set ℂ} (hZ : LiesOver (A.arcPlaces a) Z) :
    A.Shares (A.regionOf (A.pairArc a).1) Z := by
  obtain ⟨Z', hsh, hover⟩ := (A.arc_side (A.pairArc a)).1
  rw [A.pairArc_places a] at hover
  exact (hZ.eq hover).symm ▸ hsh

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
