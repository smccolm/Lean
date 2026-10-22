import Dubon2026.SourceOriginalRegionalCarrierUniqueness

/-! DUB-17/18 -> original Abel-Jacobi -> curve intersection chains.
Carrier coverage places every regular j value in its exact planar region.
At a nonregular j place, every containing cell belongs to the exterior;
regional carrier uniqueness then handles that intersection immediately.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

/-- Exact planar containment, including the closed exterior. -/
abbrev Contains := StarProperty.Contains A.planarData

/-- Planar adjacency through a prescribed base point. -/
abbrev Adj := StarProperty.Adj A.planarData

theorem contains_of_mem_carrier (i : A.Index) {P : Place ℂ F}
    (hx : jOver N ℂ ∈ P.toValuationSubring) (hP : P ∈ (A.cell i).carrier) :
    A.Contains (A.regionOf i) (originalPlaceEval N ℂ P (jOver N ℂ)) := by
  rcases i with (⟨p, i⟩ | ⟨b, v⟩) | v
  · have h := ((A.G.ordinary p.1 p.2).coverage P).mpr ⟨i, hP⟩
    exact ⟨A.regionOf_mem_window (.inl (.inl (p, i))) rfl, h.2⟩
  · have h := ((A.G.branch (A.G.branchSquare b) b (A.G.branch_cap b)).coverage P).mpr ⟨v, hP⟩
    exact ⟨A.regionOf_mem_window (.inl (.inr ⟨b, v⟩)) rfl, h.2⟩
  · have h := (A.poles.coverage P).mpr ⟨v, hP⟩
    exact (h.resolve_left (not_not_intro hx)).2

theorem region_eq_none_of_not_regular (i : A.Index) {P : Place ℂ F}
    (hx : jOver N ℂ ∉ P.toValuationSubring) (hP : P ∈ (A.cell i).carrier) :
    A.regionOf i = none := by
  rcases i with (⟨p, i⟩ | ⟨b, v⟩) | v
  · exact False.elim (hx (((A.G.ordinary p.1 p.2).coverage P).mpr ⟨i, hP⟩).1)
  · exact False.elim (hx (((A.G.branch (A.G.branchSquare b) b (A.G.branch_cap b)).coverage P).mpr ⟨v, hP⟩).1)
  · rfl

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
