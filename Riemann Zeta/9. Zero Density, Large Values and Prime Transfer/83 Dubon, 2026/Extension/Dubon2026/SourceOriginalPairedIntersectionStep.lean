import Dubon2026.SourceOriginalGlobalArcIncidence

/-! DUB-17/18 -> original Abel-Jacobi -> actual curve intersection chains.
Lift one planar shared-side step to the actual partner arc through the
original place. Exact two-region incidence identifies the destination region.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

/-- A step across an actual paired boundary arc through the specified place. -/
def PairStep (P : Place ℂ F) (i j : A.Index) : Prop :=
  ∃ (a : Fin (A.cell i).R.N) (b : Fin (A.cell j).R.N),
    A.pairArc ⟨i, a⟩ = ⟨j, b⟩ ∧ P ∈ (A.cell i).arc a

theorem exists_intersection_step (i : A.Index) {P : Place ℂ F} (hP : P ∈ (A.cell i).carrier)
    {ρ : Option (ℤ × ℤ)} (hadj : A.Adj (originalPlaceEval N ℂ P (jOver N ℂ)) (A.regionOf i) ρ) :
    ∃ j : A.Index, A.regionOf j = ρ ∧ P ∈ (A.cell j).carrier ∧
      Relation.ReflTransGen (A.PairStep P) i j := by
  obtain ⟨Z, hsh, hsh', hv⟩ := hadj
  by_cases hρ : ρ = A.regionOf i
  · exact ⟨i, hρ.symm, hP, .refl⟩
  obtain ⟨a, ha, hover⟩ := A.exists_arc_through i hP hsh hv
  obtain ⟨ρ₁, _, _, hu⟩ := StarProperty.two_regions A.planarData _ Z hsh
  have hY := A.shares_pairArc ⟨i, a⟩ hover
  have hρ₁ : ρ = ρ₁ := (hu ρ hsh').resolve_left hρ
  have hYρ : A.regionOf (A.pairArc ⟨i, a⟩).1 = ρ₁ :=
    (hu _ hY).resolve_left (A.pairArc_region_ne ⟨i, a⟩)
  refine ⟨(A.pairArc ⟨i, a⟩).1, hYρ.trans hρ₁.symm, ?_, Relation.ReflTransGen.single ?_⟩
  · have hPa : P ∈ A.arcPlaces (A.pairArc ⟨i, a⟩) := by
      rw [A.pairArc_places]
      exact ha
    exact (A.cell (A.pairArc ⟨i, a⟩).1).arc_subset_carrier _ hPa
  · exact ⟨a, (A.pairArc ⟨i, a⟩).2, rfl, ha⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
