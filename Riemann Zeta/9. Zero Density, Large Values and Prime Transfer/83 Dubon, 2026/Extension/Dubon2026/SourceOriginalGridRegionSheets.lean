import Dubon2026.SourceOriginalOrdinarySquareCells
import Dubon2026.SourceCellFiniteGridGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> coherent finite grid cells.
Use one prescribed radial rectangle for every sheet over a square. Its
boundary subdivision is therefore shared with the adjoining branch cells.
Actual convex lifts supply the sheets and exact original-place coverage.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]

theorem exists_original_square_cells_for_region {o h : ℝ} (hh : 0 < h) (j k : ℤ)
    (R : RadialRegion) (hRK : R.K = SquareGrid.gridSquare o h j k)
    (h0 : (0 : ℂ) ∉ SquareGrid.gridSquare o h j k)
    (h1728 : (1728 : ℂ) ∉ SquareGrid.gridSquare o h j k) :
    ∃ (V : Set ℂ) (C : Fin (SourceLevelProjective.dedekindPsi N) → Cell N),
      IsOpen V ∧ R.K ⊆ V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
      (∀ i, (C i).R = R) ∧
      IsOriginalSheetFamily (jOver N ℂ) V (fun i => (C i).ζ) ∧
      (∀ P : Place ℂ (modularFunctionFieldOver N ℂ),
        (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.K) ↔
        ∃ i, P ∈ (C i).carrier) ∧
      Pairwise (fun i i' => Disjoint (C i).carrier (C i').carrier) := by
  obtain ⟨V, A, hV, hQV, hV0, hV1728, hA⟩ := exists_original_j_ordinary_square_sheets N hh j k h0 h1728
  have hRV : R.K ⊆ V := hRK ▸ hQV
  let C : Fin (SourceLevelProjective.dedekindPsi N) → Cell N := fun i =>
    { toAnalyticCoord := A i, R := R, hKt := by rw [hA.1 i]; exact hRV }
  have hc (i) (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
      P ∈ (C i).carrier ↔ P ∈ (A i).ζ.source ∧ (A i).ζ P ∈ R.K :=
    (C i).mem_carrier_iff_coordinate P
  refine ⟨V, C, hV, hRV, hV0, hV1728, fun _ => rfl, hA, ?_, ?_⟩
  · intro P
    constructor
    · rintro ⟨hreg, hP⟩
      obtain ⟨i, hi⟩ := hA.2.2.2 P hreg (hRV hP)
      refine ⟨i, (hc i P).mpr ⟨hi, ?_⟩⟩
      rwa [(hA.2.1 i P hi).2]
    · rintro ⟨i, hi⟩
      obtain ⟨hsrc, hval⟩ := (hc i P).mp hi
      obtain ⟨hreg, he⟩ := hA.2.1 i P hsrc
      rw [he] at hval
      exact ⟨hreg, hval⟩
  · intro i i' hii'
    exact (hA.2.2.1 hii').mono (fun P hP => ((hc i P).mp hP).1)
      (fun P hP => ((hc i' P).mp hP).1)

end
end Dubon2026.SourceFunctionField.CellGeometry
