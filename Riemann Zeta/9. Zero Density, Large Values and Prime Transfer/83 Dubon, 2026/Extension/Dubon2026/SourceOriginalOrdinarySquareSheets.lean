import Dubon2026.SourceOriginalConvexJSheets
import Dubon2026.SourceCellGridSquares
import Mathlib.Analysis.Normed.Group.Pointwise

/-! DUB-17/18 -> original Abel-Jacobi -> ordinary analytic grid cells.
A compact convex set avoiding the branch values has a convex open collar.
Apply this to each literal ordinary closed grid square. The actual covering,
exact degree, analyticity, collar and complete fiber exhaustion are derived.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
open scoped Pointwise
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]

theorem exists_original_j_sheets_near_compact_convex {K : Set ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (h0 : (0 : ℂ) ∉ K) (h1728 : (1728 : ℂ) ∉ K) :
    ∃ (V : Set ℂ) (A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N),
      IsOpen V ∧ K ⊆ V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
        IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ) := by
  let U := ({0, 1728} : Set ℂ)ᶜ
  have hU : IsOpen U := ((finite_singleton (1728 : ℂ)).insert 0).isClosed.isOpen_compl
  have hKU : K ⊆ U := by
    intro z hz
    simp only [U, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => h0 (he ▸ hz), fun he => h1728 (he ▸ hz)⟩
  obtain ⟨δ, hδ, hs⟩ := hK.exists_thickening_subset_open hU hKU
  let V := thickening δ K
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have hVconv : Convex ℝ V := by
    change Convex ℝ (thickening δ K)
    rw [← add_ball_zero]
    exact hconv.add (convex_ball (0 : ℂ) δ)
  have hV0 : (0 : ℂ) ∉ V := fun hz => hs hz (mem_insert 0 {1728})
  have hV1728 : (1728 : ℂ) ∉ V := fun hz => hs hz (mem_insert_of_mem 0 (mem_singleton 1728))
  obtain ⟨A, hA⟩ := exists_original_j_analytic_sheets_on_convex N isOpen_thickening hVconv
    (hne.mono hKV) hV0 hV1728
  exact ⟨V, A, isOpen_thickening, hKV, hV0, hV1728, hA⟩

theorem exists_original_j_ordinary_square_sheets {o h : ℝ} (hh : 0 < h) (j k : ℤ)
    (h0 : (0 : ℂ) ∉ SquareGrid.gridSquare o h j k)
    (h1728 : (1728 : ℂ) ∉ SquareGrid.gridSquare o h j k) :
    ∃ (V : Set ℂ) (A : Fin (SourceLevelProjective.dedekindPsi N) → AnalyticCoord N),
      IsOpen V ∧ SquareGrid.gridSquare o h j k ⊆ V ∧ (0 : ℂ) ∉ V ∧ (1728 : ℂ) ∉ V ∧
        IsOriginalSheetFamily (jOver N ℂ) V (fun i => (A i).ζ) := by
  exact exists_original_j_sheets_near_compact_convex N (SquareGrid.isCompact_gridSquare o h j k)
    (SquareGrid.convex_gridSquare o h j k) ⟨_, SquareGrid.corner_mem hh j k⟩ h0 h1728

end
end Dubon2026.SourceFunctionField.CellGeometry
