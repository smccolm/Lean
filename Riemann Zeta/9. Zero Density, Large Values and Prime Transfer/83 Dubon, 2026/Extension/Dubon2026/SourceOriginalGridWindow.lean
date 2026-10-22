import Dubon2026.SourceOriginalGridCellCoverage
import Dubon2026.SourceCellWindowPerimeter

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite cell dissection.
The constructed original grid supplies every hypothesis of the exact outer
perimeter construction. Its unchanged interior contains the actual pole
scale, so the original pole cells apply to this same refined window.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (G : OriginalJFiniteGrid N Marked)

/-- The exact source perimeter data supplied by the constructed original grid. -/
def windowData : GridWindow.WinData where
  o := G.D.o
  hm := G.D.h
  hhm := G.D.mesh_pos
  jlo := G.D.lo
  jhi := G.D.hi
  klo := G.D.lo
  khi := G.D.hi
  hj := by have := G.D.window_nontrivial; omega
  hk := by have := G.D.window_nontrivial; omega
  cy := fun p => (G.D.center p).im
  hcy := fun p => (G.D.center_inside p).2
  hx₀ := by have := G.D.outer_lower; have := G.D.radius_one; linarith
  hx₁ := by have := G.D.outer_upper; have := G.D.radius_one; linarith
  hy₀ := by have := G.D.outer_lower; have := G.D.radius_one; linarith
  hy₁ := by have := G.D.outer_upper; have := G.D.radius_one; linarith
  hcy0 := fun k h0 h1 => G.D.center_right_zero (G.D.hi, k) rfl h0 h1

theorem window_K_eq (W : GridWindow.WinData.Win G.windowData) : W.R.K = G.window := W.K_eq

theorem window_contains_pole_scale (W : GridWindow.WinData.Win G.windowData) :
    Metric.closedBall 0 G.B ⊆ W.R.Kint := by
  intro z hz
  have hn : ‖z‖ ≤ G.B := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [W.Kint_eq]
  exact G.D.closedBall_inside hn

theorem exists_original_refined_window :
    ∃ W : GridWindow.WinData.Win G.windowData, Nonempty (OriginalPoleRegionFamily N W.R) := by
  obtain ⟨W⟩ := GridWindow.WinData.exists_win G.windowData
  exact ⟨W, ⟨G.pole W.R W.q_eq W.two_le_N (G.window_contains_pole_scale W)⟩⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
