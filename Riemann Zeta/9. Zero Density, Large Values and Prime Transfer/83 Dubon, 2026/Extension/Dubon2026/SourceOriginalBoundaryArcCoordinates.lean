import Dubon2026.SourceCellReciprocalArcPresentation

/-! DUB-17/18 -> original Abel-Jacobi -> actual boundary parameter transports.
Every boundary point is in its original chart and has the prescribed radial
coordinate; an arc parameter places it on the actual original boundary arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.Cell
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (C : Cell N)

theorem bdry_source_and_coordinate (t : ℝ) :
    C.bdry t ∈ C.ζ.source ∧ C.ζ (C.bdry t) = C.R.loop t := by
  have ht := C.hKt (C.R.loop_mem_K t)
  exact ⟨C.ζ.map_target ht, C.ζ.right_inv ht⟩

theorem bdry_mem_arc {a : Fin C.R.N} {t : ℝ} (ht : t ∈ C.R.arcIcc a) :
    C.bdry t ∈ C.arc a :=
  ⟨C.R.loop t, ⟨t, ht, rfl⟩, rfl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.Cell
