import Dubon2026.SourceOriginalBoundaryArcPaths
import Dubon2026.SourceOriginalPairedArcOverlap

/-! DUB-17/18 -> original Abel-Jacobi -> analytic realization of integer cycles.
Parameterize the actual analytic arcs and retain their actual original-place
endpoints. These paths will be consumed by the edge-integral and tree-walk
formulas; path-integral identities remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set CellDissection
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem vert_fst_eq (𝒟 : CellDissection N) (e : 𝒟.ιE) :
    𝒟.vert (𝒟.ends e).1 = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc) := by
  have h := (𝒟.arc_ends (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).1
  rw [CellDissection.side_arcOf] at h
  simp only [if_true] at h
  exact h.symm

theorem vert_snd_eq (𝒟 : CellDissection N) (e : 𝒟.ιE) :
    𝒟.vert (𝒟.ends e).2 = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ) := by
  have h := (𝒟.arc_ends (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).2
  rw [CellDissection.side_arcOf] at h
  simp only [if_true] at h
  exact h.symm

/-- The actual positive edge path with the dissection vertex endpoints. -/
noncomputable def edgePath (𝒟 : CellDissection N) (e : 𝒟.ιE) :
    Path (𝒟.vert (𝒟.ends e).1) (𝒟.vert (𝒟.ends e).2) :=
  (arcPath (𝒟.cell (arcOf 𝒟 (e, true)).1) (arcOf 𝒟 (e, true)).2).cast (vert_fst_eq 𝒟 e)
    (vert_snd_eq 𝒟 e)

theorem edgePath_mem_arc (𝒟 : CellDissection N) (e : 𝒟.ιE) (t : unitInterval) :
    edgePath 𝒟 e t ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).arc (arcOf 𝒟 (e, true)).2 :=
  arcPath_mem_arc _ _ t

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
