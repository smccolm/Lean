import Dubon2026.SourceOriginalBaseVertexFibers

/-! DUB-17/18 -> original Abel-Jacobi -> exact vertex count.
Every actual original arc endpoint evaluates to one of the constructed
planar vertices. Its regular j value and endpoint formula come from the
proved square or exterior presentation, including the exterior reversal.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} {A : OriginalGlobalCellCover N Marked}
local notation "F" => modularFunctionFieldOver N ℂ

theorem endpoint_over_baseVertex (V : A.BaseVertexData) (a : A.Arc) (b : Bool) :
    jOver N ℂ ∈ (CellPairing.endpoint a b).toValuationSubring ∧
      originalPlaceEval N ℂ (CellPairing.endpoint a b) (jOver N ℂ) ∈ V.points := by
  have hl : (A.cell a.1).R.φs a.2.castSucc ∈ (A.cell a.1).R.arcIcc a.2 :=
    left_mem_Icc.mpr ((A.cell a.1).R.hmono Fin.castSucc_lt_succ).le
  have hr : (A.cell a.1).R.φs a.2.succ ∈ (A.cell a.1).R.arcIcc a.2 :=
    right_mem_Icc.mpr ((A.cell a.1).R.hmono Fin.castSucc_lt_succ).le
  rcases A.exists_arc_presentation a with ⟨p, k, m, c, h⟩ | ⟨k, m, c, h⟩
  · have hp := A.regionOf_mem_window a.1 h.region
    cases b
    · change jOver N ℂ ∈ ((A.cell a.1).bdry _).toValuationSubring ∧ _
      refine ⟨(h.lies.1 _ ((A.cell a.1).bdry_mem_arc hl)).1, ?_⟩
      change originalPlaceEval N ℂ ((A.cell a.1).bdry _) (jOver N ℂ) ∈ V.points
      rw [h.read _ hl, h.start]
      exact V.square p hp k.castSucc
    · change jOver N ℂ ∈ ((A.cell a.1).bdry _).toValuationSubring ∧ _
      refine ⟨(h.lies.1 _ ((A.cell a.1).bdry_mem_arc hr)).1, ?_⟩
      change originalPlaceEval N ℂ ((A.cell a.1).bdry _) (jOver N ℂ) ∈ V.points
      rw [h.read _ hr, h.stop]
      exact V.square p hp k.succ
  · cases b
    · change jOver N ℂ ∈ ((A.cell a.1).bdry _).toValuationSubring ∧ _
      refine ⟨(h.lies.1 _ ((A.cell a.1).bdry_mem_arc hl)).1, ?_⟩
      change originalPlaceEval N ℂ ((A.cell a.1).bdry _) (jOver N ℂ) ∈ V.points
      rw [h.read _ hl, h.start]
      exact V.exterior k.succ
    · change jOver N ℂ ∈ ((A.cell a.1).bdry _).toValuationSubring ∧ _
      refine ⟨(h.lies.1 _ ((A.cell a.1).bdry_mem_arc hr)).1, ?_⟩
      change originalPlaceEval N ℂ ((A.cell a.1).bdry _) (jOver N ℂ) ∈ V.points
      rw [h.read _ hr, h.stop]
      exact V.exterior k.castSucc

theorem endpoint_mem_fiberUnion (V : A.BaseVertexData) (a : A.Arc) (b : Bool) :
    CellPairing.endpoint a b ∈ V.fiberUnion := by
  classical
  obtain ⟨hr, hv⟩ := endpoint_over_baseVertex V a b
  apply Finset.mem_biUnion.mpr
  refine ⟨originalPlaceEval N ℂ (CellPairing.endpoint a b) (jOver N ℂ), hv, ?_⟩
  have hne : jOver N ℂ - algebraMap ℂ F
      (originalPlaceEval N ℂ (CellPairing.endpoint a b) (jOver N ℂ)) ≠ 0 := by
    intro he
    exact transcendental_jOver N ℂ (sub_eq_zero.mp he ▸ isAlgebraic_algebraMap _)
  exact (OriginalChart.mem_originalPositiveFiber_iff_regular_eval N hne _).mpr ⟨hr, rfl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
