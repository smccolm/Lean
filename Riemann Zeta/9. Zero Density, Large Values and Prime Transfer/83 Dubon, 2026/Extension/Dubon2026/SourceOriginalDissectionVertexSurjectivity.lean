import Dubon2026.SourceOriginalSquareCarrierExistence

/-! DUB-17/18 -> original Abel-Jacobi -> exact original vertex count.
Every original point over a planar endpoint is itself an actual arc endpoint.
Choose its cell over the realized square, then its arc over that side. The
proved affine endpoint formula and j-injectivity identify the original point.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} {A : OriginalGlobalCellCover N Marked}
local notation "F" => modularFunctionFieldOver N ℂ

theorem mem_vertex_of_mem_fiberUnion (V : A.BaseVertexData) {P : Place ℂ F}
    (hP : P ∈ V.fiberUnion) : P ∈ CellPairing.Vertex (cell := A.cell) := by
  classical
  obtain ⟨z, hz, hP⟩ := Finset.mem_biUnion.mp hP
  have hpos := (mem_originalPositiveFiber N (jOver N ℂ) z P).mp hP
  have hx := (original_sub_const_mem_iff N P (jOver N ℂ) z).mp (P.mem_of_ord_nonneg hpos.le)
  have hval := originalPlaceEval_eq_of_ord_sub_pos N ℂ P (jOver N ℂ) z hpos
  obtain ⟨p, hp, k, hend⟩ := V.realized z hz
  have hzarc : z ∈ (A.G.region p).arcSet k := by
    rcases hend with hl | hr
    · exact ⟨_, left_mem_Icc.mpr ((A.G.region p).hmono Fin.castSucc_lt_succ).le, hl.symm⟩
    · exact ⟨_, right_mem_Icc.mpr ((A.G.region p).hmono Fin.castSucc_lt_succ).le, hr.symm⟩
  have hvarc : originalPlaceEval N ℂ P (jOver N ℂ) ∈ (A.G.region p).arcSet k := hval.symm ▸ hzarc
  obtain ⟨i, hireg, hi⟩ := A.exists_cell_over_square hp hx ((A.G.region p).arcSet_subset_K k hvarc)
  have hsh : A.Shares (A.regionOf i) ((A.G.region p).arcSet k) := by
    rw [hireg]
    exact ⟨hp, k, rfl⟩
  obtain ⟨a, hPa, hover⟩ := A.exists_arc_through i hi hsh hvarc
  rcases A.exists_arc_presentation ⟨i, a⟩ with ⟨p', k', m, c, h⟩ | ⟨k', m, c, h⟩
  · have hpp : p' = p := Option.some.inj (h.region.symm.trans hireg)
    subst p'
    have hkk : k' = k := GridWindow.arcSet_injective _ (h.lies.eq hover)
    subst k'
    rcases hend with hl | hr
    · have ht : (A.cell i).R.φs a.castSucc ∈ (A.cell i).R.arcIcc a :=
        left_mem_Icc.mpr ((A.cell i).R.hmono Fin.castSucc_lt_succ).le
      have he : P = (A.cell i).bdry ((A.cell i).R.φs a.castSucc) := by
        apply (A.arc_side ⟨i, a⟩).2 hPa ((A.cell i).bdry_mem_arc ht)
        change originalPlaceEval N ℂ P (jOver N ℂ) = originalPlaceEval N ℂ ((A.cell i).bdry _) (jOver N ℂ)
        rw [hval, h.read _ ht, h.start]
        exact hl
      exact ⟨(⟨i, a⟩, false), he.symm⟩
    · have ht : (A.cell i).R.φs a.succ ∈ (A.cell i).R.arcIcc a :=
        right_mem_Icc.mpr ((A.cell i).R.hmono Fin.castSucc_lt_succ).le
      have he : P = (A.cell i).bdry ((A.cell i).R.φs a.succ) := by
        apply (A.arc_side ⟨i, a⟩).2 hPa ((A.cell i).bdry_mem_arc ht)
        change originalPlaceEval N ℂ P (jOver N ℂ) = originalPlaceEval N ℂ ((A.cell i).bdry _) (jOver N ℂ)
        rw [hval, h.read _ ht, h.stop]
        exact hr
      exact ⟨(⟨i, a⟩, true), he.symm⟩
  · exact False.elim (Option.some_ne_none p (hireg.symm.trans h.region))

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
