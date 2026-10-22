import Dubon2026.SourceOriginalDissectionGenusCount

/-! DUB-17/18 -> original Abel-Jacobi -> exact dissection vertex count.
Extract only the vertex clauses already proved for the actual planar grid.
Their finite set, exact cardinality, endpoint realization and grid-line
location are used to identify all original vertices as unramified j fibers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The proved vertex data of the actual planar grid used in the original dissection. -/
structure BaseVertexData where
  /-- The finite set of planar endpoints. -/
  points : Finset ℂ
  /-- Its exact grid cardinality. -/
  card : points.card = ((A.G.D.hi - A.G.D.lo + 1).toNat + 1) ^ 2 +
    (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 + (A.G.D.hi - A.G.D.lo + 1).toNat
  /-- Every square endpoint belongs to the set. -/
  square : ∀ p ∈ Icc A.G.D.lo A.G.D.hi ×ˢ Icc A.G.D.lo A.G.D.hi,
    ∀ i : Fin ((A.G.region p).N + 1), (A.G.region p).loop ((A.G.region p).φs i) ∈ points
  /-- Every outer endpoint belongs to the set. -/
  exterior : ∀ i : Fin (A.W.R.N + 1), A.W.R.loop (A.W.R.φs i) ∈ points
  /-- Every point is an endpoint of an actual square side. -/
  realized : ∀ v ∈ points, ∃ p ∈ Icc A.G.D.lo A.G.D.hi ×ˢ Icc A.G.D.lo A.G.D.hi,
    ∃ k : Fin (A.G.region p).N,
      v = (A.G.region p).loop ((A.G.region p).φs k.castSucc) ∨
      v = (A.G.region p).loop ((A.G.region p).φs k.succ)
  /-- All vertices lie on grid lines, hence away from the marked branch values. -/
  grid_line : ∀ v ∈ points, ∃ j : ℤ, v.re - A.G.D.o = j * A.G.D.h

theorem nonempty_baseVertexData : Nonempty A.BaseVertexData := by
  obtain ⟨_, _, B, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, hs, he, hr, hl⟩ := A.planar_geometry
  refine ⟨⟨B, ?_, hs, he, hr, hl⟩⟩
  simpa only [pow_two] using hc

/-- The selected vertex data, with existence proved from the constructed grid. -/
def baseVertexData : A.BaseVertexData := Classical.choice A.nonempty_baseVertexData

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
