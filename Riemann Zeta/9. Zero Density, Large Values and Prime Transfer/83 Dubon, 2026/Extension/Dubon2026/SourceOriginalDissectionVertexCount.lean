import Dubon2026.SourceOriginalDissectionVertexSurjectivity

/-! DUB-17/18 -> original Abel-Jacobi -> the vertex term of the curve Euler identity.
The literal set of original boundary endpoints equals the disjoint union of
unramified j fibers over the constructed planar vertices. Consequently its
cardinality is exactly the original j degree times the proved planar count.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} {A : OriginalGlobalCellCover N Marked}

theorem vertex_set_eq_fiberUnion (V : A.BaseVertexData) :
    CellPairing.Vertex (cell := A.cell) = (V.fiberUnion : Set (Place ℂ (modularFunctionFieldOver N ℂ))) := by
  ext P
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact endpoint_mem_fiberUnion V a b
  · exact mem_vertex_of_mem_fiberUnion V

theorem card_vertices_eq_degree_mul_base (V : A.BaseVertexData) :
    Fintype.card (CellPairing.Vertex (cell := A.cell)) = V.points.card * SourceLevelProjective.dedekindPsi N := by
  have hc : Fintype.card (CellPairing.Vertex (cell := A.cell)) = V.fiberUnion.card := by
    rw [Set.fintypeCard_eq_ncard, vertex_set_eq_fiberUnion V, Set.ncard_coe_finset]
  exact hc.trans V.fiberUnion_card

theorem dissection_vertex_count (A : OriginalGlobalCellCover N Marked) :
    Fintype.card A.dissection.ιV =
      (((A.G.D.hi - A.G.D.lo + 1).toNat + 1) ^ 2 + (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 +
        (A.G.D.hi - A.G.D.lo + 1).toNat) * SourceLevelProjective.dedekindPsi N := by
  change Fintype.card (CellPairing.Vertex (cell := A.cell)) = _
  rw [card_vertices_eq_degree_mul_base A.baseVertexData, A.baseVertexData.card]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
