import Dubon2026.SourceOriginalDissectionPolygonWord

/-! DUB-17/18 -> original Abel-Jacobi -> raw matrix reciprocity.
The actual grid has at least two vertices, so the constructed primal tree
provides an edge outside the dual tree. Thus the source polygon word is
constructed without a dual-tree or nonempty-complement hypothesis, retaining
the 2g remaining edges and the original marked-point geometry.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees DissectionPolygon
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem OriginalGlobalCellCover.two_le_vertex_count {Marked : Finset ℂ}
    (A : OriginalGlobalCellCover N Marked) : 2 ≤ Fintype.card A.dissection.ιV := by
  rw [A.dissection_vertex_count]
  have hn : 2 ≤ (A.G.D.hi - A.G.D.lo + 1).toNat := by
    have := A.G.D.window_nontrivial
    omega
  have hb : 2 ≤ ((A.G.D.hi - A.G.D.lo + 1).toNat + 1) ^ 2 +
      (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 + (A.G.D.hi - A.G.D.lo + 1).toNat := by omega
  have hp : 1 ≤ SourceLevelProjective.dedekindPsi N := SourceLevelProjective.dedekindPsi_pos (NeZero.ne N)
  calc
    2 ≤ (((A.G.D.hi - A.G.D.lo + 1).toNat + 1) ^ 2 +
      (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 + (A.G.D.hi - A.G.D.lo + 1).toNat) * 1 := by
        simpa only [Nat.mul_one] using hb
    _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem OriginalGlobalCellCover.tree_cotree_polygon {Marked : Finset ℂ}
    (A : OriginalGlobalCellCover N Marked) :
    ∃ T Ts : Finset A.dissection.ιE,
      IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
      Disjoint T Ts ∧
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
      IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      PolygonWordConclusion A.dissection Ts := by
  obtain ⟨T, Ts, ht, hts, hd, hc, hw⟩ := A.tree_cotree
  haveI : Nonempty A.dissection.ιV := Fintype.card_pos_iff.mp (by have := A.two_le_vertex_count; omega)
  have hcard := spanningTree_card (hdΓ A.dissection) (tlΓ A.dissection) T ht
  have hTne : T.Nonempty := Finset.card_pos.mp (by have := A.two_le_vertex_count; omega)
  obtain ⟨e, he⟩ := hTne
  refine ⟨T, Ts, ht, hts, hd, hc, hw, ?_⟩
  exact exists_polygon_word A.dissection CellPairing.vertex_injective Ts hts
    ⟨e, fun h => Finset.disjoint_left.mp hd he h⟩

theorem exists_original_centered_polygon_word (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      ∃ T Ts : Finset A.dissection.ιE,
        IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
        IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
        Disjoint T Ts ∧
        (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
        IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T ∧
        PolygonWordConclusion A.dissection Ts := by
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  exact ⟨Marked, A, hcent, hsep, A.tree_cotree_polygon⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
