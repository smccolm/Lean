import Dubon2026.SourceOriginalCellPairingVertices
import Dubon2026.SourceOriginalCellCoverConnectivity

/-! DUB-17/18 -> raw reciprocity -> actual cell-dissection construction.
The actual paired cell cover and its pointwise intersection chains construct
the source dissection. Vertices and edges are constructed, side bijectivity
and reversal are proved, and global adjacency follows from original curve
connectedness. No transport to numbered cell indices is needed.
Construction of the geometric paired cover itself remains upstream.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N} (P : CellPairing cell)
local notation "F" => modularFunctionFieldOver N ℂ

theorem same_edge_of_pair {a b : Σ C : ι, Fin (cell C).R.N} (h : P.pair a = b) :
    (P.side a).1 = (P.side b).1 := by
  have he := congrArg Prod.fst (P.side_pair a)
  rw [h] at he
  exact he.symm

/-- The genuine source dissection built from an actual paired geometric cover. -/
def toDissection [Fintype ι]
    (hcover : ∀ x : Place ℂ F, ∃ C, x ∈ (cell C).carrier)
    (hinter : ∀ C C' (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
      Relation.ReflTransGen (fun A B : ι => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        P.pair ⟨A, k⟩ = ⟨B, k'⟩ ∧ x ∈ (cell A).arc k) C C') : CellDissection N := by
  classical
  have hi : ∀ C C' (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
      Relation.ReflTransGen (fun A B : ι => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (P.side ⟨A, k⟩).1 = (P.side ⟨B, k'⟩).1 ∧ x ∈ (cell A).arc k) C C' := by
    intro C C' x hC hC'
    apply Relation.ReflTransGen.mono _ (hinter C C' x hC hC')
    rintro A B ⟨k, k', hp, hx⟩
    exact ⟨k, k', P.same_edge_of_pair hp, hx⟩
  exact {
    ιC := ι
    ιE := P.Edge
    ιV := Vertex (cell := cell)
    cell := cell
    side := fun C k => P.side ⟨C, k⟩
    side_bij := P.side_bijective
    ends := P.ends
    vert := Subtype.val
    arc_ends := fun C k => P.arc_endpoints ⟨C, k⟩
    arc_rev := fun C k C' k' => P.reversed_side_arcs ⟨C, k⟩ ⟨C', k'⟩
    cover := eq_univ_of_forall fun x => mem_iUnion.mpr (hcover x)
    inter := hi
    conn := cell_cover_reachable cell _ hcover (fun C C' x hC hC' =>
      Relation.ReflTransGen.mono (fun A B ⟨k, k', he, _⟩ => ⟨k, k', he⟩) (hi C C' x hC hC')) }

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
