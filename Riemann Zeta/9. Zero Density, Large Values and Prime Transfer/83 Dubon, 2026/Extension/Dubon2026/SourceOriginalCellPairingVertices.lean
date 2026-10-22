import Dubon2026.SourceOriginalCellPairingSides

/-! DUB-17/18 -> raw reciprocity -> actual dissection vertices and endpoints.
Vertices are the literal finite range of original arc endpoints. Reversal of
the actual paired arcs proves their endpoint orientation law. Vertex labels
therefore remain injective original places, with no quotient or proxy curve.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {ι : Type*} {cell : ι → Cell N} (P : CellPairing cell)

/-- The original-place endpoint of an actual oriented cell arc. -/
def endpoint (a : Σ C : ι, Fin (cell C).R.N) (b : Bool) :
    Place ℂ (modularFunctionFieldOver N ℂ) :=
  if b then (cell a.1).bdry ((cell a.1).R.φs a.2.succ)
  else (cell a.1).bdry ((cell a.1).R.φs a.2.castSucc)

/-- The actual finite set of original-place vertices. -/
def Vertex := Set.range (fun p : (Σ C : ι, Fin (cell C).R.N) × Bool => endpoint p.1 p.2)

instance [Fintype ι] : Fintype (Vertex (cell := cell)) := (Set.finite_range _).fintype

/-- An actual arc endpoint, regarded as a vertex. -/
def endpointVertex (a : Σ C : ι, Fin (cell C).R.N) (b : Bool) : Vertex (cell := cell) :=
  ⟨endpoint a b, ⟨(a, b), rfl⟩⟩

theorem endpoint_pair {a b : Σ C : ι, Fin (cell C).R.N}
    (hp : P.pair a = b) (ha : P.orient a = true) :
    endpoint b false = endpoint a true ∧ endpoint b true = endpoint a false := by
  obtain ⟨ψ, _, _, hstart, hend, hpoint⟩ := P.reverse a b hp ha
  have hl : (cell b.1).R.φs b.2.castSucc ∈ (cell b.1).R.arcIcc b.2 :=
    left_mem_Icc.mpr ((cell b.1).R.hmono Fin.castSucc_lt_succ).le
  have hr : (cell b.1).R.φs b.2.succ ∈ (cell b.1).R.arcIcc b.2 :=
    right_mem_Icc.mpr ((cell b.1).R.hmono Fin.castSucc_lt_succ).le
  constructor
  · change (cell b.1).bdry _ = (cell a.1).bdry _
    rw [hpoint _ hl, hstart]
  · change (cell b.1).bdry _ = (cell a.1).bdry _
    rw [hpoint _ hr, hend]

/-- Oriented endpoints of a geometric edge, chosen from its positive arc. -/
def ends (e : P.Edge) : Vertex (cell := cell) × Vertex (cell := cell) :=
  (endpointVertex e.1 false, endpointVertex e.1 true)

theorem arc_endpoints (a : Σ C : ι, Fin (cell C).R.N) :
    endpoint a false =
        (if (P.side a).2 then (P.ends (P.side a).1).1 else (P.ends (P.side a).1).2).1 ∧
      endpoint a true =
        (if (P.side a).2 then (P.ends (P.side a).1).2 else (P.ends (P.side a).1).1).1 := by
  unfold side
  split
  · exact ⟨rfl, rfl⟩
  · next h =>
      exact P.endpoint_pair (P.involutive a) (P.orient_pair_of_not h)

theorem vertex_injective : Function.Injective (Subtype.val : Vertex (cell := cell) → _) :=
  Subtype.val_injective

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
