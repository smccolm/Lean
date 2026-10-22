import Dubon2026.SourceOriginalDissectionOfPairing
import Mathlib.Data.Set.Card

/-! DUB-17/18 -> raw reciprocity -> Euler and vertex clauses of the dissection.
The actual arc/edge-sign equivalence gives the edge count directly. Literal
endpoint vertices give the vertex count and incidence. Consequently the source
paired-family Euler count transfers to the constructed actual dissection.
The geometric paired family and its Euler count remain to be constructed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N} (P : CellPairing cell)
local notation "F" => modularFunctionFieldOver N ℂ

theorem vertex_incident (v : Vertex (cell := cell)) :
    ∃ e : P.Edge, (P.ends e).1 = v ∨ (P.ends e).2 = v := by
  obtain ⟨v, ⟨⟨a, b⟩, rfl⟩⟩ := v
  refine ⟨(P.side a).1, ?_⟩
  have h := P.arc_endpoints a
  cases b <;> cases ho : (P.side a).2
  · right
    apply Subtype.ext
    simpa only [ho, Bool.false_eq_true, if_false] using h.1.symm
  · left
    apply Subtype.ext
    simpa only [ho, if_true] using h.1.symm
  · left
    apply Subtype.ext
    simpa only [ho, Bool.false_eq_true, if_false] using h.2.symm
  · right
    apply Subtype.ext
    simpa only [ho, if_true] using h.2.symm

variable [Fintype ι]

theorem two_mul_card_edges : 2 * Fintype.card P.Edge = ∑ C : ι, (cell C).R.N := by
  have he := Fintype.card_congr P.sideEquiv
  rw [Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool] at he
  simpa only [Fintype.card_fin, mul_comm] using he.symm

theorem card_vertices : Fintype.card (Vertex (cell := cell)) =
    (Set.range (fun p : (Σ C : ι, Fin (cell C).R.N) × Bool => endpoint p.1 p.2)).ncard :=
  Set.fintypeCard_eq_ncard _

theorem dissection_euler
    (hcover : ∀ x : Place ℂ F, ∃ C, x ∈ (cell C).carrier)
    (hinter : ∀ C C' (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
      Relation.ReflTransGen (fun A B : ι => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        P.pair ⟨A, k⟩ = ⟨B, k'⟩ ∧ x ∈ (cell A).arc k) C C')
    (hEuler : 2 * ((Set.range (fun p : (Σ C : ι, Fin (cell C).R.N) × Bool =>
        endpoint p.1 p.2)).ncard : ℤ) - (∑ C : ι, ((cell C).R.N : ℤ)) +
        2 * (Fintype.card ι : ℤ) =
          2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ))) :
    let D := P.toDissection hcover hinter
    (Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
      2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) := by
  change (Fintype.card (Vertex (cell := cell)) : ℤ) - (Fintype.card P.Edge : ℤ) +
    (Fintype.card ι : ℤ) = _
  have he : (2 : ℤ) * (Fintype.card P.Edge : ℤ) = ∑ C : ι, ((cell C).R.N : ℤ) := by
    exact_mod_cast P.two_mul_card_edges
  rw [← card_vertices (cell := cell)] at hEuler
  omega

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
