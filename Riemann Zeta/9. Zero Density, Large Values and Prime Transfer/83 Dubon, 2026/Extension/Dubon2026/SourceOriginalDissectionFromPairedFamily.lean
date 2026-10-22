import Dubon2026.SourceOriginalPairedCellCounts

/-! DUB-17/18 -> raw reciprocity -> source cell-dissection existence.
The genuine source paired geometric family, its intersection chains and its
Euler count give the complete required dissection, including original-place
vertices, vertex incidence and all marked-point/centering properties. The
family-to-dissection conversion is proved; constructing that geometric family
and its count remains open. No existence premise is silently discharged.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {ι : Type} [Fintype ι] {cell : ι → Cell N} (P : CellPairing cell)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_dissection_from_paired_family
    (hcover : ∀ x : Place ℂ F, ∃ C, x ∈ (cell C).carrier)
    (hinter : ∀ C C' (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
      Relation.ReflTransGen (fun A B : ι => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        P.pair ⟨A, k⟩ = ⟨B, k'⟩ ∧ x ∈ (cell A).arc k) C C')
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    (hmarked : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C, v ∈ (cell C).interior')
    (hsep : ∀ C, ((cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ (S : Set (Place ℂ F)), ∃ C, v ∈ (cell C).interior' ∧ (cell C).ζ v = (cell C).R.q)
    (hEuler : 2 * ((Set.range (fun p : (Σ C : ι, Fin (cell C).R.N) × Bool =>
        endpoint p.1 p.2)).ncard : ℤ) - (∑ C : ι, ((cell C).R.N : ℤ)) +
        2 * (Fintype.card ι : ℤ) =
          2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ))) :
    ∃ D : CellDissection N,
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : D.ιC, v ∈ (D.cell C).interior') ∧
      (∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : D.ιC,
        v ∈ (D.cell C).interior' ∧ (D.cell C).ζ v = (D.cell C).R.q) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) := by
  exact ⟨P.toDissection hcover hinter, hmarked, hsep,
    P.dissection_euler hcover hinter hEuler, hcent, vertex_injective, P.vertex_incident⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
