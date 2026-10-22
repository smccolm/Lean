import Dubon2026.SourceOriginalDissectionEulerIdentity

/-! DUB-17/18 -> original Abel-Jacobi -> complete source dissection input.
For arbitrary marked original places, construct the actual analytic cell
dissection with its Euler formula, marked interiors, exact centers,
separation, injective vertices and incidence. No geometric or numerical
dissection hypothesis remains. Geometric loop generation and the ensuing
raw reciprocity theorem remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_euler_cell_dissection (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ D : CellDissection N,
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : D.ιC, v ∈ (D.cell C).interior') ∧
      (∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ F) : ℤ)) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : D.ιC,
        v ∈ (D.cell C).interior' ∧ (D.cell C).ζ v = (D.cell C).R.q) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) := by
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  refine ⟨A.dissection, ?_, hsep, A.dissection_euler_identity, ?_,
    CellPairing.vertex_injective, A.pairing.vertex_incident⟩
  · intro v hv
    obtain ⟨i, hi, _⟩ := hcent v hv
    exact ⟨i, hi⟩
  · intro v hv
    exact hcent v (Or.inr hv)

end
end Dubon2026.SourceFunctionField.CellGeometry
