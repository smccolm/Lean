import Dubon2026.SourceOriginalDissectionArcCount

/-! DUB-17/18 -> original Abel-Jacobi -> the source Euler identity.
The actual original vertex, edge and cell counts yield the required genus
formula. This discharges the Euler premise of the earlier paired-family
converter for the dissection constructed from the original j map.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem dissection_euler_identity :
    (Fintype.card A.dissection.ιV : ℤ) - (Fintype.card A.dissection.ιE : ℤ) +
      (Fintype.card A.dissection.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) : ℤ) := by
  have he : (2 : ℤ) * (Fintype.card A.dissection.ιE : ℤ) =
      ∑ i : A.Index, ((A.cell i).R.N : ℤ) := by
    exact_mod_cast A.pairing.two_mul_card_edges
  rw [A.sum_cell_arcs] at he
  rw [A.dissection_vertex_count, A.dissection_cell_count]
  push_cast
  nlinarith

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
