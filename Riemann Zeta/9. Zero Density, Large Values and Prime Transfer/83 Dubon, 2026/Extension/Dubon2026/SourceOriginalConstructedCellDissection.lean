import Dubon2026.SourceOriginalCellIntersectionChains
import Dubon2026.SourceOriginalDissectionFromPairedFamily

/-! DUB-17/18 -> original Abel-Jacobi -> actual analytic cell dissection.
The constructed cover, pairing and intersection chains now supply every
field of CellDissection, including global adjacency and actual vertices.
Marked interiors, exact centers, separation and vertex incidence are retained.
The additional source Euler identity is not a field of CellDissection and
remains a separate unresolved obligation before raw geometric reciprocity.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

namespace OriginalGlobalCellCover
variable {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The actual cell dissection, constructed without cover, pairing or intersection hypotheses. -/
def dissection : CellDissection N :=
  A.pairing.toDissection A.covers (fun i j _ hi hj => A.intersection_chain i j hi hj)

end OriginalGlobalCellCover

theorem exists_original_centered_dissection (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (S : Finset (Place ℂ (modularFunctionFieldOver N ℂ))) :
    ∃ D : CellDissection N,
      (∀ P ∈ insert P₀ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ))), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ)))).Subsingleton) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) := by
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  exact ⟨A.dissection, hcent, hsep, CellPairing.vertex_injective, A.pairing.vertex_incident⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
