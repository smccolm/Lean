import Dubon2026.SourceCellPlanarGridGeometry
import Dubon2026.SourceOriginalPlanarGridData

/-! DUB-17/18 -> original Abel-Jacobi -> paired cell dissection.
The actual j-cover supplies the complete planar pairing geometry: unique
neighboring regions, opposite orientations, C1 boundary transports, chains
through every shared point, and exact vertex counts and realizations.
Lifting these conclusions to the original curve and the curve Euler formula
remain separate obligations; neither is assumed or claimed here.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem OriginalGlobalCellCover.planar_geometry {Marked : Finset ℂ}
    (A : OriginalGlobalCellCover N Marked) : GridGeometry.Geometry A.planarData :=
  GridGeometry.exists_grid_geometry A.planarData

theorem exists_original_centered_planar_cover (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (S : Finset (Place ℂ (modularFunctionFieldOver N ℂ))) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked),
      (∀ P : Place ℂ (modularFunctionFieldOver N ℂ), ∃ i : A.Index, P ∈ (A.cell i).carrier) ∧
      (∀ P ∈ insert P₀ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ))), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index,
        ((A.cell i).carrier ∩ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ)))).Subsingleton) ∧
      GridGeometry.Geometry A.planarData := by
  obtain ⟨Marked, A, hcover, hcenters, hsep⟩ := exists_original_centered_global_cover N P₀ S
  exact ⟨Marked, A, hcover, hcenters, hsep, A.planar_geometry⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
