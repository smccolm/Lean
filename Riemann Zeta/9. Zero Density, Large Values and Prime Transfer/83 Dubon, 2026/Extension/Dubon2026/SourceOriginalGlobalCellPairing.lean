import Dubon2026.SourceOriginalExteriorArcReversal
import Dubon2026.SourceOriginalCellPairing

/-! DUB-17/18 -> original Abel-Jacobi -> the actual paired cell dissection.
The constructed global cover has a genuine CellPairing: involution,
opposite orientations and the complete C1 original-place reversal identity.
No global pairing or smooth-transport premise remains. Intersection chains
and the curve Euler identity are still required for the full dissection.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

namespace OriginalGlobalCellCover
variable {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem exists_arc_reversal (a b : A.Arc) (hreg : A.regionOf b.1 ≠ A.regionOf a.1)
    (hplaces : A.arcPlaces b = A.arcPlaces a) (ha : A.orientArc a = true) :
    ∃ ψ : ℝ → ℝ, A.ArcReversalClause a b ψ := by
  rcases A.exists_arc_presentation a with ⟨p, k, m, c, h⟩ | ⟨k, m, c, h⟩ <;>
    rcases A.exists_arc_presentation b with ⟨p', k', m', c', h'⟩ | ⟨k', m', c', h'⟩
  · exact A.exists_square_square_reversal a b hreg hplaces h h'
      ((A.orientArc_of_square h).symm.trans ha)
  · exact A.exists_square_exterior_reversal a b hplaces h h'
      ((A.orientArc_of_square h).symm.trans ha)
  · exact A.exists_exterior_square_reversal a b hplaces h h'
      ((A.orientArc_of_exterior h).symm.trans ha)
  · exact False.elim (hreg (h'.region.trans h.region.symm))

/-- The fully constructed pairing of the actual global original-cell family. -/
def pairing : CellPairing A.cell where
  pair := A.pairArc
  involutive := A.pairArc_involutive
  orient := A.orientArc
  orient_pair := A.orientArc_pairArc
  reverse := by
    intro a b hab ha
    subst b
    exact A.exists_arc_reversal a (A.pairArc a) (A.pairArc_region_ne a) (A.pairArc_places a) ha

end OriginalGlobalCellCover

theorem exists_original_centered_paired_cover (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (S : Finset (Place ℂ (modularFunctionFieldOver N ℂ))) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked),
      Nonempty (CellPairing A.cell) ∧
      (∀ P, ∃ i : A.Index, P ∈ (A.cell i).carrier) ∧
      (∀ P ∈ insert P₀ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ))), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ (modularFunctionFieldOver N ℂ)))).Subsingleton) := by
  obtain ⟨Marked, A, hcover, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  exact ⟨Marked, A, ⟨A.pairing⟩, hcover, hcent, hsep⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
