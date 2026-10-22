import Dubon2026.SourceOriginalCellDissectionInteriors

/-! DUB-17/18 -> raw reciprocity -> the source global residue sum.
The source interior assignment identifies each pole's unique carrier. Native
finite-sum interchange therefore collapses the per-cell residue sum to the
literal single sum over poles with their assigned-cell primitive values.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

open scoped Classical in
theorem CellDissection.sum_pole_carriers (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F)) (c : Place ℂ F → 𝒟.ιC)
    (hc : ∀ v ∈ S, v ∈ (𝒟.cell (c v)).interior') (f : 𝒟.ιC → Place ℂ F → ℂ) :
    (∑ C : 𝒟.ιC, ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).carrier), f C v) =
      ∑ v ∈ S, f (c v) v := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hiff : ∀ C : 𝒟.ιC, v ∈ (𝒟.cell C).carrier ↔ C = c v := by
    intro C
    constructor
    · intro hC
      exact (𝒟.eq_of_interior_mem_carrier (hc v hv) hC).symm
    · rintro rfl
      exact (𝒟.cell (c v)).interior_subset_carrier (hc v hv)
  simp_rw [hiff]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end
end Dubon2026.SourceFunctionField.CellGeometry
