import Dubon2026.SourceRadialCellInteriors

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
weighted residue reciprocity. Reuse the centered planar residue theorem,
finite interval partition and exact constructed primitive jumps. These prove
the global identity with the actual algebraic residues and cell coordinates. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

open scoped Classical in
theorem RadialCellDissection.sum_pole_carriers (D : RadialCellDissection X)
    (S : Finset (X)) (c : X → D.ιC)
    (hc : ∀ v ∈ S, v ∈ (D.cell (c v)).interior') (f : D.ιC → X → ℂ) :
    (∑ C : D.ιC, ∑ v ∈ S.filter (fun v => v ∈ (D.cell C).carrier), f C v) =
      ∑ v ∈ S, f (c v) v := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hiff : ∀ C : D.ιC, v ∈ (D.cell C).carrier ↔ C = c v := by
    intro C
    constructor
    · intro hC
      exact (D.eq_of_interior_mem_carrier (hc v hv) hC).symm
    · rintro rfl
      exact (D.cell (c v)).interior_subset_carrier (hc v hv)
  simp_rw [hiff]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end
end Dubon2026.SourceFunctionField.CellGeometry
