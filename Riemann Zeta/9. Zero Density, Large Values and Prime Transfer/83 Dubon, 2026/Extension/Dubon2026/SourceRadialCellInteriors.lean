import Dubon2026.SourceCoverLiftedMarkedCells
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse ->
weighted residue reciprocity. Adapt only the radial-cell consumers of the
existing boundary and interval-sum proofs. The constructed cover dissection
supplies the pole centers and carrier separation; no contour identity is assumed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped Real
variable {X : Type*} [TopologicalSpace X]

theorem RadialCell.interior_subset_carrier (C : RadialCell X) : C.interior' ⊆ C.carrier := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  exact (show ‖z - C.R.q‖ < C.R.r (Complex.arg (z - C.R.q)) from hz).le

theorem RadialCell.bdry_not_mem_interior (C : RadialCell X) (s : ℝ) : C.bdry s ∉ C.interior' := by
  rintro ⟨w, hw, he⟩
  have hwt : w ∈ C.ζ.target := C.hKt
    (show ‖w - C.R.q‖ ≤ C.R.r (Complex.arg (w - C.R.q)) from hw.le)
  have hlt := C.hKt (C.R.loop_mem_K s)
  have hwe : w = C.R.loop s := C.ζ.symm.injOn hwt hlt he
  rw [hwe] at hw
  change ‖C.R.loop s - C.R.q‖ < C.R.r (Complex.arg (C.R.loop s - C.R.q)) at hw
  rw [C.R.norm_loop_sub_center, C.R.radius_arg_loop] at hw
  exact lt_irrefl _ hw

theorem RadialCellDissection.eq_of_interior_mem_carrier (𝒟 : RadialCellDissection X)
    {C C' : 𝒟.ιC} {x : X} (hC : x ∈ (𝒟.cell C).interior')
    (hC' : x ∈ (𝒟.cell C').carrier) : C = C' := by
  obtain h0 | ⟨B, ⟨k, _, _, hk⟩, _⟩ :=
    (𝒟.inter C C' x ((𝒟.cell C).interior_subset_carrier hC) hC').cases_head
  · exact h0
  · obtain ⟨z, ⟨s, _, rfl⟩, rfl⟩ := hk
    exact ((𝒟.cell C).bdry_not_mem_interior s hC).elim

theorem RadialCellDissection.pole_center_on_carrier (𝒟 : RadialCellDissection X)
    (S : Finset (X))
    (hcent : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧
      (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (C : 𝒟.ιC) (v : X) (hvS : v ∈ S) (hvC : v ∈ (𝒟.cell C).carrier) :
    v ∈ (𝒟.cell C).ζ.source ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨D, hvD, hcenter⟩ := hcent v hvS
  have he := 𝒟.eq_of_interior_mem_carrier hvD hvC
  subst D
  refine ⟨?_, hcenter⟩
  obtain ⟨z, hz, rfl⟩ := hvC
  exact (𝒟.cell C).ζ.map_target ((𝒟.cell C).hKt hz)

end
end Dubon2026.SourceFunctionField.CellGeometry
