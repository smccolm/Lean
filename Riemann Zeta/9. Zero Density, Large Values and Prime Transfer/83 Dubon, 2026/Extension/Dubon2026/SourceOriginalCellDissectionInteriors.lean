import Dubon2026.SourceOriginalCellDissection
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> raw reciprocity -> centered-contour applicability.
The source intersection-chain condition makes a cell interior disjoint from
every other cell carrier. Thus the source's chosen centered cell for each pole
is the only carrier containing it. This derives the center condition required
by the shorter centered residue route for every relevant cell.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.interior_subset_carrier (C : Cell N) : C.interior' ⊆ C.carrier := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  exact (show ‖z - C.R.q‖ < C.R.r (Complex.arg (z - C.R.q)) from hz).le

theorem Cell.arc_subset_carrier (C : Cell N) (k : Fin C.R.N) : C.arc k ⊆ C.carrier := by
  rintro x ⟨z, ⟨s, _, rfl⟩, rfl⟩
  exact ⟨_, C.R.loop_mem_K s, rfl⟩

theorem Cell.bdry_not_mem_interior (C : Cell N) (s : ℝ) : C.bdry s ∉ C.interior' := by
  rintro ⟨w, hw, he⟩
  have hwt : w ∈ C.ζ.target := C.hKt
    (show ‖w - C.R.q‖ ≤ C.R.r (Complex.arg (w - C.R.q)) from hw.le)
  have hlt := C.hKt (C.R.loop_mem_K s)
  have hwe : w = C.R.loop s := C.ζ.symm.injOn hwt hlt he
  rw [hwe] at hw
  change ‖C.R.loop s - C.R.q‖ < C.R.r (Complex.arg (C.R.loop s - C.R.q)) at hw
  rw [C.R.norm_loop_sub_center, C.R.radius_arg_loop] at hw
  exact lt_irrefl _ hw

theorem CellDissection.eq_of_interior_mem_carrier (𝒟 : CellDissection N)
    {C C' : 𝒟.ιC} {x : Place ℂ F} (hC : x ∈ (𝒟.cell C).interior')
    (hC' : x ∈ (𝒟.cell C').carrier) : C = C' := by
  obtain h0 | ⟨B, ⟨k, _, _, hk⟩, _⟩ :=
    (𝒟.inter C C' x ((𝒟.cell C).interior_subset_carrier hC) hC').cases_head
  · exact h0
  · obtain ⟨z, ⟨s, _, rfl⟩, rfl⟩ := hk
    exact ((𝒟.cell C).bdry_not_mem_interior s hC).elim

theorem CellDissection.pole_center_on_carrier (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hcent : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧
      (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (C : 𝒟.ιC) (v : Place ℂ F) (hvS : v ∈ S) (hvC : v ∈ (𝒟.cell C).carrier) :
    v ∈ (𝒟.cell C).ζ.source ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨D, hvD, hcenter⟩ := hcent v hvS
  have he := 𝒟.eq_of_interior_mem_carrier hvD hvC
  subst D
  refine ⟨?_, hcenter⟩
  obtain ⟨z, hz, rfl⟩ := hvC
  exact (𝒟.cell C).ζ.map_target ((𝒟.cell C).hKt hz)

end
end Dubon2026.SourceFunctionField.CellGeometry
