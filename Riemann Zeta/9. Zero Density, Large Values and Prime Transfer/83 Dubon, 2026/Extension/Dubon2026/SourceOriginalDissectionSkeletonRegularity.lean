import Dubon2026.SourceOriginalCellDissectionInteriors
import Dubon2026.SourceOriginalDissectionEdgeCancellation

/-! DUB-17/18 -> raw reciprocity -> the weighted residue-jump formula.
The actual source assignment of poles to cell interiors makes the entire
dissection skeleton pole-free. Thus regularity off the finite pole set supplies
the boundary regularity used by edge cancellation and arc integration.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.interior_of_pole_mem_carrier (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hinter : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    (C : 𝒟.ιC) {v : Place ℂ F} (hv : v ∈ S) (hC : v ∈ (𝒟.cell C).carrier) :
    v ∈ (𝒟.cell C).interior' := by
  obtain ⟨B, hB⟩ := hinter v hv
  have he := 𝒟.eq_of_interior_mem_carrier hB hC
  subst B
  exact hB

theorem CellDissection.pole_not_mem_skeleton (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hinter : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    {v : Place ℂ F} (hv : v ∈ S) : v ∉ 𝒟.skeleton := by
  intro hskel
  obtain ⟨⟨C, k⟩, w, ⟨s, _, rfl⟩, rfl⟩ := mem_iUnion.mp hskel
  have hC : (𝒟.cell C).bdry s ∈ (𝒟.cell C).carrier :=
    ⟨(𝒟.cell C).R.loop s, (𝒟.cell C).R.loop_mem_K s, rfl⟩
  exact (𝒟.cell C).bdry_not_mem_interior s (𝒟.interior_of_pole_mem_carrier S hinter C hv hC)

theorem CellDissection.regular_on_skeleton (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hinter : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) :
    ∀ v ∈ 𝒟.skeleton, 0 ≤ v.ordDifferential θ := by
  intro v hv
  exact hθ v fun hS => 𝒟.pole_not_mem_skeleton S hinter hS hv

end
end Dubon2026.SourceFunctionField.CellGeometry
