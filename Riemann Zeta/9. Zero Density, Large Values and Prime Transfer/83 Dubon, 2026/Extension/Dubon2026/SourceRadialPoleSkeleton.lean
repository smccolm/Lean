import Dubon2026.SourceRadialCellInteriors
import Dubon2026.SourceRadialDissectionArcPaths

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse ->
weighted residue reciprocity. Adapt only the radial-cell consumers of the
existing boundary and interval-sum proofs. The constructed cover dissection
supplies the pole centers and carrier separation; no contour identity is assumed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped Real
variable {X : Type*} [TopologicalSpace X]

theorem RadialCellDissection.interior_of_pole_mem_carrier (𝒟 : RadialCellDissection X)
    (S : Finset (X))
    (hinter : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    (C : 𝒟.ιC) {v : X} (hv : v ∈ S) (hC : v ∈ (𝒟.cell C).carrier) :
    v ∈ (𝒟.cell C).interior' := by
  obtain ⟨B, hB⟩ := hinter v hv
  have he := 𝒟.eq_of_interior_mem_carrier hB hC
  subst B
  exact hB

theorem RadialCellDissection.pole_not_mem_skeleton (𝒟 : RadialCellDissection X)
    (S : Finset (X))
    (hinter : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior')
    {v : X} (hv : v ∈ S) : v ∉ 𝒟.skeleton := by
  intro hskel
  obtain ⟨⟨C, k⟩, w, ⟨s, _, rfl⟩, rfl⟩ := mem_iUnion.mp hskel
  have hC : (𝒟.cell C).bdry s ∈ (𝒟.cell C).carrier :=
    ⟨(𝒟.cell C).R.loop s, (𝒟.cell C).R.loop_mem_K s, rfl⟩
  exact (𝒟.cell C).bdry_not_mem_interior s (𝒟.interior_of_pole_mem_carrier S hinter C hv hC)

theorem RadialCellDissection.bdry_mem_skeleton (D : RadialCellDissection X)
    (C : D.ιC) (k : Fin (D.cell C).R.N) {s : ℝ} (hs : s ∈ (D.cell C).R.arcIcc k) :
    (D.cell C).bdry s ∈ D.skeleton :=
  mem_iUnion.2 ⟨⟨C, k⟩, _, ⟨s, hs, rfl⟩, rfl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
