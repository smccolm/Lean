import Dubon2026.SourceRadialCellInteriors

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual marked dissection already supplies separated centered poles.
Adapt the existing finite residue-vector and pole-exclusion geometry to its
radial cells. The later actual coefficient consumer supplies literal residues;
no arbitrary residue data will remain on that consumer. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Filter
open scoped Topology
variable {X R : Type*} [TopologicalSpace X]

/-- The already constructed separation and exact centered-pole clauses. -/
structure PolePos (𝒟 : RadialCellDissection X) (S : Finset (X)) : Prop where
  hd2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (X))).Subsingleton
  hd5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q

/-- The finite residue vector of the possible pole in a radial cell. -/
def ρ (𝒟 : RadialCellDissection X) (S : Finset X) (residue : X → R → ℂ)
    (C : 𝒟.ιC) : R → ℂ := by
  classical
  exact ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).interior'), residue v

variable {𝒟 : RadialCellDissection X} {S : Finset (X)} (residue : X → R → ℂ)

theorem PolePos.center {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (hS : PolePos 𝒟 S) {v : X} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).carrier) : v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨C', hC', hq⟩ := hS.hd5 v hv
  obtain rfl := 𝒟.eq_of_interior_mem_carrier hC' hvC
  exact ⟨hC', hq⟩

theorem ρ_eq_of_mem {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (residue : X → R → ℂ) (hS : PolePos 𝒟 S) {v : X} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).interior') : ρ 𝒟 S residue C = fun r => residue v r := by
  classical
  unfold ρ
  rw [Finset.sum_eq_single v]
  · intro v' hv' hne
    simp only [Finset.mem_filter] at hv'
    exact absurd (hS.hd2 C ⟨RadialCell.interior_subset_carrier _ hv'.2, hv'.1⟩
      ⟨RadialCell.interior_subset_carrier _ hvC, hv⟩) hne
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨hv, hvC⟩) h

theorem ρ_eq_zero {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (residue : X → R → ℂ) {C : 𝒟.ιC} (h : ∀ v ∈ S, v ∉ (𝒟.cell C).interior') : ρ 𝒟 S residue C = 0 := by
  classical
  unfold ρ
  rw [Finset.filter_false_of_mem h, Finset.sum_empty]


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
