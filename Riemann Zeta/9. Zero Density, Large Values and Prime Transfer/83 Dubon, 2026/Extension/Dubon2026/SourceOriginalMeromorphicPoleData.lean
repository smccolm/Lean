import Dubon2026.SourceOriginalCellDissectionInteriors
import Dubon2026.SourceOriginalCellResidues
import Dubon2026.SourceOriginalCellPrimitives

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Subtract the actual simple-pole residue term in each marked original cell.
The original coefficient expansion makes the remainder analytic on a common
open neighborhood; the already proved radial primitive theorem integrates it.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
All original coordinate, simple-pole and primitive calculus is reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- Literal original simple-pole residue value used by the source cell formulas. -/
def res (v : Place ℂ F) (θ : Ω[F⁄ℂ]) : ℂ :=
  originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ)

/-- The vector of residues of the possible single pole in a cell. -/
def ρ (𝒟 : CellDissection N) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (C : 𝒟.ιC) : R → ℂ := by
  classical
  exact ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).interior'), fun r => res v (θ r)

/-- The already constructed separation and exact centered-pole clauses. -/
structure PolePos (𝒟 : CellDissection N) (S : Finset (Place ℂ F)) : Prop where
  hd2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton
  hd5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q

variable {𝒟 : CellDissection N} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])

theorem PolePos.center {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (hS : PolePos 𝒟 S) {v : Place ℂ F} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).carrier) : v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨C', hC', hq⟩ := hS.hd5 v hv
  obtain rfl := 𝒟.eq_of_interior_mem_carrier hC' hvC
  exact ⟨hC', hq⟩

theorem ρ_eq_of_mem {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (θ : R → Ω[F⁄ℂ]) (hS : PolePos 𝒟 S) {v : Place ℂ F} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).interior') : ρ 𝒟 S θ C = fun r => res v (θ r) := by
  classical
  unfold ρ
  rw [Finset.sum_eq_single v]
  · intro v' hv' hne
    simp only [Finset.mem_filter] at hv'
    exact absurd (hS.hd2 C ⟨Cell.interior_subset_carrier _ hv'.2, hv'.1⟩
      ⟨Cell.interior_subset_carrier _ hvC, hv⟩) hne
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨hv, hvC⟩) h

theorem ρ_eq_zero {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (θ : R → Ω[F⁄ℂ]) {C : 𝒟.ιC} (h : ∀ v ∈ S, v ∉ (𝒟.cell C).interior') : ρ 𝒟 S θ C = 0 := by
  classical
  unfold ρ
  rw [Finset.filter_false_of_mem h, Finset.sum_empty]


end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
