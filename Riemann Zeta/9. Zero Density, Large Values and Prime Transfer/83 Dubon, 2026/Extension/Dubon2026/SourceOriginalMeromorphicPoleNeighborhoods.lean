import Dubon2026.SourceOriginalMeromorphicPoleData

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

variable {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}

/-- Coordinate images of poles lying outside the specified cell interior. -/
def badPts {𝒟 : CellDissection N} {S : Finset (Place ℂ F)} (C : 𝒟.ιC) : Set ℂ :=
  {w | w ∈ (𝒟.cell C).ζ.target ∧ (𝒟.cell C).ζ.symm w ∈ S ∧ (𝒟.cell C).ζ.symm w ∉ (𝒟.cell C).interior'}

theorem badPts_finite {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (C : 𝒟.ιC) : (badPts (S := S) C).Finite := by
  refine Set.Finite.of_finite_image (f := (𝒟.cell C).ζ.symm) ?_ ?_
  · exact (S.finite_toSet).subset (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.1)
  · exact (𝒟.cell C).ζ.symm.injOn.mono fun w hw => hw.1

/-- The coordinate target with all other marked poles excluded. -/
def goodSet {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (C : 𝒟.ιC) : Set ℂ := (𝒟.cell C).ζ.target \ badPts (S := S) C

theorem isOpen_goodSet {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (C : 𝒟.ιC) : IsOpen (goodSet (S := S) C) :=
  (𝒟.cell C).ζ.open_target.sdiff (badPts_finite C).isClosed

theorem K_subset_goodSet {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (hS : PolePos 𝒟 S) (C : 𝒟.ιC) :
    (𝒟.cell C).R.K ⊆ goodSet (S := S) C := by
  intro w hw
  refine ⟨(𝒟.cell C).hKt hw, fun hb => hb.2.2 ?_⟩
  exact (hS.center hb.2.1 ⟨w, hw, rfl⟩).1


theorem goodSet_pole {𝒟 : CellDissection N} {S : Finset (Place ℂ F)}
    (hS : PolePos 𝒟 S) {C : 𝒟.ιC} {w : ℂ} (hw : w ∈ goodSet (S := S) C)
    (hwS : (𝒟.cell C).ζ.symm w ∈ S) : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' ∧ w = (𝒟.cell C).R.q := by
  have hint : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' := by
    by_contra h
    exact hw.2 ⟨hw.1, hwS, h⟩
  refine ⟨hint, ?_⟩
  have := (hS.center hwS (Cell.interior_subset_carrier _ hint)).2
  rwa [(𝒟.cell C).ζ.right_inv hw.1] at this


end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
