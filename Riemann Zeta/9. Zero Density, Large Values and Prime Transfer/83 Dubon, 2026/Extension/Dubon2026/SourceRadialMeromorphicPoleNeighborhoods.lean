import Dubon2026.SourceRadialMeromorphicPoleData

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

variable {𝒟 : RadialCellDissection X} {S : Finset (X)}

/-- Coordinate images of poles lying outside the specified cell interior. -/
def badPts {𝒟 : RadialCellDissection X} {S : Finset (X)} (C : 𝒟.ιC) : Set ℂ :=
  {w | w ∈ (𝒟.cell C).ζ.target ∧ (𝒟.cell C).ζ.symm w ∈ S ∧ (𝒟.cell C).ζ.symm w ∉ (𝒟.cell C).interior'}

theorem badPts_finite {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (C : 𝒟.ιC) : (badPts (S := S) C).Finite := by
  refine Set.Finite.of_finite_image (f := (𝒟.cell C).ζ.symm) ?_ ?_
  · exact (S.finite_toSet).subset (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.1)
  · exact (𝒟.cell C).ζ.symm.injOn.mono fun w hw => hw.1

/-- The coordinate target with all other marked poles excluded. -/
def goodSet {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (C : 𝒟.ιC) : Set ℂ := (𝒟.cell C).ζ.target \ badPts (S := S) C

theorem isOpen_goodSet {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (C : 𝒟.ιC) : IsOpen (goodSet (S := S) C) :=
  (𝒟.cell C).ζ.open_target.sdiff (badPts_finite C).isClosed

theorem K_subset_goodSet {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (hS : PolePos 𝒟 S) (C : 𝒟.ιC) :
    (𝒟.cell C).R.K ⊆ goodSet (S := S) C := by
  intro w hw
  refine ⟨(𝒟.cell C).hKt hw, fun hb => hb.2.2 ?_⟩
  exact (hS.center hb.2.1 ⟨w, hw, rfl⟩).1


theorem goodSet_pole {𝒟 : RadialCellDissection X} {S : Finset (X)}
    (hS : PolePos 𝒟 S) {C : 𝒟.ιC} {w : ℂ} (hw : w ∈ goodSet (S := S) C)
    (hwS : (𝒟.cell C).ζ.symm w ∈ S) : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' ∧ w = (𝒟.cell C).R.q := by
  have hint : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' := by
    by_contra h
    exact hw.2 ⟨hw.1, hwS, h⟩
  refine ⟨hint, ?_⟩
  have := (hS.center hwS (RadialCell.interior_subset_carrier _ hint)).2
  rwa [(𝒟.cell C).ζ.right_inv hw.1] at this


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
