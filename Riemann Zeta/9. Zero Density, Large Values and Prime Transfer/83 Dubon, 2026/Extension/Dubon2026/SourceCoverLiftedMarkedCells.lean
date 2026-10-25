import Dubon2026.SourceCoverLiftedCellIncidence
import Dubon2026.SourceRadialCellDissection
import Dubon2026.SourceOriginalCellCenters

/-! DUB-17/18 -> third-kind reciprocity -> centered, separated cover poles.
Projection is injective on each actual lifted cell carrier. Thus the already
proved base centering and separation transfer to the actual marked cover
points, including distinct cover points with the same base image. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set

/-- The actual open radial cell interior. -/
def RadialCell.interior' {X : Type*} [TopologicalSpace X] (C : RadialCell X) : Set X := C.ζ.symm '' C.R.Kint

end Dubon2026.SourceFunctionField.CellGeometry
namespace Dubon2026.SourceFunctionField.SheetCover
open Set CellGeometry

theorem lifted_carrier_injOn {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (p : X → B) (e : OpenPartialHomeomorph B ℂ) (ζ : OpenPartialHomeomorph X ℂ)
    (R : RadialRegion) (hK : R.K ⊆ e.target)
    (hp : ∀ z ∈ R.K, p (ζ.symm z) = e.symm z) : Set.InjOn p (ζ.symm '' R.K) := by
  rintro x ⟨z, hz, rfl⟩ y ⟨u, hu, rfl⟩ h
  rw [hp z hz, hp u hu] at h
  exact congrArg ζ.symm (e.symm.injOn (hK hz) (hK hu) h)

theorem lifted_cell_center {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (p : X → B) (e : OpenPartialHomeomorph B ℂ) (ζ : OpenPartialHomeomorph X ℂ)
    (R : RadialRegion) (hK : R.K ⊆ e.target) (hζK : R.K ⊆ ζ.target)
    (hp : ∀ z ∈ R.K, p (ζ.symm z) = e.symm z)
    {w : X} (hw : w ∈ ζ.symm '' R.K) (hc : e (p w) = R.q) :
    w ∈ ζ.symm '' R.Kint ∧ ζ w = R.q := by
  obtain ⟨z, hz, rfl⟩ := hw
  rw [hp z hz, e.right_inv (hK hz)] at hc
  subst z
  refine ⟨⟨R.q, ?_, rfl⟩, ζ.right_inv (hζK hz)⟩
  exact R.center_mem_Kint

theorem lifted_marked_separation {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (p : X → B) (e : OpenPartialHomeomorph B ℂ) (ζ : OpenPartialHomeomorph X ℂ)
    (R : RadialRegion) (hK : R.K ⊆ e.target)
    (hp : ∀ z ∈ R.K, p (ζ.symm z) = e.symm z) (S : Set X)
    (hs : (e.symm '' R.K ∩ p '' S).Subsingleton) : (ζ.symm '' R.K ∩ S).Subsingleton := by
  intro x hx y hy
  apply lifted_carrier_injOn p e ζ R hK hp hx.1 hy.1
  exact hs ⟨lifted_carrier_projects p e ζ R hp hx.1, x, hx.2, rfl⟩
    ⟨lifted_carrier_projects p e ζ R hp hy.1, y, hy.2, rfl⟩

end Dubon2026.SourceFunctionField.SheetCover
