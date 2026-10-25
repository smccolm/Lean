import Dubon2026.SourceRadialCellBoundaryCoordinates
import Dubon2026.SourceRadialPolygonCorners

/-! DUB-17/18 -> cover period generation -> polygon jump formula.
These are the literal primitive readings and constant-jump relation on the
actual radial dissection. Their existence and signed integral identities are
proved by the actual cover consumer; these definitions assert no existence. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
open Set RadialCellDissection
variable {X : Type*} [TopologicalSpace X] {κ : Type*}

/-- The actual primitive difference on every point of each positively oriented arc. -/
def IsJump (D : RadialCellDissection X) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ) : Prop :=
  ∀ i e, ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
    Ψ i (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) -
      Ψ i (D.arcOf (e, false)).1
        ((D.cell (D.arcOf (e, false)).1).ζ ((D.cell (D.arcOf (e, true)).1).bdry s)) = J e i

/-- Primitive values at an actual original place in a specified cell chart. -/
noncomputable def gvec (D : RadialCellDissection X) (Ψ : κ → D.ιC → ℂ → ℂ)
    (y : X) (C : D.ιC) : κ → ℂ := fun i => Ψ i C ((D.cell C).ζ y)

/-- Primitive values at the starting point of an actual oriented arc. -/
noncomputable def Avec (D : RadialCellDissection X) (Ψ : κ → D.ιC → ℂ → ℂ) (q : D.ιE × Bool) :
    κ → ℂ := fun i => Ψ i (D.arcOf q).1
      ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc))

/-- Primitive values at the final point of an actual oriented arc. -/
noncomputable def Bvec (D : RadialCellDissection X) (Ψ : κ → D.ιC → ℂ → ℂ) (q : D.ιE × Bool) :
    κ → ℂ := fun i => Ψ i (D.arcOf q).1
      ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ))

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
