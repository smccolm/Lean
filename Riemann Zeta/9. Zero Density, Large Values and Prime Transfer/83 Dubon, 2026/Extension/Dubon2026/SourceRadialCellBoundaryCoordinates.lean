import Dubon2026.SourceRadialDissectionArcPaths

/-! DUB-17/18 -> cover reciprocity -> actual boundary coefficients.
The radial boundary stays in the actual cell coordinate source and has its
prescribed coordinate value. These identities serve the arc chain rule. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem RadialCell.bdry_coordinates (C : RadialCell X) (s : ℝ) :
    C.bdry s ∈ C.ζ.source ∧ C.ζ (C.bdry s) = C.R.loop s :=
  ⟨C.ζ.map_target (C.hKt (C.R.loop_mem_K s)), C.ζ.right_inv (C.hKt (C.R.loop_mem_K s))⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
