import Dubon2026.SourceRadialDissectionEdgePaths

/-! DUB-17/18 -> cover reciprocity -> actual skeleton paths.
The positive edge paths and their endpoints lie in the actual skeleton;
concatenation retains this property. Integral identities remain separate. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
noncomputable section
open SourceCurve Set RadialCellDissection
variable {X : Type*} [TopologicalSpace X]

theorem edgePath_mem_skeleton (D : RadialCellDissection X) (e : D.ιE) (t : unitInterval) :
    edgePath D e t ∈ D.skeleton :=
  mem_iUnion.2 ⟨D.arcOf (e, true), edgePath_mem_arc D e t⟩

theorem vert_mem_skeleton (D : RadialCellDissection X) (e : D.ιE) :
    D.vert (D.ends e).1 ∈ D.skeleton ∧ D.vert (D.ends e).2 ∈ D.skeleton := by
  constructor
  · rw [← (edgePath D e).source]; exact edgePath_mem_skeleton D e 0
  · rw [← (edgePath D e).target]; exact edgePath_mem_skeleton D e 1

/-- Nonnegative differential order at every actual point of the dissection skeleton. -/

theorem mem_skeleton_trans (D : RadialCellDissection X) {P Q R : X}
    {γ : Path P Q} {δ : Path Q R}
    (hγ : ∀ t, γ t ∈ D.skeleton) (hδ : ∀ t, δ t ∈ D.skeleton) :
    ∀ t, (γ.trans δ) t ∈ D.skeleton := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · exact hδ _

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
