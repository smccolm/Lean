import Dubon2026.SourceRadialCellDissection
import Dubon2026.SourceOriginalBoundaryArcPaths

/-! DUB-17/18 -> actual cover Abel converse -> geometric loop realization.
Use the native affine arc parameter, with unchanged endpoint and range proofs,
to parameterize the actual radial-cell boundaries. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set
open OriginalEdgePaths (arcParam arcParam_mem)
variable {X : Type*} [TopologicalSpace X]

/-- The actual arc with a prescribed oriented edge label. -/
noncomputable def RadialCellDissection.arcOf (D : RadialCellDissection X) (q : D.ιE × Bool) :
    Σ C : D.ιC, Fin (D.cell C).R.N := Function.surjInv D.side_bij.surjective q

/-- The union of the actual boundary arcs. -/
def RadialCellDissection.skeleton (D : RadialCellDissection X) : Set X :=
  ⋃ p : (Σ C : D.ιC, Fin (D.cell C).R.N), (D.cell p.1).arc p.2

theorem RadialCellDissection.side_arcOf (D : RadialCellDissection X) (q : D.ιE × Bool) :
    D.side (D.arcOf q).1 (D.arcOf q).2 = q :=
  Function.surjInv_eq D.side_bij.surjective q

theorem RadialCell.continuous_bdry (C : RadialCell X) : Continuous C.bdry :=
  continuous_iff_continuousAt.mpr fun s =>
    (C.ζ.continuousAt_symm (C.hKt (C.R.loop_mem_K s))).comp C.R.continuous_loop.continuousAt

/-- The continuous path along one actual radial boundary arc. -/
noncomputable def RadialCell.arcPath (C : RadialCell X) (k : Fin C.R.N) :
    Path (C.bdry (C.R.φs k.castSucc)) (C.bdry (C.R.φs k.succ)) where
  toFun t := C.bdry (arcParam C.R k t)
  continuous_toFun := by
    refine C.continuous_bdry.comp ?_
    unfold arcParam
    fun_prop
  source' := by simp [arcParam]
  target' := by simp [arcParam]

theorem RadialCell.arcPath_mem_arc (C : RadialCell X) (k : Fin C.R.N) (t : unitInterval) :
    C.arcPath k t ∈ C.arc k :=
  ⟨_, ⟨_, arcParam_mem C.R k t, rfl⟩, rfl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
