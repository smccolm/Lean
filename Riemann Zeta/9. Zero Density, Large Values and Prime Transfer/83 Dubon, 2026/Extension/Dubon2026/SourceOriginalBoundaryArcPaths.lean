import Dubon2026.SourceOriginalConstructedCycleSystem
import Dubon2026.SourceOriginalCellBoundaryIntegrability

/-! DUB-17/18 -> original Abel-Jacobi -> analytic realization of integer cycles.
Parameterize the actual analytic arcs and retain their actual original-place
endpoints. These paths will be consumed by the edge-integral and tree-walk
formulas; path-integral identities remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

/-- Affine parameter of the original closed boundary arc. -/
noncomputable def arcParam (R : RadialRegion) (k : Fin R.N) (t : ℝ) : ℝ :=
  R.φs k.castSucc + t * (R.φs k.succ - R.φs k.castSucc)

theorem arcParam_mem (R : RadialRegion) (k : Fin R.N) (t : unitInterval) :
    arcParam R k t ∈ R.arcIcc k := by
  have hab := R.hmono (Fin.castSucc_lt_succ (i := k))
  obtain ⟨ht0, ht1⟩ := t.2
  simp only [arcParam, RadialRegion.arcIcc, mem_Icc]
  constructor <;> nlinarith

theorem arcParam_mem_Ioo (R : RadialRegion) (k : Fin R.N) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    arcParam R k t ∈ Ioo (R.φs k.castSucc) (R.φs k.succ) := by
  have hab := R.hmono (Fin.castSucc_lt_succ (i := k))
  simp only [arcParam, mem_Ioo]
  constructor <;> nlinarith [ht.1, ht.2]

theorem hasDerivAt_arcParam (R : RadialRegion) (k : Fin R.N) (t : ℝ) :
    HasDerivAt (arcParam R k) (R.φs k.succ - R.φs k.castSucc) t := by
  unfold arcParam
  simpa using ((hasDerivAt_id t).mul_const (R.φs k.succ - R.φs k.castSucc)).const_add
    (R.φs k.castSucc)

/-- The actual original-place path following one analytic boundary arc. -/
noncomputable def arcPath (C : Cell N) (k : Fin C.R.N) :
    Path (C.bdry (C.R.φs k.castSucc)) (C.bdry (C.R.φs k.succ)) where
  toFun t := C.bdry (arcParam C.R k t)
  continuous_toFun := by
    refine C.continuous_bdry.comp ?_
    unfold arcParam
    fun_prop
  source' := by simp [arcParam]
  target' := by simp [arcParam]

theorem arcPath_mem_arc (C : Cell N) (k : Fin C.R.N) (t : unitInterval) :
    arcPath C k t ∈ C.arc k :=
  ⟨_, ⟨_, arcParam_mem C.R k t, rfl⟩, rfl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
