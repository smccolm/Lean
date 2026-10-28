import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_ne_zero

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} {D : Divisor K F} (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f D ≠ 0 := by
  rw [Divisor.evalFun_def]
  exact Finset.prod_ne_zero_iff.mpr fun v hv => zpow_ne_zero _ (h v hv)
