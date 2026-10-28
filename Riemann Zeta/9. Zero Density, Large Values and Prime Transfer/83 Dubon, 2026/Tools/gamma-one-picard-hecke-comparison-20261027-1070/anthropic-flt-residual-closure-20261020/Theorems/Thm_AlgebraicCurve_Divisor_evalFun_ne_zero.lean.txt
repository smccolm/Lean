import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_ne_zero

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} {D : Divisor K F} (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f D ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_ne_zero.solution
