import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_add

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_add {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D * Divisor.evalFun f E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_add.solution
