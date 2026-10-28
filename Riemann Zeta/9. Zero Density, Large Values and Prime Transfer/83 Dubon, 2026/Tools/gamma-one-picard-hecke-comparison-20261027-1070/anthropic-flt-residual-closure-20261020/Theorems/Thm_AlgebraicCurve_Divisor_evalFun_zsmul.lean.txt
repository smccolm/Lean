import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_zsmul

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_zsmul {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul.solution
