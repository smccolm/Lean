import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_single_sub_single

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_single_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single.solution
