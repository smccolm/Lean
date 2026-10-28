import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_mul

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_mul.solution
