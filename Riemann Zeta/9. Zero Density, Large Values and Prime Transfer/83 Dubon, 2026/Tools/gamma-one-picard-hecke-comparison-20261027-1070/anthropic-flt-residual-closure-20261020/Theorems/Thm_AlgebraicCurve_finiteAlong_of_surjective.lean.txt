import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteAlong_of_surjective

open AlgebraicCurve
theorem AlgebraicCurve.finiteAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteAlong_of_surjective.solution
