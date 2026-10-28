import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteAlong_comp

open AlgebraicCurve
theorem AlgebraicCurve.finiteAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteAlong_comp.solution
