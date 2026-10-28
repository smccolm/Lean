import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') : Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong.solution
