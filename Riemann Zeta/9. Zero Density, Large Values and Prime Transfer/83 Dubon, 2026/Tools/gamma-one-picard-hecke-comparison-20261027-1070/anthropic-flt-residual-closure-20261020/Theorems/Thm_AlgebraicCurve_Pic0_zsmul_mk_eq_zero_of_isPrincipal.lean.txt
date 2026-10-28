import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℤ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal.solution
