import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_zsmul_mk

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.zsmul_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) : m • Pic0.mk D = Pic0.mk (m • D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_zsmul_mk.solution
