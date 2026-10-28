import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_D_ne_zero

theorem AlgebraicCurve.exists_D_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_D_ne_zero.solution
