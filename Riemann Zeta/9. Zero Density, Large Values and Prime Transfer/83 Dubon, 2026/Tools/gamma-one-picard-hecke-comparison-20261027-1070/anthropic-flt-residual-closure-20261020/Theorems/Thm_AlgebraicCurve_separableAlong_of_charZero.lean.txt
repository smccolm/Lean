import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_separableAlong_of_charZero

open AlgebraicCurve
theorem AlgebraicCurve.separableAlong_of_charZero {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_separableAlong_of_charZero.solution
