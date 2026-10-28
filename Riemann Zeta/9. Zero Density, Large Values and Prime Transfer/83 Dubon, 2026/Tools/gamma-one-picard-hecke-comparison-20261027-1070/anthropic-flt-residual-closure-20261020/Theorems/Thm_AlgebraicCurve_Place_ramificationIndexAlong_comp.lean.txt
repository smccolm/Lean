import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_comp

open AlgebraicCurve
theorem AlgebraicCurve.Place.ramificationIndexAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : Place.ramificationIndexAlong (χ.comp φ) W = Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_comp.solution
