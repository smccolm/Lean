import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord

open AlgebraicCurve ModularCurve
theorem AlgebraicCurve.Place.exists_algHom_laurentSeries_order_eq_ord {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K, ∀ x : F, (φ x).order = w.ord x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord.solution
