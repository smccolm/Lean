import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one
