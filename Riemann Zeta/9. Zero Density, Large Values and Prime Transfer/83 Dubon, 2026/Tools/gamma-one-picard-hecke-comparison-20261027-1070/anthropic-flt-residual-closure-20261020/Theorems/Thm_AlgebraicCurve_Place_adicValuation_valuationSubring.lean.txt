import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_adicValuation_valuationSubring
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.adicValuation_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.valuationSubring = v.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_valuationSubring.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.adicValuation_valuationSubring AlgebraicCurve.Place.adicValuation_valuationSubring
