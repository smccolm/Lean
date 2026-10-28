import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq
