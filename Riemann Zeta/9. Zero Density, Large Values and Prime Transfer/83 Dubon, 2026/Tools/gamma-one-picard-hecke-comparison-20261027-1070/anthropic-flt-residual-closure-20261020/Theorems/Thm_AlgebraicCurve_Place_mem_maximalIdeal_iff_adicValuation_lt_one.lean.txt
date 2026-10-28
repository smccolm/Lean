import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one
