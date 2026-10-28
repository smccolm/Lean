import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one AlgebraicCurve.Place.mem_iff_adicValuation_le_one
