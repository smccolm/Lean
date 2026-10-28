import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete

open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.solution
