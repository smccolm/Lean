import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver

namespace AlgebraicCurve

theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.solution
