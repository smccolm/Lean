import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg

namespace AlgebraicCurve
theorem lSpace_eq_bot_of_degree_neg {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_lSpace_eq_bot_of_degree_neg.solution
end AlgebraicCurve
