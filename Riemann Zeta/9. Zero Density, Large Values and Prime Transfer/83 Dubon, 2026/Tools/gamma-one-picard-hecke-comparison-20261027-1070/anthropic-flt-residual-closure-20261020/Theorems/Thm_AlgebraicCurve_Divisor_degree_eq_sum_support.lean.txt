import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_eq_sum_support

namespace AlgebraicCurve
theorem Divisor.degree_eq_sum_support {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum_support.solution
end AlgebraicCurve
