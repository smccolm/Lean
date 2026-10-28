import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ell_le_ell_sub_single_add_deg

namespace AlgebraicCurve
theorem ell_le_ell_sub_single_add_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_le_ell_sub_single_add_deg.solution
end AlgebraicCurve
