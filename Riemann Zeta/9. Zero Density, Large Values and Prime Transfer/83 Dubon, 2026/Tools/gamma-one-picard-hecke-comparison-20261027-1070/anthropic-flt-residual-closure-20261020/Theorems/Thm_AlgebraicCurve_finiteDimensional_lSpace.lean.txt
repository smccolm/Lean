import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finiteDimensional_lSpace

namespace AlgebraicCurve
theorem finiteDimensional_lSpace {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [hL0 : FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K ↥(LSpace D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finiteDimensional_lSpace.solution
end AlgebraicCurve
