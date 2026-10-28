import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1

namespace AlgebraicCurve
theorem indexOfSpecialty_eq_finrank_H1 {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (H1 D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.solution
end AlgebraicCurve
