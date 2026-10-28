import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree

namespace AlgebraicCurve
theorem ell_sub_ell_le_degree_sub_degree {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K ↥(LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree.solution
end AlgebraicCurve
