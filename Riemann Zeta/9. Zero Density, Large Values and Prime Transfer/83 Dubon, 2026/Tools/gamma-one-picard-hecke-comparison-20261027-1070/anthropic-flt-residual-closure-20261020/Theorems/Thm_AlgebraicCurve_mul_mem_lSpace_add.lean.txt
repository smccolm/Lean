import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mul_mem_lSpace_add

namespace AlgebraicCurve
theorem mul_mem_lSpace_add {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mul_mem_lSpace_add.solution
end AlgebraicCurve
