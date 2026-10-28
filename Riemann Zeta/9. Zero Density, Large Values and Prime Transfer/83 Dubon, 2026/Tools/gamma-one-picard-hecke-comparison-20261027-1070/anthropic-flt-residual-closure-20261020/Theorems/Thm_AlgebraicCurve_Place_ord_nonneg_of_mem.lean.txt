import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_mem.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.ord_nonneg_of_mem AlgebraicCurve.Place.ord_nonneg_of_mem
