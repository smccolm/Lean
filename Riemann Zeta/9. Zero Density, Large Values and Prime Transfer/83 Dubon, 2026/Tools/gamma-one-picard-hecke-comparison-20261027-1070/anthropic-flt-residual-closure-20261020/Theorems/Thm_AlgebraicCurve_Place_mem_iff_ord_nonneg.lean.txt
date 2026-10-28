import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_iff_ord_nonneg.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg AlgebraicCurve.Place.mem_iff_ord_nonneg
