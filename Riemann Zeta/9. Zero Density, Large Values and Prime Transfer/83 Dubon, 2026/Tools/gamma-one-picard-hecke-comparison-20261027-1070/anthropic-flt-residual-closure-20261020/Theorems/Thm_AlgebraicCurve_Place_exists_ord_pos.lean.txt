import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_pos
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.exists_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_pos.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.exists_ord_pos AlgebraicCurve.Place.exists_ord_pos
