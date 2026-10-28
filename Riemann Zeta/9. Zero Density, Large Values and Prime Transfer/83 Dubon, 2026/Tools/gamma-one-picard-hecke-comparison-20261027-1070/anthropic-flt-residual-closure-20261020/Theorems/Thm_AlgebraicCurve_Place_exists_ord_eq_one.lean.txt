import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_eq_one

theorem AlgebraicCurve.Place.exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one.solution
