import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_natCast

theorem AlgebraicCurve.Place.ord_natCast {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (n : ℕ) :
    v.ord (n : F) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_natCast.solution
