import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_add_eq_of_lt

theorem AlgebraicCurve.Place.ord_add_eq_of_lt {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_add_eq_of_lt.solution
