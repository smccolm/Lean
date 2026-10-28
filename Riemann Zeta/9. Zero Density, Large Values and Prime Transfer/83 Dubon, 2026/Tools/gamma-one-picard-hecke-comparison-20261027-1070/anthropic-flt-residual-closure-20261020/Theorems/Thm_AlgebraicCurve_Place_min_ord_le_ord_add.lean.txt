import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_min_ord_le_ord_add

theorem AlgebraicCurve.Place.min_ord_le_ord_add {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add.solution
