import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_neg
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

theorem P2M.Dup.AlgebraicCurve.Place.ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord (-f) = v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_neg.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.ord_neg AlgebraicCurve.Place.ord_neg
