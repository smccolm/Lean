import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one

open AlgebraicCurve
theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one.solution
