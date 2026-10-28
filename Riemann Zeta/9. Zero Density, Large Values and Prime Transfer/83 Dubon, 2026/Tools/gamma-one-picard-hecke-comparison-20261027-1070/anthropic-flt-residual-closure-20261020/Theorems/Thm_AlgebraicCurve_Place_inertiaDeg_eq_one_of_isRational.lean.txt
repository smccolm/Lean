import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational

open AlgebraicCurve
theorem AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational) : w.inertiaDeg F = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational.solution
