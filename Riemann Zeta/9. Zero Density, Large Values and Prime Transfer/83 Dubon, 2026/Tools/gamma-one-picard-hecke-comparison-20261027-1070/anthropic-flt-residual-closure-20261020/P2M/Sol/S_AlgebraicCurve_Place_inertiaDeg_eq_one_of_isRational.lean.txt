import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [(AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hv,
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hw, one_mul] at h
  exact h
