import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_support_pushforward_subset

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.support_pushforward_subset {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') : (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_support_pushforward_subset.solution
