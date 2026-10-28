import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_support_pullback_subset

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.support_pullback_subset {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')] (E : Divisor K F) : (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_support_pullback_subset.solution
