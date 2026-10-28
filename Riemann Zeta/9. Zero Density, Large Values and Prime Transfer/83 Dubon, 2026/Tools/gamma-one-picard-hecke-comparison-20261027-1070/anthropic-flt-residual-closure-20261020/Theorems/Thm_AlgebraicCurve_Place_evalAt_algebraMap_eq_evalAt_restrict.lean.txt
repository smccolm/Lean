import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) {g : F} (hg : g ∈ (w.restrict F).toValuationSubring) : w.evalAt (algebraMap F F' g) = (w.restrict F).evalAt g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict.solution
