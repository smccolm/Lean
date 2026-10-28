import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_algebraMap

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_algebraMap.solution
