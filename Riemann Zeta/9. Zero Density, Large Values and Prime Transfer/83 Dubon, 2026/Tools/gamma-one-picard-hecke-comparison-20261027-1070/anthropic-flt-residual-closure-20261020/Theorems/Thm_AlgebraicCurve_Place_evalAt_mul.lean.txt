import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_mul

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_mul.solution
