import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v v) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem.solution
