import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.readDifferential_eventuallyEq_div_add_of_ordDifferential
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential θ z =
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) / (z - extChartAt 𝓘(ℂ, ℂ) v v) +
            G z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential.solution
