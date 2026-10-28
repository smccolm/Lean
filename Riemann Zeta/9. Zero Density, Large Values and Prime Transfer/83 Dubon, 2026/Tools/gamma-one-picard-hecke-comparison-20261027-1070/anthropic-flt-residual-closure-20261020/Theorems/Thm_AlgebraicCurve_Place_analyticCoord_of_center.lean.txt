import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_analyticCoord_of_center
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open scoped Manifold ContDiff
open AlgebraicCurve

theorem AlgebraicCurve.Place.analyticCoord_of_center {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] {v : Place ℂ F}
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hsub : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (han : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
      (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source))
    (hder : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0)
    (P : Place ℂ F) (hP : P ∈ ζ.source) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_analyticCoord_of_center.solution
