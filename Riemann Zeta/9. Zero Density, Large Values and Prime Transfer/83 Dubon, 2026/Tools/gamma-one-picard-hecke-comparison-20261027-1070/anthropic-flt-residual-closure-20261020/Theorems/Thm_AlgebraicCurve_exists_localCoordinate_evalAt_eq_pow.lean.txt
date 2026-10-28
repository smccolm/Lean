import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_localCoordinate_evalAt_eq_pow
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (v : Place ℂ F) (g : F) (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : v.evalAt g = 0) :
    ∃ (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ), 0 < ρ ∧
      v ∈ ζ.source ∧ ζ v = 0 ∧ ζ.target = Metric.ball 0 ρ ∧
      ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source) ∧
      (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source, deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) ∧
      ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧ P.evalAt g = (ζ P) ^ (v.ord g).toNat := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow.solution
