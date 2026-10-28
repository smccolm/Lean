import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (η : Ω[F⁄ℂ]) (v : Place ℂ F) (U : Set (Place ℂ F)) (hU : IsOpen U)
    (hUv : U ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (hηU : ∀ u ∈ U, 0 ≤ u.ordDifferential η)
    (hcoeff : ∀ u ∈ U, v.differentialCoeff η ∈ u.toValuationSubring)
    (hunif : ∀ u ∈ U, v.dCoordFn ∈ u.toValuationSubring)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ u ∈ U, HasDerivAt Φ (v.readDifferential η (extChartAt 𝓘(ℂ, ℂ) v u))
      (extChartAt 𝓘(ℂ, ℂ) v u))
    {P Q : Place ℂ F} (γ : Path P Q) (hγ : ∀ t, γ t ∈ U) :
    IsPrimitiveAlong η γ (fun t => Φ (extChartAt 𝓘(ℂ, ℂ) v (γ t))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.solution
