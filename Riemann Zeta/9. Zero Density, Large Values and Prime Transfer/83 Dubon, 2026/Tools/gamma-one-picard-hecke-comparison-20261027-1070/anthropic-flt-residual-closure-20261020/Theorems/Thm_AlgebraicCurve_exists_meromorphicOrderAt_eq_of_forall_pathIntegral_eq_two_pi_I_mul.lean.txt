import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ F → ℂ, ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z))
          (extChartAt 𝓘(ℂ, ℂ) v v) = (D v : WithTop ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul.solution
