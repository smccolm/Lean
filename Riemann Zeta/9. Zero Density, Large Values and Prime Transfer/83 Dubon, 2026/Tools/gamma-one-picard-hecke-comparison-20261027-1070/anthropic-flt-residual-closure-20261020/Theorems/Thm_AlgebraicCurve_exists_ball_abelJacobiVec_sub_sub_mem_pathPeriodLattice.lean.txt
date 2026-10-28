import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
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
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ Φ : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (Φ i) (P.readDifferential (b i) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiVec b P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec b P₀ P -
              (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.solution
