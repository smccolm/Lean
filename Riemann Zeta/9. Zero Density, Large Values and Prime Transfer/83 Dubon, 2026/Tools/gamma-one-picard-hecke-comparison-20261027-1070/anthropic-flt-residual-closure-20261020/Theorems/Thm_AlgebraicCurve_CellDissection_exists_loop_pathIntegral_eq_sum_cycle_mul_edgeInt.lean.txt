import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (𝒟 : CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZk : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e)
    (hZd : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0)
    (hZ0 : ∀ j ∈ 𝒯, Z j = 0)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    (j : 𝒟.ιE) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ 𝒟.skeleton) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * 𝒟.edgeInt θ e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.solution
