import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
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
    (𝒟 : CellDissection F) (poles : Finset (Place ℂ F)) (c : Place ℂ F → 𝒟.ιC)
    (hc : ∀ v ∈ poles, v ∈ (𝒟.cell (c v)).interior')
    (θ : Ω[F⁄ℂ]) (hθpol : ∀ v ∈ poles, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q : Place ℂ F, Q ∉ poles → 0 ≤ Q.ordDifferential θ)
    (η : Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (hΨ : ∀ C, ∀ w ∈ V C, HasDerivAt (Ψ C) (coeffIn (𝒟.cell C).ζ η w) w) :
    ∃ J : 𝒟.ιE → ℂ,
      (∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e) ∧
      2 * π * I * ∑ v ∈ poles,
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ (c v) ((𝒟.cell (c v)).ζ v) =
        ∑ e : 𝒟.ιE, J e * 𝒟.edgeInt θ e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt.solution
