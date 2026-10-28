import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

theorem AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] (A : ValuationSubring K) {j : F}
    (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {B : Subring F} (hconst : ∀ a : A, algebraMap K F a ∈ B) (hjB : j ∈ B)
    (hint : ∀ b : B,
      IsIntegral (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})) (b : F))
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮)
    (a₀ : A) (hja : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔮) :
    ∃ w : AlgebraicCurve.Place K F,
      0 < w.ord (j - algebraMap K F a₀) ∧
      ∀ b : B, b ∈ 𝔮 ↔ ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        ((b : F) - algebraMap K F a) ∈ w.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.solution
