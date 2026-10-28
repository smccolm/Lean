import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

namespace AlgebraicCurve
theorem localUnitDerivativeRegular_of_isCurveOver {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver.solution
end AlgebraicCurve
