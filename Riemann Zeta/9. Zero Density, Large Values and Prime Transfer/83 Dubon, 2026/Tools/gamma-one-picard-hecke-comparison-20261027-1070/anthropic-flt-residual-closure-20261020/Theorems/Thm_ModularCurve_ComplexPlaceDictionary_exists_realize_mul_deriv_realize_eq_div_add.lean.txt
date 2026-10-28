import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisor
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionary.exists_realize_mul_deriv_realize_eq_div_add
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)
    [∀ w : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      w.DCoordGenerates]
    (a x π : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (τ : ℍ)
    (η : Ω[(ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))⁄ℂ])
    (hηax : η = a • KaehlerDifferential.D ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) x)
    (hη : η ≠ 0) (hord : -1 ≤ (D.pt τ).ordDifferential η)
    (hπ : (D.pt τ).ord π = 1)
    (hdπ : (D.pt τ).dCoord = KaehlerDifferential.D ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) π) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff η * π -
          algebraMap ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ρ ∈
        (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential η = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        ModularCurve.realize N (a : LaurentSeries ℂ) (ofComplex z) *
            deriv (fun w : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex w)) z =
          (D.ramification τ : ℂ) * ρ / (z - τ) + g z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.solution
