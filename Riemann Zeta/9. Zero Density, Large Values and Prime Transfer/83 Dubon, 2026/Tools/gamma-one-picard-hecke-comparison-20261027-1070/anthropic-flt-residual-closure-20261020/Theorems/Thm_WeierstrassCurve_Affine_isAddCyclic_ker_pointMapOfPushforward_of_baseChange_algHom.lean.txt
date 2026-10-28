import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply
attribute [-simp] ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec
attribute [-simp] WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
    (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.solution
