import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum
attribute [-simp] ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve

universe u v w x

theorem AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type w) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E : Type x) (FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    ∃ (F'E : Type (max w x)) (_ : Field F'E) (_ : Algebra E F'E) (_ : Algebra F' F'E)
      (_ : Algebra K F'E) (_ : IsScalarTower K E F'E) (_ : IsScalarTower K F' F'E)
      (_ : IsCurveOver E F'E)
      (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
      (_ : FundamentalIdentityAlong E φE hφE) (hfinE : FiniteAlong E ψE)
      (_ : NormFormulaAlong E ψE hfinE),
      (∃ x' : F'E, Transcendental E x' ∧
        FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E) ∧
      IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤ ∧
      (∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f)) ∧
      (∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f)) ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ (Q : Place E FE) (e' : F →ₐ[K] E),
        (∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) →
          Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q =
            (∑ᶠ σ ∈ {σ : F' →ₐ[K] E | σ.comp φ = e},
              Finsupp.single (σ.comp ψ) (1 : ℤ) : (F →ₐ[K] E) →₀ ℤ) e') ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ e' : F →ₐ[K] E, ∀ f : F,
            Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) ∧
      (∀ P : Place E FE, (∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.solution
