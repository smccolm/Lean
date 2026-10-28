import Mathlib
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import P2M.Util
import P2M.Sol.S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ
attribute [-simp] ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

theorem ModularCurve.pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
    (N q n : ℕ) [NeZero N] [NeZero q] [NeZero n]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q))]
    (hpull : ModularCurve.DegeneracyPullbackInputs N q)
    (hpush : ModularCurve.DegeneracyPushforwardInputs N q)
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (e' : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (i : Fin 2)
    (x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (x' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (y' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (y : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (hx : (x' : ModularCurve.JZero (N * q)) =
      ModularCurve.degeneracyPullbackPair N q i (x : ModularCurve.JZero N))
    (hy : (y : ModularCurve.JZero N) =
      ModularCurve.degeneracyPushforwardPair N q i (y' : ModularCurve.JZero (N * q))) :
    e'.pair x' y' = e.pair x y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair.solution
