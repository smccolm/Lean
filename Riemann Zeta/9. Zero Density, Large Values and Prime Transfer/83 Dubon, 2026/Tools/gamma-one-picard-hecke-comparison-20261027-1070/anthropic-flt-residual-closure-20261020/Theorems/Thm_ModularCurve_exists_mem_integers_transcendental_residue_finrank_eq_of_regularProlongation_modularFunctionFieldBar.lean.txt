import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X
attribute [-simp] ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open AlgebraicCurve ModularCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
theorem ModularCurve.exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
    (M : ℕ) [NeZero M]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [IsAlgClosed (ResidueField ↥A)]
    (R : RegularProlongation A (modularFunctionFieldBar M)
        (modularFunctionFieldFullC (ResidueField ↥A) M))
    (hspec : ∀ (y : LaurentSeries ↥A)
        (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar M) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldFullC (ResidueField ↥A) M)
            : LaurentSeries (ResidueField ↥A))
          = coeffMap (IsLocalRing.residue ↥A) y) :
    ∃ x : R.integers,
      Transcendental (ResidueField ↥A) (R.residue x)
      ∧ 0 < Module.finrank
          (IntermediateField.adjoin (ResidueField ↥A)
            ({R.residue x} : Set (modularFunctionFieldFullC (ResidueField ↥A) M)))
          (modularFunctionFieldFullC (ResidueField ↥A) M)
      ∧ Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({(x : modularFunctionFieldBar M)} : Set (modularFunctionFieldBar M)))
          (modularFunctionFieldBar M)
        = Module.finrank
          (IntermediateField.adjoin (ResidueField ↥A)
            ({R.residue x} : Set (modularFunctionFieldFullC (ResidueField ↥A) M)))
          (modularFunctionFieldFullC (ResidueField ↥A) M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar.solution
