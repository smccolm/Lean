import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open ModularCurve AlgebraicCurve
theorem ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange {L : Type*} [Field L] [Algebra ℚ L]
    [IsAlgClosed L] {N M : ℕ} [NeZero M]
    (φ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M))
    (hφ : φ.toRingHom.IsIntegral)
    (W : Place L (laurentBaseChange L (modularFunctionFieldFull M))) :
    W.inertiaDegAlong φ hφ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange.solution
