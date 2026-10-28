import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import P2M.Util
import P2M.Sol.S_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.CompEq.finrank_adjoin_jBar_eq_dedekindPsi (N : ℕ) [NeZero N] :
    Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi.solution
