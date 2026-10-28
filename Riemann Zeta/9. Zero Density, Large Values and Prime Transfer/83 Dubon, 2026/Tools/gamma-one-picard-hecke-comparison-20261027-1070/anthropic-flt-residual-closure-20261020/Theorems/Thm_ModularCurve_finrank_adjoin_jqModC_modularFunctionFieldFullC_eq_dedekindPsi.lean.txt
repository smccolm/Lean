import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    Module.finrank
        (IntermediateField.adjoin K
          ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi.solution
