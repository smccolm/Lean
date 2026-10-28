import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open IntermediateField AlgebraicCurve
theorem ModularCurve.finrank_jAdjoin_modularFunctionField_eq_dedekindPsi (N : ℕ) [NeZero N] :
    @Module.finrank ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) _ _
      (ModularCurve.jAdjoinAlgebra N).toModule = ModularCurve.dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi.solution
