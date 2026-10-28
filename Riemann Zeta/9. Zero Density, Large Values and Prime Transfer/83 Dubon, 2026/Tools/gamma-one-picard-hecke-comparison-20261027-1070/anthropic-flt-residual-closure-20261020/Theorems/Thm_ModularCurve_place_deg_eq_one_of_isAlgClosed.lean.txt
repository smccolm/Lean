import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_ModularCurve_place_deg_eq_one_of_isAlgClosed
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem ModularCurve.place_deg_eq_one_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K]
    (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_place_deg_eq_one_of_isAlgClosed.solution
