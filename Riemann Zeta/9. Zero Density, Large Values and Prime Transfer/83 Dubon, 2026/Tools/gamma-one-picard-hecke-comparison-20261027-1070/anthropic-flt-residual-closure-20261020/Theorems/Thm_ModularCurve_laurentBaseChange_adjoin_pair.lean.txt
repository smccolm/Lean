import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_adjoin_pair
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.laurentBaseChange_adjoin_pair (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (hgenQ : FunctionFieldGeneration M) : laurentBaseChange L (modularFunctionFieldFull M) = IntermediateField.adjoin L {jqModC L, jqNModC L M} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_adjoin_pair.solution
