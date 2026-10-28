import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_jqN_pow_not_mem_adjoin_full
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.jqN_pow_not_mem_adjoin_full (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hF : jqN p ∉ modularFunctionFieldFull M) : jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ ((modularFunctionFieldFull M : Set (LaurentSeries ℚ)) ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqN_pow_not_mem_adjoin_full.solution
