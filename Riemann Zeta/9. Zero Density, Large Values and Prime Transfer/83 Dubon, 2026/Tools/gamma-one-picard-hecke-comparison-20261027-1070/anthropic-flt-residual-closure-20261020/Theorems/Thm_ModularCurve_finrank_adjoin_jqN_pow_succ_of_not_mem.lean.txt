import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqN_pow_succ_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ) (h0 : jqN (p ^ k) ∈ F) (h1 : jqN (p ^ (k + 1)) ∈ F) (hF : jqN (p ^ (k + 2)) ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN (p ^ (k + 2))} : Set (LaurentSeries ℚ))) = p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.solution
