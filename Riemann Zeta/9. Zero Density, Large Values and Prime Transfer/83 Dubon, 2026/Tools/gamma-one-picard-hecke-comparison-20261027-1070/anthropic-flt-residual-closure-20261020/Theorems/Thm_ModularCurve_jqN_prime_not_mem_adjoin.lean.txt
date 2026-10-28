import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_jqN_prime_not_mem_adjoin
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.jqN_prime_not_mem_adjoin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ) [hr : Fact (Nat.Prime r)] (hrS : r ∉ S) : jqN r ∉ IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ S, ∃ _ : NeZero p, x = jqN p}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqN_prime_not_mem_adjoin.solution
