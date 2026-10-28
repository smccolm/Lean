import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionary.two_mul_ramification_eq_card_stabilizer
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer.solution
