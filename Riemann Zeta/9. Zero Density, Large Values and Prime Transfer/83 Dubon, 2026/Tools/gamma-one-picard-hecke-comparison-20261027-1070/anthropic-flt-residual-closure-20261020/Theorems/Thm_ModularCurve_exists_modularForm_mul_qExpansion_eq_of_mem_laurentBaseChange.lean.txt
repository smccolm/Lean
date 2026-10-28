import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane in

theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange (N : ℕ)
    [NeZero N] (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange.solution
