import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane
theorem ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC (ℓ : ℕ) [NeZero ℓ] : ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 ℓ) 12, H ≠ 0 ∧ ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.jqNModC ℂ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.solution
