import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open UpperHalfPlane
theorem ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant : ModularCurve.jqModC ℂ = (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.solution
