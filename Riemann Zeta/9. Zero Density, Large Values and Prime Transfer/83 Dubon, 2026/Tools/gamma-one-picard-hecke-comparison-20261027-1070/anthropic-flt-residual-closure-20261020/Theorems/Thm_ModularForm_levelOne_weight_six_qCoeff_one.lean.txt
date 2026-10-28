import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import P2M.Util
import P2M.Sol.S_ModularForm_levelOne_weight_six_qCoeff_one

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) : ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_levelOne_weight_six_qCoeff_one.solution
