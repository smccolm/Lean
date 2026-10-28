import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant

open scoped MatrixGroups

theorem ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.solution
