import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import P2M.Util
namespace P2MW.S_CuspForm_finiteDimensional_of_isArithmetic

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic 𝒢 k
  exact Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
end
