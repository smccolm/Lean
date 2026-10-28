import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_ModularForm_finiteDimensional_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒢 k) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_finiteDimensional_of_isArithmetic.solution
