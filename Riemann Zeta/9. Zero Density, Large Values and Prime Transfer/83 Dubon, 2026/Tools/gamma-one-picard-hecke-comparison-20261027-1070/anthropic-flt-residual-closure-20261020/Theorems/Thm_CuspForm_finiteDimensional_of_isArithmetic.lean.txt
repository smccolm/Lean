import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_CuspForm_finiteDimensional_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_finiteDimensional_of_isArithmetic.solution
