import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_CuspForm_finiteDimensional_Gamma0

open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_finiteDimensional_Gamma0.solution
