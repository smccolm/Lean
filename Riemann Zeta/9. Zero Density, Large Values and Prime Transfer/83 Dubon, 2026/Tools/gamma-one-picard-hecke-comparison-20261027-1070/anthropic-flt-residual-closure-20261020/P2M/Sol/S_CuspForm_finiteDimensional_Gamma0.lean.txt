import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import P2M.Util
namespace P2MW.S_CuspForm_finiteDimensional_Gamma0

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
  exact CuspForm.finiteDimensional_of_isArithmetic _ k
end
