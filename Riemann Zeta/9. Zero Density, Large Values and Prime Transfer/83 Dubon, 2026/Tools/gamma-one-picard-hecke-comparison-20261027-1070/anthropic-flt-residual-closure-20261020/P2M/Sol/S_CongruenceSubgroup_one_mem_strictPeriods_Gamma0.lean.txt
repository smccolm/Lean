import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import P2M.Util
namespace P2MW.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)
