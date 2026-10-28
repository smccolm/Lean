import Mathlib.NumberTheory.ModularForms.Cusps
import P2M.Util
import P2M.Sol.S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj

open scoped MatrixGroups Pointwise
theorem Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.solution
