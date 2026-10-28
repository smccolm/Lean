import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0

theorem CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.solution
