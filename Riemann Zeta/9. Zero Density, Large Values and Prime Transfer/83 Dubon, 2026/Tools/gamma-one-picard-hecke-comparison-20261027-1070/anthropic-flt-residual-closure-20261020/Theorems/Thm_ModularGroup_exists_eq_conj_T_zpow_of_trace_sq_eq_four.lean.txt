import Mathlib
import P2M.Util
import P2M.Sol.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.solution
