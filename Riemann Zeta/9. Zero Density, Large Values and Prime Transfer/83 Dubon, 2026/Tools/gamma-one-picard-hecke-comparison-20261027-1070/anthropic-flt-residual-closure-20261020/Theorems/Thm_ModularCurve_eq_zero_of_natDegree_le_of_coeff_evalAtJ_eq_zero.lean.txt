import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero

open ModularCurve Polynomial
theorem ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero (P : Polynomial ℤ) (n : ℕ)
    (hP : P.natDegree ≤ n) (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) : P = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero.solution
