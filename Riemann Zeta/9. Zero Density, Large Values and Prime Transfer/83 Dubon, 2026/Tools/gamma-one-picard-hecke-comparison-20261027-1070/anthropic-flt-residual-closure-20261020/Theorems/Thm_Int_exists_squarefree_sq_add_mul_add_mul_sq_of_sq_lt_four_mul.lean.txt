import Mathlib
import P2M.Util
import P2M.Sol.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul

theorem Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by p2m_exact_reverting @_root_.P2MW.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.solution
