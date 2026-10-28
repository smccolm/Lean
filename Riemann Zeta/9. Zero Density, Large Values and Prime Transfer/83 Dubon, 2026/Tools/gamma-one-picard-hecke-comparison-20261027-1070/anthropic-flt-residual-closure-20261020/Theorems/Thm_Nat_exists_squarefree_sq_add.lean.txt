import Mathlib
import P2M.Util
import P2M.Sol.S_Nat_exists_squarefree_sq_add

theorem Nat.exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D) := by p2m_exact_reverting @_root_.P2MW.S_Nat_exists_squarefree_sq_add.solution
