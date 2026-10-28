import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_transpose_mul_mul_eq_J

theorem Matrix.exists_transpose_mul_mul_eq_J {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hQ : Q.transpose = -Q) (hdet : IsUnit Q.det) :
    ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ, IsUnit P.det ∧
      P.transpose * Q * P = Matrix.J (Fin n) ℤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_transpose_mul_mul_eq_J.solution
