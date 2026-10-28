import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one

theorem Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
    {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.solution
