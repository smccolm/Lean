import Mathlib

example {n : ℕ} (i j : Fin n) (hij : (i : ℚ) = (j : ℚ)) : i = j := by
  apply Fin.ext
  exact_mod_cast hij

example {n : ℕ} (i j : Fin n) (hij : (i : ℚ) = (j : ℚ)) : i = j := by
  apply Fin.ext
  norm_num at hij ⊢
