import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor

lemma test (A : ℝ) (hApos : 0 ≤ A) (h : (3 : ℝ) ≤ A) : 3 ≤ ⌊A⌋₊ := by
  exact_mod_cast h
