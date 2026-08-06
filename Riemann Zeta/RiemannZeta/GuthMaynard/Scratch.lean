import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open Complex

lemma exp_smoothing_bound (n : ℕ) (T : ℝ) (hn : 0 < n) (hT : 1 ≤ T) :
  ‖Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ))‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  have h_exp_pos : 0 ≤ Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ)) := (Real.exp_pos _).le
  rw [abs_of_nonneg h_exp_pos]
  have h1 : 0 ≤ T ^ (1/2 : ℝ) := by positivity
  have h2 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : 0 ≤ (n : ℝ) / T ^ (1/2 : ℝ) := div_nonneg h2 h1
  have h4 : -(n : ℝ) / T ^ (1/2 : ℝ) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr h3
  have h5 : Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h4
  rw [Real.exp_zero] at h5
  exact h5
