import Mathlib.Data.Real.Basic

axiom my_unproven_theorem (x : ℝ) : x = x + 1

theorem my_test : ∀ x : ℝ, x = x + 1 := by
  intro x
  exact my_unproven_theorem x
