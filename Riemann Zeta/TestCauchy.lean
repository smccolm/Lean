import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

open Finset

lemma discrete_duality_cauchy_schwarz (R : ℕ) (a b : ℕ → ℝ) :
  (∑ r ∈ Ico 0 R, a r * b r)^2 ≤ (∑ r ∈ Ico 0 R, a r ^ 2) * (∑ r ∈ Ico 0 R, b r ^ 2) := by
  exact sum_mul_sq_le_sq_mul_sq (Ico 0 R) a b
