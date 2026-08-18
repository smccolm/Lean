import Mathlib

open scoped BigOperators

example (s : Finset ℤ) (A B : ℝ) (f : ℤ → ℝ) :
    (∑ r ∈ s, A * f r * B) = A * (∑ r ∈ s, f r) * B := by
  rw [Finset.mul_sum, Finset.sum_mul]

example (s : Finset ℤ) (T S O C : ℝ) (f : ℤ → ℝ) :
    (∑ r ∈ s, T * (S * O) * (C * f r)) =
      T * O * (∑ r ∈ s, S * (C * f r)) := by
  calc
    (∑ r ∈ s, T * (S * O) * (C * f r)) =
        ∑ r ∈ s, (T * O) * (S * (C * f r)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          ring
    _ = T * O * (∑ r ∈ s, S * (C * f r)) := by
      rw [Finset.mul_sum]
