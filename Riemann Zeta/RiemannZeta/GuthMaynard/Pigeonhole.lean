import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

lemma pigeonhole_real_sum (n : ℕ) (a : ℕ → ℝ) (S : ℝ) (hS : S ≤ ∑ i ∈ range n, a i) (hn : 0 < n) :
  ∃ i ∈ range n, S / n ≤ a i := by
  by_contra h
  push_neg at h
  have h_sum : ∑ i ∈ range n, a i < ∑ i ∈ range n, (S / n) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact le_of_lt (h i (by assumption))
    · exists 0
      constructor
      · exact Finset.mem_range.mpr hn
      · exact h 0 (Finset.mem_range.mpr hn)
  have h_sum_eq : ∑ i ∈ range n, (S / n) = S := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    exact mul_div_cancel₀ S hn_real
  rw [h_sum_eq] at h_sum
  linarith
end RiemannZeta.GuthMaynard
