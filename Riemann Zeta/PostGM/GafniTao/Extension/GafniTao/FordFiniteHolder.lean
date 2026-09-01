import GafniTao.FordLemma51Entry
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite Hölder power inequality for Ford's Section 5

The first Hölder step in the proof of Ford's Lemma 5.1 is a finite Jensen
power estimate applied after the triangle inequality.  This file records the
exact cardinality exponent `r-1` used in equation (5.3).
-/

open Finset

namespace GafniTao

theorem ford_finite_holder_power
    {α : Type*} (B : Finset α) (V : α → ℂ) {r : ℕ} (hr : 1 ≤ r) :
    ‖∑ b ∈ B, V b‖ ^ r ≤
      (B.card : ℝ) ^ (r - 1) * ∑ b ∈ B, ‖V b‖ ^ r := by
  have htri : ‖∑ b ∈ B, V b‖ ≤ ∑ b ∈ B, ‖V b‖ := norm_sum_le B V
  have hp : ‖∑ b ∈ B, V b‖ ^ r ≤ (∑ b ∈ B, ‖V b‖) ^ r :=
    pow_le_pow_left₀ (norm_nonneg _) htri r
  have hj := pow_sum_le_card_mul_sum_pow
    (s := B) (f := fun b => ‖V b‖) (fun b hb => norm_nonneg (V b)) (r - 1)
  rw [Nat.sub_add_cancel hr] at hj
  exact hp.trans hj

#print axioms ford_finite_holder_power

end GafniTao
