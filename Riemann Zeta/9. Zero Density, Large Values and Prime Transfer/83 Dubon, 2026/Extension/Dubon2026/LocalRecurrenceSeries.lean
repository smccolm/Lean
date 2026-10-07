import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! # Exact Euler denominators from convergent coefficient recurrences -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- An actually convergent second-order coefficient series has its exact Euler denominator; no value for the series is an input. -/
theorem tsum_second_order_recurrence {u : ℕ → ℂ} {a b : ℂ}
    (hu : Summable u) (h0 : u 0 = 1) (h1 : u 1 = a)
    (hrec : ∀ r : ℕ, u (r + 2) = a * u (r + 1) - b * u r) :
    (1 - a + b) * (∑' r : ℕ, u r) = 1 := by
  have hs1 : Summable (fun r : ℕ => u (r + 1)) := hu.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he0 := hu.tsum_eq_zero_add
  have he1 := hs1.tsum_eq_zero_add
  rw [h0] at he0
  simp only [zero_add, h1, Nat.add_assoc] at he1
  have he2 : (∑' r : ℕ, u (r + 2)) = a * (∑' r : ℕ, u (r + 1)) - b * (∑' r : ℕ, u r) := by
    simp_rw [hrec]
    rw [(hs1.mul_left a).tsum_sub (hu.mul_left b), tsum_mul_left, tsum_mul_left]
  linear_combination (1 - a) * he0 + he1 + he2

/-- The genuine convergent recurrence makes its local Euler denominator nonzero. -/
theorem second_order_euler_denominator_ne_zero {u : ℕ → ℂ} {a b : ℂ}
    (hu : Summable u) (h0 : u 0 = 1) (h1 : u 1 = a)
    (hrec : ∀ r : ℕ, u (r + 2) = a * u (r + 1) - b * u r) : 1 - a + b ≠ 0 := by
  intro hz
  have he := tsum_second_order_recurrence hu h0 h1 hrec
  rw [hz, zero_mul] at he
  exact zero_ne_one he

/-- The reciprocal Euler factor is derived from the convergent original coefficient series. -/
theorem tsum_second_order_eq_euler_inverse {u : ℕ → ℂ} {a b : ℂ}
    (hu : Summable u) (h0 : u 0 = 1) (h1 : u 1 = a)
    (hrec : ∀ r : ℕ, u (r + 2) = a * u (r + 1) - b * u r) :
    (∑' r : ℕ, u r) = (1 - a + b)⁻¹ := by
  have he := tsum_second_order_recurrence hu h0 h1 hrec
  exact eq_inv_of_mul_eq_one_right he

end
end Dubon2026
