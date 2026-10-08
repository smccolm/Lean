import Dubon2026.LocalRecurrenceSeries

/-! # Literal cubic Euler denominator from a genuinely convergent recurrence -/

namespace Dubon2026

noncomputable section

/-- Summing an actual convergent third-order recurrence gives its exact cubic Euler numerator and denominator. -/
theorem tsum_third_order_recurrence {u : ℕ → ℂ} {a b c : ℂ}
    (hu : Summable u)
    (hrec : ∀ r : ℕ, u (r + 3) = a * u (r + 2) + b * u (r + 1) + c * u r) :
    (1 - a - b - c) * (∑' r : ℕ, u r) =
      (1 - a - b) * u 0 + (1 - a) * u 1 + u 2 := by
  have hs1 : Summable (fun r : ℕ => u (r + 1)) := hu.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs2 : Summable (fun r : ℕ => u (r + 2)) := hu.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he0 := hu.tsum_eq_zero_add
  have he1 := hs1.tsum_eq_zero_add
  have he2 := hs2.tsum_eq_zero_add
  simp only [zero_add, Nat.add_assoc] at he1 he2
  have he3 : (∑' r : ℕ, u (r + 3)) =
      a * (∑' r : ℕ, u (r + 2)) + b * (∑' r : ℕ, u (r + 1)) + c * (∑' r : ℕ, u r) := by
    simp_rw [hrec]
    rw [((hs2.mul_left a).add (hs1.mul_left b)).tsum_add (hu.mul_left c),
      (hs2.mul_left a).tsum_add (hs1.mul_left b), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  linear_combination (1 - a - b) * he0 + (1 - a) * he1 + he2 + he3

/-- Squaring the genuine determinant-one second-order recurrence produces the exact symmetric-square cubic recurrence. -/
theorem square_sequence_third_order {v : ℕ → ℂ} {x : ℂ}
    (hrec : ∀ r : ℕ, v (r + 2) = x * v (r + 1) - v r) (r : ℕ) :
    v (r + 3) ^ 2 = (x ^ 2 - 1) * v (r + 2) ^ 2 -
      (x ^ 2 - 1) * v (r + 1) ^ 2 + v r ^ 2 := by
  have h3 := hrec (r + 1)
  simp only [Nat.add_assoc] at h3
  rw [h3, hrec r]
  ring

/-- The square recurrence remains exact after multiplication by the original geometric local Dirichlet coordinate. -/
theorem weighted_square_sequence_third_order {v : ℕ → ℂ} {x : ℂ}
    (hrec : ∀ r : ℕ, v (r + 2) = x * v (r + 1) - v r) (z : ℂ) (r : ℕ) :
    v (r + 3) ^ 2 * z ^ (r + 3) =
      ((x ^ 2 - 1) * z) * (v (r + 2) ^ 2 * z ^ (r + 2)) +
      (-(x ^ 2 - 1) * z ^ 2) * (v (r + 1) ^ 2 * z ^ (r + 1)) +
      z ^ 3 * (v r ^ 2 * z ^ r) := by
  rw [square_sequence_third_order hrec r]
  simp only [pow_add]
  ring

/-- The genuine square-coefficient generating series has exactly numerator 1+z and the symmetric-square denominator. -/
theorem tsum_square_recurrence_euler {v : ℕ → ℂ} {x z : ℂ}
    (h0 : v 0 = 1) (h1 : v 1 = x)
    (hrec : ∀ r : ℕ, v (r + 2) = x * v (r + 1) - v r)
    (hs : Summable (fun r : ℕ => v r ^ 2 * z ^ r)) :
    (1 - (x ^ 2 - 1) * z + (x ^ 2 - 1) * z ^ 2 - z ^ 3) *
      (∑' r : ℕ, v r ^ 2 * z ^ r) = 1 + z := by
  have he := tsum_third_order_recurrence hs (weighted_square_sequence_third_order hrec z)
  have h2 : v 2 = x ^ 2 - 1 := by simpa [h0, h1, pow_two] using hrec 0
  simp only [h0,h1,h2,pow_zero,pow_one,one_pow,mul_one] at he
  linear_combination he

end
end Dubon2026
