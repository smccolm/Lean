import Mathlib

open scoped BigOperators

namespace RamanujanPetersson

/--
Lean-generated witness form of the prime-power bound in Corollary 5.3.

The source proof writes `a_{p^m}` as the coefficient sum
`∑_{j=0}^m αₚ^j βₚ^(m-j)` and then bounds each summand using
`‖αₚ‖ = ‖βₚ‖ = p^((k - 1) / 2)`.

This declaration formalizes exactly that coefficient-sum estimate. It does not yet
formalize the Euler product / multiplicativity input needed for the later
coprime-index consequence in Corollary 5.3.
-/
theorem corollary53_primePowers_witnessForm
    {a α β : ℂ} {p k m N : ℕ}
    (hp : Nat.Prime p) (hpnmidN : ¬ p ∣ N)
    (ha : a = ∑ j ∈ Finset.range (m + 1), α ^ j * β ^ (m - j))
    (hα : ‖α‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2))
    (hβ : ‖β‖ = (p : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖a‖ ≤ (m + 1) * ((p : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ m := by
  let _ := hp
  let _ := hpnmidN
  let R : ℝ := (p : ℝ) ^ ((k - 1 : ℝ) / 2)
  have hsum :
      ‖∑ j ∈ Finset.range (m + 1), α ^ j * β ^ (m - j)‖ ≤
        ∑ j ∈ Finset.range (m + 1), ‖α ^ j * β ^ (m - j)‖ := by
    simpa using
      (norm_sum_le (s := Finset.range (m + 1)) (f := fun j => α ^ j * β ^ (m - j)))
  rw [ha]
  have hEq :
      ∑ j ∈ Finset.range (m + 1), ‖α ^ j * β ^ (m - j)‖ =
        (m + 1) * R ^ m := by
    calc
      ∑ j ∈ Finset.range (m + 1), ‖α ^ j * β ^ (m - j)‖
          = ∑ j ∈ Finset.range (m + 1), (‖α‖ ^ j * ‖β‖ ^ (m - j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [norm_mul, norm_pow, norm_pow]
      _ = ∑ j ∈ Finset.range (m + 1), (R ^ j * R ^ (m - j)) := by
            simp [R, hα, hβ]
      _ = ∑ j ∈ Finset.range (m + 1), R ^ m := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            simpa [add_comm] using (pow_mul_pow_sub R hj')
      _ = (m + 1) * R ^ m := by
            simp
  exact hsum.trans (by simpa [R] using hEq.le)

end RamanujanPetersson
