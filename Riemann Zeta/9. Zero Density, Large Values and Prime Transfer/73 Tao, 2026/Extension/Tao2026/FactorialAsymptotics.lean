import Tao2026.Asymptotics
import Tao2026.FactorialOneTerm

/-!
# Lower asymptotics for the factorial-square problem

The exact square family supplies more than a cardinal inequality: it proves
the reverse-big-O half of the `x^(1/2+o(1))` contracts in Tao's Theorems 1.9
and 1.10.  The analytic upper halves remain separate obligations.
-/

open Filter Asymptotics

namespace Tao2026

private theorem power_half_sub_le_two_mul_factorialThreeOneTermCount
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := by
  filter_upwards [eventually_ge_atTop 9] with n hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 9) hn)
  have hpow : (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  have hsqrtNat : 3 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt']
    norm_num
    exact hn
  have hroot : Real.sqrt n ≤
      2 * (factorialThreeOneTermCount n : ℝ) := by
    calc
      Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1 :=
        Real.real_sqrt_le_nat_sqrt_succ
      _ ≤ 2 * (Nat.sqrt n - 1 : ℕ) := by
        norm_cast
        omega
      _ ≤ 2 * (factorialThreeOneTermCount n : ℝ) := by
        gcongr
        exact_mod_cast sqrt_sub_one_le_factorialThreeOneTermCount n
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.norm_of_nonneg
      (Nat.cast_nonneg (factorialThreeOneTermCount n) :
        0 ≤ (factorialThreeOneTermCount n : ℝ))]
  exact hpow.trans hroot

/-- The square family proves the lower half of the `F₃¹` square-root scale. -/
theorem factorialThreeOneTermCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialThreeOneTermCount n : ℝ)) := by
  intro ε hε
  exact IsBigO.of_bound 2
    (power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε)

/-- The same lower half transfers from `F₃¹` to all `F₃` endpoints. -/
theorem factorialThreeCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialThreeCount n : ℝ)) := by
  intro ε hε
  refine IsBigO.of_bound 2 ?_
  filter_upwards
      [power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε] with n hn
  calc
    ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := hn
    _ ≤ 2 * ‖(factorialThreeCount n : ℝ)‖ := by
      rw [Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeOneTermCount n) :
            0 ≤ (factorialThreeOneTermCount n : ℝ)),
        Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeCount n) :
            0 ≤ (factorialThreeCount n : ℝ))]
      gcongr
      exact_mod_cast factorialThreeOneTermCount_le_factorialThreeCount n

/-- The exact endpoint projection transfers the lower half to the factorial-
square triple count, completing the lower half of Theorem 1.10's contract. -/
theorem factorialSquareTripleCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialSquareTripleCount n : ℝ)) := by
  intro ε hε
  refine IsBigO.of_bound 2 ?_
  filter_upwards
      [power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε] with n hn
  calc
    ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := hn
    _ ≤ 2 * ‖(factorialSquareTripleCount n : ℝ)‖ := by
      rw [Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeOneTermCount n) :
            0 ≤ (factorialThreeOneTermCount n : ℝ)),
        Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialSquareTripleCount n) :
            0 ≤ (factorialSquareTripleCount n : ℝ))]
      gcongr
      exact_mod_cast le_trans
        (factorialThreeOneTermCount_le_factorialThreeCount n)
        (factorialThreeCount_le_factorialSquareTripleCount n)

end Tao2026
