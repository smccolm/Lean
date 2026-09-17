import Tao2026.SmoothNumberSaddleIndexedPhase

/-!
# Scale retention over an indexed shell range

The rounding loss after `k` square roots is explicit.  This module converts
the closed-form envelope into the four-fifths scale hypothesis used by the
uniform phase theorem.  It also shows that noncollapse of the terminal scale
automatically supplies every intermediate largeness hypothesis.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

theorem smoothSaddleIteratedPrimeScale_antitone (y : ℕ) :
    Antitone (fun k => smoothSaddleIteratedPrimeScale k y) := by
  apply antitone_nat_of_succ_le
  intro k
  exact Nat.sqrt_le_self _

theorem four_le_iteratedPrimeScale_of_le
    {j k y : ℕ} (hjk : j ≤ k)
    (hk : 4 ≤ smoothSaddleIteratedPrimeScale k y) :
    4 ≤ smoothSaddleIteratedPrimeScale j y := by
  exact hk.trans (smoothSaddleIteratedPrimeScale_antitone y hjk)

theorem iteratedPrimeScale_all_four_of_terminal
    {k y : ℕ} (hk : 4 ≤ smoothSaddleIteratedPrimeScale k y) :
    ∀ j < k, 4 ≤ smoothSaddleIteratedPrimeScale j y := by
  intro j hj
  exact four_le_iteratedPrimeScale_of_le hj.le hk

theorem half_pow_mul_two_pow (k : ℕ) :
    (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
  rw [← mul_pow]
  norm_num

theorem iteratedRoot_four_fifths_log_lower
    {k y : ℕ} (hterminal : 4 ≤ smoothSaddleIteratedPrimeScale k y)
    (hlogY : 10 * ((2 : ℝ) ^ k - 1) * Real.log 2 ≤
      Real.log (y : ℝ)) :
    (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) ≤
      Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) := by
  let a : ℝ := (1 / 2 : ℝ) ^ k
  let q : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by dsimp only [a]; positivity
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have haq : a * q = 1 := by
    dsimp only [a, q]
    exact half_pow_mul_two_pow k
  have hmul := mul_le_mul_of_nonneg_left hlogY ha.le
  have hround : 2 * (1 - a) * Real.log 2 ≤
      (1 / 5 : ℝ) * a * Real.log (y : ℝ) := by
    dsimp only [a, q] at hmul haq ⊢
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlower := smoothSaddleIteratedLogLower_le_log
    (iteratedPrimeScale_all_four_of_terminal hterminal)
  rw [smoothSaddleIteratedLogLower_eq] at hlower
  dsimp only [a] at hround
  calc
    (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) ≤
        (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) -
          2 * (1 - (1 / 2 : ℝ) ^ k) * Real.log 2 := by
      nlinarith
    _ ≤ Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) := hlower

theorem iteratedRoot_ideal_log_upper
    {k y : ℕ} (hterminal : 4 ≤ smoothSaddleIteratedPrimeScale k y) :
    Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ≤
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) := by
  exact (iteratedRoot_log_bounds
    (iteratedPrimeScale_all_four_of_terminal hterminal)).2

theorem indexedIteratedRoot_scale_bounds
    {k y : ℕ} (hterminal : 4 ≤ smoothSaddleIteratedPrimeScale k y)
    (hlogY : 10 * ((2 : ℝ) ^ k - 1) * Real.log 2 ≤
      Real.log (y : ℝ)) :
    (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) ≤
        Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ∧
      Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ≤
        (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) := by
  exact ⟨iteratedRoot_four_fifths_log_lower hterminal hlogY,
    iteratedRoot_ideal_log_upper hterminal⟩

end

end Tao2026
