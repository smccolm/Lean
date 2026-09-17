import Tao2026.SmoothNumberSaddleIndexedScaleRange

/-!
# Eventual admissibility at every fixed indexed depth

For a fixed number of iterated square roots, the terminal prime scale is
eventually noncollapsed in every Tao-critical regime.  Together with the
explicit logarithmic rounding criterion, this makes every fixed finite prefix
of the indexed shell family eventually admissible.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

/-- Exact arithmetic criterion for surviving `k` iterated natural square
roots.  In particular, no information is lost by reasoning with the single
threshold `a ^ (2 ^ k)`. -/
theorem le_smoothSaddleIteratedPrimeScale_iff (a k y : ℕ) :
    a ≤ smoothSaddleIteratedPrimeScale k y ↔ a ^ (2 ^ k) ≤ y := by
  induction k generalizing a with
  | zero => simp [smoothSaddleIteratedPrimeScale]
  | succ k ih =>
      rw [smoothSaddleIteratedPrimeScale, Nat.le_sqrt', ih]
      have hpow : (a ^ 2) ^ (2 ^ k) = a ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]
        congr 1
        exact Nat.mul_comm 2 (2 ^ k)
      rw [hpow]

/-- A fixed iterated-root scale eventually remains at least four in every
critical smooth-number regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_four_le_iteratedPrimeScale
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    ∀ᶠ n in atTop, 4 ≤ smoothSaddleIteratedPrimeScale k (y n) := by
  have hy := (hregime.tendsto_y_atTop hα).eventually
    (eventually_ge_atTop (4 ^ (2 ^ k)))
  filter_upwards [hy] with n hn
  exact (le_smoothSaddleIteratedPrimeScale_iff 4 k (y n)).2 hn

/-- The explicit logarithmic rounding condition for a fixed indexed depth is
eventually automatic in every critical smooth-number regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_indexedLogRoundingCriterion
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    ∀ᶠ n in atTop,
      10 * ((2 : ℝ) ^ k - 1) * Real.log 2 ≤ Real.log (y n : ℝ) := by
  exact (hregime.tendsto_log_y_atTop hα).eventually
    (eventually_ge_atTop (10 * ((2 : ℝ) ^ k - 1) * Real.log 2))

/-- Every fixed indexed depth is eventually scale-admissible: the terminal
scale remains noncollapsed and obeys both ideal logarithmic bounds required
by the uniform indexed phase theorem. -/
theorem IsTaoCriticalSmoothRegime.eventually_indexedIteratedRoot_scale_bounds
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    ∀ᶠ n in atTop,
      4 ≤ smoothSaddleIteratedPrimeScale k (y n) ∧
        (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ k * Real.log (y n : ℝ) ≤
          Real.log (smoothSaddleIteratedPrimeScale k (y n) : ℝ) ∧
        Real.log (smoothSaddleIteratedPrimeScale k (y n) : ℝ) ≤
          (1 / 2 : ℝ) ^ k * Real.log (y n : ℝ) := by
  filter_upwards [hregime.eventually_four_le_iteratedPrimeScale hα k,
    hregime.eventually_indexedLogRoundingCriterion hα k] with n hterminal hlogY
  exact ⟨hterminal, indexedIteratedRoot_scale_bounds hterminal hlogY⟩

end

end Tao2026
