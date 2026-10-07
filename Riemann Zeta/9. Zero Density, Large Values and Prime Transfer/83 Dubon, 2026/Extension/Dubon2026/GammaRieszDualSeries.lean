import Dubon2026.GammaRieszDualTerm

/-! # Actual convergence and second differences of the dual Riesz Gamma series -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The genuine dual Riesz Gamma series, with its exact reciprocal coefficient and parameter weight. -/
def gammaRieszDualSeries (a : ℕ → ℝ) (k A x : ℝ) : ℂ :=
  ∑' n : ℕ, gammaRieszDualTerm a k A x n

/-- The actual dual series is absolutely convergent, by the proved sharp coefficient tail and genuine Gamma bound. -/
theorem summable_norm_gammaRieszDualTerm {a : ℕ → ℝ} {k A B x : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hx : 0 < x) :
    Summable (fun n : ℕ => ‖gammaRieszDualTerm a k A x n‖) := by
  obtain ⟨C, _, hC⟩ := exists_gammaRieszDualTerm_bound hk hA
  have hs := (linearPowerTail_summable_bound ha hB hb
    (by norm_num : (1 : ℝ) < 9 / 8) (le_refl (1 : ℕ))).1
  apply (hs.mul_left (C * x ^ (15 / 8 : ℝ))).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), if_pos (by omega : 1 < n)]
  exact hC a x n (ha n) hx (by omega)

/-- The true complex dual terms are summable at every positive parameter. -/
theorem summable_gammaRieszDualTerm {a : ℕ → ℝ} {k A B x : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hx : 0 < x) :
    Summable (gammaRieszDualTerm a k A x) :=
  (summable_norm_gammaRieszDualTerm hk hA ha hB hb hx).of_norm

/-- Absolute convergence justifies the exact second finite difference of the actual dual series. -/
theorem gammaRieszDualSeries_difference {a : ℕ → ℝ} {k A B x h : ℝ}
    (hk : 2 ≤ k) (hA : 0 < A) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hx : 0 < x) (hh : 0 ≤ h) :
    gammaRieszDualSeries a k A (x + 2 * h) - 2 * gammaRieszDualSeries a k A (x + h) +
      gammaRieszDualSeries a k A x =
        ∑' n : ℕ, ((a n / (n : ℝ) : ℝ) : ℂ) * gammaRieszSecondDifference k (A * n) x h := by
  have h0 := summable_gammaRieszDualTerm hk hA ha hB hb hx
  have h1 := summable_gammaRieszDualTerm hk hA ha hB hb (by linarith : 0 < x + h)
  have h2 := summable_gammaRieszDualTerm hk hA ha hB hb (by linarith : 0 < x + 2 * h)
  have hs := (h2.hasSum.sub (h1.hasSum.mul_left (2 : ℂ))).add h0.hasSum
  simp_rw [gammaRieszDualTerm_difference] at hs
  exact hs.tsum_eq.symm

end
end Dubon2026
