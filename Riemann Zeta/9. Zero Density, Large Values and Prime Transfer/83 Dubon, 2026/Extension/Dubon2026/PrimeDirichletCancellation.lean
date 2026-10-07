import Dubon2026.SignedWienerTransfer
import Dubon2026.WeightedPrimeAverages

/-! # Boundary continuation of the actual prime Dirichlet series implies cancellation -/

namespace Dubon2026

open Filter ArithmeticFunction
open scoped Topology

noncomputable section

/-- The actual prime-supported logarithmic coefficients of a real prime sequence. -/
def primeLogCoefficients (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime n then u n * Real.log n else 0

/-- A genuine prime bound gives domination by the actual von Mangoldt function. -/
theorem abs_primeLogCoefficients_le {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ p, Nat.Prime p → |u p| ≤ C) (n : ℕ) :
    |primeLogCoefficients u n| ≤ C * vonMangoldt n := by
  by_cases hn : Nat.Prime n
  · rw [primeLogCoefficients, if_pos hn, abs_mul,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn.one_le)), vonMangoldt_apply_prime hn]
    exact mul_le_mul_of_nonneg_right (hu n hn) (Real.log_nonneg (by exact_mod_cast hn.one_le))
  · rw [primeLogCoefficients, if_neg hn, abs_zero]
    exact mul_nonneg hC vonMangoldt_nonneg

/-- The actual inclusive prime logarithmic sum is the next prefix sum of the genuine coefficient sequence. -/
theorem sum_primeLogCoefficients (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), primeLogCoefficients u n) =
      ∑ p ∈ Nat.primesLE N, u p * Real.log p := by
  rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rfl

/-- A displayed continuous extension of the genuine prime-supported L-series to Re(s)=1 forces its actual ordinary prime average to vanish. -/
theorem prime_average_zero_of_boundary_continuation {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ p, Nat.Prime p → |u p| ≤ C) (G : ℂ → ℂ)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hseries : Set.EqOn G (LSeries (fun n => (primeLogCoefficients u n : ℂ))) {s | 1 < s.re}) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N) atTop (𝓝 0) := by
  have ht := signed_wiener_vonMangoldt_cancellation hC (abs_primeLogCoefficients_le hC hu) G hG hseries
  have hnext : Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, u p * Real.log p) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have he := ht.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), primeLogCoefficients u n) /
      ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) at he
    simpa only [sum_primeLogCoefficients] using he
  have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have he : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
    apply he.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    rw [add_div, div_self hn]
  apply prime_average_zero_of_log_weighted hu
  have he := hnext.mul hratio
  simp only [zero_mul] at he
  apply he.congr
  intro N
  have hn : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]

end
end Dubon2026
