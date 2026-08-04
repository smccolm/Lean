import Mathlib
import RiemannZeta.GuthMaynard.ExtractSeparated

open Finset

namespace RiemannZeta.GuthMaynard

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (M : ℕ) :
    (zeroCountRect model σ 1 T (T + M + 1) : ℝ) ≤ ∑ k ∈ Finset.range (M + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction M with
  | zero =>
    have eq_T : T + ↑(0 : ℕ) + 1 = T + 1 := by push_cast; ring
    have eq_k : T + ↑(0 : ℕ) = T := by push_cast; ring
    rw [Finset.sum_range_one]
    rw [eq_T, eq_k]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h_split := zeroCountRect_split model σ 1 T (T + ↑M + 1) (T + ↑(M + 1) + 1)
    have h_cast : (zeroCountRect model σ 1 T (T + ↑(M + 1) + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ↑M + 1) : ℝ) + (zeroCountRect model σ 1 (T + ↑M + 1) (T + ↑(M + 1) + 1) : ℝ) := by exact_mod_cast h_split
    have eq_mid : T + ↑(M + 1) = T + ↑M + 1 := by push_cast; ring
    have h_cast2 : (zeroCountRect model σ 1 T (T + ↑(M + 1) + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ↑M + 1) : ℝ) + (zeroCountRect model σ 1 (T + ↑(M + 1)) (T + ↑(M + 1) + 1) : ℝ) := by
      rw [← eq_mid] at h_cast
      exact h_cast
    linarith

end RiemannZeta.GuthMaynard
