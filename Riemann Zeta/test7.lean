import Mathlib
import RiemannZeta.GuthMaynard.ExtractSeparated

open Finset

namespace RiemannZeta.GuthMaynard

lemma sum_zeroCountRect_bound (model : ZetaZeroCountModel) (σ T : ℝ) (M : ℕ) :
    (zeroCountRect model σ 1 T (T + M + 1) : ℝ) ≤ ∑ k ∈ Finset.range (M + 1), (zeroCountRect model σ 1 (T + k) (T + k + 1) : ℝ) := by
  induction M with
  | zero =>
    have eq1 : (0 : ℝ) = 0 := rfl
    have eq2 : T + 0 + 1 = T + 1 := by ring
    rw [eq2]
    have eq3 : ∑ k ∈ range 1, (zeroCountRect model σ 1 (T + ↑k) (T + ↑k + 1) : ℝ) = (zeroCountRect model σ 1 T (T + 1) : ℝ) := by
      simp
    rw [eq3]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h_split := zeroCountRect_split model σ 1 T (T + M + 1) (T + M + 1 + 1)
    have eq1 : T + ↑(M + 1) + 1 = T + ↑M + 1 + 1 := by push_cast; ring
    rw [eq1]
    have h_cast : (zeroCountRect model σ 1 T (T + ↑M + 1 + 1) : ℝ) ≤ (zeroCountRect model σ 1 T (T + ↑M + 1) : ℝ) + (zeroCountRect model σ 1 (T + ↑M + 1) (T + ↑M + 1 + 1) : ℝ) := by exact_mod_cast h_split
    linarith

end RiemannZeta.GuthMaynard
