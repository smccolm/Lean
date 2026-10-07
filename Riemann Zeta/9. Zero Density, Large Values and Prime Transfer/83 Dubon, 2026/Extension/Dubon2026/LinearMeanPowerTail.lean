import Dubon2026.LinearMeanPowerBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Genuine infinite weighted tails from a linear coefficient mean -/

namespace Dubon2026

noncomputable section

/-- Every finite subset of the actual weighted tail is bounded by one exact interval tail. -/
theorem linearPowerTail_finset_le {c : ℕ → ℝ} {B p : ℝ} (hc : ∀ n, 0 ≤ c n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N)
    (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) (u : Finset ℕ) :
    (∑ n ∈ u, if N < n then c n * (n : ℝ) ^ (-p) else 0) ≤
      B * (1 + p / (p - 1)) * (N : ℝ) ^ (1 - p) := by
  let M := max N (u.sup id)
  have hsub : u.filter (fun n => N < n) ⊆ Finset.Ioc N M := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn'.2, (Finset.le_sup (f := id) hn'.1).trans (le_max_right _ _)⟩
  rw [← Finset.sum_filter]
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => mul_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans
  exact linearPowerTail_le hc hB hb hp hN (le_max_left _ _)

/-- The real weighted tail is summable, with the sharp exponent inherited from the actual linear mean. -/
theorem linearPowerTail_summable_bound {c : ℕ → ℝ} {B p : ℝ} (hc : ∀ n, 0 ≤ c n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, c n) ≤ B * N)
    (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => if N < n then c n * (n : ℝ) ^ (-p) else 0) ∧
      (∑' n : ℕ, if N < n then c n * (n : ℝ) ^ (-p) else 0) ≤
        B * (1 + p / (p - 1)) * (N : ℝ) ^ (1 - p) := by
  have hn : ∀ n : ℕ, 0 ≤ (if N < n then c n * (n : ℝ) ^ (-p) else 0) := by
    intro n
    split_ifs
    · exact mul_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact le_rfl
  have hs := summable_of_sum_le hn (linearPowerTail_finset_le hc hB hb hp hN)
  exact ⟨hs, hs.tsum_le_of_sum_le (linearPowerTail_finset_le hc hB hb hp hN)⟩

end
end Dubon2026
