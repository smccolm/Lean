import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_ratio
    {Q X : ℝ} (hQ : 0 < Q)
    {a q n : ℕ} (ha : 0 < a) (hq : 0 < q) (hn : 0 < n)
    (D : ℝ) (k : ℕ) :
    (((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ)) ^ k *
        (D * (X / a) *
          (2 * ((a : ℝ) / ((q : ℝ) * Q))) ^ 2) ^ k =
      ((D / Real.pi ^ 2) *
        (((a : ℝ) * X) / ((n : ℝ) * Q ^ 2))) ^ k := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hQR : Q ≠ 0 := ne_of_gt hQ
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [← mul_pow]
  congr 1
  field_simp

end RiemannZeta.GuthMaynard
