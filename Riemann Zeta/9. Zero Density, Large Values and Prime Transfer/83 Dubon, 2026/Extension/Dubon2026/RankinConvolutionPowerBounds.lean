import Dubon2026.LinearMeanPowerTail
import Dubon2026.RankinConvolutionEnergy

/-! # Sharp actual Rankin convolution coefficient sums for the low/high dual split -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The proved actual Rankin convolution mean gives both exact coefficient powers, including convergence of the high tail. -/
theorem exists_rankinConvolution_power_bounds {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re * (n : ℝ) ^ (-(5 / 8 : ℝ))) ≤
          C * (N : ℝ) ^ (3 / 8 : ℝ) ∧
      Summable (fun n : ℕ => if N < n then
        (rankinConvolutionCoefficients f n).re * (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ∧
      (∑' n : ℕ, if N < n then (rankinConvolutionCoefficients f n).re *
        (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ≤ C * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := exists_rankinConvolution_sum_upper f hk
  have hc0 : (rankinConvolutionCoefficients f 0).re = 0 := by simp [rankinConvolutionCoefficients_zero]
  have hb' (N : ℕ) : (∑ n ∈ Finset.Icc 0 N, (rankinConvolutionCoefficients f n).re) ≤ B * N := by
    rw [sum_Icc_zero_eq_positive hc0]
    exact hb N
  refine ⟨10 * B, by positivity, fun N hN => ?_⟩
  have hl := linearPowerSum_le hc0 hB.le hb' (by norm_num : (0 : ℝ) < 5 / 8)
    (by norm_num : (5 / 8 : ℝ) < 1) hN
  rw [sum_Icc_zero_eq_positive (by simp only [hc0, zero_mul])] at hl
  have ht := linearPowerTail_summable_bound (rankinConvolutionCoefficients_re_nonneg f) hB.le hb'
    (by norm_num : (1 : ℝ) < 9 / 8) hN
  norm_num at hl ht
  refine ⟨?_, ht.1, ?_⟩
  · exact hl.trans (by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 8 : ℝ)])
  · convert ht.2 using 1
    ring

end
end Dubon2026
