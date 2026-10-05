import DhimanKadiriQuesadaHerrera2026.AFEDigammaNumerics

/-! # Certified numerical constants for the stationary-phase error

The bound uses the existing finite Euler/digamma and logarithm enclosures.
No floating-point evaluation or external numerical certificate is a premise.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The source B-process digamma contribution has a kernel-checked outward decimal bound. -/
theorem stationary_digamma_constant_le :
    2 / Real.pi * (Real.eulerMascheroniConstant + 2 * Real.log 2) ≤ 1.251 := by
  have hγ := euler_constant_upper_finite 7
  have hL := logRationalLower_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 4
  rw [show (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 by norm_num] at hL
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.cast_ofNat, show (7 : ℝ) + 1 = 8 by norm_num] at hγ
  rw [h8] at hγ
  have hc : (∑ n ∈ Finset.range 7, 1 / ((n : ℝ) + 1)) - logRationalLower 4 (1 / 3) +
      1 / (2 * 8) + 1 / (12 * 8 ^ 2) ≤ (1.251 : ℝ) * 3.1415 / 2 := by
    norm_num [logRationalLower, Finset.sum_range_succ]
  have h : 2 * (Real.eulerMascheroniConstant + 2 * Real.log 2) ≤ 1.251 * Real.pi := by
    linarith [Real.pi_gt_d4]
  simpa only [div_mul_eq_mul_div] using (div_le_iff₀ Real.pi_pos).mpr h

end DhimanKadiriQuesadaHerrera2026
