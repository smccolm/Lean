import Tao2026.TypeIIKernel

/-!
# Type II logarithmic exponent arithmetic

This module records the exact real-power bookkeeping behind the source's
high-frequency condition `F > log^(C A) P`.  It contains no exponential-sum
estimate: it converts a proved lower bound for `F` into the logarithmic saving
required after the Type II distance-kernel summation.
-/

namespace Tao2026

/-- A power lower bound for the frequency absorbs a positive logarithmic
factor against `F⁻ᶜ`, with every exponent displayed explicitly. -/
theorem rpow_mul_frequencyDecay_le
    {ℓ F b c d t : ℝ} (hℓ : 1 ≤ ℓ) (hFd : ℓ ^ d ≤ F)
    (hc : 0 ≤ c) (hexponent : b + t ≤ d * c) :
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ (-t) := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hbasepos : 0 < ℓ ^ d := Real.rpow_pos_of_pos hℓpos d
  have hdecay : F ^ (-c) ≤ (ℓ ^ d) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hFd (neg_nonpos.mpr hc)
  calc
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ b * (ℓ ^ d) ^ (-c) :=
      mul_le_mul_of_nonneg_left hdecay
        (Real.rpow_nonneg (zero_le_one.trans hℓ) _)
    _ = ℓ ^ (b - d * c) := by
      rw [← Real.rpow_mul (zero_le_one.trans hℓ) d (-c),
        ← Real.rpow_add hℓpos]
      congr 1
      ring
    _ ≤ ℓ ^ (-t) :=
      Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)

/-- Direct exponent subtraction for two powers of the same logarithmic base. -/
theorem rpow_mul_rpow_neg_le
    {ℓ b d t : ℝ} (hℓ : 1 ≤ ℓ) (hexponent : b + t ≤ d) :
    ℓ ^ b * ℓ ^ (-d) ≤ ℓ ^ (-t) := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  rw [← Real.rpow_add hℓpos]
  exact Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)

/-- The strict high-frequency inequality used in the source supplies the weak
power lower bound needed by `rpow_mul_frequencyDecay_le`. -/
theorem rpow_mul_frequencyDecay_le_of_lt
    {ℓ F b c d t : ℝ} (hℓ : 1 ≤ ℓ) (hFd : ℓ ^ d < F)
    (hc : 0 ≤ c) (hexponent : b + t ≤ d * c) :
    ℓ ^ b * F ^ (-c) ≤ ℓ ^ (-t) :=
  rpow_mul_frequencyDecay_le hℓ hFd.le hc hexponent

/-- Source-facing specialization with the logarithmic base `log P`.  The
explicit threshold `exp 1 ≤ P` is exactly what guarantees `1 ≤ log P`. -/
theorem log_rpow_mul_frequencyDecay_le
    {P F b c d t : ℝ} (hP : Real.exp 1 ≤ P)
    (hFd : (Real.log P) ^ d ≤ F) (hc : 0 ≤ c)
    (hexponent : b + t ≤ d * c) :
    (Real.log P) ^ b * F ^ (-c) ≤ (Real.log P) ^ (-t) := by
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hP
  have hlog : 1 ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).2 hP
  exact rpow_mul_frequencyDecay_le hlog hFd hc hexponent

/-- Strict source high-frequency version of
`log_rpow_mul_frequencyDecay_le`. -/
theorem log_rpow_mul_frequencyDecay_le_of_lt
    {P F b c d t : ℝ} (hP : Real.exp 1 ≤ P)
    (hFd : (Real.log P) ^ d < F) (hc : 0 ≤ c)
    (hexponent : b + t ≤ d * c) :
    (Real.log P) ^ b * F ^ (-c) ≤ (Real.log P) ^ (-t) :=
  log_rpow_mul_frequencyDecay_le hP hFd.le hc hexponent

end Tao2026
