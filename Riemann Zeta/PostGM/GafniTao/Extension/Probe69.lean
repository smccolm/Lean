import GafniTao.WooleyInitialConditioning

open Finset
open scoped BigOperators

theorem probe_real_add_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℕ} (hs : 1 ≤ s) :
    (a + b) ^ s ≤ 2 ^ (s - 1) * (a ^ s + b ^ s) := by
  let aa : NNReal := ⟨a, ha⟩
  let bb : NNReal := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow aa bb
    (p := (s : ℝ)) (by exact_mod_cast hs)
  norm_cast at h
  simpa [aa, bb, Real.rpow_natCast] using h

#check pow_le_pow_left₀
#check pow_le_pow_left
#check pow_le_pow_right₀
#check mul_le_mul_of_nonneg_left
#check Real.rpow_le_rpow_of_exponent_le
#check Real.rpow_add
#check Real.rpow_neg
#check Real.rpow_natCast
#check Nat.ceil_le
#check Nat.le_ceil
#check Real.rpow_le_rpow
#check Real.rpow_le_rpow_of_exponent_nonpos
#check Real.rpow_le_rpow_of_exponent_nonneg
#check Real.rpow_mul
#check Real.rpow_zero
