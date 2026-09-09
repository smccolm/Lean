import Tao2026.FourierSlices

open Real

#check Real.rpow_neg
#check Real.rpow_natCast
#check Real.rpow_neg_one
#check inv_le_inv₀
#check one_div_le_one_div_of_le
#check pow_le_pow_left₀
#check pow_le_pow_left
#check Real.one_div_rpow
#check Real.rpow_neg_natCast
#check abs_pos.mpr
#check Int.cast_ne_zero.mpr
#check mul_inv_rev₀

theorem test_radial (a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    (2 * Real.pi * a)⁻¹ ^ 3 ≤
      27 * (1 + a + b) ^ (-(3 : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hmul : a ≤ 2 * Real.pi * a := by nlinarith
  have hinv : (2 * Real.pi * a)⁻¹ ≤ a⁻¹ := by
    exact (inv_le_inv₀ (by positivity) ha0).2 hmul
  have hinvpow : (2 * Real.pi * a)⁻¹ ^ 3 ≤ a⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hinv 3
  have hz : 1 + a + b ≤ 3 * a := by nlinarith
  have hzpos : 0 < 1 + a + b := by positivity
  have hpow : (1 + a + b) ^ 3 ≤ (3 * a) ^ 3 :=
    pow_le_pow_left₀ hzpos.le hz 3
  have hinv2 : ((3 * a) ^ 3)⁻¹ ≤ ((1 + a + b) ^ 3)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hscale : a⁻¹ ^ 3 = 27 * ((3 * a) ^ 3)⁻¹ := by
    field_simp
    <;> ring
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc
    (2 * Real.pi * a)⁻¹ ^ 3 ≤ a⁻¹ ^ 3 := hinvpow
    _ = 27 * ((3 * a) ^ 3)⁻¹ := hscale
    _ ≤ 27 * ((1 + a + b) ^ 3)⁻¹ := by positivity
