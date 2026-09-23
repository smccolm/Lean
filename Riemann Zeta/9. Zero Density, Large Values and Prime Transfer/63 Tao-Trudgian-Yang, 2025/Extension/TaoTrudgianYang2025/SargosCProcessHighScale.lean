import TaoTrudgianYang2025.SargosCProcessScale

/-! Quantitative high-height control of the actual optimizing scale. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_cap_exponent_bound {k l : ℝ} (h : InExponentPairTriangle k l) :
    (1+5*k-l-k*sargosCProcessThreshold k l)/(1+4*k) ≤ 2/3-1/100 := by
  have hd : 0 < 1+4*k := by linarith [h.1]
  apply (div_le_iff₀ hd).mpr
  have hm := sargosCProcessThreshold_cap_margin h
  have hku := h.2.1
  nlinarith

theorem sargosCProcess_secondary_exponent_bound {k l : ℝ} (h : InExponentPairTriangle k l) :
    13/3 ≤ ((1+k)*sargosCProcessThreshold k l+3+15*k-3*l)/(1+4*k) := by
  have hd : 0 < 1+4*k := by linarith [h.1]
  apply (le_div_iff₀ hd).mpr
  have hm := sargosCProcessThreshold_secondary_margin h
  have hku := h.2.1
  nlinarith

theorem sargosCProcessScale_high_cap {k l T N : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N)
    (hhigh : N^(sargosCProcessThreshold k l) ≤ T) :
    sargosCProcessScale k l T N ≤ N^(2/3-1/100:ℝ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hT : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hhigh
  have hR := sargosCProcessScale_pos (k := k) (l := l) hT hNp
  have hd : 0 < 1+4*k := by linarith [hkl.1]
  have ht := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hhigh
  rw [Real.log_rpow hNp] at ht
  have hkt := mul_le_mul_of_nonneg_left ht hkl.1
  apply (Real.log_le_log_iff hR (Real.rpow_pos_of_pos hNp _)).mp
  rw [sargosCProcessScale_log_physical hkl.1 hT hNp,Real.log_rpow hNp]
  calc
    _ ≤ ((1+5*k-l-k*sargosCProcessThreshold k l)*Real.log N)/(1+4*k) :=
      div_le_div_of_nonneg_right (by nlinarith only [hkt]) hd.le
    _ = ((1+5*k-l-k*sargosCProcessThreshold k l)/(1+4*k))*Real.log N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sargosCProcess_cap_exponent_bound hkl)
      (Real.log_nonneg hN)

theorem sargosCProcessScale_secondary_log {k l T N : ℝ}
    (hk : 0 ≤ k) (hT : 0 < T) (hN : 0 < N) :
    Real.log (T*(sargosCProcessScale k l T N)^3) =
      ((1+k)*Real.log T+(3+15*k-3*l)*Real.log N)/(1+4*k) := by
  have hd : 0 < 1+4*k := by linarith
  have hR := sargosCProcessScale_pos (k := k) (l := l) hT hN
  rw [Real.log_mul hT.ne' (by positivity),Real.log_pow,
    sargosCProcessScale_log_physical hk hT hN]
  field_simp
  ring

theorem sargosCProcessScale_high_secondary {k l T N : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N)
    (hhigh : N^(sargosCProcessThreshold k l) ≤ T) :
    N^(13/3:ℝ) ≤ T*(sargosCProcessScale k l T N)^3 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hT : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hhigh
  have hR := sargosCProcessScale_pos (k := k) (l := l) hT hNp
  have hd : 0 < 1+4*k := by linarith [hkl.1]
  have ht := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hhigh
  rw [Real.log_rpow hNp] at ht
  have hkt := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1+k by linarith [hkl.1])
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hNp _) (by positivity)).mp
  rw [Real.log_rpow hNp,sargosCProcessScale_secondary_log hkl.1 hT hNp]
  calc
    _ ≤ (((1+k)*sargosCProcessThreshold k l+3+15*k-3*l)/(1+4*k))*Real.log N :=
      mul_le_mul_of_nonneg_right (sargosCProcess_secondary_exponent_bound hkl)
        (Real.log_nonneg hN)
    _ = (((1+k)*sargosCProcessThreshold k l+3+15*k-3*l)*Real.log N)/(1+4*k) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hkt]) hd.le

end TaoTrudgianYang2025
