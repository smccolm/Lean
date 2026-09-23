import TaoTrudgianYang2025.SargosCProcessParameters

/-! The optimizing scale is linked to the original real T and N. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosCProcessScale (k l T N : ℝ) : ℝ :=
  (T/N)^(-k/(1+4*k))*N^((1+4*k-l)/(1+4*k))

theorem sargosCProcessScale_pos {k l T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    0 < sargosCProcessScale k l T N := by
  unfold sargosCProcessScale
  positivity

theorem sargosCProcessScale_log {k l T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    Real.log (sargosCProcessScale k l T N) =
      (-k/(1+4*k))*Real.log (T/N)+((1+4*k-l)/(1+4*k))*Real.log N := by
  have hr : 0 < T/N := by positivity
  rw [sargosCProcessScale,Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hr,Real.log_rpow hN]

theorem sargosCProcessScale_log_physical {k l T N : ℝ}
    (hk : 0 ≤ k) (hT : 0 < T) (hN : 0 < N) :
    Real.log (sargosCProcessScale k l T N) =
      ((1+5*k-l)*Real.log N-k*Real.log T)/(1+4*k) := by
  have hd : 0 < 1+4*k := by linarith
  rw [sargosCProcessScale_log hT hN,Real.log_div hT.ne' hN.ne']
  field_simp
  ring

theorem sargosCProcessScale_balance {k l T N : ℝ}
    (hk : 0 ≤ k) (hT : 0 < T) (hN : 0 < N) :
    ((T/N^5)^k*N^l)*(sargosCProcessScale k l T N)^(1+4*k) = N := by
  have hd : 1+4*k ≠ 0 := by linarith
  have hR := sargosCProcessScale_pos (k := k) (l := l) hT hN
  apply Real.log_injOn_pos
    (show 0 < ((T/N^5)^k*N^l)*(sargosCProcessScale k l T N)^(1+4*k) by positivity) hN
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity),Real.log_rpow hN,Real.log_rpow hR,
    sargosCProcessScale_log_physical hk hT hN,
    Real.log_div hT.ne' (by positivity),Real.log_pow]
  field_simp
  ring

theorem sargosCProcessScale_cost {k l T N : ℝ}
    (hk : 0 ≤ k) (hT : 0 < T) (hN : 0 < N) :
    N^12/sargosCProcessScale k l T N =
      ((T/N)^(sargosCProcessK k)*N^(sargosCProcessL k l))^12 := by
  have hd : 1+4*k ≠ 0 := by linarith
  have hR := sargosCProcessScale_pos (k := k) (l := l) hT hN
  have hr : 0 < T/N := by positivity
  apply Real.log_injOn_pos
    (show 0 < N^12/sargosCProcessScale k l T N by positivity)
    (show 0 < ((T/N)^(sargosCProcessK k)*N^(sargosCProcessL k l))^12 by positivity)
  rw [Real.log_div (by positivity) hR.ne',Real.log_pow,
    sargosCProcessScale_log hT hN,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_rpow hr,Real.log_rpow hN]
  unfold sargosCProcessK sargosCProcessL
  field_simp
  ring

theorem sargosCProcessScale_le_scale {k l T N : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N) (hNT : N ≤ T) :
    sargosCProcessScale k l T N ≤ N := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hd : 0 < 1+4*k := by linarith [hkl.1]
  have hr : 1 ≤ T/N := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNT)
  have hfirst : (T/N)^(-k/(1+4*k)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr
      (div_nonpos_of_nonpos_of_nonneg (by linarith [hkl.1]) hd.le)
  have hsecond : N^((1+4*k-l)/(1+4*k)) ≤ N := by
    calc
      _ ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        ((div_le_iff₀ hd).mpr (by linarith [hkl.2.2.1]))
      _ = _ := Real.rpow_one _
  unfold sargosCProcessScale
  exact (mul_le_mul_of_nonneg_right hfirst (by positivity)).trans (by simpa only [one_mul] using hsecond)

end TaoTrudgianYang2025
