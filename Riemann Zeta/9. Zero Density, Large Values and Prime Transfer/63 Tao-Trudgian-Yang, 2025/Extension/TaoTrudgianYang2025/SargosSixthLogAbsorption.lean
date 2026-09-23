import TaoTrudgianYang2025.SargosSixthExponentAlgebra

/-! A global logarithmic-loss estimate, including the finite initial range. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargos_log_six_le_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    (1+Real.log x)^6 ≤ (1+6/ε)^6*x^ε := by
  have hxp : 0 < x := by linarith only [hx]
  have hη : 0 < ε/6 := by positivity
  have hlog := Real.log_le_rpow_div hxp.le hη
  have hpow := Real.one_le_rpow hx hη.le
  have hinv : 1/(ε/6) = 6/ε := by field_simp
  have hb : 1+Real.log x ≤ (1+6/ε)*x^(ε/6) := by
    calc
      _ ≤ x^(ε/6)+x^(ε/6)/(ε/6) := add_le_add hpow hlog
      _ = x^(ε/6)+(1/(ε/6))*x^(ε/6) := by ring
      _ = _ := by rw [hinv]; ring
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hh := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ 1+Real.log x) hb 6
  have he : (x^(ε/6))^6 = x^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hxp.le]
    congr 1
    norm_num
  simpa only [mul_pow,he] using hh

end TaoTrudgianYang2025
