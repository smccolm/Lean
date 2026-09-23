import TaoTrudgianYang2025.SargosQuarticSourceMoment

/-! Logarithmic normalization and absorption of the genuine source error. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticDualSixthIntegral_le_logN {M : ℕ}
    (hM : 2 ≤ M) {N Δ : ℝ} (hN : 0 < N) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2)
    (hscale : (M:ℝ) ≤ 4*Δ*N) (hMN : (M:ℝ) ≤ N) :
    sargosQuarticDualSixthIntegral M N Δ ≤
      ENNReal.ofReal (15728640*sargosWindowConstant 3 1916928*Δ^4*
        (Real.log N)^6*sargosSixthBaseMoment M) := by
  have hh := sargosQuarticDual_sixth_moment hM hN hΔ hΔ₁ hscale
  have hMp : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 0 ≤ Real.log (M:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hp := pow_le_pow_left₀ hlog (Real.log_le_log hMp hMN) 6
  have hC := sargosWindowConstant_nonneg 3 (by norm_num : (0:ℝ) ≤ 1916928)
  have hI := sargosSixthBaseMoment_nonneg M
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) hI

theorem sargos_sixth_log_absorb_error {N Δ B : ℝ}
    (hN : 2 ≤ N) (hΔ : 0 ≤ Δ) (hB : 1/64 ≤ B) :
    2*Δ ≤ (128/(Real.log 2)^6)*Δ*(Real.log N)^6*B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith only [hN])
  have hlogle : (Real.log 2)^6 ≤ (Real.log N)^6 :=
    pow_le_pow_left₀ hlog2.le (Real.log_le_log (by norm_num) hN) 6
  have hB1 : 1 ≤ 64*B := by linarith only [hB]
  have hh := mul_le_mul_of_nonneg_left hB1 (pow_nonneg hlogN 6)
  have hq : (Real.log 2)^6 ≤ 64*(Real.log N)^6*B := by
    nlinarith only [hlogle,hh]
  have hm := mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hΔ)
  calc
    _ ≤ (128*Δ*(Real.log N)^6*B)/(Real.log 2)^6 := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith only [hm]
    _ = _ := by ring

end TaoTrudgianYang2025
