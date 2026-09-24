import TaoTrudgianYang2025.ZetaReflectionPatternEntry
import TaoTrudgianYang2025.BourgainBandLogBounds

/-! Rounded dyadic band counts have genuine logarithmic size under a physical power cap. -/

noncomputable section
open Complex Filter MeasureTheory Set RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem reflectionBandCount_le_power_log (S : Finset ℕ) {a B T u : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hT : 1 ≤ T) (hu : 0 ≤ u)
    (hcap : (S.card : ℝ)/a ≤ B*T^u) :
    (reflectionBandCount S a : ℝ) ≤
      2+(Real.log (B+1)+u*Real.log T)/Real.log 2 := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  let m := Nat.ceil ((S.card : ℝ)/a)
  by_cases hm : m = 0
  · simp only [reflectionBandCount,show Nat.ceil ((S.card : ℝ)/a) = 0 from hm,
      Nat.clog_zero_right,Nat.cast_add,Nat.cast_zero,Nat.cast_one]
    have hnon : 0 ≤ (Real.log (B+1)+u*Real.log T)/Real.log 2 := by positivity
    linarith
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hc : (m : ℝ) < (S.card : ℝ)/a+1 := Nat.ceil_lt_add_one (by positivity)
    have hone : 1 ≤ T^u := Real.one_le_rpow hT hu
    have hmb : (m : ℝ) ≤ (B+1)*T^u := by nlinarith
    have hlog : Real.log (m : ℝ) ≤ Real.log (B+1)+u*Real.log T := by
      calc
        _ ≤ Real.log ((B+1)*T^u) := Real.log_le_log hmp hmb
        _ = _ := by
          rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hTp _).ne',
            Real.log_rpow hTp]
    have hb := heathBrown_natCast_clog_two_le_one_add_log m hm1
    have hd := div_le_div_of_nonneg_right hlog hlog2.le
    change ((Nat.clog 2 m+1 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

theorem reflectionBandCount_le_const_log (S : Finset ℕ) {a B T u : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hT : 1 ≤ T) (hlogT : 1 ≤ Real.log T)
    (hu : 0 ≤ u) (hcap : (S.card : ℝ)/a ≤ B*T^u) :
    (reflectionBandCount S a : ℝ) ≤
      (2+(Real.log (B+1)+u)/Real.log 2)*Real.log T := by
  have h := reflectionBandCount_le_power_log S ha hB hT hu hcap
  have hB0 : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 ≤ 2+Real.log (B+1)/Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hlogT hcoef
  calc
    _ ≤ 2+(Real.log (B+1)+u*Real.log T)/Real.log 2 := h
    _ = (2+Real.log (B+1)/Real.log 2)+(u/Real.log 2)*Real.log T := by ring
    _ ≤ (2+Real.log (B+1)/Real.log 2)*Real.log T+(u/Real.log 2)*Real.log T := by
      linarith
    _ = _ := by ring

end TaoTrudgianYang2025
