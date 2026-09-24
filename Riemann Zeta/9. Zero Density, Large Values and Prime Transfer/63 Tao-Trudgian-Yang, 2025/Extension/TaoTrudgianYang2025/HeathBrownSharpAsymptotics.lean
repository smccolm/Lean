import TaoTrudgianYang2025.HeathBrownSharpFinite
import TaoTrudgianYang2025.ZetaSourceLogScales

/-! Uniform absorption of the actual sharp Gram near-row losses. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem heathBrown_near_value_factor {N : ℝ} (hN : 1 ≤ N) :
    4*N*(2+200*Real.sqrt (N^(7/5 : ℝ))) ≤ 808*N^(17/10 : ℝ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hs : Real.sqrt (N^(7/5 : ℝ)) = N^(7/10 : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hNp.le]
    norm_num
  have hone : 1 ≤ N^(7/10 : ℝ) := Real.one_le_rpow hN (by norm_num)
  rw [hs]
  calc
    _ ≤ 808*(N*N^(7/10 : ℝ)) := by nlinarith
    _ = _ := by
      rw [show (17/10 : ℝ) = 1+7/10 by norm_num,Real.rpow_add hNp,Real.rpow_one]

theorem eventually_heathBrown_near_value_factor :
    ∀ᶠ N : ℝ in atTop,
      4*N*(2+200*Real.sqrt (N^(7/5 : ℝ))) ≤ N^(171/100 : ℝ) := by
  filter_upwards [eventually_const_log_pow_le_rpow 808 (by norm_num) 0
    (η := 1/100) (by norm_num),eventually_ge_atTop (1 : ℝ)] with N hsmall hN
  norm_num only [pow_zero,mul_one] at hsmall
  calc
    _ ≤ 808*N^(17/10 : ℝ) := heathBrown_near_value_factor hN
    _ ≤ N^(1/100 : ℝ)*N^(17/10 : ℝ) :=
      mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [← Real.rpow_add (by linarith : 0 < N)]; norm_num

theorem eventually_heathBrown_diagonal_factor {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop,
      8*N*(2*N+24*Real.pi*N*(harmonic (Nat.ceil (N^(7/5 : ℝ))) : ℝ)) ≤
        N^(2+η) := by
  filter_upwards [eventually_const_log_pow_le_rpow (16+768*Real.pi) (by positivity) 1 hη,
    eventually_ge_atTop (2 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with N hsmall hN hlog
  have hNp : 0 < N := by linarith
  have hL : 1 ≤ N^(7/5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hc : (Nat.ceil (N^(7/5 : ℝ)) : ℝ) ≤ 2*N^(7/5 : ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (7/5))
    linarith
  have hc0 : (0 : ℝ) < Nat.ceil (N^(7/5 : ℝ)) :=
    (Real.rpow_pos_of_pos hNp _).trans_le (Nat.le_ceil _)
  have hl := Real.log_le_log hc0 hc
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
    Real.log_rpow hNp] at hl
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hh : (harmonic (Nat.ceil (N^(7/5 : ℝ))) : ℝ) ≤ 4*Real.log N := by
    have hb := harmonic_le_one_add_log (Nat.ceil (N^(7/5 : ℝ)))
    linarith
  have hdiag :
      8*N*(2*N+24*Real.pi*N*(harmonic (Nat.ceil (N^(7/5 : ℝ))) : ℝ)) ≤
        N^2*((16+768*Real.pi)*Real.log N) := by
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 192*Real.pi*N^2)
    have hn := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 16*N^2)
    nlinarith
  norm_num only [pow_one] at hsmall
  calc
    _ ≤ N^2*((16+768*Real.pi)*Real.log N) := hdiag
    _ ≤ N^2*N^η := mul_le_mul_of_nonneg_left hsmall (sq_nonneg N)
    _ = _ := by rw [Real.rpow_add hNp,Real.rpow_two]

end TaoTrudgianYang2025
