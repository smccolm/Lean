import TaoTrudgianYang2025.AtkinsonPowerGapBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic losses at the physical cutoff

The actual dyadic block count and separated harmonic sum are bounded
uniformly when the retained index is at most the physical height.
-/

noncomputable section

open Filter

namespace TaoTrudgianYang2025

theorem atkinson_clog_le_height_log {H : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H) :
    (Nat.clog 2 N:ℝ) ≤ (1/Real.log 2+1)*Real.log (2*H) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hN0 : N = 0
  · subst N
    simp only [Nat.clog_zero_right, Nat.cast_zero]
    positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hN1)
  have he := Real.natCeil_logb_natCast 2 N
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hceil
  have hl : Real.log (N:ℝ) ≤ Real.log (2*H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hd := div_le_div_of_nonneg_right hl h2.le
  unfold Real.logb at hceil
  calc
    _ ≤ Real.log (2*H)/Real.log 2+Real.log (2*H) := by linarith
    _ = _ := by ring

theorem atkinson_harmonic_le_height_log {H G : ℝ} {N : ℕ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) :
    (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ) ≤ 2*Real.log (2*H) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hs : Real.sqrt (H*(N:ℝ)) ≤ H := by
    apply (Real.sqrt_le_left hH0.le).2
    nlinarith
  have hq : Real.sqrt (H*(N:ℝ))/G ≤ H :=
    (div_le_iff₀ hG0).2 (by nlinarith)
  have hm := atkinson_harmonic_mono (Nat.ceil_mono hq)
  have hc : (Nat.ceil H:ℝ) ≤ 2*H := by
    have hh := Nat.ceil_lt_add_one hH0.le
    linarith
  have hc0 : (0:ℝ) < Nat.ceil H := hH0.trans_le (Nat.le_ceil H)
  have hl := Real.log_le_log hc0 hc
  have hb := harmonic_le_one_add_log (Nat.ceil H)
  linarith

theorem eventually_atkinson_height_log_pow_le_rpow (k : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ H : ℝ in atTop, (Real.log (2*H))^k ≤ H^ν := by
  filter_upwards [eventually_const_log_pow_le_rpow ((2:ℝ)^k) (by positivity) k hν,
    eventually_ge_atTop (2:ℝ)] with H hsmall hH
  have hH0 : 0 < H := by linarith
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hH
  have hlog : Real.log (2*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hp := pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 2*H)) hlog k
  rw [mul_pow] at hp
  exact hp.trans hsmall

end TaoTrudgianYang2025
