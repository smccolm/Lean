import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Exact power integrals and lower-order energy remainders, including the logarithmic case -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

theorem integral_power_Ioc_one {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : r ≠ -1) :
    (∫ x in Ioc (1 : ℝ) N, x ^ r) = ((N : ℝ) ^ (r + 1) - 1) / (r + 1) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNr]
  rw [integral_rpow (Or.inr ⟨hr, ?_⟩), Real.one_rpow]
  rw [Set.uIcc_of_le hNr]
  simp

theorem integral_inv_Ioc_one {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioc (1 : ℝ) N, x ^ (-1 : ℝ)) = Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNr]
  simp only [Real.rpow_neg_one]
  rw [integral_inv_of_pos zero_lt_one (by linarith), div_one]

/-- Covers the power, logarithmic and bounded-integral error regimes in one statement. -/
theorem tendsto_power_integral_div_rpow {r d : ℝ} (hd : 0 < d) (hr : r + 1 < d) :
    Tendsto (fun N : ℕ => (∫ x in Ioc (1 : ℝ) N, x ^ r) / (N : ℝ) ^ d)
      atTop (𝓝 0) := by
  by_cases he : r = -1
  · subst r
    have hh := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
    have hn := hh.comp tendsto_natCast_atTop_atTop
    apply hn.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    rw [integral_inv_Ioc_one hN]
    rfl
  · have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (r + 1 - d)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      convert h using 1
      funext N
      congr 1
      ring
    have hinv := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hh := (hpow.sub hinv).div_const (r + 1)
    simp only [sub_self, zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [Function.comp_def]
    rw [integral_power_Ioc_one hN he, Real.rpow_sub hN0, Real.rpow_neg hN0.le]
    field_simp

theorem integral_power_Ioc_one_bound {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : r < -1) :
    0 ≤ (∫ x in Ioc (1 : ℝ) N, x ^ r) ∧
      (∫ x in Ioc (1 : ℝ) N, x ^ r) ≤ 1 / (-r - 1) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp0 : 0 ≤ (N : ℝ) ^ (r + 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hp1 : (N : ℝ) ^ (r + 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  rw [integral_power_Ioc_one hN (ne_of_lt hr)]
  have he : ((N : ℝ) ^ (r + 1) - 1) / (r + 1) =
      (1 - (N : ℝ) ^ (r + 1)) / (-r - 1) := by
    field_simp [show r + 1 ≠ 0 by linarith, show -r - 1 ≠ 0 by linarith]
    ring
  rw [he]
  exact ⟨div_nonneg (sub_nonneg.mpr hp1) (by linarith),
    div_le_div_of_nonneg_right (by linarith : 1 - (N : ℝ) ^ (r + 1) ≤ 1) (by linarith)⟩

end Dubon2026
