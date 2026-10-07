import Dubon2026.PowerSumIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-! # The exact leading asymptotic of real power sums for every exponent greater than -1 -/

namespace Dubon2026

open Filter
open scoped Topology

theorem power_sum_normalized_error {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : -1 < r) :
    |(∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) / (N : ℝ) ^ (r + 1) - 1 / (r + 1)| ≤
      (1 + 1 / (r + 1)) / (N : ℝ) ^ (r + 1) + 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hN0 (r + 1)
  have hh := div_le_div_of_nonneg_right (abs_power_sum_sub_main hN hr) hp.le
  have he : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) / (N : ℝ) ^ (r + 1) - 1 / (r + 1) =
      ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) - (N : ℝ) ^ (r + 1) / (r + 1)) /
        (N : ℝ) ^ (r + 1) := by field_simp
  rw [he, abs_div, abs_of_pos hp]
  convert hh using 1
  rw [Real.rpow_add_one hN0.ne']
  field_simp [(Real.rpow_pos_of_pos hN0 r).ne', hN0.ne']
  ring

theorem tendsto_power_sum_ratio {r : ℝ} (hr : -1 < r) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ r) /
      (N : ℝ) ^ (r + 1)) atTop (𝓝 (1 / (r + 1))) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (r + 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => (1 + 1 / (r + 1)) / (N : ℝ) ^ (r + 1) +
      1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using
      (hp.const_div_atTop (1 + 1 / (r + 1))).add
        (tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall (fun _ => norm_nonneg _))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact power_sum_normalized_error hN hr

theorem tendsto_nat_div_natCast_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  have hh := (tendsto_nat_floor_mul_div_atTop
    (div_pos zero_lt_one (by exact_mod_cast hd) : (0 : ℝ) < 1 / d).le).comp
    tendsto_natCast_atTop_atTop
  convert hh using 1
  ext N
  simp only [Function.comp_apply]
  rw [one_div, mul_comm, ← div_eq_mul_inv, Nat.floor_div_eq_div]

end Dubon2026
