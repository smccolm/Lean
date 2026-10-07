import Dubon2026.PowerSumLimit

/-! # Power sums at the exact natural-division cutoff in Möbius inversion -/

namespace Dubon2026

open Filter
open scoped Topology

theorem tendsto_nat_div_fixed {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => N / d) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (n * d)] with N hN
  exact (Nat.le_div_iff_mul_le hd).mpr hN

theorem tendsto_scaled_power_sum {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : -1 < r) :
    Tendsto (fun N : ℕ => (d : ℝ) ^ r *
      (∑ n ∈ Finset.Icc 1 (N / d), (n : ℝ) ^ r) / (N : ℝ) ^ (r + 1))
      atTop (𝓝 (1 / ((d : ℝ) * (r + 1)))) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hh := (tendsto_power_sum_ratio hr).comp (tendsto_nat_div_fixed hd)
  have hp := (tendsto_nat_div_natCast_ratio hd).rpow_const
    (Or.inr (by linarith : 0 ≤ r + 1))
  have ht := (hh.mul hp).const_mul ((d : ℝ) ^ r)
  have hc : (d : ℝ) ^ r * (1 / (r + 1) * (1 / (d : ℝ)) ^ (r + 1)) =
      1 / ((d : ℝ) * (r + 1)) := by
    rw [Real.div_rpow zero_le_one hdr.le, Real.one_rpow, Real.rpow_add_one hdr.ne']
    field_simp [(Real.rpow_pos_of_pos hdr r).ne', hdr.ne']
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hN
  have hk0 : (0 : ℝ) < (N / d : ℕ) := by
    exact_mod_cast (Nat.div_pos hN hd)
  simp only [Function.comp_apply]
  rw [Real.div_rpow hk0.le hN0.le]
  field_simp [(Real.rpow_pos_of_pos hk0 (r + 1)).ne']

end Dubon2026
