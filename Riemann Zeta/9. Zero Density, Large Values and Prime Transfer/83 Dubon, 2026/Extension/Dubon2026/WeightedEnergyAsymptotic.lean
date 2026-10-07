import Dubon2026.WeightedEnergyError

/-! # The sharp left and central weighted energies from a Rankin–Selberg remainder -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem weightedEnergyMain_sub_leading {N : ℕ} (hN : 1 ≤ N) {σ : ℝ}
    (hσ : σ ≠ 1 / 2) (c : ℝ) :
    weightedEnergyMain c N σ - c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ) =
      -(2 * σ * c / (1 - 2 * σ)) := by
  rw [weightedEnergyMain, integral_power_Ioc_one hN (by intro h; apply hσ; linarith : -2 * σ ≠ -1)]
  have he : -2 * σ + 1 = 1 - 2 * σ := by ring
  rw [he]
  field_simp [show 1 - 2 * σ ≠ 0 by intro h; apply hσ; linarith]
  ring

theorem weightedEnergyMain_center {N : ℕ} (hN : 1 ≤ N) (c : ℝ) :
    weightedEnergyMain c N (1 / 2) = c + c * Real.log N := by
  unfold weightedEnergyMain
  norm_num only
  rw [Real.rpow_zero, mul_one, integral_inv_Ioc_one hN]
  ring

theorem tendsto_weighted_energy_remainder {a : ℕ → ℂ} {c C β σ : ℝ}
    (hβ : β < 1) (hσ : σ < 1 / 2)
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β) :
    Tendsto (fun N : ℕ => (coefficientEnergy a N σ - weightedEnergyMain c N σ) /
      (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) := by
  have hterm : Tendsto (fun N : ℕ => (N : ℝ) ^ (β - 2 * σ) /
      (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [Function.comp_def]
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  have hint := tendsto_power_integral_div_rpow
    (r := β - 2 * σ - 1) (d := 1 - 2 * σ) (by linarith) (by linarith)
  have hbound := (hterm.add (hint.const_mul (2 * |σ|))).const_mul C
  simp only [mul_zero, add_zero] at hbound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := Real.rpow_pos_of_pos hN0 (1 - 2 * σ)
  have hh := div_le_div_of_nonneg_right (weighted_energy_error_bound he hN σ) hp.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
  convert hh using 1
  ring

theorem weighted_energy_left_of_remainder {a : ℕ → ℂ} {c C β σ : ℝ}
    (hβ : β < 1) (hσ : σ < 1 / 2)
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β) :
    Tendsto (fun N : ℕ => (coefficientEnergy a N σ -
      c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * σ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_weighted_energy_remainder hβ hσ he).add
    (hp.const_div_atTop (-(2 * σ * c / (1 - 2 * σ))))
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hm := weightedEnergyMain_sub_leading hN (ne_of_lt hσ) c
  rw [← add_div]
  congr 1
  linarith

theorem weighted_energy_center_of_remainder {a : ℕ → ℂ} {c C β : ℝ}
    (hC : 0 ≤ C) (hβ : β < 1)
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β)
    {N : ℕ} (hN : 1 ≤ N) :
    |coefficientEnergy a N (1 / 2) - c * Real.log N| ≤ |c| + C * (1 + 1 / (1 - β)) := by
  have hh := weighted_energy_error_bound he hN (1 / 2)
  norm_num only at hh
  simp only [one_mul] at hh
  have hp : (N : ℝ) ^ (β - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
  have hi := (integral_power_Ioc_one_bound hN (r := β - 2) (by linarith)).2
  have heq : β - 1 - 1 = β - 2 := by ring
  rw [heq] at hh
  have hden : -(β - 2) - 1 = 1 - β := by ring
  rw [hden] at hi
  have hu := hh.trans (mul_le_mul_of_nonneg_left (add_le_add hp hi) hC)
  rw [weightedEnergyMain_center hN c] at hu
  have hid : coefficientEnergy a N (1 / 2) - c * Real.log N =
      (coefficientEnergy a N (1 / 2) - (c + c * Real.log N)) + c := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

end

end Dubon2026
