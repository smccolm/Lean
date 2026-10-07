import Dubon2026.RankinSelbergInputBridge

/-! # Weighted coefficient asymptotics from a genuine linear mean -/

namespace Dubon2026

open Filter Set MeasureTheory Asymptotics
open scoped Topology

noncomputable section

/-- An actual o(x) square-sum remainder is bounded everywhere above one by a constant plus εx. -/
theorem squareSummatory_error_affine_bound {a : ℕ → ℂ} {c : ℝ}
    (hR : (fun x : ℝ => squareSummatory a x - c * x) =o[atTop] (fun x : ℝ => x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C + ε * x := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hR.bound hε)
  obtain ⟨M, hM⟩ := exists_nat_ge (max T 1)
  let C := squareSummatory a M + |c| * M
  have hC : 0 ≤ C := add_nonneg (squareSummatory_nonneg a M) (by positivity)
  refine ⟨C, hC, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  by_cases hxM : (M : ℝ) ≤ x
  · have hh := hT x ((le_max_left T 1).trans (hM.trans hxM))
    simp only [Real.norm_eq_abs, abs_of_nonneg hx0] at hh
    exact hh.trans (by linarith)
  · have hs := squareSummatory_mono a (le_of_not_ge hxM)
    have hb := abs_sub (squareSummatory a x) (c * x)
    rw [abs_of_nonneg (squareSummatory_nonneg a x), abs_mul, abs_of_nonneg hx0] at hb
    have hc := mul_le_mul_of_nonneg_left (le_of_not_ge hxM) (abs_nonneg c)
    dsimp only [C]
    nlinarith [mul_nonneg hε.le hx0]

/-- Abel summation retains both pieces of a constant-plus-linear remainder majorant. -/
theorem weighted_energy_error_bound_affine {a : ℕ → ℂ} {c C ε : ℝ}
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C + ε * x)
    {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    |coefficientEnergy a N σ - weightedEnergyMain c N σ| ≤
      C * ((N : ℝ) ^ (-2 * σ) + 2 * |σ| * ∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ - 1)) +
      ε * ((N : ℝ) ^ (1 - 2 * σ) + 2 * |σ| * ∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hterm : |(squareSummatory a N - c * N) * (N : ℝ) ^ (-2 * σ)| ≤
      C * (N : ℝ) ^ (-2 * σ) + ε * (N : ℝ) ^ (1 - 2 * σ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
    calc
      _ ≤ (C + ε * N) * (N : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right (he N (by exact_mod_cast hN)) (Real.rpow_nonneg hN0.le _)
      _ = _ := by
        rw [add_mul, mul_assoc, mul_comm (N : ℝ), ← Real.rpow_add_one hN0.ne']
        rw [show -2 * σ + 1 = 1 - 2 * σ by ring]
  have hiC := ((integrableOn_power_Icc_one N (-2 * σ - 1)).mono_set Ioc_subset_Icc_self).const_mul C
  have hiε := ((integrableOn_power_Icc_one N (-2 * σ)).mono_set Ioc_subset_Icc_self).const_mul ε
  have hint : |∫ x in Ioc (1 : ℝ) N,
      (squareSummatory a x - c * x) * x ^ (-2 * σ - 1)| ≤
      C * (∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ - 1)) +
      ε * (∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hiC hiε, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hiC.add hiε)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ (C + ε * x) * x ^ (-2 * σ - 1) :=
        mul_le_mul_of_nonneg_right (he x hx.1.le) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [add_mul, mul_assoc, mul_power_sub_one hx0]; rfl
  rw [coefficientEnergy_sub_main a hN]
  apply (abs_add_le _ _).trans
  rw [abs_mul (2 * σ), abs_mul (2 : ℝ) σ, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hh := add_le_add hterm (mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 2 * |σ|))
  convert hh using 1
  ring

/-- The exact power integral divided by its own growth power tends to the reciprocal exponent. -/
theorem tendsto_power_integral_div_same_rpow {d : ℝ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (∫ x in Ioc (1 : ℝ) N, x ^ (d - 1)) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / d)) := by
  have hz := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (hz.const_sub 1).div_const d
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [Function.comp_def]
  rw [integral_power_Ioc_one hN (by linarith), sub_add_cancel, Real.rpow_neg hN0.le]
  field_simp

/-- The genuine o(x) remainder suffices for the source's entire left weighted-energy asymptotic. -/
theorem weighted_energy_left_of_linear_littleO {a : ℕ → ℂ} {c σ : ℝ}
    (hR : (fun x : ℝ => squareSummatory a x - c * x) =o[atTop] (fun x : ℝ => x))
    (hσ : σ < 1 / 2) :
    Tendsto (fun N : ℕ => (coefficientEnergy a N σ -
      c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) / (N : ℝ) ^ (1 - 2 * σ))
      atTop (𝓝 0) := by
  have hd : 0 < 1 - 2 * σ := by linarith
  have hrem : Tendsto (fun N : ℕ => (coefficientEnergy a N σ - weightedEnergyMain c N σ) /
      (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    let K : ℝ := 1 + 2 * |σ| / (1 - 2 * σ)
    have hK : 0 < K := by dsimp [K]; positivity
    let ε : ℝ := δ / (2 * K)
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨C, _, he⟩ := squareSummatory_error_affine_bound hR hε
    have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-2 * σ) / (N : ℝ) ^ (1 - 2 * σ))
        atTop (𝓝 (0 : ℝ)) := by
      have hh := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      apply hh.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      dsimp only [Function.comp_def]
      rw [← Real.rpow_sub hN0]
      congr 1
      ring
    have hi1 := tendsto_power_integral_div_rpow (r := -2 * σ - 1) hd (by linarith)
    have hi2 : Tendsto (fun N : ℕ => (∫ x in Ioc (1 : ℝ) N, x ^ (-2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 (1 / (1 - 2 * σ))) := by
      simpa only [show (1 - 2 * σ) - 1 = -2 * σ by ring] using
        tendsto_power_integral_div_same_rpow hd
    have hu := ((ht.add (hi1.const_mul (2 * |σ|))).const_mul C).add
      (((hi2.const_mul (2 * |σ|)).const_add 1).const_mul ε)
    simp only [mul_zero, add_zero, zero_add] at hu
    have hlim : ε * (1 + 2 * |σ| * (1 / (1 - 2 * σ))) < δ := by
      have hsame : ε * (1 + 2 * |σ| * (1 / (1 - 2 * σ))) = δ / 2 := by
        dsimp [ε, K]
        field_simp
      rw [hsame]
      linarith
    filter_upwards [hu.eventually (Iio_mem_nhds hlim), eventually_ge_atTop (1 : ℕ)] with N hsmall hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hp := Real.rpow_pos_of_pos hN0 (1 - 2 * σ)
    have hb := div_le_div_of_nonneg_right (weighted_energy_error_bound_affine he hN σ) hp.le
    simp only [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hp]
    apply lt_of_le_of_lt hb
    convert hsmall using 1
    field_simp [hp.ne']
  have hg := (tendsto_rpow_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hrem.add (hg.const_div_atTop (-(2 * σ * c / (1 - 2 * σ))))
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hm := weightedEnergyMain_sub_leading hN (ne_of_lt hσ) c
  dsimp only [Function.comp_def]
  rw [← add_div]
  congr 1
  linarith

end
end Dubon2026
