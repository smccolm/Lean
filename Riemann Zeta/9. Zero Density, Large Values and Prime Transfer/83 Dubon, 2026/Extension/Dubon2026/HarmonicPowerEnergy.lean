import Dubon2026.PotentialPointwise
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Harmonic majorants for the genuine global coefficient energy -/

namespace Dubon2026

open Filter
open scoped Topology

theorem real_power_le_harmonic_weight {x X r : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) :
    x ^ r ≤ X ^ (max (r + 1) 0) * x⁻¹ := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : x ^ (r + 1) ≤ X ^ (max (r + 1) 0) := by
    by_cases hr : 0 ≤ r + 1
    · rw [max_eq_left hr]
      exact Real.rpow_le_rpow hx0.le hxX hr
    · rw [max_eq_right (le_of_not_ge hr), Real.rpow_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (le_of_not_ge hr)
  calc
    x ^ r = x ^ (r + 1) * x⁻¹ := by rw [Real.rpow_add_one hx0.ne']; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hx0.le)

theorem coefficientEnergy_le_power_harmonic {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    (N : ℕ) (σ : ℝ) :
    coefficientEnergy a N σ ≤ (N : ℝ) ^ (max (-2 * σ + 1) 0) * (harmonic N : ℝ) := by
  rw [coefficientEnergy]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        (N : ℝ) ^ (max (-2 * σ + 1) 0) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hs : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a n), ha n]
      calc
        _ ≤ (n : ℝ) ^ (-2 * σ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
            (Real.rpow_nonneg (Nat.cast_nonneg n) (-2 * σ))
        _ ≤ _ := real_power_le_harmonic_weight (by exact_mod_cast hn'.1)
          (by exact_mod_cast hn'.2)
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem one_le_real_harmonic {N : ℕ} (hN : 1 ≤ N) : 1 ≤ (harmonic N : ℝ) := by
  have hh := Finset.single_le_sum (fun n (_ : n ∈ Finset.Icc 1 N) =>
    inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
    (show 1 ∈ Finset.Icc 1 N by simp [hN])
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Nat.cast_one, inv_one] using hh

theorem tendsto_log_harmonic_ratio :
    Tendsto (fun N : ℕ => Real.log (harmonic N : ℝ) / Real.log N) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact hh.comp hlogN
  have hu : Tendsto (fun N : ℕ =>
      (Real.log 2 + Real.log (Real.log N)) / Real.log N) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using (hlogN.const_div_atTop (Real.log 2)).add he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact div_nonneg (Real.log_nonneg (one_le_real_harmonic (by omega)))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  · filter_upwards [eventually_ge_atTop (2 : ℕ), hlogN.eventually_ge_atTop 1] with N hN hl
    have hH : 0 < (harmonic N : ℝ) := zero_lt_one.trans_le (one_le_real_harmonic (by omega))
    have hb : (harmonic N : ℝ) ≤ 2 * Real.log N := by
      have hh := harmonic_le_one_add_log N
      linarith
    have hh := Real.log_le_log hH hb
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : Real.log N ≠ 0)] at hh
    exact div_le_div_of_nonneg_right hh (by linarith)

theorem coefficientEnergy_log_upper {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha1 : a 1 = 1) {N : ℕ} (hN : 2 ≤ N) (σ : ℝ) :
    Real.log (coefficientEnergy a N σ) / (2 * Real.log N) ≤
      max (1 / 2 - σ) 0 + (Real.log (harmonic N : ℝ) / Real.log N) / 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hH : 0 < (harmonic N : ℝ) := zero_lt_one.trans_le (one_le_real_harmonic (by omega))
  have hE := Real.log_le_log (zero_lt_one.trans_le (one_le_coefficientEnergy (by omega) ha1 σ))
    (coefficientEnergy_le_power_harmonic ha N σ)
  rw [Real.log_mul (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _).ne' hH.ne',
    Real.log_rpow (zero_lt_one.trans hNr)] at hE
  have hh := div_le_div_of_nonneg_right hE (by positivity : 0 ≤ 2 * Real.log N)
  have hm : max (-2 * σ + 1) 0 = 2 * max (1 / 2 - σ) 0 := by
    by_cases hs : σ ≤ 1 / 2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  convert hh using 1
  rw [hm]
  field_simp [(Real.log_pos hNr).ne']

theorem isolatedPrimeEnergy_le_coefficientEnergy {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) (N : ℕ) (σ : ℝ) :
    isolatedPrimeEnergy a Q N σ ≤ coefficientEnergy a N σ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_Icc.mpr ⟨(hQ N p hp).1.one_le, (hQ N p hp).2.2⟩
  · intro p _ _
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)

end Dubon2026
