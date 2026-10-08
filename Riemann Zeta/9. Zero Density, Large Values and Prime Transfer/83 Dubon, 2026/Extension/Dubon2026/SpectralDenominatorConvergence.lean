import Dubon2026.SpectralFormalEvaluation

/-! # Convergent actual Euler coefficients exclude every zero of their literal denominator -/

namespace Dubon2026

noncomputable section

/-- Convergent evaluation respects multiplication of actual formal series. -/
theorem spectral_weighted_mul_hasSum {φ ψ : PowerSeries ℂ} {z a b : ℂ}
    (hφ : HasSum (fun n : ℕ => PowerSeries.coeff n φ * z ^ n) a)
    (hψ : HasSum (fun n : ℕ => PowerSeries.coeff n ψ * z ^ n) b) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (φ * ψ) * z ^ n) (a * b) := by
  have hh := summable_norm_sum_mul_antidiagonal_of_summable_norm hφ.summable.norm hψ.summable.norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hφ.summable.norm hψ.summable.norm
  rw [hφ.tsum_eq, hψ.tsum_eq] at he
  have ht := hh.of_norm.hasSum
  rw [← he] at ht
  simpa only [spectral_weighted_coeff_mul] using ht

/-- The constant formal series evaluates to one at every point. -/
theorem spectral_weighted_one_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

/-- The literal linear Euler denominator evaluates to its usual polynomial value. -/
theorem spectral_weighted_linear_hasSum (w z : ℂ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (1 - PowerSeries.C w * PowerSeries.X) * z ^ n)
      (1 - w * z) := by
  have hh := (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).sub (hasSum_ite_eq (1 : ℕ) (w * z))
  convert hh using 1
  funext n
  by_cases hn0 : n = 0
  · simp [hn0]
  · by_cases hn1 : n = 1
    · simp [hn1, PowerSeries.coeff_one]
    · simp [hn0, hn1, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_C_mul]

/-- The literal finite formal denominator evaluates at every complex point. -/
theorem spectral_weighted_denominator_hasSum {ι : Type*} (s : Finset ι) (w : ι → ℂ) (z : ℂ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n
      (∏ i ∈ s, (1 - PowerSeries.C (w i) * PowerSeries.X)) * z ^ n)
      (∏ i ∈ s, (1 - w i * z)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using spectral_weighted_one_hasSum z
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact spectral_weighted_mul_hasSum (spectral_weighted_linear_hasSum (w a) z) ih

/-- The actual finite formal Euler product has exactly numerator one. -/
theorem spectralFormalEuler_mul_denominator {ι : Type*} (s : Finset ι) (w : ι → ℂ) :
    spectralFormalEuler s w * (∏ i ∈ s, (1 - PowerSeries.C (w i) * PowerSeries.X)) = 1 := by
  rw [spectralFormalEuler, ← Finset.prod_mul_distrib]
  simp only [spectralGeometricSeries_mul_denominator, Finset.prod_const_one]

/-- Convergence of the genuine Euler coefficient series excludes a zero of its exact denominator.
No preexisting bound on individual roots is required. -/
theorem spectral_denominator_ne_zero_of_summable {ι : Type*} (s : Finset ι) (w : ι → ℂ) (z : ℂ)
    (hs : Summable (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler s w) * z ^ n)) :
    (∏ i ∈ s, (1 - w i * z)) ≠ 0 := by
  have hh := spectral_weighted_mul_hasSum hs.hasSum (spectral_weighted_denominator_hasSum s w z)
  rw [spectralFormalEuler_mul_denominator] at hh
  have he := hh.unique (spectral_weighted_one_hasSum z)
  intro hz
  rw [hz, mul_zero] at he
  exact zero_ne_one he

/-- Summability on a circle of radius |z| bounds every genuine local root strictly inside
its geometric disk. The proof evaluates the exact numerator-one identity at a reciprocal root. -/
theorem spectral_root_norm_lt_one_of_summable {ι : Type*} (s : Finset ι) (w : ι → ℂ) (z : ℂ)
    (hs : Summable (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler s w) * z ^ n))
    {i : ι} (hi : i ∈ s) : ‖w i * z‖ < 1 := by
  classical
  by_contra hlt
  have hz : 1 ≤ ‖w i‖ * ‖z‖ := by simpa only [norm_mul] using not_lt.mp hlt
  have hw : w i ≠ 0 := by
    intro h
    norm_num [h] at hz
  have hwpos : 0 < ‖w i‖ := norm_pos_iff.mpr hw
  have hrec : ‖(w i)⁻¹‖ ≤ ‖z‖ := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ hwpos]
    simpa only [mul_comm] using hz
  have hsum : Summable (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler s w) * ((w i)⁻¹) ^ n) := by
    apply hs.norm.of_norm_bounded
    intro n
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hrec n) (norm_nonneg _)
  have hne := spectral_denominator_ne_zero_of_summable s w ((w i)⁻¹) hsum
  apply hne
  apply Finset.prod_eq_zero hi
  rw [mul_inv_cancel₀ hw, sub_self]

end
end Dubon2026
