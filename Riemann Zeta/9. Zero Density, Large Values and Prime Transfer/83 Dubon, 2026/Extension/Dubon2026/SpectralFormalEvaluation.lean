import Dubon2026.SpectralFormalSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Convergent evaluation of the genuine finite spectral Euler series -/

namespace Dubon2026

noncomputable section

/-- Weighted formal multiplication is the actual Cauchy product at every degree. -/
theorem spectral_weighted_coeff_mul (φ ψ : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (φ * ψ) * z ^ n =
      ∑ t ∈ Finset.antidiagonal n,
        (PowerSeries.coeff t.1 φ * z ^ t.1) * (PowerSeries.coeff t.2 ψ * z ^ t.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mem_antidiagonal.mp ht, pow_add]
  ring

/-- The true finite formal Euler product evaluates absolutely to its literal reciprocal
 denominator wherever every spectral geometric series converges. -/
theorem spectralFormalEuler_evaluation {ι : Type*} (s : Finset ι) (w : ι → ℂ) (z : ℂ)
    (hw : ∀ i ∈ s, ‖w i * z‖ < 1) :
    (Summable fun n : ℕ => ‖PowerSeries.coeff n (spectralFormalEuler s w) * z ^ n‖) ∧
    HasSum (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler s w) * z ^ n)
      (∏ i ∈ s, (1 - w i * z)⁻¹) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : (fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler ∅ w) * z ^ n) =
        (fun n => if n = 0 then (1 : ℂ) else 0) := by
      funext n
      by_cases hn : n = 0 <;> simp [spectralFormalEuler, PowerSeries.coeff_one, hn]
    rw [he]
    constructor
    · change Summable (fun n : ℕ => ‖(fun n : ℕ => PowerSeries.coeff n (spectralFormalEuler ∅ w) * z ^ n) n‖)
      rw [he]
      exact (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).summable.norm
    · simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  | @insert a s ha ih =>
    obtain ⟨hs, hsum⟩ := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
    have hwa := hw a (Finset.mem_insert_self a s)
    have haSum : HasSum (fun n : ℕ =>
        PowerSeries.coeff n (spectralGeometricSeries (w a)) * z ^ n) (1 - w a * z)⁻¹ := by
      simpa only [spectralGeometricSeries, PowerSeries.coeff_mk, ← mul_pow] using
        hasSum_geometric_of_norm_lt_one hwa
    have haNorm : Summable (fun n : ℕ =>
        ‖PowerSeries.coeff n (spectralGeometricSeries (w a)) * z ^ n‖) := haSum.summable.norm
    have he (n : ℕ) : PowerSeries.coeff n (spectralFormalEuler (insert a s) w) * z ^ n =
        ∑ t ∈ Finset.antidiagonal n,
          (PowerSeries.coeff t.1 (spectralGeometricSeries (w a)) * z ^ t.1) *
          (PowerSeries.coeff t.2 (spectralFormalEuler s w) * z ^ t.2) := by
      change PowerSeries.coeff n (∏ i ∈ insert a s, spectralGeometricSeries (w i)) * z ^ n = _
      rw [Finset.prod_insert ha]
      exact spectral_weighted_coeff_mul _ _ _ _
    have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm haNorm hs
    constructor
    · simpa only [he] using hn
    · have ht := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm haNorm hs
      rw [haSum.tsum_eq, hsum.tsum_eq] at ht
      have hh := hn.of_norm.hasSum
      rw [← ht] at hh
      simpa only [he, Finset.prod_insert ha] using hh

end
end Dubon2026
