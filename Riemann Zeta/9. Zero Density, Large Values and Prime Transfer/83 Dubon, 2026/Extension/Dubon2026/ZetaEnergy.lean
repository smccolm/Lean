import Dubon2026.BoundedCoefficientEnergy
import Dubon2026.DyadicEnergyLimit

/-! # Literal H1 and H2 for the zeta partial-sum coefficients -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem globalEnergyAsymptotic_one :
    GlobalEnergyAsymptotic (fun _ => (1 : ℂ)) (1 / 2) :=
  globalEnergyAsymptotic_of_bounded_isolated rfl (by intro n; simp only [norm_one, le_refl])
    isolatedPrimeBlocks_dyadicPrimes tendsto_card_dyadicPrimes
    (primeCoefficientComparability_one (1 / 2)) isolatedEnergyAsymptotic_one

theorem zeta_energy_hypotheses :
    (∀ σ : ℝ, Tendsto (fun N : ℕ =>
      Real.log (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      atTop (𝓝 (max (1 / 2 - σ) 0))) ∧
    PrimeCoefficientComparability (fun _ => (1 : ℂ)) dyadicPrimes (1 / 2) ∧
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      Real.log (∑ p ∈ dyadicPrimes N, (p : ℝ) ^ (-2 * σ)) / (2 * Real.log N))
      (fun σ => 1 / 2 - σ) atTop := by
  refine ⟨?_, primeCoefficientComparability_one (1 / 2), ?_⟩
  · simpa only [GlobalEnergyAsymptotic, coefficientEnergy, norm_one, one_pow, one_mul] using
      globalEnergyAsymptotic_one
  · simpa only [isolatedPrimeEnergy, norm_one, one_pow, one_mul] using
      tendstoLocallyUniformly_dyadic_energy

end Dubon2026
