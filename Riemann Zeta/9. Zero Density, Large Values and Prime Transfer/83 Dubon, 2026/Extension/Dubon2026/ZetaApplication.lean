import Dubon2026.ZetaEnergy
import Dubon2026.ConcentrationTails

/-! # Actual zeta Jessen potential and probability concentration

These statements concern the actual vertical logarithmic mean and its Stieltjes measure.
`ZetaZeroCount` subsequently proves the nested limits of literal zero counts with
the source's explicit atom-free boundary convention.
-/

namespace Dubon2026

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

theorem zeta_lastIndex {N : ℕ} (hN : 1 ≤ N) : lastIndex (fun _ => (1 : ℂ)) N = N :=
  lastIndex_eq_of_last_coefficient hN one_ne_zero

theorem zeta_jessenProbability_eq {N : ℕ} (hN : 2 ≤ N) :
    (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ) =
      (ENNReal.ofReal (Real.log N))⁻¹ •
        (jessenStieltjes (a := fun _ => (1 : ℂ)) (by omega : 1 ≤ N) one_ne_zero).measure := by
  rw [jessenProbability_eq rfl (by omega) (by rw [zeta_lastIndex (by omega)]; omega),
    normalizedJessenMeasure, zeta_lastIndex (by omega)]
  rfl

theorem zeta_jessen_concentration :
    TendstoLocallyUniformly (normalizedJessen (fun _ => (1 : ℂ)))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    IsTightMeasureSet (range (fun N =>
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ))) ∧
    Tendsto (jessenProbability (a := fun _ => (1 : ℂ)) rfl) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, f x
      ∂(jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ))
      atTop (𝓝 (f (1 / 2)))) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N =>
      (jessenProbability (a := fun _ => (1 : ℂ)) rfl N : Measure ℝ)
        {x | ε ≤ |x - 1 / 2|}) atTop (𝓝 0)) := by
  have hh := abstract_jessen_concentration rfl isolatedPrimeBlocks_dyadicPrimes
    tendsto_card_dyadicPrimes (primeCoefficientComparability_one (1 / 2))
    globalEnergyAsymptotic_one isolatedEnergyAsymptotic_one
  refine ⟨hh.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1, ?_⟩
  intro ε hε
  exact tendsto_jessenProbability_outside rfl isolatedPrimeBlocks_dyadicPrimes
    tendsto_card_dyadicPrimes (primeCoefficientComparability_one (1 / 2))
    globalEnergyAsymptotic_one isolatedEnergyAsymptotic_one hε

end Dubon2026
