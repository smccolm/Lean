import Dubon2026.CharacterEnergy
import Dubon2026.ConcentrationTails

/-! # Jessen concentration for all fixed positive-modulus Dirichlet characters

No primitivity or nonprincipal assumption is imposed. The measure is normalized by
the actual last nonzero coefficient, which need not occur at N.
-/

namespace Dubon2026

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

theorem dirichlet_jessen_concentration {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    TendstoLocallyUniformly (normalizedJessen (characterCoefficients χ))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex (characterCoefficients χ) N) / Real.log N)
      atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun N =>
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ))) ∧
    Tendsto (jessenProbability (characterCoefficients_one χ)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, f x
      ∂(jessenProbability (characterCoefficients_one χ) N : Measure ℝ))
      atTop (𝓝 (f (1 / 2)))) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (characterCoefficients χ) N ∧
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ) =
        (ENNReal.ofReal (Real.log (lastIndex (characterCoefficients χ) N)))⁻¹ •
          (jessenStieltjes hN ((characterCoefficients_one χ).trans_ne one_ne_zero)).measure) := by
  exact abstract_jessen_concentration (characterCoefficients_one χ)
    isolatedPrimeBlocks_dyadicPrimes tendsto_card_dyadicPrimes
    (primeCoefficientComparability_character χ (1 / 2))
    (globalEnergyAsymptotic_character χ) (isolatedEnergyAsymptotic_character χ)

theorem tendsto_dirichlet_jessenProbability_outside {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => (jessenProbability (characterCoefficients_one χ) N : Measure ℝ)
      {x | ε ≤ |x - 1 / 2|}) atTop (𝓝 0) :=
  tendsto_jessenProbability_outside (characterCoefficients_one χ)
    isolatedPrimeBlocks_dyadicPrimes tendsto_card_dyadicPrimes
    (primeCoefficientComparability_character χ (1 / 2))
    (globalEnergyAsymptotic_character χ) (isolatedEnergyAsymptotic_character χ) hε

end Dubon2026
