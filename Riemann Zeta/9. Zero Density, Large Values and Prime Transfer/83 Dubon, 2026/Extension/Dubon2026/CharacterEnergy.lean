import Dubon2026.CharacterCoefficients
import Dubon2026.ZetaEnergy

/-! # Literal H1 and H2 for every character of a fixed positive modulus -/

namespace Dubon2026

open Filter
open scoped Topology

theorem primeCoefficientComparability_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (α : ℝ) :
    PrimeCoefficientComparability (characterCoefficients χ) dyadicPrimes α := by
  intro l u hlu hu
  obtain ⟨K, hK, hk⟩ := primeCoefficientComparability_one α l u hlu hu
  refine ⟨K, hK, ?_⟩
  filter_upwards [hk, eventually_dyadic_character_norm χ] with N hn hc
  intro σ hσ p hp r hr
  simpa only [hc p hp, hc r hr, norm_one] using hn σ hσ p hp r hr

theorem tendstoLocallyUniformly_character_isolatedEnergy {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    TendstoLocallyUniformly (fun N : ℕ => fun σ : ℝ =>
      Real.log (isolatedPrimeEnergy (characterCoefficients χ) dyadicPrimes N σ) /
        (2 * Real.log N)) (fun σ => 1 / 2 - σ) atTop := by
  apply tendstoLocallyUniformly_dyadic_energy.congr_inseparable
  filter_upwards [eventually_character_isolatedEnergy_eq χ] with N hn
  intro σ
  rw [hn σ]

theorem isolatedEnergyAsymptotic_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    IsolatedEnergyAsymptotic (characterCoefficients χ) dyadicPrimes (1 / 2) :=
  (tendstoLocallyUniformly_character_isolatedEnergy χ).tendstoLocallyUniformlyOn

theorem globalEnergyAsymptotic_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    GlobalEnergyAsymptotic (characterCoefficients χ) (1 / 2) :=
  globalEnergyAsymptotic_of_bounded_isolated (characterCoefficients_one χ)
    (norm_characterCoefficients_le_one χ) isolatedPrimeBlocks_dyadicPrimes
    tendsto_card_dyadicPrimes (primeCoefficientComparability_character χ (1 / 2))
    (isolatedEnergyAsymptotic_character χ)

end Dubon2026
