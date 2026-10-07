import Dubon2026.GeneralOutsideDensity
import Dubon2026.DirichletApplication

/-! # Concentration of the actual normalized zero-frequency measures -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem tendsto_normalized_verticalZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (hM : 1 < lastIndex a N) (l u : ℝ) :
    Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex a N)) *
      ((verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T)))
      atTop (𝓝 (((jessenProbability ha N : Measure ℝ) (Ioo l u)).toReal)) := by
  have hlog : 0 < Real.log (lastIndex a N) := Real.log_pos (by exact_mod_cast hM)
  have hh := (tendsto_zeroDensity_jessenMeasure hN ha l u).const_mul
    (2 * Real.pi / Real.log (lastIndex a N))
  rw [jessenProbability_eq ha hN hM, normalizedJessenMeasure, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hlog.le]
  convert hh using 1
  field_simp

/-- The abstract H1/H2 theorem now consumes the actual multiplicity-weighted
zero-frequency limit, with the fixed-length height limit taken first. -/
theorem abstract_actual_zero_concentration {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    TendstoLocallyUniformly (normalizedJessen a) (fun σ => max (α - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun N => (jessenProbability ha N : Measure ℝ))) ∧
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex a N)) *
        ((verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T)))
        atTop (𝓝 (((jessenProbability ha N : Measure ℝ) (Ioo l u)).toReal))) := by
  obtain ⟨hp, hs, ht, hw, _, he⟩ := abstract_jessen_concentration ha hQ hcard hc hH1 hH2
  refine ⟨hp, hs, ht, hw, ?_⟩
  filter_upwards [he] with N hN
  obtain ⟨hN, hM, _⟩ := hN
  exact ⟨hN, hM, tendsto_normalized_verticalZeroCount hN ha hM⟩

theorem dirichlet_actual_zero_concentration {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    TendstoLocallyUniformly (normalizedJessen (characterCoefficients χ))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex (characterCoefficients χ) N) / Real.log N)
      atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun N =>
      (jessenProbability (characterCoefficients_one χ) N : Measure ℝ))) ∧
    Tendsto (jessenProbability (characterCoefficients_one χ)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (characterCoefficients χ) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (characterCoefficients χ) N)) *
        ((verticalZeroCount (characterCoefficients χ) N hN
          ((characterCoefficients_one χ).trans_ne one_ne_zero) l u T : ℝ) / (2 * T)))
        atTop (𝓝 (((jessenProbability (characterCoefficients_one χ) N : Measure ℝ)
          (Ioo l u)).toReal))) :=
  abstract_actual_zero_concentration (characterCoefficients_one χ)
    isolatedPrimeBlocks_dyadicPrimes tendsto_card_dyadicPrimes
    (primeCoefficientComparability_character χ (1 / 2))
    (globalEnergyAsymptotic_character χ) (isolatedEnergyAsymptotic_character χ)

end

end Dubon2026
