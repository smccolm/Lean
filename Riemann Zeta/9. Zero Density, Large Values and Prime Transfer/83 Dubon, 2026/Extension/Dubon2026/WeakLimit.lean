import Dubon2026.JessenIntervalLimit
import Dubon2026.NeighborhoodConcentration

/-! # The abstract potential and weak probability concentration criterion -/

namespace Dubon2026

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology

/-- The actual normalized Stieltjes probabilities converge weakly to the single corner. -/
theorem tendsto_jessenProbability {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  tendsto_probability_dirac_of_Ioo (jessenProbability ha) α
    (fun _ _ hl hu => tendsto_jessenProbability_Ioo ha hQ hcard hc hH1 hH2 hl hu)

theorem isTightMeasureSet_jessenProbability {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    IsTightMeasureSet (range (fun N => (jessenProbability ha N : Measure ℝ))) :=
  isTightMeasureSet_of_Ioo_limit (jessenProbability ha)
    (tendsto_jessenProbability_Ioo ha hQ hcard hc hH1 hH2
      (l := α - 1) (u := α + 1) (by linarith) (by linarith))

/-- Every bounded continuous test, not only compact or smooth tests, has the claimed limit. -/
theorem tendsto_integral_jessenProbability {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun N => ∫ x, f x ∂(jessenProbability ha N : Measure ℝ)) atTop (𝓝 (f α)) := by
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_jessenProbability ha hQ hcard hc hH1 hH2) f
  simpa only [ProbabilityMeasure.coe_mk, integral_dirac] using hh

/-- Theorem 2.2's analytic conclusion for the actual Jessen function and its Stieltjes measure.
The separate Jessen–Tornehave theorem identifies that measure with vertical zero frequencies. -/
theorem abstract_jessen_concentration {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    TendstoLocallyUniformly (normalizedJessen a) (fun σ => max (α - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun N => (jessenProbability ha N : Measure ℝ))) ∧
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, f x ∂(jessenProbability ha N : Measure ℝ))
      atTop (𝓝 (f α))) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧
      (jessenProbability ha N : Measure ℝ) = normalizedJessenMeasure hN (ha.trans_ne one_ne_zero)) :=
  ⟨tendstoLocallyUniformly_normalizedJessen ha hQ hcard hc hH1 hH2,
    tendsto_isolated_log_lastIndex_ratio hQ hcard hc,
    isTightMeasureSet_jessenProbability ha hQ hcard hc hH1 hH2,
    tendsto_jessenProbability ha hQ hcard hc hH1 hH2,
    tendsto_integral_jessenProbability ha hQ hcard hc hH1 hH2,
    eventually_jessenProbability_eq ha hQ hcard hc⟩

end Dubon2026
