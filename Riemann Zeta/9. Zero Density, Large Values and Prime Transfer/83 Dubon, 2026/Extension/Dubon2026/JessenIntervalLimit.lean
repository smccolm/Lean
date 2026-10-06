import Dubon2026.JessenProbability
import Dubon2026.JessenDerivativeLimit

/-! # Concentration of the actual normalized Jessen measure on every neighborhood of the corner -/

namespace Dubon2026

open MeasureTheory Filter Set
open scoped Topology

/-- Actual open-interval mass tends to one whenever the interval straddles α. -/
theorem tendsto_jessenProbability_Ioo {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α)
    {l u : ℝ} (hl : l < α) (hu : α < u) :
    Tendsto (fun N => (jessenProbability ha N : Measure ℝ) (Ioo l u)) atTop (𝓝 1) := by
  have hp := tendsto_normalizedJessen ha hQ hcard hc hH1 hH2
  have hM := tendsto_isolated_log_lastIndex_ratio hQ hcard hc
  have hleft := tendsto_div_log_lastIndex
    (tendsto_normalized_jessen_derivatives_of_lt ha hp hl).2 hM
  have hright := tendsto_div_log_lastIndex
    (tendsto_normalized_jessen_derivatives_of_gt ha hp hu).1 hM
  have hdiff : Tendsto (fun N =>
      (derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / Real.log (lastIndex a N))
      atTop (𝓝 1) := by
    simpa only [sub_div, sub_neg_eq_add, zero_add] using hright.sub hleft
  have hh : Tendsto (fun N => ENNReal.ofReal
      ((derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / Real.log (lastIndex a N)))
      atTop (𝓝 1) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hdiff
  apply hh.congr'
  filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc] with N hn
  have hN : 1 ≤ N := (le_of_lt hn.2.2).trans hn.2.1
  exact (jessenProbability_Ioo ha hN hn.2.2 l u).symm

end Dubon2026
