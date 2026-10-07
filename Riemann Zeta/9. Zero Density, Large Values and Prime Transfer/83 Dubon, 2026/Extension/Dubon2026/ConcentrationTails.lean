import Dubon2026.WeakLimit

/-! # Mass outside a fixed closed distance from the concentration line -/

namespace Dubon2026

open MeasureTheory Filter Set
open scoped Topology

theorem outside_eq_compl_Ioo (α ε : ℝ) :
    {x : ℝ | ε ≤ |x - α|} = (Ioo (α - ε) (α + ε))ᶜ := by
  ext x
  change (ε ≤ |x - α|) ↔ ¬(α - ε < x ∧ x < α + ε)
  rw [← not_lt, abs_lt]
  apply not_congr
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem tendsto_jessenProbability_outside {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => (jessenProbability ha N : Measure ℝ) {x | ε ≤ |x - α|})
      atTop (𝓝 0) := by
  have hh := tendsto_jessenProbability_Ioo ha hQ hcard hc hH1 hH2
    (l := α - ε) (u := α + ε) (by linarith) (by linarith)
  have ht := ENNReal.Tendsto.sub tendsto_const_nhds hh (Or.inl ENNReal.one_ne_top)
  simpa only [outside_eq_compl_Ioo, measure_compl measurableSet_Ioo (measure_ne_top _ _),
    measure_univ, tsub_self] using ht

end Dubon2026
