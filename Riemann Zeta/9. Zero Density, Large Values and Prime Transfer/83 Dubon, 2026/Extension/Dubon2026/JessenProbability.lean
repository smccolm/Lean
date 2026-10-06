import Dubon2026.IsolatedPrimeSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Actual Jessen probability measures, with an explicit finite-degeneracy convention -/

namespace Dubon2026

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- For supported length greater than one this is exactly J″/log M.
The Dirac convention is used only when no probability normalization exists. -/
def jessenProbability {a : ℕ → ℂ} (ha : a 1 = 1) (N : ℕ) : ProbabilityMeasure ℝ :=
  if h : 1 ≤ N ∧ 1 < lastIndex a N then
    ⟨normalizedJessenMeasure h.1 (ha.trans_ne one_ne_zero),
      normalizedJessenMeasure_isProbability h.1 ha h.2⟩
  else ⟨Measure.dirac 0, inferInstance⟩

theorem jessenProbability_eq {a : ℕ → ℂ} (ha : a 1 = 1) {N : ℕ}
    (hN : 1 ≤ N) (hM : 1 < lastIndex a N) :
    (jessenProbability ha N : Measure ℝ) = normalizedJessenMeasure hN (ha.trans_ne one_ne_zero) := by
  unfold jessenProbability
  rw [dif_pos ⟨hN, hM⟩]
  rfl

theorem normalizedJessenMeasure_Ioo {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (hM : 1 < lastIndex a N) (l u : ℝ) :
    normalizedJessenMeasure hN ha (Ioo l u) = ENNReal.ofReal
      ((derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / Real.log (lastIndex a N)) := by
  have hlog : 0 < Real.log (lastIndex a N) := Real.log_pos (by exact_mod_cast hM)
  rw [normalizedJessenMeasure, Measure.smul_apply, smul_eq_mul, jessenMeasure_Ioo,
    ENNReal.ofReal_div_of_pos hlog, div_eq_mul_inv, mul_comm]

theorem jessenProbability_Ioo {a : ℕ → ℂ} (ha : a 1 = 1) {N : ℕ}
    (hN : 1 ≤ N) (hM : 1 < lastIndex a N) (l u : ℝ) :
    (jessenProbability ha N : Measure ℝ) (Ioo l u) = ENNReal.ofReal
      ((derivWithin (jessenFunction a N) (Iio u) u -
        derivWithin (jessenFunction a N) (Ioi l) l) / Real.log (lastIndex a N)) := by
  rw [jessenProbability_eq ha hN hM, normalizedJessenMeasure_Ioo hN _ hM]

/-- H2 removes every degenerate convention from the eventual sequence. -/
theorem eventually_jessenProbability_eq {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    ∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧
      (jessenProbability ha N : Measure ℝ) = normalizedJessenMeasure hN (ha.trans_ne one_ne_zero) := by
  filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc] with N hn
  have hN : 1 ≤ N := (le_of_lt hn.2.2).trans hn.2.1
  exact ⟨hN, hn.2.2, jessenProbability_eq ha hN hn.2.2⟩

end

end Dubon2026
