import Dubon2026.MeanSquareEnergy
import Dubon2026.SelectedPrimeEnergy
import Dubon2026.ActualZeroConcentration

/-! # Actual zero concentration from a mean-square limit and selected-prime density

This deduction is conditional on two explicitly stated arithmetic inputs. It
proves H1 and H2 from them before invoking the abstract zero-frequency theorem.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- A mean-square limit and positive-density bounded prime coefficients imply the
full normalized potential, tightness, weak probability and actual height-limit conclusions. -/
theorem mean_square_prime_density_concentration {a : ℕ → ℂ} {S : ℕ → Prop} {c η : ℝ}
    (ha : a 1 = 1)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N)
      atTop (𝓝 c))
    (hη : 0 < η)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η))
    (hb : ∀ p, Nat.Prime p → S p → 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) :
    TendstoLocallyUniformly (normalizedJessen a) (fun σ => max ((1 / 2) - σ) 0) atTop ∧
    Tendsto (fun N : ℕ => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) ∧
    IsTightMeasureSet (range (fun N => (jessenProbability ha N : Measure ℝ))) ∧
    Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex a N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex a N)) *
        ((verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T)))
        atTop (𝓝 (((jessenProbability ha N : Measure ℝ) (Ioo l u)).toReal))) := by
  obtain ⟨hQ, hcard, hc, hH2⟩ := selected_primes_H2 hη hd hb
  have hH1 := globalEnergyAsymptotic_of_mean_isolated ha hmean hQ hcard hc hH2
  exact abstract_actual_zero_concentration ha hQ hcard hc hH1 hH2

end

end Dubon2026
