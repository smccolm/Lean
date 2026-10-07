import Dubon2026.SelectedPrimeDensity
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The literal empirical probability distribution of coefficients at primes -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

/-- Uniform mass at each coefficient indexed by a prime up to N.
The empty initial prime ranges use a Dirac mass solely to totalize the family. -/
def primeEmpirical (x : ℕ → ℝ) (N : ℕ) : ProbabilityMeasure ℝ := by
  classical
  exact if h : (Nat.primesLE N).Nonempty then
    ⟨Measure.map x (PMF.uniformOfFinset (Nat.primesLE N) h).toMeasure,
      Measure.isProbabilityMeasure_map (measurable_of_countable x).aemeasurable⟩
  else ⟨Measure.dirac 0, inferInstance⟩

theorem primeEmpirical_apply {x : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (primeEmpirical x N : Measure ℝ) A =
      ((selectedPrimesUpTo (fun p => x p ∈ A) N).card : ℝ≥0∞) / Nat.primeCounting N := by
  classical
  have h : (Nat.primesLE N).Nonempty := ⟨2, Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩⟩
  simp only [primeEmpirical, dif_pos h]
  change Measure.map x (PMF.uniformOfFinset (Nat.primesLE N) h).toMeasure A = _
  rw [Measure.map_apply (measurable_of_countable x) hA,
    PMF.toMeasure_uniformOfFinset_apply h _ ((measurable_of_countable x) hA),
    Nat.primesLE_card_eq_primeCounting]
  rfl

/-- Weak convergence gives the exact natural density on a continuity set. -/
theorem prime_density_of_empirical_convergence {x : ℕ → ℝ} {μ : ProbabilityMeasure ℝ}
    (hx : Tendsto (primeEmpirical x) atTop (𝓝 μ)) {A : Set ℝ}
    (hA : MeasurableSet A) (hbd : (μ : Measure ℝ) (frontier A) = 0) :
    Tendsto (fun N : ℕ => ((selectedPrimesUpTo (fun p => x p ∈ A) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 (((μ : Measure ℝ) A).toReal)) := by
  have hh := (ENNReal.continuousAt_toReal (measure_ne_top (μ : Measure ℝ) A)).tendsto.comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hx hbd)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  simp only [Function.comp_def]
  rw [primeEmpirical_apply hN hA, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]

end

end Dubon2026
