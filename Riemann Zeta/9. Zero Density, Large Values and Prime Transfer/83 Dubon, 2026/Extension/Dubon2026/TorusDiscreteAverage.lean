import Dubon2026.DiscreteObservable

/-! # Prime torus equidistribution for bounded natural-valued observables

The conclusion is the literal symmetric time integral, at every real height
tending to infinity. Measurability, boundedness and Haar-almost-everywhere
continuity are explicit upstream conditions on the observable.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem integral_timeWindowProbability_real (T : ℝ) (f : ℝ → ℝ) :
    (∫ t, f t ∂(timeWindowProbability T : Measure ℝ)) =
      (2 * orbitHeight T)⁻¹ * ∫ t in -orbitHeight T..orbitHeight T, f t := by
  change (∫ t, f t ∂ProbabilityTheory.cond volume
    (Set.Ioc (-orbitHeight T) (orbitHeight T))) = _
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith [orbitHeight_pos T]),
    intervalIntegral.integral_of_le (by linarith [orbitHeight_pos T])]
  simp only [smul_eq_mul, sub_neg_eq_add, ← two_mul]

theorem integral_torusOrbitProbability_real (N : ℕ) (T : ℝ)
    {f : PrimeTorus N → ℝ} (hf : StronglyMeasurable f) :
    (∫ z, f z ∂(torusOrbitProbability N T : Measure (PrimeTorus N))) =
      (2 * orbitHeight T)⁻¹ *
        ∫ t in -orbitHeight T..orbitHeight T, f (primeTorusFlow N t) := by
  change (∫ z, f z ∂Measure.map (primeTorusFlow N)
    (timeWindowProbability T : Measure ℝ)) = _
  rw [integral_map_of_stronglyMeasurable (continuous_primeTorusFlow N).measurable hf,
    integral_timeWindowProbability_real]

theorem tendsto_torusAverage_bounded_nat (N : ℕ) {g : PrimeTorus N → ℕ}
    (hg : Measurable g) (hgc : ∀ᵐ z ∂torusHaar N, ContinuousAt g z)
    (K : ℕ) (hK : ∀ z, g z ≤ K) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ *
      ∫ t in -T..T, (g (primeTorusFlow N t) : ℝ)) atTop
        (𝓝 (∫ z, (g z : ℝ) ∂torusHaar N)) := by
  have hf : StronglyMeasurable (fun z => (g z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hg
      |>.stronglyMeasurable
  have hh := tendsto_integral_bounded_nat_of_ae_continuous
    (tendsto_torusOrbitProbability N) hg hgc K hK
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [integral_torusOrbitProbability_real N T hf]
  simp only [orbitHeight, max_eq_left hT]

end

end Dubon2026
