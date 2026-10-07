import Dubon2026.TorusEquidistribution
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Probability measures of the actual prime torus orbit

The window is clipped at height one only to define a probability measure at every
real parameter. At every height at least one it is exactly the normalized time
average on `(-T,T]`. Continuous-test equidistribution implies weak convergence and
therefore convergence on every Haar continuity set.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

/-- A positive averaging height, equal to the input for heights at least one. -/
def orbitHeight (T : ℝ) : ℝ := max T 1

theorem orbitHeight_pos (T : ℝ) : 0 < orbitHeight T :=
  lt_of_lt_of_le zero_lt_one (le_max_right T 1)

/-- Lebesgue probability on the actual symmetric time window. -/
def timeWindowProbability (T : ℝ) : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.cond volume (Set.Ioc (-orbitHeight T) (orbitHeight T)),
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [orbitHeight_pos T]))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)⟩

/-- Push the normalized time window along the actual prime torus flow. -/
def torusOrbitProbability (N : ℕ) (T : ℝ) : ProbabilityMeasure (PrimeTorus N) :=
  (timeWindowProbability T).map (continuous_primeTorusFlow N).measurable.aemeasurable

/-- The already constructed Haar probability as a bundled probability measure. -/
def torusHaarProbability (N : ℕ) : ProbabilityMeasure (PrimeTorus N) :=
  ⟨torusHaar N, inferInstance⟩

theorem integral_timeWindowProbability (T : ℝ) (f : ℝ → ℂ) :
    (∫ t, f t ∂(timeWindowProbability T : Measure ℝ)) =
      symmetricAverage f (orbitHeight T) := by
  change (∫ t, f t ∂ProbabilityTheory.cond volume
    (Set.Ioc (-orbitHeight T) (orbitHeight T))) = _
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith [orbitHeight_pos T])]
  unfold symmetricAverage
  rw [intervalIntegral.integral_of_le (by linarith [orbitHeight_pos T])]
  congr 2
  ring

theorem integral_torusOrbitProbability (N : ℕ) (T : ℝ)
    (f : C(PrimeTorus N, ℂ)) :
    (∫ z, f z ∂(torusOrbitProbability N T : Measure (PrimeTorus N))) =
      torusAverage N f (orbitHeight T) := by
  change (∫ z, f z ∂Measure.map (primeTorusFlow N)
    (timeWindowProbability T : Measure ℝ)) = _
  rw [integral_map (continuous_primeTorusFlow N).measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_timeWindowProbability]
  rfl

theorem tendsto_orbitHeight : Tendsto orbitHeight atTop atTop :=
  tendsto_atTop_mono (fun T => le_max_left T 1) tendsto_id

theorem tendsto_torusOrbitProbability (N : ℕ) :
    Tendsto (torusOrbitProbability N) atTop (𝓝 (torusHaarProbability N)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  change Tendsto (fun T => ∫ z, f.toContinuousMap z
    ∂(torusOrbitProbability N T : Measure (PrimeTorus N))) atTop
      (𝓝 (∫ z, f.toContinuousMap z ∂torusHaar N))
  simp only [integral_torusOrbitProbability]
  exact (tendsto_torusAverage N f.toContinuousMap).comp tendsto_orbitHeight

theorem tendsto_torusOrbitProbability_set (N : ℕ) {S : Set (PrimeTorus N)}
    (hS : torusHaar N (frontier S) = 0) :
    Tendsto (fun T => (torusOrbitProbability N T : Measure (PrimeTorus N)) S)
      atTop (𝓝 (torusHaar N S)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_torusOrbitProbability N) hS

end

end Dubon2026
