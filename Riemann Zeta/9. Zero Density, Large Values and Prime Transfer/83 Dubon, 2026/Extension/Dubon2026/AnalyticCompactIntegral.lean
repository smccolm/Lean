import Dubon2026.CompactPhaseAlgebra
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Analytic phase dependence of compact contour integrals -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- Integration on a compact finite-measure space as an actual complex continuous linear map. -/
def compactIntegralCLM (μ : Measure K) [IsFiniteMeasure μ] : C(K, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

theorem compactIntegralCLM_apply (μ : Measure K) [IsFiniteMeasure μ] (f : C(K, ℂ)) :
    compactIntegralCLM μ f = ∫ t, f t ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ f)

omit [MeasurableSpace K] [BorelSpace K] in
theorem eventually_ne_zero_complexPhase_compact (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ)
    (hn : ∀ t, complexPhaseFamily a N (x, γ t) ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∀ t, complexPhaseFamily a N (y, γ t) ≠ 0 := by
  have hi := isUnit_compactPhaseFamily a N γ x hn
  have he := (analyticAt_compactPhaseFamily a N γ x).continuousAt
    (Units.isOpen.mem_nhds hi)
  filter_upwards [he] with y hy
  simpa only [compactPhaseFamily_apply] using
    (ContinuousMap.isUnit_iff_forall_ne_zero _).mp hy

theorem analyticAt_integral_compactPhase_logDeriv (a : ℕ → ℂ) (N : ℕ)
    (γ ω : C(K, ℂ)) (μ : Measure K) [IsFiniteMeasure μ]
    (x : PrimeCoordinate N → ℂ)
    (hn : ∀ t, complexPhaseFamily a N (x, γ t) ≠ 0) :
    AnalyticAt ℂ (fun y => ∫ t, ω t *
      logDeriv (dirichletSum (complexPhaseCoefficients a N y) N) (γ t) ∂μ) x := by
  have hf : AnalyticAt ℂ (fun y => ω * compactPhaseLogDeriv a N γ y) x :=
    analyticAt_const.mul (analyticAt_compactPhaseLogDeriv a N γ x hn)
  have hJ := (compactIntegralCLM μ).analyticAt (ω * compactPhaseLogDeriv a N γ x)
  apply (AnalyticAt.comp (f := fun y => ω * compactPhaseLogDeriv a N γ y)
    (x := x) hJ hf).congr
  filter_upwards [eventually_ne_zero_complexPhase_compact a N γ x hn] with y hy
  dsimp only [Function.comp_def]
  rw [compactIntegralCLM_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp only [ContinuousMap.mul_apply, compactPhaseLogDeriv_apply a N γ y hy t])

end

end Dubon2026
