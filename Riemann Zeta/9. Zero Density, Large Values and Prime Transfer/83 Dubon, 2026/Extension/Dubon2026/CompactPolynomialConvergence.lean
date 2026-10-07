import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Weak probability convergence from polynomial integrals on a common interval -/

namespace Dubon2026

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A continuous function is integrable for a finite measure concentrated on a compact interval. -/
theorem continuous_integrable_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g μ := by
  have he : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem hμ
  have hi : IntegrableOn g (Icc a b) μ := hg.integrableOn_Icc
  simpa only [IntegrableOn, he] using hi

/-- Uniform approximation on the actual support controls the probability integral by the same error. -/
theorem probability_integral_sub_le_on_Icc (μ : ProbabilityMeasure ℝ) {a b ε : ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) {g h : ℝ → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hε : ∀ x ∈ Icc a b, |g x - h x| ≤ ε) :
    |(∫ x, g x ∂(μ : Measure ℝ)) - ∫ x, h x ∂(μ : Measure ℝ)| ≤ ε := by
  rw [← integral_sub (continuous_integrable_of_ae_mem_Icc hμ hg)
    (continuous_integrable_of_ae_mem_Icc hμ hh), ← Real.norm_eq_abs]
  have hb : ∀ᵐ x ∂(μ : Measure ℝ), ‖g x - h x‖ ≤ ε := by
    filter_upwards [hμ] with x hx
    simpa only [Real.norm_eq_abs] using hε x hx
  simpa using norm_integral_le_of_norm_le_const hb

/-- Polynomial test convergence on a fixed compact interval gives genuine weak probability convergence. -/
theorem probability_tendsto_of_polynomial_integrals {μs : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} {a b : ℝ}
    (hs : ∀ N, ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Icc a b)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b)
    (hpoly : ∀ p : Polynomial ℝ,
      Tendsto (fun N => ∫ x, p.eval x ∂(μs N : Measure ℝ)) atTop
        (𝓝 (∫ x, p.eval x ∂(μ : Measure ℝ)))) :
    Tendsto μs atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b g g.continuous.continuousOn
    (ε / 3) (by positivity)
  have he (ν : ProbabilityMeasure ℝ) (hν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b) :
      |(∫ x, p.eval x ∂(ν : Measure ℝ)) - ∫ x, g x ∂(ν : Measure ℝ)| ≤ ε / 3 :=
    probability_integral_sub_le_on_Icc ν hν p.continuous g.continuous
      (fun x hx => (hp x hx).le)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpoly p) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hpN := hN n hn
  have ha := he (μs n) (hs n)
  have hb := he μ hμ
  rw [Real.dist_eq] at hpN ⊢
  have ht := abs_add_three
    ((∫ x, g x ∂(μs n : Measure ℝ)) - ∫ x, p.eval x ∂(μs n : Measure ℝ))
    ((∫ x, p.eval x ∂(μs n : Measure ℝ)) - ∫ x, p.eval x ∂(μ : Measure ℝ))
    ((∫ x, p.eval x ∂(μ : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ))
  rw [abs_sub_comm (∫ x, g x ∂(μs n : Measure ℝ))] at ht
  have hid : ((∫ x, g x ∂(μs n : Measure ℝ)) - ∫ x, p.eval x ∂(μs n : Measure ℝ)) +
      ((∫ x, p.eval x ∂(μs n : Measure ℝ)) - ∫ x, p.eval x ∂(μ : Measure ℝ)) +
      ((∫ x, p.eval x ∂(μ : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ)) =
      (∫ x, g x ∂(μs n : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ) := by ring
  rw [hid] at ht
  linarith

end
end Dubon2026
