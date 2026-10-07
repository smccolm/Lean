import Dubon2026.AnalyticVerticalPolynomial
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # One-dimensional analytic slices and almost-everywhere radial nonvanishing -/

namespace Dubon2026

open Filter Set MeasureTheory Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A nonzero value on a connected real interval rules out a positive-measure zero set. -/
theorem analytic_ae_ne_zero_interval {f : ℝ → ℝ} {a b t₀ : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (ht₀ : t₀ ∈ Icc a b) (hn : f t₀ ≠ 0) :
    ∀ᵐ t ∂volume.restrict (Icc a b), f t ≠ 0 := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Icc with hz | hnz
  · exact (hn (hz ht₀)).elim
  · exact ae_restrict_le_codiscreteWithin measurableSet_Icc hnz

theorem smul_mem_ball_zero_of_mem_unitInterval {R : ℝ} {z : V}
    (hz : z ∈ ball 0 R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • z ∈ ball 0 R := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz

theorem analytic_radial_ae_ne_zero {f : V → ℝ} {R : ℝ}
    (hf : AnalyticOnNhd ℝ f (ball 0 R)) (hn : f 0 ≠ 0) {z : V} (hz : z ∈ ball 0 R) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), f (t • z) ≠ 0 := by
  apply analytic_ae_ne_zero_interval (t₀ := 0)
  · intro t ht
    exact AnalyticAt.comp (f := fun u : ℝ => u • z)
      (hf (t • z) (smul_mem_ball_zero_of_mem_unitInterval hz ht))
      (analyticAt_id.smul analyticAt_const)
  · exact ⟨le_rfl, zero_le_one⟩
  · simpa only [zero_smul] using hn

variable [MeasurableSpace V] [BorelSpace V]

theorem ae_radial_parameter_ae_ne_zero (μ : Measure V) [SFinite μ]
    {f : V → ℝ} {R : ℝ} (hf : AnalyticOnNhd ℝ f (ball 0 R)) (hn : f 0 ≠ 0)
    (hm : Measurable f) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ∀ᵐ z ∂μ.restrict (ball 0 R), f (t • z) ≠ 0 := by
  have hset : MeasurableSet {x : V × ℝ | f (x.2 • x.1) ≠ 0} :=
    ((hm.comp (measurable_snd.smul measurable_fst)) (measurableSet_singleton 0)).compl
  apply (Measure.ae_ae_comm hset).mp
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact analytic_radial_ae_ne_zero hf hn hz

end Dubon2026
