import Dubon2026.RealAnalyticZeroNull
import Mathlib.Topology.Instances.Sign

/-! # Almost-everywhere continuity of signs of real-analytic functions -/

namespace Dubon2026

open Filter Set MeasureTheory Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- At an analytic point, a neighborhood is either identically zero or has a null zero set. -/
theorem analytic_exists_ball_zero_or_ae_ne (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {x : V} (hf : AnalyticAt ℝ f x) :
    ∃ r > 0, EqOn f 0 (ball x r) ∨ ∀ᵐ y ∂μ.restrict (ball x r), f y ≠ 0 := by
  by_cases hzero : ∀ᶠ y in 𝓝 x, f y = 0
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hzero
    exact ⟨r, hr, Or.inl (fun y hy => hball hy)⟩
  · obtain ⟨R, hR, hA⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
    have hy : ∃ y ∈ ball x (R / 8), f y ≠ 0 := by
      by_contra h
      push Not at h
      apply hzero
      filter_upwards [ball_mem_nhds x (by linarith : 0 < R / 8)] with y hy
      exact h y hy
    obtain ⟨y, hy, hfy⟩ := hy
    have hsmall : ball x (R / 8) ⊆ ball y (R / 4) := by
      intro z hz
      have hd := dist_triangle z x y
      rw [mem_ball] at hy hz ⊢
      rw [dist_comm x y] at hd
      linarith
    have hlarge : ball y (R / 2) ⊆ ball x R := by
      intro z hz
      have hd := dist_triangle z y x
      rw [mem_ball] at hy hz ⊢
      linarith
    have ha : AnalyticOnNhd ℝ f (ball y (R / 2)) := fun z hz => hA (hlarge hz)
    have hn := analytic_ae_ne_zero_ball_center μ (by linarith : 0 < R / 4)
      (by linarith : R / 4 < R / 2) ha hfy
    exact ⟨R / 8, by linarith, Or.inr (ae_restrict_of_ae_restrict_of_subset hsmall hn)⟩

/-- Every analytic point has a neighborhood where the sign is continuous almost everywhere. -/
theorem analytic_exists_ball_ae_continuousAt_sign (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {x : V} (hf : AnalyticAt ℝ f x) :
    ∃ r > 0, ∀ᵐ y ∂μ.restrict (ball x r), ContinuousAt (fun z => SignType.sign (f z)) y := by
  obtain ⟨r, hr, hzero | hn⟩ := analytic_exists_ball_zero_or_ae_ne μ hf
  · refine ⟨r, hr, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    apply (continuousAt_const (y := (0 : SignType))).congr
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [hzero hz, Pi.zero_apply, sign_zero]
  · obtain ⟨s, hs, hc⟩ := Metric.eventually_nhds_iff.mp hf.eventually_continuousAt
    refine ⟨min r s, lt_min hr hs, ?_⟩
    have hsub : ball x (min r s) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hn,
      ae_restrict_mem measurableSet_ball] with y hy hyball
    have hc' : ContinuousAt f y := hc (lt_of_lt_of_le hyball (min_le_right _ _))
    exact (continuousAt_sign_of_ne_zero hy).comp hc'

/-- A countable neighborhood cover gives almost-everywhere sign continuity on any
set on which the original function is analytic in a neighborhood. -/
theorem analytic_ae_continuousAt_sign (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {s : Set V} (hf : AnalyticOnNhd ℝ f s) :
    ∀ᵐ y ∂μ.restrict s, ContinuousAt (fun z => SignType.sign (f z)) y := by
  classical
  have hlocal : ∀ x ∈ s, ∃ r > 0,
      ∀ᵐ y ∂μ.restrict (ball x r), ContinuousAt (fun z => SignType.sign (f z)) y :=
    fun x hx => analytic_exists_ball_ae_continuousAt_sign μ (hf x hx)
  choose! r hr hgood using hlocal
  obtain ⟨t, hts, ht, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (r x)) (fun x hx =>
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx)))
  apply ae_restrict_of_ae_restrict_of_subset hcover
  apply (ae_restrict_biUnion_iff (fun x => ball x (r x)) ht _).mpr
  intro x hx
  exact hgood x (hts hx)

/-- Any function of finitely many analytic signs is continuous almost everywhere.
The finite sign representation itself remains a separate algebraic obligation. -/
theorem analytic_finite_signs_ae_continuousAt (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι] {W : Type*} [TopologicalSpace W]
    (F : (ι → SignType) → W) {f : ι → V → ℝ} {s : Set V}
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) s) :
    ∀ᵐ y ∂μ.restrict s, ContinuousAt (fun z => F (fun i => SignType.sign (f i z))) y := by
  have ha : ∀ᵐ y ∂μ.restrict s, ∀ i, ContinuousAt (fun z => SignType.sign (f i z)) y :=
    ae_all_iff.mpr (fun i => analytic_ae_continuousAt_sign μ (hf i))
  filter_upwards [ha] with y hy
  have hc : Continuous F := continuous_of_discreteTopology
  exact hc.continuousAt.comp (continuousAt_pi.mpr hy)

end Dubon2026
