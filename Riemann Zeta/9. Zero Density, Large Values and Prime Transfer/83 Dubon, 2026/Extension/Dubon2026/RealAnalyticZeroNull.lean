import Dubon2026.RealAnalyticRadialZeros

/-! # Local nullity of the zeros of a real-analytic function -/

namespace Dubon2026

open Filter Set MeasureTheory Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Shrinking a ball and using almost every radial parameter transfers slice nullity
back to the actual finite-dimensional Haar measure. -/
theorem analytic_ae_ne_zero_smaller_ball_measurable (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℝ f (ball 0 R)) (hn : f 0 ≠ 0) (hm : Measurable f) :
    ∀ᵐ z ∂μ.restrict (ball 0 r), f z ≠ 0 := by
  have hR : 0 < R := hr.trans hrR
  have ha : 0 < r / R := div_pos hr hR
  have hb : r / R < 1 := (div_lt_one hR).mpr hrR
  have hp : volume (Ioo (r / R) 1) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hb)).ne'
  have hall := ae_radial_parameter_ae_ne_zero μ hf hn hm
  have hs : Ioo (r / R) 1 ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨(ha.trans ht.1).le, ht.2.le⟩
  obtain ⟨t, ht, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae_restrict_of_subset hs hall)
  have htpos : 0 < t := ha.trans ht.1
  have hrt : r < t * R := (div_lt_iff₀ hR).mp ht.1
  have hmaps : MapsTo (fun z : V => t⁻¹ • z) (ball 0 r) (ball 0 R) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    have hnr : ‖z‖ < t * R := hz.trans hrt
    exact (inv_mul_lt_iff₀ htpos).mpr (by simpa only [mul_comm] using hnr)
  have hq := (Measure.quasiMeasurePreserving_smul μ (inv_ne_zero htpos.ne')).restrict hmaps
  have hh := hq.ae hgood
  simpa only [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul] using hh

/-- No global measurability assumption is needed: the continuous local function has
an explicit measurable extension, which agrees on the smaller ball. -/
theorem analytic_ae_ne_zero_smaller_ball (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℝ f (ball 0 R)) (hn : f 0 ≠ 0) :
    ∀ᵐ z ∂μ.restrict (ball 0 r), f z ≠ 0 := by
  classical
  let g := (ball (0 : V) R).piecewise f (fun _ => 0)
  have hm : Measurable g := hf.continuousOn.measurable_piecewise
    continuousOn_const measurableSet_ball
  have hg : AnalyticOnNhd ℝ g (ball 0 R) := by
    intro z hz
    apply (hf z hz).congr
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact (piecewise_eq_of_mem _ _ _ hy).symm
  have hn' : g 0 ≠ 0 := by
    simpa only [g, piecewise_eq_of_mem _ _ _ (mem_ball_self (hr.trans hrR))] using hn
  have hg' := analytic_ae_ne_zero_smaller_ball_measurable μ hr hrR hg hn' hm
  filter_upwards [hg', ae_restrict_mem measurableSet_ball] with z hz hzmem
  have hzR : z ∈ ball (0 : V) R := ball_subset_ball hrR.le hzmem
  simpa only [g, piecewise_eq_of_mem _ _ _ hzR] using hz

/-- Translation gives the same local nullity statement at an arbitrary center. -/
theorem analytic_ae_ne_zero_ball_center (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {c : V} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℝ f (ball c R)) (hn : f c ≠ 0) :
    ∀ᵐ z ∂μ.restrict (ball c r), f z ≠ 0 := by
  have hg : AnalyticOnNhd ℝ (fun y => f (c + y)) (ball 0 R) := by
    intro y hy
    have hm : c + y ∈ ball c R := by
      simpa only [mem_ball, dist_self_add_left, dist_zero_right] using hy
    exact AnalyticAt.comp (f := fun y : V => c + y) (hf _ hm)
      (analyticAt_const.add analyticAt_id)
  have hzero : f (c + 0) ≠ 0 := by simpa only [add_zero] using hn
  have hh := analytic_ae_ne_zero_smaller_ball μ hr hrR hg hzero
  have hmaps : MapsTo (fun z : V => -c + z) (ball c r) (ball 0 r) := by
    intro z hz
    simpa only [mem_ball, dist_zero_right, neg_add_eq_sub, dist_eq_norm, sub_zero] using hz
  have hq := (measurePreserving_add_left μ (-c)).quasiMeasurePreserving.restrict hmaps
  have ht := hq.ae hh
  simpa only [add_neg_cancel_left] using ht

end Dubon2026
