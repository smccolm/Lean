import Dubon2026.GaussianSmoothingBounds
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Identification of test-function integrals by Gaussian smoothing -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace CompactlySupported

noncomputable section

theorem integrable_planarGaussian_test_prod {μ : Measure ℂ} [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 ≤ c) {f : ℂ → ℝ} (hf : Integrable f) :
    Integrable (fun p : ℂ × ℂ => planarGaussian c (p.1 - p.2) * f p.1) (volume.prod μ) := by
  apply ((hf.norm.const_mul (c / Real.pi)).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℂ => (1 : ℝ)) μ)).mono'
  · exact ((continuous_planarGaussian c).comp
      (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul hf.1.comp_fst
  · filter_upwards with p
    simp only [norm_mul, Real.norm_eq_abs, mul_one]
    rw [abs_of_nonneg (planarGaussian_nonneg hc _)]
    exact mul_le_mul_of_nonneg_right (planarGaussian_le hc _) (abs_nonneg _)

theorem integral_planarGaussianSmoothing_test {μ : Measure ℂ} [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 ≤ c) {f : ℂ → ℝ} (hf : Integrable f) :
    (∫ x : ℂ, f x * planarGaussianSmoothing μ c x) =
      ∫ y, (∫ x : ℂ, planarGaussian c (x - y) * f x) ∂μ := by
  unfold planarGaussianSmoothing
  simp_rw [← integral_const_mul, mul_comm (f _)]
  exact integral_integral_swap (integrable_planarGaussian_test_prod hc hf)

theorem tendsto_integral_planarGaussianSmoothing_test {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : ℂ → ℝ} (hf : Integrable f) (hfc : Continuous f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun c : ℝ => ∫ x : ℂ, f x * planarGaussianSmoothing μ c x) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  have ht : Tendsto (fun c : ℝ => ∫ y, (∫ x : ℂ, planarGaussian c (x - y) * f x) ∂μ)
      atTop (𝓝 (∫ y, f y ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      exact (integrable_planarGaussian_test_prod hc.le hf).integral_prod_right.1
    · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      filter_upwards with y
      exact norm_integral_planarGaussian_test_le hc f hB y
    · exact integrable_const _
    · filter_upwards with y
      simpa only [planarGaussian_sub_comm _ y] using
        (tendsto_planarGaussian_test hf (hfc.continuousAt (x := y)))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  exact (integral_planarGaussianSmoothing_test hc.le hf).symm

theorem tendsto_integral_test_planarCharDensity {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) {f : ℂ → ℝ} (hf : Integrable f) :
    Tendsto (fun c : ℝ => ∫ x : ℂ, f x * planarGaussianSmoothing μ c x) atTop
      (𝓝 (∫ x : ℂ, f x * planarCharDensity μ x)) := by
  let L : ℝ := ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ, ‖charFun μ ξ‖
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * L)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact hf.1.mul (continuous_planarGaussianSmoothing μ hc.le).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs (planarGaussianSmoothing μ c x),
      abs_of_nonneg (planarGaussianSmoothing_nonneg μ hc.le x)]
    exact mul_le_mul_of_nonneg_left (planarGaussianSmoothing_le hμ hc x) (norm_nonneg _)
  · exact hf.norm.mul_const L
  · filter_upwards with x
    exact (tendsto_planarGaussianSmoothing hμ x).const_mul (f x)

/-- The continuous inverse integral gives the actual measure on every compact test. -/
theorem integral_test_planarCharDensity {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (f : C_c(ℂ, ℝ)) :
    (∫ x : ℂ, f x * planarCharDensity μ x) = ∫ x, f x ∂μ := by
  have hf : Integrable f := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  exact tendsto_nhds_unique (tendsto_integral_test_planarCharDensity hμ hf)
    (tendsto_integral_planarGaussianSmoothing_test hf f.continuous
      (fun x => f.toBoundedContinuousFunction.norm_coe_le_norm x))

end

end Dubon2026
