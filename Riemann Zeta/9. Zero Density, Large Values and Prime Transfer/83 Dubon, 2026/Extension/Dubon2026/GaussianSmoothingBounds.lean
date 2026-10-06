import Dubon2026.GaussianTestKernel

/-! # Uniform bounds and integrability for the actual Gaussian-smoothed measure -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

theorem norm_gaussian_damping_le {c : ℝ} (hc : 0 ≤ c) (ξ : ℂ) :
    ‖Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2)‖ ≤ 1 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)

theorem integrable_gaussian_damped {φ : ℂ → ℂ} (hφ : Integrable φ)
    {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun ξ : ℂ => Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * φ ξ) := by
  apply hφ.norm.mono'
  · exact (by fun_prop : Continuous (fun ξ : ℂ =>
      Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2))).aestronglyMeasurable.mul hφ.1
  · filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussian_damping_le hc ξ)

theorem planarGaussianSmoothing_le {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) {c : ℝ} (hc : 0 < c) (x : ℂ) :
    planarGaussianSmoothing μ c x ≤
      ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ, ‖charFun μ ξ‖ := by
  have he : (planarGaussianSmoothing μ c x : ℂ) =
      planarInverseCharacteristic (fun ξ : ℂ =>
        Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * charFun μ ξ) x := by
    rw [planarGaussian_convolution_inverse hc, integral_complex_ofReal]
    rfl
  calc
    planarGaussianSmoothing μ c x ≤ ‖(planarGaussianSmoothing μ c x : ℂ)‖ := by
      simpa only [Complex.ofReal_re] using Complex.re_le_norm (planarGaussianSmoothing μ c x : ℂ)
    _ = ‖planarInverseCharacteristic (fun ξ : ℂ =>
        Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * charFun μ ξ) x‖ := congrArg norm he
    _ ≤ ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ,
        ‖Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * charFun μ ξ‖ :=
      norm_planarInverseCharacteristic_le _ _
    _ ≤ ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ, ‖charFun μ ξ‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono (integrable_gaussian_damped hμ hc.le).norm hμ.norm
      intro ξ
      dsimp only
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_gaussian_damping_le hc.le ξ)

theorem integrable_planarGaussian_finite_measure (μ : Measure ℂ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 ≤ c) (x : ℂ) :
    Integrable (fun y => planarGaussian c (x - y)) μ := by
  apply (integrable_const (c / Real.pi)).mono'
  · exact ((continuous_planarGaussian c).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (planarGaussian_nonneg hc _)]
    exact planarGaussian_le hc _

theorem continuous_planarGaussianSmoothing (μ : Measure ℂ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 ≤ c) : Continuous (planarGaussianSmoothing μ c) := by
  apply continuous_of_dominated (bound := fun _ => c / Real.pi)
  · exact fun x => (integrable_planarGaussian_finite_measure μ hc x).1
  · intro x
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (planarGaussian_nonneg hc _)]
    exact planarGaussian_le hc _
  · exact integrable_const _
  · filter_upwards with y
    exact (continuous_planarGaussian c).comp (continuous_id.sub continuous_const)

end

end Dubon2026
