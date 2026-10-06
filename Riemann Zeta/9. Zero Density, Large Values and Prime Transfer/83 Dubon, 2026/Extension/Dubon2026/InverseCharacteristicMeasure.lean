import Dubon2026.PlanarGaussian

/-! # Convolution identity for the actual finite-measure characteristic function -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

theorem inverseCharacteristicKernel_mul_character (x y ξ : ℂ) :
    inverseCharacteristicKernel x ξ * Complex.exp ((inner ℝ y ξ : ℝ) * Complex.I) =
      inverseCharacteristicKernel (x - y) ξ := by
  unfold inverseCharacteristicKernel
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub]
  ring

theorem inverseCharacteristicKernel_convolution {μ : Measure ℂ} [IsFiniteMeasure μ]
    {φ : ℂ → ℂ} (hφ : Integrable φ) (x : ℂ) :
    (∫ ξ : ℂ, inverseCharacteristicKernel x ξ * (φ ξ * charFun μ ξ)) =
      ∫ y, (∫ ξ : ℂ, inverseCharacteristicKernel (x - y) ξ * φ ξ) ∂μ := by
  have hprod : Integrable (fun p : ℂ × ℂ =>
      inverseCharacteristicKernel (x - p.2) p.1 * φ p.1) (volume.prod μ) := by
    apply (hφ.norm.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℂ => (1 : ℝ)) μ)).mono'
    · exact (continuous_inverseCharacteristicKernel.comp
        ((continuous_const.sub continuous_snd).prodMk continuous_fst)).aestronglyMeasurable.mul
          hφ.1.comp_fst
    · filter_upwards with p
      simp only [norm_mul, norm_inverseCharacteristicKernel, one_mul, mul_one, le_refl]
  calc
    (∫ ξ : ℂ, inverseCharacteristicKernel x ξ * (φ ξ * charFun μ ξ)) =
        ∫ ξ : ℂ, ∫ y, inverseCharacteristicKernel (x - y) ξ * φ ξ ∂μ := by
      congr 1
      ext ξ
      rw [charFun_apply, ← integral_const_mul, ← integral_const_mul]
      congr 1
      ext y
      rw [← inverseCharacteristicKernel_mul_character]
      ring
    _ = ∫ y, (∫ ξ : ℂ, inverseCharacteristicKernel (x - y) ξ * φ ξ) ∂μ :=
      integral_integral_swap hprod

theorem planarInverseCharacteristic_convolution {μ : Measure ℂ} [IsFiniteMeasure μ]
    {φ : ℂ → ℂ} (hφ : Integrable φ) (x : ℂ) :
    planarInverseCharacteristic (fun ξ => φ ξ * charFun μ ξ) x =
      ∫ y, planarInverseCharacteristic φ (x - y) ∂μ := by
  unfold planarInverseCharacteristic
  rw [inverseCharacteristicKernel_convolution hφ, integral_smul]

/-- Gaussian smoothing of the actual finite measure, expressed by its characteristic function. -/
theorem planarGaussian_convolution_inverse {μ : Measure ℂ} [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 < c) (x : ℂ) :
    planarInverseCharacteristic (fun ξ : ℂ =>
      Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * charFun μ ξ) x =
      ∫ y, (planarGaussian c (x - y) : ℂ) ∂μ := by
  have hi : Integrable (fun ξ : ℂ => Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := ℂ) (b := (((4 * c)⁻¹ : ℝ) : ℂ)) (by simp; positivity) 0 0
  rw [planarInverseCharacteristic_convolution hi]
  simp_rw [inverse_integral_gaussian hc]

end

end Dubon2026
