import Dubon2026.InverseCharacteristicMeasure

/-! # Positive Gaussian approximations to the continuous inverse integral -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- The real inverse integral, before its measure-identification theorem. -/
def planarCharDensity (μ : Measure ℂ) (x : ℂ) : ℝ :=
  (planarInverseCharacteristic (charFun μ) x).re

/-- Convolution of a finite measure with the normalized planar Gaussian. -/
def planarGaussianSmoothing (μ : Measure ℂ) (c : ℝ) (x : ℂ) : ℝ :=
  ∫ y, planarGaussian c (x - y) ∂μ

theorem tendsto_gaussian_damped_inverse {φ : ℂ → ℂ} (hφ : Integrable φ) (x : ℂ) :
    Tendsto (fun c : ℝ => planarInverseCharacteristic
      (fun ξ : ℂ => Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2) * φ ξ) x)
      atTop (𝓝 (planarInverseCharacteristic φ x)) := by
  have h := (Real.tendsto_integral_cexp_sq_smul
    (integrable_inverseCharacteristicKernel_mul hφ x)).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hs := h.const_smul (((2 * Real.pi) ^ 2)⁻¹ : ℝ)
  convert hs using 1
  ext c
  unfold planarInverseCharacteristic
  congr 1
  congr 1
  ext ξ
  simp only [id_eq, smul_eq_mul]
  ring

theorem tendsto_planarGaussianSmoothing_complex {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (x : ℂ) :
    Tendsto (fun c : ℝ => (planarGaussianSmoothing μ c x : ℂ)) atTop
      (𝓝 (planarInverseCharacteristic (charFun μ) x)) := by
  apply (tendsto_gaussian_damped_inverse hμ x).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  rw [planarGaussian_convolution_inverse hc, integral_complex_ofReal]
  rfl

theorem tendsto_planarGaussianSmoothing {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (x : ℂ) :
    Tendsto (fun c : ℝ => planarGaussianSmoothing μ c x) atTop
      (𝓝 (planarCharDensity μ x)) := by
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_planarGaussianSmoothing_complex hμ x)

theorem planarGaussianSmoothing_nonneg (μ : Measure ℂ) {c : ℝ} (hc : 0 ≤ c) (x : ℂ) :
    0 ≤ planarGaussianSmoothing μ c x :=
  integral_nonneg (fun y => planarGaussian_nonneg hc (x - y))

theorem planarCharDensity_nonneg {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (charFun μ)) (x : ℂ) : 0 ≤ planarCharDensity μ x := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_planarGaussianSmoothing hμ x)
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with c hc
  exact planarGaussianSmoothing_nonneg μ hc x

theorem continuous_planarCharDensity {μ : Measure ℂ} (hμ : Integrable (charFun μ)) :
    Continuous (planarCharDensity μ) :=
  Complex.continuous_re.comp (continuous_planarInverseCharacteristic hμ)

theorem planarCharDensity_le (μ : Measure ℂ) (x : ℂ) :
    planarCharDensity μ x ≤ ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ, ‖charFun μ ξ‖ :=
  (Complex.re_le_norm _).trans (norm_planarInverseCharacteristic_le _ _)

end

end Dubon2026
