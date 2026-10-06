import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Fourier.Inversion

/-! # The inverse integral of an integrable planar characteristic function

This module constructs the continuous bounded inverse integral. Identification
with the density of the original measure is a separate theorem.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- The inverse-characteristic kernel, with the probability convention. -/
def inverseCharacteristicKernel (x ξ : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ))

/-- The planar inverse integral; the normalization is `(2π)⁻²`. -/
def planarInverseCharacteristic (φ : ℂ → ℂ) (x : ℂ) : ℂ :=
  ((2 * Real.pi) ^ 2)⁻¹ • ∫ ξ : ℂ, inverseCharacteristicKernel x ξ * φ ξ

theorem norm_inverseCharacteristicKernel (x ξ : ℂ) :
    ‖inverseCharacteristicKernel x ξ‖ = 1 := by
  unfold inverseCharacteristicKernel
  rw [show -Complex.I * (inner ℝ x ξ : ℝ) =
    Complex.I * ((-(inner ℝ x ξ) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

theorem continuous_inverseCharacteristicKernel :
    Continuous (fun p : ℂ × ℂ => inverseCharacteristicKernel p.1 p.2) := by
  unfold inverseCharacteristicKernel
  fun_prop

theorem integrable_inverseCharacteristicKernel_mul {φ : ℂ → ℂ}
    (hφ : Integrable φ) (x : ℂ) :
    Integrable (fun ξ => inverseCharacteristicKernel x ξ * φ ξ) := by
  apply hφ.norm.mono'
  · exact ((continuous_inverseCharacteristicKernel.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul hφ.1
  · filter_upwards with ξ
    simp only [norm_mul, norm_inverseCharacteristicKernel, one_mul, le_refl]

theorem continuous_planarInverseCharacteristic {φ : ℂ → ℂ} (hφ : Integrable φ) :
    Continuous (planarInverseCharacteristic φ) := by
  apply Continuous.const_smul
  apply continuous_of_dominated (bound := fun ξ => ‖φ ξ‖)
  · exact fun x => (integrable_inverseCharacteristicKernel_mul hφ x).1
  · intro x
    filter_upwards with ξ
    simp only [norm_mul, norm_inverseCharacteristicKernel, one_mul, le_refl]
  · exact hφ.norm
  · filter_upwards with ξ
    exact (continuous_inverseCharacteristicKernel.comp
      (continuous_id.prodMk continuous_const)).mul continuous_const

theorem norm_planarInverseCharacteristic_le (φ : ℂ → ℂ) (x : ℂ) :
    ‖planarInverseCharacteristic φ x‖ ≤
      ((2 * Real.pi) ^ 2)⁻¹ * ∫ ξ : ℂ, ‖φ ξ‖ := by
  unfold planarInverseCharacteristic
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∫ ξ : ℂ, inverseCharacteristicKernel x ξ * φ ξ‖ ≤
        ∫ ξ : ℂ, ‖inverseCharacteristicKernel x ξ * φ ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ : ℂ, ‖φ ξ‖ := by
      simp only [norm_mul, norm_inverseCharacteristicKernel, one_mul]

end

end Dubon2026
