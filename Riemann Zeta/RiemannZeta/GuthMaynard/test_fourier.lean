import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Complex

noncomputable def fourierTransformΦ (Φ : ℝ → ℝ) (ξ : ℝ) : ℂ := 0

lemma fourier_inversion_integrand_bound (Φ : ℝ → ℝ) (ξ x : ℝ) :
  ‖fourierTransformΦ Φ ξ * cexp (2 * Real.pi * I * x * ξ)‖ = ‖fourierTransformΦ Φ ξ‖ := by
  rw [norm_mul]
  have h_im : 2 * Real.pi * I * x * ξ = ((2 * Real.pi * x * ξ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h_im]
  have h_norm : ‖cexp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * I)‖ = 1 := by simp
  rw [h_norm, mul_one]
