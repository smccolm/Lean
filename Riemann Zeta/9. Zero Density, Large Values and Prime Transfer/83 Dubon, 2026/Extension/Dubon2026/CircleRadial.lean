import Dubon2026.BesselJ0
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Radial characteristic functions and the Fourier normalization for the actual circle law -/

namespace Dubon2026

open MeasureTheory
open scoped ComplexConjugate

theorem circle_fourier_angle (θ : ℝ) :
    fourier 1 ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem circle_fourier_shift (z w : UnitAddCircle) :
    fourier 1 (z + w) = fourier 1 z * fourier 1 w := by
  simp only [fourier_one, AddCircle.toCircle_add, Circle.coe_mul]

theorem integral_circle_exp_re_mul (ξ : ℂ) :
    (∫ z : UnitAddCircle, Complex.exp (Complex.I * (((ξ * fourier 1 z).re : ℝ) : ℂ))
      ∂AddCircle.haarAddCircle) = (besselJ0 ‖ξ‖ : ℂ) := by
  let w : UnitAddCircle := ((ξ.arg / (2 * Real.pi) : ℝ) : UnitAddCircle)
  have he (z : UnitAddCircle) : (‖ξ‖ : ℂ) * fourier 1 (z + w) = ξ * fourier 1 z := by
    rw [circle_fourier_shift, show fourier 1 w = Complex.exp ((ξ.arg : ℂ) * Complex.I) from
      circle_fourier_angle ξ.arg]
    calc
      _ = ((‖ξ‖ : ℂ) * Complex.exp ((ξ.arg : ℂ) * Complex.I)) * fourier 1 z := by ring
      _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I]
  have hr (z : UnitAddCircle) : ‖ξ‖ * (fourier 1 (z + w)).re = (ξ * fourier 1 z).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using congrArg Complex.re (he z)
  have hi (z : UnitAddCircle) :
      Complex.exp (Complex.I * (((ξ * fourier 1 z).re : ℝ) : ℂ)) =
        circleExponential ‖ξ‖ (z + w) := by
    change _ = Complex.exp (Complex.I * ((‖ξ‖ * (fourier 1 (z + w)).re : ℝ) : ℂ))
    rw [hr]
  simp_rw [hi]
  rw [integral_add_right_eq_self]
  exact (besselJ0_eq_circleCharacteristic ‖ξ‖).symm

theorem circle_radial_characteristic (ξ : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ z : UnitAddCircle, Complex.exp
      (Complex.I * (((conj ξ * ((c : ℂ) * fourier 1 z)).re : ℝ) : ℂ))
      ∂AddCircle.haarAddCircle) = (besselJ0 (c * ‖ξ‖) : ℂ) := by
  simp_rw [← mul_assoc]
  rw [integral_circle_exp_re_mul]
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [mul_comm]

theorem circle_radial_fourier (ξ : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ z : UnitAddCircle, Complex.exp
      (-(2 * Real.pi : ℝ) * Complex.I * (((conj ξ * ((c : ℂ) * fourier 1 z)).re : ℝ) : ℂ))
      ∂AddCircle.haarAddCircle) = (besselJ0 (2 * Real.pi * c * ‖ξ‖) : ℂ) := by
  have hh := integral_circle_exp_re_mul ((-(2 * Real.pi) : ℂ) * conj ξ * (c : ℂ))
  have he (z : UnitAddCircle) :
      -(2 * Real.pi : ℝ) * Complex.I * (((conj ξ * ((c : ℂ) * fourier 1 z)).re : ℝ) : ℂ) =
      Complex.I * (((((-(2 * Real.pi) : ℂ) * conj ξ * (c : ℂ)) * fourier 1 z).re : ℝ) : ℂ) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, Complex.mul_im, Complex.ofReal_mul, Complex.ofReal_sub,
      show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl]
    push_cast
    ring
  simp_rw [he]
  rw [hh]
  simp [abs_of_nonneg hc, abs_of_pos Real.pi_pos, mul_assoc]
  rw [mul_comm ‖ξ‖ c]

end Dubon2026
