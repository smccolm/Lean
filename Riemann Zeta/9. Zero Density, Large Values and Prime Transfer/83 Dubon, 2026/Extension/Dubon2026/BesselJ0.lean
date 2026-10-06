import Dubon2026.CircleSeries
import Dubon2026.CircleGaussian

/-! # The source's J0 power series and its actual circle-integral representation -/

namespace Dubon2026

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- The literal real power series in equation (J0-definition) of the frozen source. -/
def besselJ0 (u : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n)

theorem bessel_circle_exponent (u : ℝ) (z : UnitAddCircle) :
    (Complex.I * (u : ℂ) / 2) * fourier 1 z +
      (Complex.I * (u : ℂ) / 2) * fourier (-1) z =
        Complex.I * ((u * (fourier 1 z).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.re_eq_add_conj, ← fourier_neg]
  ring

theorem bessel_diagonal_coefficient (u : ℝ) (n : ℕ) :
    (Complex.I * (u : ℂ) / 2) ^ (2 * n) / (n.factorial : ℂ) ^ 2 =
      (((-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n) : ℝ) : ℂ) := by
  push_cast
  rw [show Complex.I * (u : ℂ) / 2 = Complex.I * ((u : ℂ) / 2) by ring,
    mul_pow, pow_mul, Complex.I_sq]
  ring

theorem hasSum_besselJ0_complex (u : ℝ) :
    HasSum (fun n : ℕ =>
      (((-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n) : ℝ) : ℂ))
      (circleCharacteristic u) := by
  have hh := hasSum_circle_integral_diagonal (Complex.I * (u : ℂ) / 2)
  simp_rw [bessel_diagonal_coefficient, bessel_circle_exponent] at hh
  exact hh

theorem hasSum_besselJ0 (u : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (n.factorial : ℝ) ^ 2 * (u / 2) ^ (2 * n))
      (circleCharacteristic u).re := by
  exact (hasSum_besselJ0_complex u).map Complex.reCLM Complex.reCLM.continuous

theorem besselJ0_eq_re_circleCharacteristic (u : ℝ) :
    besselJ0 u = (circleCharacteristic u).re :=
  (hasSum_besselJ0 u).tsum_eq

theorem besselJ0_eq_circleCharacteristic (u : ℝ) :
    (besselJ0 u : ℂ) = circleCharacteristic u := by
  apply Complex.ext
  · exact besselJ0_eq_re_circleCharacteristic u
  · simp only [Complex.ofReal_im, circleCharacteristic_im]

theorem besselJ0_eq_circle_integral (u : ℝ) :
    (besselJ0 u : ℂ) = (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi,
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)) := by
  rw [besselJ0_eq_circleCharacteristic, circleCharacteristic_eq_interval]

theorem besselJ0_zero : besselJ0 0 = 1 := by
  rw [besselJ0_eq_re_circleCharacteristic, circleCharacteristic_zero, Complex.one_re]

theorem continuous_besselJ0 : Continuous besselJ0 := by
  simp_rw [funext besselJ0_eq_re_circleCharacteristic]
  exact Complex.continuous_re.comp continuous_circleCharacteristic

theorem abs_besselJ0_le_one (u : ℝ) : |besselJ0 u| ≤ 1 := by
  rw [besselJ0_eq_re_circleCharacteristic, ← norm_circleCharacteristic_eq_abs_re]
  exact norm_circleCharacteristic_le_one u

theorem abs_besselJ0_lt_one {u : ℝ} (hu : u ≠ 0) : |besselJ0 u| < 1 := by
  rw [besselJ0_eq_re_circleCharacteristic, ← norm_circleCharacteristic_eq_abs_re]
  exact norm_circleCharacteristic_lt_one hu

theorem abs_besselJ0_le_gaussian {u : ℝ} (hu : |u| ≤ 1) :
    |besselJ0 u| ≤ Real.exp (-u ^ 2 / Real.pi ^ 2) := by
  rw [besselJ0_eq_re_circleCharacteristic, ← norm_circleCharacteristic_eq_abs_re]
  exact norm_circleCharacteristic_le_gaussian hu

end

end Dubon2026
