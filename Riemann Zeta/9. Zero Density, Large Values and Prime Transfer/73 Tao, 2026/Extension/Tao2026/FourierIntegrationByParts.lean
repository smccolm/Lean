import Tao2026.TorusFourier

/-!
# Cubic Fourier decay by periodic integration by parts

This module isolates the one-dimensional analytic calculation used on slices
of Tao's two-dimensional periodic weight.  It proves one and three successive
unit-interval integrations by parts, including a quantitative norm bound in
terms of the third derivative.  The remaining two-dimensional step must
identify the relevant slices and compare their derivative bound with
`taoC3Norm`.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate Interval

namespace Tao2026

noncomputable section

theorem fourierCoeffOn_zero_one_eq_deriv
    {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hper : f 0 = f 1)
    (hint : IntervalIntegrable f' volume 0 1) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      (1 / (2 * (Real.pi : ℂ) * I * (n : ℂ))) *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f' n := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (fun x _ => hderiv x) hint]
  simp only [hper, sub_self, mul_zero, zero_sub]
  norm_num

theorem norm_fourierCoeffOn_zero_one_le
    {f : ℝ → ℂ} {B : ℝ}
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ B) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤ B := by
  have hformula := fourierCoeffOn_eq_integral f n
    (by norm_num : (0 : ℝ) < 1)
  norm_num at hformula
  rw [hformula]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := 1) (C := B) ?_).trans ?_
  · intro x hx
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * I * (n : ℂ) * (x : ℂ)) =
        fourier n (x : UnitAddCircle) := by
      simpa only [ofReal_one, div_one] using
        (fourier_coe_apply (T := (1 : ℝ)) (n := n) (x := x)).symm
    rw [hexp]
    rw [norm_mul]
    change ‖conj (fourier n (x : UnitAddCircle))‖ * ‖f x‖ ≤ B
    rw [Complex.norm_conj]
    simp only [fourier_apply, Circle.norm_coe, one_mul]
    have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [uIcc_of_le] using hx
    exact hbound x ⟨hx'.1.le, hx'.2⟩
  · norm_num

/-- The norm of the reciprocal derivative multiplier in the unit-period
Fourier convention. -/
theorem norm_fourierDerivativeMultiplier (n : ℤ) :
    ‖1 / (2 * (Real.pi : ℂ) * I * (n : ℂ))‖ =
      (2 * Real.pi * |(n : ℝ)|)⁻¹ := by
  rw [div_eq_mul_inv, one_mul, norm_inv, norm_mul, norm_mul, norm_mul]
  simp only [norm_ofNat, norm_real, norm_I, norm_intCast, mul_one]
  rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Three integrations by parts for a periodic unit-interval function. -/
theorem fourierCoeffOn_zero_one_eq_thirdDeriv
    {f₀ f₁ f₂ f₃ : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hderiv₀ : ∀ x, HasDerivAt f₀ (f₁ x) x)
    (hderiv₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hderiv₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hper₀ : f₀ 0 = f₀ 1) (hper₁ : f₁ 0 = f₁ 1)
    (hper₂ : f₂ 0 = f₂ 1)
    (hint₁ : IntervalIntegrable f₁ volume 0 1)
    (hint₂ : IntervalIntegrable f₂ volume 0 1)
    (hint₃ : IntervalIntegrable f₃ volume 0 1) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f₀ n =
      (1 / (2 * (Real.pi : ℂ) * I * (n : ℂ))) ^ 3 *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f₃ n := by
  rw [fourierCoeffOn_zero_one_eq_deriv hn hderiv₀ hper₀ hint₁,
    fourierCoeffOn_zero_one_eq_deriv hn hderiv₁ hper₁ hint₂,
    fourierCoeffOn_zero_one_eq_deriv hn hderiv₂ hper₂ hint₃]
  ring

/-- Quantitative one-dimensional cubic Fourier decay after three periodic
integrations by parts. -/
theorem norm_fourierCoeffOn_zero_one_le_thirdDeriv
    {f₀ f₁ f₂ f₃ : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hderiv₀ : ∀ x, HasDerivAt f₀ (f₁ x) x)
    (hderiv₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hderiv₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hper₀ : f₀ 0 = f₀ 1) (hper₁ : f₁ 0 = f₁ 1)
    (hper₂ : f₂ 0 = f₂ 1)
    (hint₁ : IntervalIntegrable f₁ volume 0 1)
    (hint₂ : IntervalIntegrable f₂ volume 0 1)
    (hint₃ : IntervalIntegrable f₃ volume 0 1)
    {B : ℝ} (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f₃ x‖ ≤ B) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f₀ n‖ ≤
      ‖1 / (2 * (Real.pi : ℂ) * I * (n : ℂ))‖ ^ 3 * B := by
  rw [fourierCoeffOn_zero_one_eq_thirdDeriv hn hderiv₀ hderiv₁ hderiv₂
    hper₀ hper₁ hper₂ hint₁ hint₂ hint₃, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (norm_fourierCoeffOn_zero_one_le hbound n) (by positivity)

/-- The preceding estimate with the multiplier norm evaluated explicitly. -/
theorem norm_fourierCoeffOn_zero_one_le_thirdDeriv_explicit
    {f₀ f₁ f₂ f₃ : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hderiv₀ : ∀ x, HasDerivAt f₀ (f₁ x) x)
    (hderiv₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hderiv₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hper₀ : f₀ 0 = f₀ 1) (hper₁ : f₁ 0 = f₁ 1)
    (hper₂ : f₂ 0 = f₂ 1)
    (hint₁ : IntervalIntegrable f₁ volume 0 1)
    (hint₂ : IntervalIntegrable f₂ volume 0 1)
    (hint₃ : IntervalIntegrable f₃ volume 0 1)
    {B : ℝ} (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f₃ x‖ ≤ B) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f₀ n‖ ≤
      (2 * Real.pi * |(n : ℝ)|)⁻¹ ^ 3 * B := by
  simpa only [norm_fourierDerivativeMultiplier] using
    norm_fourierCoeffOn_zero_one_le_thirdDeriv hn hderiv₀ hderiv₁ hderiv₂
      hper₀ hper₁ hper₂ hint₁ hint₂ hint₃ hbound

end

end Tao2026
