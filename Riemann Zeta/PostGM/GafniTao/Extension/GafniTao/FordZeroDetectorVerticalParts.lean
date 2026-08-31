import GafniTao.FordLogNormDerivative

/-!
# Vertical integration by parts in Ford's zero detector

On either detector line `Re z = ±η`, Ford's cotangent is the purely
imaginary function `-(π/(2η)) i tanh u`.  This file proves that identity
with its literal normalization and the real integration-by-parts formula
which changes a logarithmic derivative into the source weight
`cosh(u)^{-2}`.  Boundary terms remain explicit.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

theorem fordCotKernel_pos_vertical {eta : ℝ} (heta : 0 < eta) (u : ℝ) :
    fordCotKernel eta
      ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I := by
  unfold fordCotKernel Complex.cot
  rw [fordCotKernel_scale_mul heta]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) + (u : ℂ) * I =
      (u : ℂ) * I + (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two,
    Complex.sin_mul_I, Complex.cos_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Real.tanh_eq_sinh_div_cosh]
  push_cast
  ring

theorem fordCotKernel_neg_vertical {eta : ℝ} (heta : 0 < eta) (u : ℝ) :
    fordCotKernel eta
      ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I := by
  unfold fordCotKernel Complex.cot
  rw [fordCotKernel_scale_neg_mul heta]
  rw [show (-((Real.pi / 2 : ℝ) : ℂ)) + (u : ℂ) * I =
      (u : ℂ) * I - (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two,
    Complex.sin_mul_I, Complex.cos_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Real.tanh_eq_sinh_div_cosh]
  push_cast
  ring

theorem hasDerivAt_tanh_sechSq (u : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh u ^ 2) u := by
  have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u)
    (Real.cosh_pos u).ne'
  convert h using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · have hcs := Real.cosh_sq_sub_sinh_sq u
    rw [show Real.cosh u * Real.cosh u -
        Real.sinh u * Real.sinh u = 1 by nlinarith]

/-- Ford's exact finite-height Abel identity.  No endpoint is discarded:
the two displayed boundary terms are the ones cancelled by the horizontal
edges before taking the good-height limit. -/
theorem integral_tanh_mul_deriv_eq_boundary_sub_sechSq
    {q q' : ℝ → ℝ} {a b : ℝ}
    (hq : ∀ u ∈ uIcc a b, HasDerivAt q (q' u) u)
    (hq' : IntervalIntegrable q' volume a b) :
    (∫ u in a..b, Real.tanh u * q' u) =
      Real.tanh b * q b - Real.tanh a * q a -
        ∫ u in a..b, q u / Real.cosh u ^ 2 := by
  have htanh : ∀ u ∈ uIcc a b,
      HasDerivAt Real.tanh (1 / Real.cosh u ^ 2) u := by
    intro u _hu
    exact hasDerivAt_tanh_sechSq u
  have hsechInt : IntervalIntegrable
      (fun u : ℝ => 1 / Real.cosh u ^ 2) volume a b := by
    exact ((continuous_const.div
      (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    htanh hq hsechInt hq'
  simpa only [div_eq_mul_inv, inv_pow, mul_comm, one_mul] using hparts

end

end GafniTao
