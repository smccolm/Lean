import GafniTao.FordCotangentPositivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Vertical-edge normalization in Ford's zero detector

After integration by parts, Ford parametrizes the two vertical sides by
`z = ±η + 2ηiu/π`.  The derivative of the cotangent kernel, the Jacobian,
and the normalized contour factor combine to the literal coefficient
`-1/(4η)` multiplying `cosh(u)⁻²`.  These identities retain both signs and
are the local calculation behind lines 490--497 of Ford's proof.
-/

open Complex Set

namespace GafniTao

noncomputable section

theorem fordDetector_rightEdge_pointwise
    {eta : ℝ} (heta : 0 < eta) (L : ℂ → ℂ) (u : ℝ) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (Complex.I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        deriv (fordCotKernel eta)
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) *
        L ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) =
      ((-1 / (4 * eta) : ℝ) : ℂ) *
        (L ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) /
          (Real.cosh u : ℂ) ^ 2) := by
  rw [deriv_fordCotKernel_pos_vertical heta u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hcosh : (Real.cosh u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne'
  push_cast
  field_simp [hpi, hetaC, hcosh]
  ring

theorem fordDetector_leftEdge_pointwise
    {eta : ℝ} (heta : 0 < eta) (L : ℂ → ℂ) (u : ℝ) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (Complex.I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        deriv (fordCotKernel eta)
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) *
        L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) =
      ((-1 / (4 * eta) : ℝ) : ℂ) *
        (L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) /
          (Real.cosh u : ℂ) ^ 2) := by
  rw [deriv_fordCotKernel_neg_vertical heta u]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hcosh : (Real.cosh u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne'
  push_cast
  field_simp [hpi, hetaC, hcosh]
  ring

theorem fordDetector_rightEdge_integral
    {eta : ℝ} (heta : 0 < eta) (L : ℂ → ℂ) (a b : ℝ) :
    (∫ u in a..b,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (Complex.I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        deriv (fordCotKernel eta)
          ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) *
        L ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I)) =
      ((-1 / (4 * eta) : ℝ) : ℂ) *
        ∫ u in a..b,
          L ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) /
            (Real.cosh u : ℂ) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact fordDetector_rightEdge_pointwise heta L u

theorem fordDetector_leftEdge_integral
    {eta : ℝ} (heta : 0 < eta) (L : ℂ → ℂ) (a b : ℝ) :
    (∫ u in a..b,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (Complex.I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        deriv (fordCotKernel eta)
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) *
        L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I)) =
      ((-1 / (4 * eta) : ℝ) : ℂ) *
        ∫ u in a..b,
          L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) /
            (Real.cosh u : ℂ) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  exact fordDetector_leftEdge_pointwise heta L u

/-- The left edge of the positively oriented rectangle is traversed
downwards.  Its orientation reverses the sign in the pointwise formula. -/
theorem fordDetector_leftEdge_down_integral
    {eta : ℝ} (heta : 0 < eta) (L : ℂ → ℂ) (a b : ℝ) :
    -(∫ u in a..b,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (Complex.I * ((2 * eta / Real.pi : ℝ) : ℂ)) *
        deriv (fordCotKernel eta)
          ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) *
        L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I)) =
      ((1 / (4 * eta) : ℝ) : ℂ) *
        ∫ u in a..b,
          L ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * Complex.I) /
            (Real.cosh u : ℂ) ^ 2 := by
  rw [fordDetector_leftEdge_integral heta]
  push_cast
  ring

end

end GafniTao
