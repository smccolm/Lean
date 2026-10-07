import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # The exact modulus and phase derivatives of a genuine complex differential equation -/

namespace Dubon2026

open Complex
open scoped InnerProductSpace

noncomputable section

/-- The real part of an actual complex logarithmic rate is the exact derivative of log-modulus. -/
theorem hasDerivAt_norm_of_complex_rate {z : ℝ → ℂ} {c : ℂ} {t : ℝ}
    (hz : HasDerivAt z (c * z t) t) (hne : z t ≠ 0) :
    HasDerivAt (fun u => ‖z u‖) (c.re * ‖z t‖) t := by
  have hd := (hz.differentiableAt.norm ℂ hne).hasDerivAt
  have hi : inner ℝ (z t) (c * z t) = c.re * ‖z t‖ ^ 2 := by
    rw [real_inner_eq_re_inner ℂ]
    change (inner ℂ (z t) (c • z t)).re = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    change (c * (‖z t‖ : ℂ) ^ 2).re = c.re * ‖z t‖ ^ 2
    simp [pow_two]
  have he := hz.norm_sq.unique (hd.pow 2)
  rw [hi] at he
  convert hd using 1
  apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : ℝ) ≠ 0) (norm_ne_zero_iff.mpr hne))
  norm_num at he
  nlinarith

/-- The imaginary part of the actual complex rate is exactly the frequency of the normalized phase. -/
theorem hasDerivAt_normalized_complex_phase {z : ℝ → ℂ} {c : ℂ} {t : ℝ}
    (hz : HasDerivAt z (c * z t) t) (hne : z t ≠ 0) :
    HasDerivAt (fun u => z u / (‖z u‖ : ℂ))
      (I * (c.im : ℂ) * (z t / (‖z t‖ : ℂ))) t := by
  have hn : (‖z t‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne)
  have hd := (hasDerivAt_norm_of_complex_rate hz hne).ofReal_comp
  convert hz.div hd hn using 1
  push_cast
  field_simp
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, sub_zero, add_zero,
    I_im, mul_one]
  ring

/-- Normalizing any genuine nonzero complex value gives unit modulus. -/
theorem norm_normalized_complex_phase {z : ℂ} (hz : z ≠ 0) : ‖z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  exact div_self (norm_ne_zero_iff.mpr hz)

end
end Dubon2026
