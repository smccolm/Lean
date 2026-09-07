import GafniTao.FordLogNormDerivative

#check Real.hasDerivAt_sinh
#check Real.hasDerivAt_cosh
#check Complex.cos_add_pi_div_two
#check Complex.cos_sub_pi_div_two
#check Complex.sin_mul_I
#check Real.tanh_eq_sinh_div_cosh
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check intervalIntegral.integral_deriv_mul_eq_sub

open Complex

example {eta : ℝ} (heta : 0 < eta) (u : ℝ) :
    GafniTao.fordCotKernel eta
      ((eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I := by
  unfold GafniTao.fordCotKernel Complex.cot
  rw [GafniTao.fordCotKernel_scale_mul heta]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) + (u : ℂ) * I =
      (u : ℂ) * I + (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two,
    Complex.sin_mul_I, Complex.cos_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Real.tanh_eq_sinh_div_cosh]
  push_cast
  ring

example (u : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh u ^ 2) u := by
  have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u)
    (Real.cosh_pos u).ne'
  convert h using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · have hcs := Real.cosh_sq_sub_sinh_sq u
    rw [show Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u = 1 by
      nlinarith]

example {eta : ℝ} (heta : 0 < eta) (u : ℝ) :
    GafniTao.fordCotKernel eta
      ((-eta : ℂ) + (2 * eta * u / Real.pi : ℝ) * I) =
      -((Real.pi / (2 * eta) : ℝ) : ℂ) *
        (Real.tanh u : ℂ) * I := by
  unfold GafniTao.fordCotKernel Complex.cot
  rw [GafniTao.fordCotKernel_scale_neg_mul heta]
  rw [show (-((Real.pi / 2 : ℝ) : ℂ)) + (u : ℂ) * I =
      (u : ℂ) * I - (Real.pi : ℂ) / 2 by push_cast; ring,
    Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two,
    Complex.sin_mul_I, Complex.cos_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Real.tanh_eq_sinh_div_cosh]
  push_cast
  ring
