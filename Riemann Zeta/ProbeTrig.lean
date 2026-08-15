import RiemannZeta.GuthMaynard.DFIComplexLaplace
open Complex
example (y : ℝ) :
    (Real.sin y : ℂ) =
      (cexp (I * y) - cexp (-(I * y))) / (2 * I) := by
  rw [show I * (y : ℂ) = (y : ℂ) * I by ring,
    show -((y : ℂ) * I) = ((-y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.ofReal_neg]
  rw [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  field_simp
  ring
