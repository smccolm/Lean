import GafniTao.PintzMobiusWeight

/-!
# Pintz's source-facing Gaussian weight

This file identifies the integer-indexed weight arising from the genuine
Möbius Dirichlet series with the notation used in Pintz equations
(4.2)--(4.4).  In particular, the shift parameter is not an independent
variable: it is exactly `h = lambda - log n`.
-/

open Complex MeasureTheory

namespace GafniTao

noncomputable section

/-- The entire numerator `exp(s²/λ + h s)` of Pintz's weight `w_j(h)`. -/
noncomputable def pintzSourceWeightNumerator
    (lambda h : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s ^ 2 / (lambda : ℂ) + (h : ℂ) * s)

/-- Pintz's complete-line weight `w_ρ(h)`, with the source normalization
`1 / (2 π i)`. -/
noncomputable def pintzSourceWeight
    (rho : ℂ) (lambda h : ℝ) : ℂ :=
  VerticalIntegral' (fun s : ℂ =>
    riemannZeta (s + rho) * pintzSourceWeightNumerator lambda h s / s) 3

/-- The `n⁻ˢ` factor in the Möbius expansion changes the Gaussian parameter
from `lambda` to the literal source value `lambda - log n`. -/
theorem pintz_mobius_kernel_eq_source_kernel
    {lambda : ℝ} {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-s) * pintzGaussianKernel lambda s =
      pintzSourceWeightNumerator lambda (lambda - Real.log n) s / s := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnComplex : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log hnReal.le).symm
  rw [Complex.cpow_def_of_ne_zero hnComplex]
  rw [pintzGaussianKernel, pintzGaussianNumerator,
    pintzSourceWeightNumerator]
  rw [hlog]
  rw [← mul_div_assoc]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Exact identification of the integer-indexed weight with Pintz's
`w_j(lambda - log n)`. -/
theorem pintzMobiusWeight_eq_sourceWeight
    {rho : ℂ} {lambda : ℝ} {n : ℕ} (hn : 0 < n) :
    pintzMobiusWeight rho lambda n =
      pintzSourceWeight rho lambda (lambda - Real.log n) := by
  rw [pintzMobiusWeight, pintzSourceWeight]
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_assoc, pintz_mobius_kernel_eq_source_kernel hn]
  ring_nf

#print axioms pintz_mobius_kernel_eq_source_kernel
#print axioms pintzMobiusWeight_eq_sourceWeight

end

end GafniTao
