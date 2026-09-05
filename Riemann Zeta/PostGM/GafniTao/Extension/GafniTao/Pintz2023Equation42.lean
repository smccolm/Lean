import GafniTao.Pintz2023Polynomial
import GafniTao.PintzGaussianBareShift

/-!
# Pintz (2023), equation (4.2): the exact source Dirichlet series

This file starts a source-specific proof of Pintz's Theorem 1.  The older
near-one detector in this package uses a different adaptive truncation and is
not used here.  Pintz's source object is the product of the finite mollifier
`M_X` with zeta; its Dirichlet coefficient is the actual convolution
`pintz2023Coeff X`.

The identities below retain the source Gaussian kernel and the complete
vertical line.  No asymptotic estimate or independently supplied polynomial
is introduced.
-/

open Complex MeasureTheory

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal integrand on the first line of Pintz (4.2). -/
noncomputable def pintz2023Equation42Integrand
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  zetaMollifier X (rho + s) * riemannZeta (rho + s) *
    pintzGaussianKernel lambda s

/-- The same integrand written using the exact convolution coefficient
`a_n = ∑_{d∣n,d≤X} μ(d)` from Pintz (4.1). -/
noncomputable def pintz2023Equation42SeriesIntegrand
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  LSeries (pintz2023Coeff X) (rho + s) *
    pintzGaussianKernel lambda s

/-- Pintz's complete normalized source integral `I_j`. -/
noncomputable def pintz2023Equation42Integral
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ :=
  VerticalIntegral' (pintz2023Equation42Integrand X rho lambda) 3

/-- Pointwise product-to-convolution identity on the source line
`Re s = 3`. -/
theorem pintz2023_equation42_integrand_eq_series
    {X : ℕ} {rho : ℂ} {lambda t : ℝ}
    (hrho : 1 / 2 ≤ rho.re) :
    pintz2023Equation42Integrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) =
      pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hAbs : 1 <
      (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)).re := by
    norm_num [Complex.mul_re]
    linarith
  unfold pintz2023Equation42Integrand
    pintz2023Equation42SeriesIntegrand pintz2023Coeff
  rw [mul_comm (zetaMollifier X _) (riemannZeta _),
    riemannZeta_mul_zetaMollifier_eq_LSeries X hAbs]

/-- Exact complete-line form of equation (4.2).  In particular, the series
side is not the bare Möbius polynomial used by the separate adaptive detector.
-/
theorem pintz2023_equation_4_2
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) :
    pintz2023Equation42Integral X rho lambda =
      VerticalIntegral'
        (pintz2023Equation42SeriesIntegrand X rho lambda) 3 := by
  unfold pintz2023Equation42Integral VerticalIntegral' VerticalIntegral
  have hfunctions :
      (fun t : ℝ => pintz2023Equation42Integrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
      (fun t : ℝ => pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    funext t
    exact pintz2023_equation42_integrand_eq_series hrho
  rw [hfunctions]

#print axioms pintz2023_equation42_integrand_eq_series
#print axioms pintz2023_equation_4_2

end

end GafniTao
