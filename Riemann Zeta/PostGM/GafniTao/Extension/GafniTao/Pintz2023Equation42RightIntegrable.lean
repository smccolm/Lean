import GafniTao.Pintz2023Equation42Residue
import GafniTao.Pintz2023Equation42Series
import RiemannZeta.GuthMaynard.HughesYoungEndpointDecay

/-!
# Pintz (2023), equation (4.2): integrability of the source line

The complete contour displacement starts on `Re s = 3`.  On this line the
literal product `M_X(rho+s) * zeta(rho+s)` is represented by its absolutely
convergent Dirichlet series.  This file combines the termwise Gaussian
majorants from `Pintz2023Equation42Series` into integrability of the literal
source integrand.  Thus the right-line hypothesis of the residue-bearing
complete shift is discharged without a zeta-growth assumption.
-/

open Complex Filter MeasureTheory
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz2023Equation42SeriesIntegrand_eq_tsum
    {X : ℕ} {rho : ℂ} {lambda t : ℝ}
    (hrho : 1 / 2 ≤ rho.re) :
    pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, pintz2023Equation42VerticalTerm X rho lambda n t := by
  have hsRe : 1 <
      (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)).re := by
    norm_num [Complex.mul_re]
    linarith
  have hsum := (mollifiedZetaCoeff_LSeriesSummable X hsRe).LSeriesHasSum
  have hscaled := hsum.mul_right
    (pintzGaussianKernel lambda
      (((3 : ℝ) : ℂ) + (t : ℂ) * I))
  unfold pintz2023Equation42SeriesIntegrand
    pintz2023Equation42VerticalTerm pintz2023Coeff
  exact hscaled.tsum_eq.symm

theorem integrable_pintz2023Equation42SeriesIntegrand_three
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    Integrable (fun t : ℝ =>
      pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hsum : Integrable (fun t : ℝ =>
      ∑' n : ℕ, pintz2023Equation42VerticalTerm X rho lambda n t) :=
    integrable_tsum_of_summable_integral_norm
      (fun n => integrable_pintz2023Equation42VerticalTerm
        (X := X) (rho := rho) hlambda n)
      (summable_integral_norm_pintz2023Equation42VerticalTerm
        (X := X) hrho hlambda)
  exact hsum.congr (ae_of_all _ fun t =>
    (pintz2023Equation42SeriesIntegrand_eq_tsum
      (X := X) (rho := rho) (lambda := lambda) hrho).symm)

theorem integrable_pintz2023Equation42Integrand_three
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    Integrable (fun t : ℝ =>
      pintz2023Equation42Integrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hseries := integrable_pintz2023Equation42SeriesIntegrand_three
    (X := X) (rho := rho) hrho hlambda
  exact hseries.congr (ae_of_all _ fun t =>
    (pintz2023_equation42_integrand_eq_series
      (X := X) (rho := rho) (lambda := lambda) hrho).symm)

#print axioms pintz2023Equation42SeriesIntegrand_eq_tsum
#print axioms integrable_pintz2023Equation42SeriesIntegrand_three
#print axioms integrable_pintz2023Equation42Integrand_three

end

end GafniTao
