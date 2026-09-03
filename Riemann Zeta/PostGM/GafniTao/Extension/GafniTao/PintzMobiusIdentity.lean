import GafniTao.PintzGaussianBareShift
import RiemannZeta.GuthMaynard.ClassicalDensity

/-!
# The zeta--Möbius identity in Pintz equation (4.1)

The bare contour calculation is now connected to the actual reciprocal
Dirichlet series.  This is the source entry for the Halász--Turán detector;
the integrand is not replaced by a separately supplied function.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

noncomputable section

/-- The genuine Möbius Dirichlet series used in Pintz Section 4. -/
noncomputable def pintzMoebiusSeries (s : ℂ) : ℂ :=
  LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s

/-- Absolute convergence of the actual Möbius series in its source
half-plane. -/
theorem pintzMoebiusSeries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs

/-- Möbius inversion gives the literal product one on `re s > 1`. -/
theorem riemannZeta_mul_pintzMoebiusSeries {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * pintzMoebiusSeries s = 1 := by
  rw [pintzMoebiusSeries, ← LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

/-- The complete source integrand before applying Möbius inversion. -/
noncomputable def pintzMobiusIntegrand
    (rho : ℂ) (lambda : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + rho) * pintzMoebiusSeries (s + rho) *
    pintzGaussianKernel lambda s

/-- On the right line of Pintz's contour, the genuine zeta--Möbius
integrand is exactly the bare Gaussian kernel. -/
theorem pintzMobiusIntegrand_right_eq
    {rho : ℂ} {lambda t : ℝ} (hrho : -2 < rho.re) :
    pintzMobiusIntegrand rho lambda ((3 : ℝ) + (t : ℂ) * I) =
      pintzGaussianKernel lambda ((3 : ℝ) + (t : ℂ) * I) := by
  rw [pintzMobiusIntegrand,
    riemannZeta_mul_pintzMoebiusSeries (by simp; linarith)]
  exact one_mul _

/-- The complete normalized right-line integrals agree exactly. -/
theorem pintzMobius_verticalIntegral_right_eq
    {rho : ℂ} {lambda : ℝ} (hrho : -2 < rho.re) :
    VerticalIntegral' (pintzMobiusIntegrand rho lambda) 3 =
      VerticalIntegral' (pintzGaussianKernel lambda) 3 := by
  unfold VerticalIntegral' VerticalIntegral
  simp_rw [pintzMobiusIntegrand_right_eq hrho]

/-- Pintz (4.1) with its actual zeta and Möbius factors present. -/
theorem pintz_mobius_equation_4_1
    {rho : ℂ} {lambda : ℝ}
    (hrho : -2 < rho.re) (hlambda : 8 <= lambda) :
    ‖VerticalIntegral' (pintzMobiusIntegrand rho lambda) 3 - 1‖ <=
      Real.exp (-2 * lambda) := by
  rw [pintzMobius_verticalIntegral_right_eq hrho]
  exact pintz_equation_4_1 hlambda

#print axioms riemannZeta_mul_pintzMoebiusSeries
#print axioms pintz_mobius_equation_4_1

end

end GafniTao
