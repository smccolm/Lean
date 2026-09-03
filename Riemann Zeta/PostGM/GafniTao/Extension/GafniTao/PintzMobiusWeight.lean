import GafniTao.PintzMobiusSeries

/-!
# Pintz's individual Möbius weights

The termwise complete integral is factored into its exact Möbius coefficient
and a zeta--Gaussian weight.  The following file will identify the latter
with Pintz's `w_j(lambda - log n)` notation and truncate its tail.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

noncomputable section

/-- The exact complete right-line weight attached to the integer `n`. -/
noncomputable def pintzMobiusWeight
    (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  VerticalIntegral' (fun s : ℂ =>
    riemannZeta (s + rho) * (n : ℂ) ^ (-s) *
      pintzGaussianKernel lambda s) 3

/-- Pointwise factorization of a genuine term in the Möbius expansion. -/
theorem pintzMobiusVerticalTerm_factor
    (rho : ℂ) (lambda : ℝ) (n : ℕ) (t : ℝ) :
    pintzMobiusVerticalTerm rho lambda n t =
      LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
        (riemannZeta
            ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) *
          (n : ℂ) ^ (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
          pintzGaussianKernel lambda
            (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  by_cases hn : n = 0
  · subst n
    simp [pintzMobiusVerticalTerm, LSeries.term_def]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [pintzMobiusVerticalTerm]
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    have hpowS : (n : ℂ) ^
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    have hpowRho : (n : ℂ) ^ rho ≠ 0 :=
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    field_simp

/-- The normalized integral of a term factors exactly into the source
Möbius coefficient and its weight. -/
theorem normalized_integral_pintzMobiusVerticalTerm_eq
    (rho : ℂ) (lambda : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi * I) : ℂ) * I *
        (∫ t : ℝ, pintzMobiusVerticalTerm rho lambda n t) =
      LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
        pintzMobiusWeight rho lambda n := by
  rw [pintzMobiusWeight]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  have hIntegral :
      (∫ t : ℝ, pintzMobiusVerticalTerm rho lambda n t) =
        LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
          (∫ t : ℝ,
            riemannZeta
                ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) *
              (n : ℂ) ^
                (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
              pintzGaussianKernel lambda
                (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    calc
      (∫ t : ℝ, pintzMobiusVerticalTerm rho lambda n t) =
          ∫ t : ℝ,
            LSeries.term
                (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
              (riemannZeta
                  ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) *
                (n : ℂ) ^
                  (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
                pintzGaussianKernel lambda
                  (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
            apply integral_congr_ae
            filter_upwards [] with t
            exact pintzMobiusVerticalTerm_factor rho lambda n t
      _ = LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
          (∫ t : ℝ,
            riemannZeta
                ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) *
              (n : ℂ) ^
                (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
              pintzGaussianKernel lambda
                (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
            rw [integral_const_mul]
  rw [hIntegral]
  ring

/-- Source equation (4.2) on the complete line: the actual zeta--Möbius
integral is the convergent sum of the actual Möbius coefficients and
individual weights. -/
theorem pintz_mobius_equation_4_2_complete
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) :
    VerticalIntegral' (pintzMobiusIntegrand rho lambda) 3 =
      ∑' n : ℕ,
        LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
            pintzMobiusWeight rho lambda n := by
  rw [pintzMobius_verticalIntegral_eq_tsum hrho hlambda]
  apply tsum_congr
  intro n
  exact normalized_integral_pintzMobiusVerticalTerm_eq rho lambda n

/-- Quantitative complete-series form of equations (4.1)--(4.2). -/
theorem pintz_mobius_complete_series_ne_one
    {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 8 <= lambda) :
    ‖(∑' n : ℕ,
        LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
            pintzMobiusWeight rho lambda n) - 1‖ <=
      Real.exp (-2 * lambda) := by
  rw [← pintz_mobius_equation_4_2_complete hrho (by linarith)]
  exact pintz_mobius_equation_4_1 (by linarith) hlambda

#print axioms pintz_mobius_equation_4_2_complete
#print axioms pintz_mobius_complete_series_ne_one

end

end GafniTao
