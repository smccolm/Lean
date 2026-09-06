import GafniTao.Pintz2023Equation47Complete

/-!
# Pintz (2023), equation (4.7): exact ordinate truncation

No error is discarded here.  The complete positive vertical line is split
into the literal segment `[-2*lambda,2*lambda]` and a named remainder.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023TruncatedBareWeight
    (lambda h : ℝ) : ℂ :=
  VIntegral' (pintz2023BareWeightIntegrand lambda h)
    (1 / lambda) (-2 * lambda) (2 * lambda)

noncomputable def pintz2023TruncatedSmallLineTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (pintz2023Coeff X) rho n *
    pintz2023TruncatedBareWeight lambda (lambda - Real.log n)

noncomputable def pintz2023SmallLineTailTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  pintz2023SmallLineTerm X rho lambda n -
    pintz2023TruncatedSmallLineTerm X rho lambda n

theorem pintz2023SmallLineTerm_eq_truncated_add_tail
    (X n : ℕ) (rho : ℂ) (lambda : ℝ) :
    pintz2023SmallLineTerm X rho lambda n =
      pintz2023TruncatedSmallLineTerm X rho lambda n +
        pintz2023SmallLineTailTerm X rho lambda n := by
  unfold pintz2023SmallLineTailTerm
  ring

noncomputable def pintz2023Equation47TruncatedRemainder
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℂ :=
  pintz2023Equation47Remainder X rho lambda +
    ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
      pintz2023SmallLineTailTerm X rho lambda n

/-- Exact finite-height version of Pintz equation (4.7). -/
theorem pintz2023_equation_4_7_exact
    {X : ℕ} {rho : ℂ} {lambda eta : ℝ}
    (hrho : 1 - eta ≤ rho.re) (hlambda : 8 ≤ lambda)
    (heta : eta ≤ 1 / 24) (hX : 1 ≤ X)
    (hXC : X ≤ pintz2023Cutoff lambda) :
    pintz2023Equation42Integral X rho lambda =
      1 +
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023TruncatedSmallLineTerm X rho lambda n +
        pintz2023Equation47TruncatedRemainder X rho lambda := by
  rw [pintz2023_equation_4_7_completeLine
    hrho hlambda heta hX hXC]
  unfold pintz2023Equation47TruncatedRemainder
  have hsum :
      (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023SmallLineTerm X rho lambda n) =
      (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X rho lambda n) +
      ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023SmallLineTailTerm X rho lambda n := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact pintz2023SmallLineTerm_eq_truncated_add_tail X n rho lambda
  rw [hsum]
  ring

/-- The literal finite-interval integrand for one source coefficient. -/
noncomputable def pintz2023TruncatedSmallLineVerticalTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (pintz2023Coeff X) rho n *
    pintz2023BareWeightIntegrand lambda (lambda - Real.log n)
      (((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I)

theorem pintz2023TruncatedSmallLineTerm_eq_integral
    (X n : ℕ) (rho : ℂ) (lambda : ℝ) :
    pintz2023TruncatedSmallLineTerm X rho lambda n =
      (1 / (2 * Real.pi * I) : ℂ) * I *
        ∫ t in (-2 * lambda)..(2 * lambda),
          pintz2023TruncatedSmallLineVerticalTerm X rho lambda n t := by
  unfold pintz2023TruncatedSmallLineTerm pintz2023TruncatedBareWeight
    pintz2023TruncatedSmallLineVerticalTerm VIntegral' VIntegral
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Finite summation may be moved inside the literal equation-(4.7)
integral. -/
theorem pintz2023_truncated_sum_eq_integral_sum
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (hlambda : 0 < lambda) :
    (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X rho lambda n) =
      (1 / (2 * Real.pi * I) : ℂ) * I *
        ∫ t in (-2 * lambda)..(2 * lambda),
          ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
            pintz2023TruncatedSmallLineVerticalTerm X rho lambda n t := by
  simp_rw [pintz2023TruncatedSmallLineTerm_eq_integral]
  rw [← Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum]
  intro n hn
  have hi := (integrable_pintz2023BareWeightIntegrand_vertical_pos
    (h := lambda - Real.log n) hlambda (one_div_pos.mpr hlambda)).const_mul
      (LSeries.term (pintz2023Coeff X) rho n)
  exact hi.intervalIntegrable

noncomputable def pintz2023Equation47Shift
    (lambda t : ℝ) : ℂ :=
  ((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I

noncomputable def pintz2023Equation47Polynomial
    (X : ℕ) (rho : ℂ) (lambda t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
    LSeries.term (pintz2023Coeff X)
      (rho + pintz2023Equation47Shift lambda t) n

theorem pintz2023_LSeries_term_shift_factor
    (X n : ℕ) (rho s : ℂ) :
    LSeries.term (pintz2023Coeff X) rho n *
        ((n : ℂ) ^ (-s) * pintzGaussianKernel 1 s) =
      LSeries.term (pintz2023Coeff X) (rho + s) n *
        pintzGaussianKernel 1 s := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    have hpowS : (n : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hpowRho : (n : ℂ) ^ rho ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    field_simp

/-- Parameter-general version of the preceding factorization. -/
theorem pintz2023_LSeries_term_shift_factor_kernel
    (X n : ℕ) (rho s : ℂ) (lambda : ℝ) :
    LSeries.term (pintz2023Coeff X) rho n *
        ((n : ℂ) ^ (-s) * pintzGaussianKernel lambda s) =
      LSeries.term (pintz2023Coeff X) (rho + s) n *
        pintzGaussianKernel lambda s := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    have hpowS : (n : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hpowRho : (n : ℂ) ^ rho ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    field_simp

theorem pintz2023TruncatedSmallLineVerticalTerm_eq
    {X n : ℕ} (rho : ℂ) (lambda t : ℝ) (hn : 0 < n) :
    pintz2023TruncatedSmallLineVerticalTerm X rho lambda n t =
      LSeries.term (pintz2023Coeff X)
          (rho + pintz2023Equation47Shift lambda t) n *
        pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t) := by
  unfold pintz2023TruncatedSmallLineVerticalTerm
    pintz2023Equation47Shift pintz2023BareWeightIntegrand
  rw [← pintz_mobius_kernel_eq_source_kernel hn]
  exact pintz2023_LSeries_term_shift_factor_kernel X n rho _ lambda

theorem pintz2023_vertical_sum_eq_polynomial_mul_kernel
    {X : ℕ} (rho : ℂ) (lambda t : ℝ) :
    (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineVerticalTerm X rho lambda n t) =
      pintz2023Equation47Polynomial X rho lambda t *
        pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t) := by
  unfold pintz2023Equation47Polynomial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pintz2023TruncatedSmallLineVerticalTerm_eq]
  have hnLower := (Finset.mem_Ioc.mp hn).1
  omega

/-- Literal source integrand form of the truncated equation (4.7). -/
theorem pintz2023_truncated_sum_eq_source_integral
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (hlambda : 0 < lambda) :
    (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X rho lambda n) =
      (1 / (2 * Real.pi * I) : ℂ) * I *
        ∫ t in (-2 * lambda)..(2 * lambda),
          pintz2023Equation47Polynomial X rho lambda t *
            pintzGaussianKernel lambda
              (pintz2023Equation47Shift lambda t) := by
  rw [pintz2023_truncated_sum_eq_integral_sum X rho lambda hlambda]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact pintz2023_vertical_sum_eq_polynomial_mul_kernel rho lambda t

#print axioms pintz2023_equation_4_7_exact
#print axioms pintz2023_truncated_sum_eq_integral_sum
#print axioms pintz2023_truncated_sum_eq_source_integral

end

end GafniTao
