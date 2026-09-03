import GafniTao.PintzEquation47
import RiemannZeta.GuthMaynard.FiniteDensityTransfer

/-!
# Quantitative bounds for the finite Pintz contour

This module bounds the actual finite Möbius polynomial on the horizontal
edges of the rectangle used in Pintz equation (4.6).  The cutoff and the
partial harmonic sum remain explicit, so subsequent estimates can account
for every loss rather than hiding them in contour notation.
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A finite Möbius polynomial is bounded by the corresponding partial
Dirichlet sum whenever its evaluation point has real part at least `β`. -/
theorem norm_pintzFiniteMobiusPolynomial_le_partialSum
    {rho s : ℂ} {lambda beta : ℝ}
    (hbeta : beta <= (rho + s).re) :
    ‖pintzFiniteMobiusPolynomial rho lambda s‖ <=
      ∑ n ∈ Finset.Icc 1 (pintzMobiusCutoff lambda),
        (n : ℝ) ^ (-beta) := by
  unfold pintzFiniteMobiusPolynomial
  calc
    ‖∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            (rho + s) n‖ <=
        ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
          ‖LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
              (rho + s) n‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
          if n = 0 then 0 else (n : ℝ) ^ (-beta) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp [LSeries.term_def]
      · rw [if_neg hn0]
        have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
        calc
          ‖LSeries.term
              (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
                (rho + s) n‖ <=
              ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (rho + s) n‖ :=
            LSeries.norm_term_le (rho + s) (moebius_coeff_norm_le_one n)
          _ <= ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
                ((beta : ℝ) : ℂ) n‖ :=
            LSeries.norm_term_le_of_re_le_re (fun _ : ℕ => (1 : ℂ))
              (by simpa using hbeta) n
          _ = (n : ℝ) ^ (-beta) := by
            rw [LSeries.norm_term_eq]
            simp only [if_neg hn0, norm_one, Complex.ofReal_re]
            rw [one_div]
            rw [Real.rpow_neg (by positivity : (0 : ℝ) <= n)]
    _ = ∑ n ∈ Finset.Icc 1 (pintzMobiusCutoff lambda),
          (n : ℝ) ^ (-beta) := by
      have hsubset : Finset.Icc 1 (pintzMobiusCutoff lambda) ⊆
          Finset.range (pintzMobiusCutoff lambda + 1) := by
        intro n hn
        simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
        omega
      have hsum := Finset.sum_subset (f := fun n : ℕ =>
          if n = 0 then 0 else (n : ℝ) ^ (-beta)) hsubset
        (by
          intro n hnRange hnIcc
          simp only [Finset.mem_range] at hnRange
          simp only [Finset.mem_Icc, not_and_or, not_le] at hnIcc
          have hnZero : n = 0 := by omega
          simp [hnZero])
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnNe : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hn).1
        omega
      simp [hnNe]

/-- In the half-plane `Re (rho+s) ≥ 1/2`, Cauchy--Schwarz gives the
source-relevant square-root/harmonic bound for the exact finite polynomial. -/
theorem norm_pintzFiniteMobiusPolynomial_le_sqrt_harmonic
    {rho s : ℂ} {lambda : ℝ} (hre : 1 / 2 <= (rho + s).re) :
    ‖pintzFiniteMobiusPolynomial rho lambda s‖ <=
      Real.sqrt (pintzMobiusCutoff lambda) *
        Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ) := by
  exact (norm_pintzFiniteMobiusPolynomial_le_partialSum hre).trans
    (sum_rpow_neg_le_sqrt_mul_sqrt_harmonic
      (pintzMobiusCutoff lambda) (1 / 2) (by norm_num))

/-- Exact Gaussian decay on either horizontal edge at height `2 * lambda`,
uniformly for real parts between `-3` and `3`. -/
theorem norm_pintzGaussianNumerator_horizontal_two_lambda_le
    {lambda x R : ℝ} (hlambda : 0 < lambda)
    (hxLower : -3 <= x) (hxUpper : x <= 3) (hR : |R| = 2 * lambda) :
    ‖pintzGaussianNumerator lambda ((x : ℂ) + (R : ℂ) * I)‖ <=
      Real.exp (9 / lambda - lambda) := by
  have hRtwo : R ^ 2 = (2 * lambda) ^ 2 := by
    nlinarith [sq_abs R]
  have hxSq : x ^ 2 <= 9 := by nlinarith
  rw [show (R : ℂ) * I = I * R by simp [mul_comm]]
  rw [norm_pintzGaussianNumerator_vertical lambda x R hlambda]
  apply Real.exp_le_exp.mpr
  rw [hRtwo]
  have hdiv : (x ^ 2 - (2 * lambda) ^ 2) / lambda <=
      (9 - (2 * lambda) ^ 2) / lambda := by
    exact div_le_div_of_nonneg_right (sub_le_sub_right hxSq _) hlambda.le
  calc
    (x ^ 2 - (2 * lambda) ^ 2) / lambda + lambda * x <=
        (9 - (2 * lambda) ^ 2) / lambda + lambda * x :=
      by simpa [add_comm] using add_le_add_right hdiv (lambda * x)
    _ <= (9 - (2 * lambda) ^ 2) / lambda + lambda * 3 := by
      gcongr
    _ = 9 / lambda - lambda := by
      field_simp [ne_of_gt hlambda]
      ring

/-- Pointwise bound for the actual regularized finite contour integrand on
either height-`2 lambda` horizontal edge.  The zeta value is left visible for
the later source-specific `M₁` estimate; every other factor is explicit. -/
theorem norm_pintzFiniteContourIntegrand_horizontal_two_lambda_le
    {rho : ℂ} {lambda x R : ℝ}
    (hrhoZero : riemannZeta rho = 0) (hlambda : 0 < lambda)
    (hxLower : -3 <= x) (hxUpper : x <= 3)
    (hR : |R| = 2 * lambda) (hre : 1 / 2 <=
      (rho + ((x : ℂ) + (R : ℂ) * I)).re) :
    ‖pintzFiniteContourIntegrand rho lambda
        ((x : ℂ) + (R : ℂ) * I)‖ <=
      ‖riemannZeta (rho + ((x : ℂ) + (R : ℂ) * I))‖ *
        (Real.sqrt (pintzMobiusCutoff lambda) *
          Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
        Real.exp (9 / lambda - lambda) / (2 * lambda) := by
  let s : ℂ := (x : ℂ) + (R : ℂ) * I
  have hs : s ≠ 0 := by
    intro hsZero
    have him := congrArg Complex.im hsZero
    have hRzero : R = 0 := by simpa [s] using him
    have : 0 < |R| := by rw [hR]; positivity
    rw [hRzero, abs_zero] at this
    exact lt_irrefl 0 this
  have hden : 2 * lambda <= ‖s‖ := by
    rw [← hR]
    have him : s.im = R := by simp [s, Complex.mul_im]
    rw [← him]
    exact Complex.abs_im_le_norm s
  have hpoly := norm_pintzFiniteMobiusPolynomial_le_sqrt_harmonic
    (rho := rho) (s := s) (lambda := lambda) hre
  have hgauss := norm_pintzGaussianNumerator_horizontal_two_lambda_le
    hlambda hxLower hxUpper hR
  rw [pintzFiniteContourIntegrand_eq_div hrhoZero hs]
  unfold pintzFiniteContourNumerator
  rw [norm_div, norm_mul, norm_mul]
  have hnum :
      ‖riemannZeta (rho + s)‖ * ‖pintzFiniteMobiusPolynomial rho lambda s‖ *
          ‖pintzGaussianNumerator lambda s‖ <=
        ‖riemannZeta (rho + s)‖ *
          (Real.sqrt (pintzMobiusCutoff lambda) *
            Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
          Real.exp (9 / lambda - lambda) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hpoly (norm_nonneg _)) hgauss
      (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (by positivity))
  calc
    (‖riemannZeta (rho + s)‖ * ‖pintzFiniteMobiusPolynomial rho lambda s‖ *
          ‖pintzGaussianNumerator lambda s‖) / ‖s‖ <=
        (‖riemannZeta (rho + s)‖ *
          (Real.sqrt (pintzMobiusCutoff lambda) *
            Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
          Real.exp (9 / lambda - lambda)) / ‖s‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ <= (‖riemannZeta (rho + s)‖ *
          (Real.sqrt (pintzMobiusCutoff lambda) *
            Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
          Real.exp (9 / lambda - lambda)) / (2 * lambda) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- Integrated horizontal-edge estimate.  `Z` is precisely the uniform zeta
envelope on this edge; no other analytic quantity is suppressed. -/
theorem norm_pintzFiniteContour_HIntegral'_two_lambda_le
    {rho : ℂ} {lambda left R Z : ℝ}
    (hrhoZero : riemannZeta rho = 0) (hlambda : 0 < lambda)
    (hleftLower : -3 <= left) (hleftUpper : left <= 3)
    (hR : |R| = 2 * lambda) (hZnonneg : 0 <= Z)
    (hre : ∀ x ∈ Set.Icc left 3,
      1 / 2 <= (rho + ((x : ℂ) + (R : ℂ) * I)).re)
    (hZeta : ∀ x ∈ Set.Icc left 3,
      ‖riemannZeta (rho + ((x : ℂ) + (R : ℂ) * I))‖ <= Z) :
    ‖HIntegral' (pintzFiniteContourIntegrand rho lambda) left 3 R‖ <=
      6 * (Z *
        (Real.sqrt (pintzMobiusCutoff lambda) *
          Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
        Real.exp (9 / lambda - lambda) / (2 * lambda)) := by
  let C : ℝ := Z *
    (Real.sqrt (pintzMobiusCutoff lambda) *
      Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
    Real.exp (9 / lambda - lambda) / (2 * lambda)
  have hCnonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hraw :
      ‖HIntegral (pintzFiniteContourIntegrand rho lambda) left 3 R‖ <=
        C * |3 - left| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hxIcc : x ∈ Set.Icc left 3 := by
      rw [← Set.uIcc_of_le hleftUpper]
      exact Set.uIoc_subset_uIcc hx
    have hpoint :=
      norm_pintzFiniteContourIntegrand_horizontal_two_lambda_le
        hrhoZero hlambda (hleftLower.trans hxIcc.1) hxIcc.2 hR
          (hre x hxIcc)
    exact hpoint.trans (by
      dsimp [C]
      gcongr
      exact hZeta x hxIcc)
  have hlength : |3 - left| <= 6 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hleftUpper)]
    linarith
  unfold HIntegral'
  rw [norm_smul]
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ <= 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) <= Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ <= (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    calc
      Real.pi⁻¹ * (1 / 2 : ℝ) <= 1 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hpiInv (by norm_num)
      _ <= 1 := by norm_num
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (pintzFiniteContourIntegrand rho lambda) left 3 R‖ <=
      1 * (C * |3 - left|) :=
        mul_le_mul hscalar hraw (norm_nonneg _) (by positivity)
    _ <= 1 * (C * 6) := by
      gcongr
    _ = 6 * C := by ring
    _ = _ := by rfl

/-- The exact finite coefficient mass occurring on Pintz's right line. -/
noncomputable def pintzRightCoefficientMass (rho : ℂ) (lambda : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
    ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
      (((3 + rho.re : ℝ) : ℂ)) n‖

/-- The finite right-line contour has the same Gaussian majorant as the
termwise series, with the exact finite coefficient mass factored out. -/
theorem norm_pintzFiniteContourIntegrand_three_le
    {rho : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (hrhoHalf : 1 / 2 <= rho.re) (hlambda : 0 < lambda) (t : ℝ) :
    ‖pintzFiniteContourIntegrand rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖ <=
      pintzRightCoefficientMass rho lambda *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  rw [pintzFiniteContourIntegrand_three_eq_sum hrhoZero]
  calc
    ‖∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        pintzMobiusVerticalTerm rho lambda n t‖ <=
      ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        ‖pintzMobiusVerticalTerm rho lambda n t‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        ‖LSeries.term (fun m =>
          ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            (((3 + rho.re : ℝ) : ℂ)) n‖ *
          hughesYoungZetaHalfPlaneMajorant *
          ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
      exact Finset.sum_le_sum fun n _ =>
        norm_pintzMobiusVerticalTerm_le hrhoHalf hlambda n t
    _ = pintzRightCoefficientMass rho lambda *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
      unfold pintzRightCoefficientMass
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-- Absolute integrability of the actual finite contour on the complete
right vertical line. -/
theorem integrable_pintzFiniteContourIntegrand_three
    {rho : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (hrhoHalf : 1 / 2 <= rho.re) (hlambda : 0 < lambda) :
    Integrable (fun t : ℝ => pintzFiniteContourIntegrand rho lambda
      (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        pintzMobiusVerticalTerm rho lambda n t) := by
    induction Finset.range (pintzMobiusCutoff lambda + 1) using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
        simpa [Finset.sum_insert hn] using
          (integrable_pintzMobiusVerticalTerm hrhoHalf hlambda n).add ih
  apply hsum.congr
  filter_upwards with t
  exact (pintzFiniteContourIntegrand_three_eq_sum hrhoZero t).symm

/-- General Gaussian deletion estimate specialized to the moving cutoff
`[-2 lambda,2 lambda]`. -/
theorem integral_compl_Ioc_exp_neg_inv_lambda_sq_le
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
      Real.exp (-(1 / lambda) * t ^ 2)) <=
      Real.exp (-(7 / 2 : ℝ) * lambda) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-(7 / 2 : ℝ) * lambda) *
      Real.exp (-(1 / (8 * lambda)) * t ^ 2)
  have hsource : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)
  have hg : Integrable g := by
    simpa only [g] using
      (integrable_exp_neg_mul_sq (by positivity : 0 < (1 / (8 * lambda)))).const_mul
        (Real.exp (-(7 / 2 : ℝ) * lambda))
  have hpoint : ∀ t ∈ (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
      Real.exp (-(1 / lambda) * t ^ 2) <= g t := by
    intro t ht
    have hcut : 2 * lambda <= |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or] at ht
      rcases ht with ht | ht
      · have htt : t <= -2 * lambda := le_of_not_gt ht
        rw [abs_of_nonpos (htt.trans (by linarith))]
        linarith
      · have htt : 2 * lambda < t := lt_of_not_ge ht
        rw [abs_of_nonneg (by linarith : 0 <= t)]
        exact htt.le
    have hsq : (2 * lambda) ^ 2 <= t ^ 2 := by
      rw [← sq_abs t]
      nlinarith [sq_nonneg (|t| - 2 * lambda)]
    unfold g
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambda
    field_simp [hlambdaNe]
    nlinarith
  calc
    (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        Real.exp (-(1 / lambda) * t ^ 2)) <=
      ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, g t :=
        MeasureTheory.setIntegral_mono_on hsource.integrableOn hg.integrableOn
          measurableSet_Ioc.compl hpoint
    _ <= ∫ t : ℝ, g t := by
      apply MeasureTheory.setIntegral_le_integral hg
      filter_upwards with t
      unfold g
      positivity
    _ = Real.exp (-(7 / 2 : ℝ) * lambda) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by
      unfold g
      rw [integral_const_mul, integral_gaussian]

/-- Complete quantitative right-line truncation error in equation (4.6). -/
theorem norm_pintzMobiusFiniteHead_sub_rightSegment_le
    {rho : ℂ} {lambda : ℝ} (hrhoZero : riemannZeta rho = 0)
    (hrhoHalf : 1 / 2 <= rho.re) (hlambda : 0 < lambda) :
    ‖pintzMobiusFiniteHead rho lambda -
        VIntegral' (pintzFiniteContourIntegrand rho lambda)
          3 (-2 * lambda) (2 * lambda)‖ <=
      pintzRightCoefficientMass rho lambda *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
  let f : ℝ → ℂ := fun t => pintzFiniteContourIntegrand rho lambda
    (((3 : ℝ) : ℂ) + (t : ℂ) * I)
  let C : ℝ := pintzRightCoefficientMass rho lambda *
    hughesYoungZetaHalfPlaneMajorant *
    ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda))
  have hf : Integrable f :=
    integrable_pintzFiniteContourIntegrand_three hrhoZero hrhoHalf hlambda
  have htail := norm_integral_sub_symmetricIntervalIntegral_le_compl_norm
    hf (by positivity : 0 <= 2 * lambda)
  have htail' :
      ‖(∫ t : ℝ, f t) - ∫ t in (-2 * lambda)..(2 * lambda), f t‖ <=
        ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖ := by
    simpa only [neg_mul] using htail
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  have hCnonneg : 0 <= C := by
    have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
      tsum_nonneg (fun _ => norm_nonneg _)
    dsimp [C, pintzRightCoefficientMass]
    exact mul_nonneg
      (mul_nonneg
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        hHnonneg)
      (by positivity)
  have hcomp : (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖) <=
      ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        C * Real.exp (-(1 / lambda) * t ^ 2) := by
    apply MeasureTheory.setIntegral_mono_on hf.norm.integrableOn
      hmajor.integrableOn measurableSet_Ioc.compl
    intro t ht
    simpa only [f, C] using
      norm_pintzFiniteContourIntegrand_three_le
        hrhoZero hrhoHalf hlambda t
  have hgauss := integral_compl_Ioc_exp_neg_inv_lambda_sq_le hlambda
  have hnormScalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ <= 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) <= Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ <= (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    calc
      Real.pi⁻¹ * (1 / 2 : ℝ) <= 1 * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hpiInv (by norm_num)
      _ <= 1 := by norm_num
  have hhead := pintzFiniteContour_verticalIntegral_three_eq_head
    hrhoZero hrhoHalf hlambda
  have hnormScalarI :
      ‖(1 / (2 * Real.pi * I) : ℂ) * I‖ <= 1 := by
    simpa [norm_mul] using hnormScalar
  rw [← hhead]
  unfold VerticalIntegral' VerticalIntegral VIntegral' VIntegral
  simp only [smul_eq_mul]
  simp only [← mul_assoc]
  change ‖((1 / (2 * Real.pi * I) : ℂ) * I) * (∫ t : ℝ, f t) -
      ((1 / (2 * Real.pi * I) : ℂ) * I) *
        (∫ t in (-2 * lambda)..(2 * lambda), f t)‖ <= _
  rw [← mul_sub]
  rw [norm_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ) * I‖ *
        ‖(∫ t : ℝ, f t) - ∫ t in (-2 * lambda)..(2 * lambda), f t‖ <=
      1 * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖) :=
        mul_le_mul hnormScalarI htail' (norm_nonneg _) (by positivity)
    _ <= 1 * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        C * Real.exp (-(1 / lambda) * t ^ 2)) := by gcongr
    _ = C * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        Real.exp (-(1 / lambda) * t ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
      ring
    _ <= C * (Real.exp (-(7 / 2 : ℝ) * lambda) *
        Real.sqrt (Real.pi / (1 / (8 * lambda)))) :=
      mul_le_mul_of_nonneg_left hgauss hCnonneg
    _ = _ := by
      dsimp [C]
      ring

/-- Explicit right-line contribution to the equation-(4.6) error ledger. -/
noncomputable def pintzEquation46RightTailBound
    (etaJ gamma lambda : ℝ) : ℝ :=
  pintzRightCoefficientMass (pintzRho etaJ gamma) lambda *
    hughesYoungZetaHalfPlaneMajorant *
    ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
    (Real.exp (-(7 / 2 : ℝ) * lambda) *
      Real.sqrt (Real.pi / (1 / (8 * lambda))))

/-- Explicit bound for one normalized horizontal edge, after supplying a
uniform bound `Z` for zeta on that edge. -/
noncomputable def pintzEquation46HorizontalBound
    (lambda Z : ℝ) : ℝ :=
  6 * (Z *
    (Real.sqrt (pintzMobiusCutoff lambda) *
      Real.sqrt (harmonic (pintzMobiusCutoff lambda) : ℝ)) *
    Real.exp (9 / lambda - lambda) / (2 * lambda))

/-- The complete quantitative form of the contour error in Pintz (4.6).
The only inputs not expanded here are the two literal horizontal zeta
envelopes, which are exactly the `M₁` quantities bounded later in (4.8). -/
theorem norm_pintzEquation46ContourError_le
    {Delta eta etaJ gamma lambda Zminus Zplus : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hlambda : 0 < lambda) (hleftLower :
      -3 <= pintzLeftEdge Delta eta etaJ)
    (hleftUpper : pintzLeftEdge Delta eta etaJ <= 3)
    (hDeltaNonneg : 0 <= Delta)
    (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hxi : pintzXi Delta eta <= 1 / 2)
    (hZminusNonneg : 0 <= Zminus) (hZplusNonneg : 0 <= Zplus)
    (hZminus : ∀ x ∈ Set.Icc (pintzLeftEdge Delta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ gamma +
        ((x : ℂ) + ((-2 * lambda : ℝ) : ℂ) * I))‖ <= Zminus)
    (hZplus : ∀ x ∈ Set.Icc (pintzLeftEdge Delta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ gamma +
        ((x : ℂ) + ((2 * lambda : ℝ) : ℂ) * I))‖ <= Zplus) :
    ‖pintzEquation46ContourError Delta eta etaJ gamma lambda‖ <=
      pintzEquation46RightTailBound etaJ gamma lambda +
        pintzEquation46HorizontalBound lambda Zminus +
        pintzEquation46HorizontalBound lambda Zplus := by
  have hrhoHalf : 1 / 2 <= (pintzRho etaJ gamma).re := by
    simp [pintzRho]
    have hxLower := hleftLower
    unfold pintzLeftEdge pintzDeltaJ at hxLower
    unfold pintzDeltaJ at hdeltaJ
    unfold pintzXi at hxi
    linarith
  have hre (R : ℝ) (x : ℝ)
      (hx : x ∈ Set.Icc (pintzLeftEdge Delta eta etaJ) 3) :
      1 / 2 <= (pintzRho etaJ gamma +
        ((x : ℂ) + (R : ℂ) * I)).re := by
    simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, I_re,
      I_im, mul_zero, sub_zero]
    simp [pintzRho]
    have hxLower := hx.1
    unfold pintzLeftEdge pintzDeltaJ at hxLower
    unfold pintzXi at hxi
    linarith
  have hRminus : |(-2 * lambda : ℝ)| = 2 * lambda := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hRplus : |(2 * lambda : ℝ)| = 2 * lambda :=
    abs_of_pos (by positivity)
  have hright := norm_pintzMobiusFiniteHead_sub_rightSegment_le
    hrhoZero hrhoHalf hlambda
  have hminus := norm_pintzFiniteContour_HIntegral'_two_lambda_le
    hrhoZero hlambda hleftLower hleftUpper hRminus hZminusNonneg
      (hre (-2 * lambda)) hZminus
  have hplus := norm_pintzFiniteContour_HIntegral'_two_lambda_le
    hrhoZero hlambda hleftLower hleftUpper hRplus hZplusNonneg
      (hre (2 * lambda)) hZplus
  unfold pintzEquation46ContourError
  dsimp only
  calc
    ‖(pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
          VIntegral' (pintzFiniteContourIntegrand
            (pintzRho etaJ gamma) lambda) 3
              (-2 * lambda) (2 * lambda)) -
        HIntegral' (pintzFiniteContourIntegrand
          (pintzRho etaJ gamma) lambda)
            (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda) +
        HIntegral' (pintzFiniteContourIntegrand
          (pintzRho etaJ gamma) lambda)
            (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)‖ <=
      ‖pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
          VIntegral' (pintzFiniteContourIntegrand
            (pintzRho etaJ gamma) lambda) 3
              (-2 * lambda) (2 * lambda)‖ +
        ‖HIntegral' (pintzFiniteContourIntegrand
          (pintzRho etaJ gamma) lambda)
            (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda)‖ +
        ‖HIntegral' (pintzFiniteContourIntegrand
          (pintzRho etaJ gamma) lambda)
            (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)‖ := by
      calc
        _ <= ‖(pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
              VIntegral' (pintzFiniteContourIntegrand
                (pintzRho etaJ gamma) lambda) 3
                  (-2 * lambda) (2 * lambda)) -
            HIntegral' (pintzFiniteContourIntegrand
              (pintzRho etaJ gamma) lambda)
                (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda)‖ +
            ‖HIntegral' (pintzFiniteContourIntegrand
              (pintzRho etaJ gamma) lambda)
                (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)‖ :=
          norm_add_le _ _
        _ <= (‖pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
              VIntegral' (pintzFiniteContourIntegrand
                (pintzRho etaJ gamma) lambda) 3
                  (-2 * lambda) (2 * lambda)‖ +
            ‖HIntegral' (pintzFiniteContourIntegrand
              (pintzRho etaJ gamma) lambda)
                (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda)‖) +
            ‖HIntegral' (pintzFiniteContourIntegrand
              (pintzRho etaJ gamma) lambda)
                (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)‖ :=
          by
            simpa [add_assoc, add_comm, add_left_comm] using
              add_le_add_right (norm_sub_le
                (pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
                  VIntegral' (pintzFiniteContourIntegrand
                    (pintzRho etaJ gamma) lambda) 3
                      (-2 * lambda) (2 * lambda))
                (HIntegral' (pintzFiniteContourIntegrand
                  (pintzRho etaJ gamma) lambda)
                    (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda)))
                ‖HIntegral' (pintzFiniteContourIntegrand
                  (pintzRho etaJ gamma) lambda)
                    (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)‖
        _ = _ := by ring
    _ <= pintzEquation46RightTailBound etaJ gamma lambda +
        pintzEquation46HorizontalBound lambda Zminus +
        pintzEquation46HorizontalBound lambda Zplus := by
      exact add_le_add (add_le_add
        (by simpa [pintzEquation46RightTailBound] using hright)
        (by simpa [pintzEquation46HorizontalBound] using hminus))
        (by simpa [pintzEquation46HorizontalBound] using hplus)

#print axioms norm_pintzFiniteMobiusPolynomial_le_partialSum
#print axioms norm_pintzFiniteMobiusPolynomial_le_sqrt_harmonic
#print axioms norm_pintzGaussianNumerator_horizontal_two_lambda_le
#print axioms norm_pintzFiniteContourIntegrand_horizontal_two_lambda_le
#print axioms norm_pintzFiniteContour_HIntegral'_two_lambda_le
#print axioms norm_pintzFiniteContourIntegrand_three_le
#print axioms integrable_pintzFiniteContourIntegrand_three
#print axioms integral_compl_Ioc_exp_neg_inv_lambda_sq_le
#print axioms norm_pintzMobiusFiniteHead_sub_rightSegment_le
#print axioms norm_pintzEquation46ContourError_le

end

end GafniTao
