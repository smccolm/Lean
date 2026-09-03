import GafniTao.PintzMobiusIdentity
import RiemannZeta.GuthMaynard.HughesYoungEquation98Bounds

/-!
# Termwise Möbius expansion of Pintz equation (4.1)

This file justifies the infinite-series/integral interchange on the complete
right vertical line.  Every summand is the genuine Möbius `LSeries.term`;
absolute convergence and the Gaussian ordinate supply the Tonelli majorant.
-/

open Complex Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintzMobiusVerticalTerm
    (rho : ℂ) (lambda : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let s : ℂ := (3 : ℝ) + (t : ℂ) * I
  riemannZeta (s + rho) *
    LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
      (s + rho) n *
    pintzGaussianKernel lambda s

/-- The norm of a Möbius `LSeries.term` is constant along the vertical
line used in Pintz (4.1). -/
theorem norm_pintzMobius_term_vertical_eq
    (rho : ℂ) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        (((3 : ℝ) : ℂ) + (t : ℂ) * I + rho) n‖ =
      ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        (((3 + rho.re : ℝ) : ℂ)) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    congr 1
    change
      ‖((n : ℝ) : ℂ) ^ (((3 : ℝ) : ℂ) + (t : ℂ) * I + rho)‖ =
        ‖((n : ℝ) : ℂ) ^ (((3 + rho.re : ℝ) : ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp

/-- Gaussian majorant for the bare kernel on the right line, valid at every
ordinate (including the central range). -/
theorem norm_pintzGaussianKernel_right_le
    {lambda t : ℝ} (hlambda : 0 < lambda) :
    ‖pintzGaussianKernel lambda (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖ <=
      (1 / 3 : ℝ) *
        (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2)) := by
  rw [pintzGaussianKernel, norm_div]
  have hden : (3 : ℝ) <= ‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm
      (((3 : ℝ) : ℂ) + (t : ℂ) * I)
    norm_num at hre ⊢
    exact hre
  calc
    ‖pintzGaussianNumerator lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖ /
        ‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖
        <= ‖pintzGaussianNumerator lambda
            (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖ / 3 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ = (1 / 3 : ℝ) *
        (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2)) := by
      rw [show (t : ℂ) * I = I * t by simp [mul_comm]]
      rw [norm_pintzGaussianNumerator_vertical_factored lambda 3 t hlambda]
      ring_nf

private theorem continuous_pintzMobiusVerticalTerm
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (n : ℕ) :
    Continuous (pintzMobiusVerticalTerm rho lambda n) := by
  have hs : Continuous (fun t : ℝ =>
      (((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) := by fun_prop
  have hsZeta : Continuous (fun t : ℝ =>
      riemannZeta ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_riemannZeta (by
      intro hone
      have hre := congrArg Complex.re hone
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, zero_mul, Complex.I_re, Complex.I_im, mul_zero,
        sub_zero, one_re] at hre
      linarith)).continuousAt.comp hs.continuousAt
  have hsKernel : Continuous (fun t : ℝ =>
      pintzGaussianKernel lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    unfold pintzGaussianKernel
    have hline : Continuous (fun u : ℝ =>
        (((3 : ℝ) : ℂ) + (u : ℂ) * I)) := by fun_prop
    have hnum : Continuous (fun u : ℝ =>
        pintzGaussianNumerator lambda
          (((3 : ℝ) : ℂ) + (u : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (analyticAt_pintzGaussianNumerator lambda _).continuousAt.comp
        hline.continuousAt
    exact hnum.div hline (fun t => by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre)
  have hsTerm : Continuous (fun t : ℝ =>
      LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) n) := by
    by_cases hn : n = 0
    · subst n
      have hzero : (fun t : ℝ =>
          LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho) 0) =
          fun _ : ℝ => (0 : ℂ) := by
        funext t
        simp [LSeries.term_def]
      rw [hzero]
      exact continuous_const
    · simp_rw [LSeries.term_of_ne_zero hn]
      have hpow : Continuous (fun t : ℝ =>
          (n : ℂ) ^ ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho)) := by
        exact Continuous.cpow continuous_const hs
          (fun _ => Complex.natCast_mem_slitPlane.mpr hn)
      exact continuous_const.div hpow (fun t => by
        rw [Complex.cpow_ne_zero_iff]
        exact Or.inl (by exact_mod_cast hn))
  unfold pintzMobiusVerticalTerm
  exact (hsZeta.mul hsTerm).mul hsKernel

theorem norm_pintzMobiusVerticalTerm_le
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) (n : ℕ) (t : ℝ) :
    ‖pintzMobiusVerticalTerm rho lambda n t‖ <=
      ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
          (((3 + rho.re : ℝ) : ℂ)) n‖ *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  have hzeta : ‖riemannZeta
      ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho)‖ <=
      hughesYoungZetaHalfPlaneMajorant :=
    norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant (by simp; linarith)
  have hkernel := norm_pintzGaussianKernel_right_le
    (lambda := lambda) (t := t) hlambda
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant := by
    exact tsum_nonneg (fun _ => norm_nonneg _)
  unfold pintzMobiusVerticalTerm
  rw [norm_mul, norm_mul, norm_pintzMobius_term_vertical_eq rho n t]
  calc
    ‖riemannZeta (((3 : ℝ) + (t : ℂ) * I) + rho)‖ *
          ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            ((3 + rho.re : ℝ) : ℂ) n‖ *
          ‖pintzGaussianKernel lambda ((3 : ℝ) + (t : ℂ) * I)‖
        <= hughesYoungZetaHalfPlaneMajorant *
          ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            ((3 + rho.re : ℝ) : ℂ) n‖ *
          ((1 / 3 : ℝ) *
            (Real.exp (9 / lambda + 3 * lambda) *
              Real.exp (-(1 / lambda) * t ^ 2))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hzeta (norm_nonneg _)) hkernel
        (norm_nonneg _)
        (mul_nonneg hHnonneg (norm_nonneg _))
    _ = _ := by ring

theorem integrable_pintzMobiusVerticalTerm
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) (n : ℕ) :
    Integrable (pintzMobiusVerticalTerm rho lambda n) := by
  let C : ℝ :=
    ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        (((3 + rho.re : ℝ) : ℂ)) n‖ *
      hughesYoungZetaHalfPlaneMajorant *
      ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda))
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  apply Integrable.mono' hmajor
  · exact (continuous_pintzMobiusVerticalTerm hrho n).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_pintzMobiusVerticalTerm_le hrho hlambda n t

/-- The sum of the integrated term norms is finite; this is the exact
Tonelli condition for the source expansion. -/
theorem summable_integral_norm_pintzMobiusVerticalTerm
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖pintzMobiusVerticalTerm rho lambda n t‖) := by
  let C : ℝ := hughesYoungZetaHalfPlaneMajorant *
    ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
      Real.sqrt (Real.pi / (1 / lambda))
  have hsRe : 1 < (3 + rho.re : ℝ) := by linarith
  have hsComplex : 1 < (((3 + rho.re : ℝ) : ℂ)).re := by
    simpa using hsRe
  have hseries : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m =>
          ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        (((3 + rho.re : ℝ) : ℂ)) n‖) :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsComplex).norm
  refine (hseries.mul_right C).of_nonneg_of_le
    (fun n => integral_nonneg (fun _ => norm_nonneg _)) (fun n => ?_)
  calc
    ∫ t : ℝ, ‖pintzMobiusVerticalTerm rho lambda n t‖ <=
        ∫ t : ℝ,
          ‖LSeries.term
              (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
              (((3 + rho.re : ℝ) : ℂ)) n‖ *
            hughesYoungZetaHalfPlaneMajorant *
            ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
            Real.exp (-(1 / lambda) * t ^ 2) := by
      apply integral_mono (integrable_pintzMobiusVerticalTerm
        hrho hlambda n).norm
      · exact (integrable_exp_neg_mul_sq
          (one_div_pos.mpr hlambda)).const_mul _
      · intro t
        exact norm_pintzMobiusVerticalTerm_le hrho hlambda n t
    _ = ‖LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            (((3 + rho.re : ℝ) : ℂ)) n‖ * C := by
      rw [integral_const_mul, integral_gaussian]
      simp only [C]
      ring

/-- Complete termwise integral expansion of the actual source integrand. -/
theorem integral_pintzMobiusIntegrand_eq_tsum
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) :
    (∫ t : ℝ, pintzMobiusIntegrand rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ∑' n : ℕ, ∫ t : ℝ,
        pintzMobiusVerticalTerm rho lambda n t := by
  have hinterchange := integral_tsum_of_summable_integral_norm
    (fun n => integrable_pintzMobiusVerticalTerm hrho hlambda n)
    (summable_integral_norm_pintzMobiusVerticalTerm hrho hlambda)
  calc
    (∫ t : ℝ, pintzMobiusIntegrand rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, ∑' n : ℕ,
          pintzMobiusVerticalTerm rho lambda n t := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hsRe : 1 <
          ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho).re := by
        simp
        linarith
      have hsum :=
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsRe).LSeriesHasSum
      have hscaled := (hsum.mul_left
        (riemannZeta
          ((((3 : ℝ) : ℂ) + (t : ℂ) * I) + rho))).mul_right
        (pintzGaussianKernel lambda
          (((3 : ℝ) : ℂ) + (t : ℂ) * I))
      unfold pintzMobiusIntegrand pintzMobiusVerticalTerm
      exact hscaled.tsum_eq.symm
    _ = ∑' n : ℕ, ∫ t : ℝ,
        pintzMobiusVerticalTerm rho lambda n t := hinterchange.symm

/-- The normalized complete right line is the `tsum` of normalized genuine
Möbius summands. -/
theorem pintzMobius_verticalIntegral_eq_tsum
    {rho : ℂ} {lambda : ℝ} (hrho : 1 / 2 <= rho.re)
    (hlambda : 0 < lambda) :
    VerticalIntegral' (pintzMobiusIntegrand rho lambda) 3 =
      ∑' n : ℕ,
        (1 / (2 * Real.pi * I) : ℂ) * I *
          (∫ t : ℝ, pintzMobiusVerticalTerm rho lambda n t) := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [integral_pintzMobiusIntegrand_eq_tsum hrho hlambda]
  rw [← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  ring

#print axioms summable_integral_norm_pintzMobiusVerticalTerm
#print axioms pintzMobius_verticalIntegral_eq_tsum

end

end GafniTao
