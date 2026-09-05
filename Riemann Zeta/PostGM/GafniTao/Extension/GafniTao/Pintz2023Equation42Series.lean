import GafniTao.Pintz2023Equation42
import GafniTao.PintzMobiusSeries

/-!
# Pintz (2023), equation (4.2): termwise source expansion

This file performs the complete-line sum/integral interchange for the actual
finite-mollifier coefficient `a_n`.  It is deliberately separate from the
older full-Moebius-series detector: the summands here are
`LSeries.term (pintz2023Coeff X) (rho + s) n`.
-/

open Complex Filter MeasureTheory Topology
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023Equation42VerticalTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let s : ℂ := ((3 : ℝ) : ℂ) + (t : ℂ) * I
  LSeries.term (pintz2023Coeff X) (rho + s) n *
    pintzGaussianKernel lambda s

theorem norm_pintz2023Equation42_term_vertical_eq
    (X : ℕ) (rho : ℂ) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (pintz2023Coeff X)
        (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)) n‖ =
      ‖LSeries.term (pintz2023Coeff X)
        (((3 + rho.re : ℝ) : ℂ)) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    congr 1
    change
      ‖((n : ℝ) : ℂ) ^ (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I))‖ =
        ‖((n : ℝ) : ℂ) ^ (((3 + rho.re : ℝ) : ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp [add_comm]

private theorem continuous_pintz2023Equation42VerticalTerm
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (n : ℕ) :
    Continuous (pintz2023Equation42VerticalTerm X rho lambda n) := by
  have hs : Continuous (fun t : ℝ =>
      rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by fun_prop
  have hsTerm : Continuous (fun t : ℝ =>
      LSeries.term (pintz2023Coeff X)
        (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)) n) := by
    by_cases hn : n = 0
    · subst n
      have hzero : (fun t : ℝ =>
          LSeries.term (pintz2023Coeff X)
            (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I)) 0) =
          fun _ : ℝ => (0 : ℂ) := by
        funext t
        simp [LSeries.term_def]
      rw [hzero]
      exact continuous_const
    · simp_rw [LSeries.term_of_ne_zero hn]
      have hpow : Continuous (fun t : ℝ =>
          (n : ℂ) ^ (rho + (((3 : ℝ) : ℂ) + (t : ℂ) * I))) := by
        exact Continuous.cpow continuous_const hs
          (fun _ => Complex.natCast_mem_slitPlane.mpr hn)
      exact continuous_const.div hpow (fun t => by
        rw [Complex.cpow_ne_zero_iff]
        exact Or.inl (by exact_mod_cast hn))
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
  unfold pintz2023Equation42VerticalTerm
  exact hsTerm.mul hsKernel

theorem norm_pintz2023Equation42VerticalTerm_le
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hlambda : 0 < lambda)
    (n : ℕ) (t : ℝ) :
    ‖pintz2023Equation42VerticalTerm X rho lambda n t‖ ≤
      ‖LSeries.term (pintz2023Coeff X)
          (((3 + rho.re : ℝ) : ℂ)) n‖ *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  have hkernel := norm_pintzGaussianKernel_right_le
    (lambda := lambda) (t := t) hlambda
  unfold pintz2023Equation42VerticalTerm
  rw [norm_mul, norm_pintz2023Equation42_term_vertical_eq X rho n t]
  calc
    ‖LSeries.term (pintz2023Coeff X) ((3 + rho.re : ℝ) : ℂ) n‖ *
        ‖pintzGaussianKernel lambda (((3 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      ‖LSeries.term (pintz2023Coeff X) ((3 + rho.re : ℝ) : ℂ) n‖ *
        ((1 / 3 : ℝ) *
          (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * t ^ 2))) :=
      mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
    _ = _ := by ring

theorem integrable_pintz2023Equation42VerticalTerm
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hlambda : 0 < lambda)
    (n : ℕ) :
    Integrable (pintz2023Equation42VerticalTerm X rho lambda n) := by
  let C : ℝ :=
    ‖LSeries.term (pintz2023Coeff X)
        (((3 + rho.re : ℝ) : ℂ)) n‖ *
      ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda))
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  apply Integrable.mono' hmajor
  · exact (continuous_pintz2023Equation42VerticalTerm n).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_pintz2023Equation42VerticalTerm_le hlambda n t

theorem summable_integral_norm_pintz2023Equation42VerticalTerm
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖pintz2023Equation42VerticalTerm X rho lambda n t‖) := by
  let C : ℝ :=
    ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
      Real.sqrt (Real.pi / (1 / lambda))
  have hsRe : 1 < (3 + rho.re : ℝ) := by linarith
  have hsComplex : 1 < (((3 + rho.re : ℝ) : ℂ)).re := by
    simpa using hsRe
  have hseries : Summable (fun n : ℕ =>
      ‖LSeries.term (pintz2023Coeff X)
        (((3 + rho.re : ℝ) : ℂ)) n‖) :=
    (mollifiedZetaCoeff_LSeriesSummable X hsComplex).norm
  refine (hseries.mul_right C).of_nonneg_of_le
    (fun n => integral_nonneg (fun _ => norm_nonneg _)) (fun n => ?_)
  calc
    ∫ t : ℝ, ‖pintz2023Equation42VerticalTerm X rho lambda n t‖ ≤
        ∫ t : ℝ,
          ‖LSeries.term (pintz2023Coeff X)
              (((3 + rho.re : ℝ) : ℂ)) n‖ *
            ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
            Real.exp (-(1 / lambda) * t ^ 2) := by
      apply integral_mono
        (integrable_pintz2023Equation42VerticalTerm hlambda n).norm
      · exact (integrable_exp_neg_mul_sq
          (one_div_pos.mpr hlambda)).const_mul _
      · intro t
        exact norm_pintz2023Equation42VerticalTerm_le hlambda n t
    _ = ‖LSeries.term (pintz2023Coeff X)
            (((3 + rho.re : ℝ) : ℂ)) n‖ * C := by
      rw [integral_const_mul, integral_gaussian]
      simp only [C]
      ring

theorem integral_pintz2023Equation42SeriesIntegrand_eq_tsum
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    (∫ t : ℝ, pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ∑' n : ℕ, ∫ t : ℝ,
        pintz2023Equation42VerticalTerm X rho lambda n t := by
  have hinterchange := integral_tsum_of_summable_integral_norm
    (fun n => integrable_pintz2023Equation42VerticalTerm
      (X := X) hlambda n)
    (summable_integral_norm_pintz2023Equation42VerticalTerm
      (X := X) hrho hlambda)
  calc
    (∫ t : ℝ, pintz2023Equation42SeriesIntegrand X rho lambda
        (((3 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, ∑' n : ℕ,
          pintz2023Equation42VerticalTerm X rho lambda n t := by
      apply integral_congr_ae
      filter_upwards [] with t
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
    _ = ∑' n : ℕ, ∫ t : ℝ,
        pintz2023Equation42VerticalTerm X rho lambda n t := hinterchange.symm

noncomputable def pintz2023GaussianWeight
    (lambda : ℝ) (n : ℕ) : ℂ :=
  VerticalIntegral' (fun s : ℂ =>
    (n : ℂ) ^ (-s) * pintzGaussianKernel lambda s) 3

theorem pintz2023Equation42VerticalTerm_factor
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) (t : ℝ) :
    pintz2023Equation42VerticalTerm X rho lambda n t =
      LSeries.term (pintz2023Coeff X) rho n *
        ((n : ℂ) ^ (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
          pintzGaussianKernel lambda
            (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  by_cases hn : n = 0
  · subst n
    simp [pintz2023Equation42VerticalTerm, LSeries.term_def]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [pintz2023Equation42VerticalTerm]
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    have hpowS : (n : ℂ) ^
        (((3 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hpowRho : (n : ℂ) ^ rho ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    field_simp

theorem normalized_integral_pintz2023Equation42VerticalTerm_eq
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi * I) : ℂ) * I *
        (∫ t : ℝ, pintz2023Equation42VerticalTerm X rho lambda n t) =
      LSeries.term (pintz2023Coeff X) rho n *
        pintz2023GaussianWeight lambda n := by
  rw [pintz2023GaussianWeight]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  have hIntegral :
      (∫ t : ℝ, pintz2023Equation42VerticalTerm X rho lambda n t) =
        LSeries.term (pintz2023Coeff X) rho n *
          (∫ t : ℝ,
            (n : ℂ) ^ (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
              pintzGaussianKernel lambda
                (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    calc
      _ = ∫ t : ℝ,
          LSeries.term (pintz2023Coeff X) rho n *
            ((n : ℂ) ^ (-(((3 : ℝ) : ℂ) + (t : ℂ) * I)) *
              pintzGaussianKernel lambda
                (((3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact pintz2023Equation42VerticalTerm_factor X rho lambda n t
      _ = _ := by rw [integral_const_mul]
  rw [hIntegral]
  ring

theorem pintz2023_equation_4_2_complete
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    pintz2023Equation42Integral X rho lambda =
      ∑' n : ℕ,
        LSeries.term (pintz2023Coeff X) rho n *
          pintz2023GaussianWeight lambda n := by
  rw [pintz2023_equation_4_2 hrho]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [integral_pintz2023Equation42SeriesIntegrand_eq_tsum hrho hlambda]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [mul_assoc] using
    normalized_integral_pintz2023Equation42VerticalTerm_eq
      X rho lambda n

#print axioms summable_integral_norm_pintz2023Equation42VerticalTerm
#print axioms pintz2023_equation_4_2_complete

end

end GafniTao
