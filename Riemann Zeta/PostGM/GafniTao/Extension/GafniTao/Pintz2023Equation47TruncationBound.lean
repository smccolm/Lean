import GafniTao.Pintz2023Equation47Truncation
import RiemannZeta.GuthMaynard.HughesYoungSmallContourQuantitative
import RiemannZeta.GuthMaynard.ArithmeticCoefficients

/-!
# Pintz (2023), equation (4.7): quantitative ordinate tail

The complement of `[-2*lambda,2*lambda]` is estimated for the literal
small-line weight.  The first result retains the exact finite coefficient
mass, so subsequent parameter estimates cannot hide a normalization loss.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The Gaussian mass outside Pintz's literal ordinate window
`[-2 * lambda, 2 * lambda]`.  This local source-specific copy avoids importing
the older adaptive Pintz detector and its unrelated dependency graph. -/
theorem integral_compl_Ioc_pintz2023_gaussian_le
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
      Real.exp (-(1 / lambda) * t ^ 2)) ≤
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
      Real.exp (-(1 / lambda) * t ^ 2) ≤ g t := by
    intro t ht
    have hcut : 2 * lambda ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or] at ht
      rcases ht with ht | ht
      · have htt : t ≤ -2 * lambda := le_of_not_gt ht
        rw [abs_of_nonpos (htt.trans (by linarith))]
        linarith
      · have htt : 2 * lambda < t := lt_of_not_ge ht
        rw [abs_of_nonneg (by linarith : 0 ≤ t)]
        exact htt.le
    have hsq : (2 * lambda) ^ 2 ≤ t ^ 2 := by
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
        Real.exp (-(1 / lambda) * t ^ 2)) ≤
      ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, g t :=
        MeasureTheory.setIntegral_mono_on hsource.integrableOn hg.integrableOn
          measurableSet_Ioc.compl hpoint
    _ ≤ ∫ t : ℝ, g t := by
      apply MeasureTheory.setIntegral_le_integral hg
      filter_upwards with t
      unfold g
      positivity
    _ = Real.exp (-(7 / 2 : ℝ) * lambda) *
        Real.sqrt (Real.pi / (1 / (8 * lambda))) := by
      unfold g
      rw [integral_const_mul, integral_gaussian]

private theorem norm_pintz2023Truncation_normalization_le_one :
    ‖(1 / (2 * Real.pi * I) : ℂ) * I‖ ≤ 1 := by
  rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ Real.pi_pos).2 hpi
  calc
    Real.pi⁻¹ * (1 / 2 : ℝ) ≤ 1 * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hpiInv (by norm_num)
    _ ≤ 1 := by norm_num

theorem norm_pintz2023BareWeight_sub_truncated_le
    {lambda h : ℝ} (hlambda : 0 < lambda) :
    ‖pintz2023BareWeight lambda h (1 / lambda) -
        pintz2023TruncatedBareWeight lambda h‖ ≤
      ((1 / (1 / lambda)) *
        Real.exp ((1 / lambda) ^ 2 / lambda + h * (1 / lambda))) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
  let f : ℝ → ℂ := fun t =>
    pintz2023BareWeightIntegrand lambda h
      (((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I)
  let C : ℝ := (1 / (1 / lambda)) *
    Real.exp ((1 / lambda) ^ 2 / lambda + h * (1 / lambda))
  have hc : 0 < 1 / lambda := one_div_pos.mpr hlambda
  have hf : Integrable f :=
    integrable_pintz2023BareWeightIntegrand_vertical_pos hlambda hc
  have htail :=
    RiemannZeta.GuthMaynard.norm_integral_sub_symmetricIntervalIntegral_le_compl_norm
    hf (by positivity : 0 ≤ 2 * lambda)
  have htail' :
      ‖(∫ t : ℝ, f t) - ∫ t in (-2 * lambda)..(2 * lambda), f t‖ ≤
        ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖ := by
    simpa only [neg_mul] using htail
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcomp :
      (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖) ≤
        ∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
          C * Real.exp (-(1 / lambda) * t ^ 2) := by
    apply MeasureTheory.setIntegral_mono_on hf.norm.integrableOn
      hmajor.integrableOn measurableSet_Ioc.compl
    intro t ht
    simpa only [f, C, mul_assoc] using
      (norm_pintz2023BareWeightIntegrand_vertical_le_div
        (h := h) (c := 1 / lambda) (t := t) hlambda hc)
  have hgauss := integral_compl_Ioc_pintz2023_gaussian_le hlambda
  unfold pintz2023BareWeight pintz2023TruncatedBareWeight
    VerticalIntegral' VerticalIntegral VIntegral' VIntegral
  simp only [smul_eq_mul]
  simp only [← mul_assoc]
  change ‖((1 / (2 * Real.pi * I) : ℂ) * I) * (∫ t : ℝ, f t) -
      ((1 / (2 * Real.pi * I) : ℂ) * I) *
        (∫ t in (-2 * lambda)..(2 * lambda), f t)‖ ≤ _
  rw [← mul_sub, norm_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ) * I‖ *
        ‖(∫ t : ℝ, f t) -
          ∫ t in (-2 * lambda)..(2 * lambda), f t‖ ≤
      1 * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ, ‖f t‖) :=
        mul_le_mul norm_pintz2023Truncation_normalization_le_one
          htail' (norm_nonneg _) (by positivity)
    _ ≤ 1 * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        C * Real.exp (-(1 / lambda) * t ^ 2)) := by gcongr
    _ = C * (∫ t in (Set.Ioc (-2 * lambda) (2 * lambda))ᶜ,
        Real.exp (-(1 / lambda) * t ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
      ring
    _ ≤ C * (Real.exp (-(7 / 2 : ℝ) * lambda) *
        Real.sqrt (Real.pi / (1 / (8 * lambda)))) :=
      mul_le_mul_of_nonneg_left hgauss hCnonneg
    _ = _ := by
      dsimp [C]
      ring_nf

noncomputable def pintz2023SmallLineTailMass
    (X : ℕ) (rho : ℂ) (lambda : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
    ‖LSeries.term (pintz2023Coeff X) rho n‖ *
      ((1 / (1 / lambda)) *
        Real.exp ((1 / lambda) ^ 2 / lambda +
          (lambda - Real.log n) * (1 / lambda)))

theorem norm_pintz2023SmallLineTailTerm_le
    {X n : ℕ} {rho : ℂ} {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖pintz2023SmallLineTailTerm X rho lambda n‖ ≤
      (‖LSeries.term (pintz2023Coeff X) rho n‖ *
        ((1 / (1 / lambda)) *
          Real.exp ((1 / lambda) ^ 2 / lambda +
            (lambda - Real.log n) * (1 / lambda)))) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
  unfold pintz2023SmallLineTailTerm pintz2023SmallLineTerm
    pintz2023TruncatedSmallLineTerm
  rw [← mul_sub, norm_mul]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (norm_pintz2023BareWeight_sub_truncated_le
        (h := lambda - Real.log n) hlambda)
      (norm_nonneg (LSeries.term (pintz2023Coeff X) rho n)))

/-- Exact finite-mass bound for the entire discarded ordinate tail. -/
theorem norm_sum_pintz2023SmallLineTailTerm_le
    {X : ℕ} {rho : ℂ} {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023SmallLineTailTerm X rho lambda n‖ ≤
      pintz2023SmallLineTailMass X rho lambda *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
  calc
    ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023SmallLineTailTerm X rho lambda n‖ ≤
      ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        ‖pintz2023SmallLineTailTerm X rho lambda n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
      (‖LSeries.term (pintz2023Coeff X) rho n‖ *
        ((1 / (1 / lambda)) *
          Real.exp ((1 / lambda) ^ 2 / lambda +
            (lambda - Real.log n) * (1 / lambda)))) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
      exact Finset.sum_le_sum fun n hn =>
        norm_pintz2023SmallLineTailTerm_le hlambda
    _ = pintz2023SmallLineTailMass X rho lambda *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
      unfold pintz2023SmallLineTailMass
      rw [Finset.sum_mul]

private theorem pintz2023Cutoff_cast_lt_two_exp_local
    {lambda : ℝ} (hlambda : -3 ≤ lambda) :
    (pintz2023Cutoff lambda : ℝ) < 2 * Real.exp (lambda + 3) := by
  have hexpOne : 1 ≤ Real.exp (lambda + 3) :=
    Real.one_le_exp (by linarith)
  have hceil : (pintz2023Cutoff lambda : ℝ) <
      Real.exp (lambda + 3) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  linarith

private theorem pintz2023_smallLine_exponential_le
    {lambda : ℝ} {n : ℕ} (hlambda : 8 ≤ lambda) (hn : 0 < n) :
    Real.exp ((1 / lambda) ^ 2 / lambda +
        (lambda - Real.log n) * (1 / lambda)) ≤ Real.exp 2 := by
  have hlambdaPos : 0 < lambda := by linarith
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnOne
  have hinv : (1 / lambda) ^ 2 / lambda ≤ 1 := by
    have hlambdaOne : 1 ≤ lambda := by linarith
    have hpos : 0 < lambda ^ 3 := pow_pos hlambdaPos 3
    rw [show (1 / lambda) ^ 2 / lambda = 1 / lambda ^ 3 by field_simp]
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (lambda - 1)]
  have hlinear : (lambda - Real.log n) * (1 / lambda) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hlambdaPos).mpr (by linarith)
  exact Real.exp_le_exp.mpr (by linarith)

/-- The exact coefficient mass in the ordinate tail has only one exponential
factor in `lambda`.  This is deliberately crude but uniform in the zero and
the finite mollifier length, and leaves more than the `exp (-2 lambda)` saving
required in Pintz (4.7). -/
theorem pintz2023SmallLineTailMass_le_exp :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 8 ≤ lambda → eta ≤ 1 / 24 →
        pintz2023SmallLineTailMass X rho lambda ≤
          C * lambda * Real.exp (lambda + 5) := by
  obtain ⟨C₀, hC₀, hdiv⟩ :=
    divisorCountBound_native (1 / 48 : ℝ) (by norm_num)
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro X rho eta lambda hrho hlambda heta
  have hlambdaPos : 0 < lambda := by linarith
  have hterm : ∀ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
      ‖LSeries.term (pintz2023Coeff X) rho n‖ *
          ((1 / (1 / lambda)) *
            Real.exp ((1 / lambda) ^ 2 / lambda +
              (lambda - Real.log n) * (1 / lambda))) ≤
        C₀ * (lambda * Real.exp 2) := by
    intro n hnmem
    have hn : 0 < n := by
      have := (Finset.mem_Ioc.mp hnmem).1
      omega
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoeff := norm_pintz2023_LSeries_term_le
      (X := X) (n := n) hrho hn
    have hdivn := hdiv n hn
    have hexponents : (1 / 48 : ℝ) ≤ 1 - eta := by linarith
    have hpowers : (n : ℝ) ^ (1 / 48 : ℝ) ≤
        (n : ℝ) ^ (1 - eta) :=
      Real.rpow_le_rpow_of_exponent_le hnOne hexponents
    have hdenPos : 0 < (n : ℝ) ^ (1 - eta) := by positivity
    have hcoeffC : ‖LSeries.term (pintz2023Coeff X) rho n‖ ≤ C₀ := by
      calc
        ‖LSeries.term (pintz2023Coeff X) rho n‖ ≤
            (n.divisors.card : ℝ) / (n : ℝ) ^ (1 - eta) := hcoeff
        _ ≤ (C₀ * (n : ℝ) ^ (1 / 48 : ℝ)) /
            (n : ℝ) ^ (1 - eta) :=
          div_le_div_of_nonneg_right hdivn hdenPos.le
        _ ≤ (C₀ * (n : ℝ) ^ (1 - eta)) /
            (n : ℝ) ^ (1 - eta) := by
          gcongr
        _ = C₀ := by field_simp
    have hexp := pintz2023_smallLine_exponential_le hlambda hn
    have hnormalization : 1 / (1 / lambda) = lambda := by field_simp
    rw [hnormalization]
    exact mul_le_mul hcoeffC
      (mul_le_mul_of_nonneg_left hexp hlambdaPos.le)
      (by positivity) (by positivity)
  unfold pintz2023SmallLineTailMass
  calc
    (∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        ‖LSeries.term (pintz2023Coeff X) rho n‖ *
          ((1 / (1 / lambda)) *
            Real.exp ((1 / lambda) ^ 2 / lambda +
              (lambda - Real.log n) * (1 / lambda)))) ≤
      ∑ _n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        C₀ * (lambda * Real.exp 2) :=
      Finset.sum_le_sum fun n hn => hterm n hn
    _ = ((Finset.Ioc X (pintz2023Cutoff lambda)).card : ℝ) *
        (C₀ * (lambda * Real.exp 2)) := by simp
    _ ≤ (pintz2023Cutoff lambda : ℝ) *
        (C₀ * (lambda * Real.exp 2)) := by
      gcongr
      exact_mod_cast (show (Finset.Ioc X (pintz2023Cutoff lambda)).card ≤
        pintz2023Cutoff lambda by simp)
    _ ≤ (2 * Real.exp (lambda + 3)) *
        (C₀ * (lambda * Real.exp 2)) := by
      gcongr
      exact (pintz2023Cutoff_cast_lt_two_exp_local (by linarith)).le
    _ = (2 * C₀) * lambda *
        (Real.exp (lambda + 3) * Real.exp 2) := by ring
    _ = (2 * C₀) * lambda * Real.exp (lambda + 5) := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem pintz2023_gaussian_sqrt_le_eight_mul
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    Real.sqrt (Real.pi / (1 / (8 * lambda))) ≤ 8 * lambda := by
  have hlambdaPos : 0 < lambda := by linarith
  have hrad : 0 ≤ Real.pi / (1 / (8 * lambda)) := by positivity
  have hsq : (Real.sqrt (Real.pi / (1 / (8 * lambda)))) ^ 2 =
      Real.pi / (1 / (8 * lambda)) := Real.sq_sqrt hrad
  have hidentity : Real.pi / (1 / (8 * lambda)) =
      8 * Real.pi * lambda := by field_simp
  have hbound : Real.pi / (1 / (8 * lambda)) ≤ (8 * lambda) ^ 2 := by
    rw [hidentity]
    nlinarith [Real.pi_lt_four]
  nlinarith [Real.sqrt_nonneg (Real.pi / (1 / (8 * lambda)))]

private theorem pintz2023_lambda_sq_le_exp_half
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    lambda ^ 2 ≤ 8 * Real.exp (lambda / 2) := by
  have hx : 0 ≤ lambda / 2 := by linarith
  have hseries := Real.pow_div_factorial_le_exp (lambda / 2) hx 2
  norm_num at hseries ⊢
  nlinarith

/-- Complete `O(exp (-2 lambda))` estimate for the finite-height correction
in Pintz equation (4.7), with one constant uniform in every source
parameter. -/
theorem norm_sum_pintz2023SmallLineTailTerm_le_exp_neg_two :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 8 ≤ lambda → eta ≤ 1 / 24 →
        ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
            pintz2023SmallLineTailTerm X rho lambda n‖ ≤
          K * Real.exp (-2 * lambda) := by
  obtain ⟨C, hC, hmass⟩ := pintz2023SmallLineTailMass_le_exp
  let K : ℝ := 64 * C * Real.exp 5
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro X rho eta lambda hrho hlambda heta
  have hlambdaPos : 0 < lambda := by linarith
  have hraw := norm_sum_pintz2023SmallLineTailTerm_le
    (X := X) (rho := rho) hlambdaPos
  have hm := hmass (X := X) (rho := rho) hrho hlambda heta
  have hsqrt := pintz2023_gaussian_sqrt_le_eight_mul hlambda
  have hlambdaSq := pintz2023_lambda_sq_le_exp_half hlambda
  calc
    ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023SmallLineTailTerm X rho lambda n‖ ≤
      pintz2023SmallLineTailMass X rho lambda *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := hraw
    _ ≤ (C * lambda * Real.exp (lambda + 5)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) * (8 * lambda)) := by
      gcongr
    _ = (8 * C * Real.exp 5) * lambda ^ 2 *
        Real.exp (-(5 / 2 : ℝ) * lambda) := by
      have hexp : Real.exp (lambda + 5) *
          Real.exp (-(7 / 2 : ℝ) * lambda) =
          Real.exp 5 * Real.exp (-(5 / 2 : ℝ) * lambda) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        (C * lambda * Real.exp (lambda + 5)) *
            (Real.exp (-(7 / 2 : ℝ) * lambda) * (8 * lambda)) =
          8 * C * lambda ^ 2 *
            (Real.exp (lambda + 5) *
              Real.exp (-(7 / 2 : ℝ) * lambda)) := by ring
        _ = 8 * C * lambda ^ 2 *
            (Real.exp 5 * Real.exp (-(5 / 2 : ℝ) * lambda)) := by rw [hexp]
        _ = (8 * C * Real.exp 5) * lambda ^ 2 *
            Real.exp (-(5 / 2 : ℝ) * lambda) := by ring
    _ ≤ (8 * C * Real.exp 5) * (8 * Real.exp (lambda / 2)) *
        Real.exp (-(5 / 2 : ℝ) * lambda) := by
      gcongr
    _ = K * Real.exp (-2 * lambda) := by
      dsimp [K]
      have hexp : Real.exp (lambda / 2) *
          Real.exp (-(5 / 2 : ℝ) * lambda) =
          Real.exp (-2 * lambda) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        8 * C * Real.exp 5 * (8 * Real.exp (lambda / 2)) *
            Real.exp (-(5 / 2 : ℝ) * lambda) =
          64 * C * Real.exp 5 *
            (Real.exp (lambda / 2) *
              Real.exp (-(5 / 2 : ℝ) * lambda)) := by ring
        _ = 64 * C * Real.exp 5 * Real.exp (-2 * lambda) := by rw [hexp]

/-- The entire remainder in the finite-height equation (4.7), including the
right-line tail and both small-line ordinate tails, has the source's uniform
`exp (-2 lambda)` size. -/
theorem norm_pintz2023Equation47TruncatedRemainder_le_exp_neg_two :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 8 ≤ lambda → eta ≤ 1 / 24 →
        ‖pintz2023Equation47TruncatedRemainder X rho lambda‖ ≤
          K * Real.exp (-2 * lambda) := by
  obtain ⟨K₁, hK₁, hcomplete⟩ :=
    norm_pintz2023Equation47Remainder_le_exp_neg_two
  obtain ⟨K₂, hK₂, hsmall⟩ :=
    norm_sum_pintz2023SmallLineTailTerm_le_exp_neg_two
  refine ⟨K₁ + K₂, add_pos hK₁ hK₂, ?_⟩
  intro X rho eta lambda hrho hlambda heta
  unfold pintz2023Equation47TruncatedRemainder
  calc
    ‖pintz2023Equation47Remainder X rho lambda +
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023SmallLineTailTerm X rho lambda n‖ ≤
      ‖pintz2023Equation47Remainder X rho lambda‖ +
        ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023SmallLineTailTerm X rho lambda n‖ := norm_add_le _ _
    _ ≤ K₁ * Real.exp (-2 * lambda) +
        K₂ * Real.exp (-2 * lambda) :=
      add_le_add (hcomplete hrho hlambda heta) (hsmall hrho hlambda heta)
    _ = (K₁ + K₂) * Real.exp (-2 * lambda) := by ring

#print axioms norm_pintz2023BareWeight_sub_truncated_le
#print axioms norm_sum_pintz2023SmallLineTailTerm_le
#print axioms pintz2023SmallLineTailMass_le_exp
#print axioms norm_sum_pintz2023SmallLineTailTerm_le_exp_neg_two
#print axioms norm_pintz2023Equation47TruncatedRemainder_le_exp_neg_two

end

end GafniTao
