import GafniTao.Pintz2023DetectionIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The logarithmic mass of Pintz's equation-(4.7) kernel

The denominator on the line `Re s = 1/lambda` contributes the logarithm in
Pintz (4.12).  We split at `|t| = 1/lambda`: the central interval is paid for
by the real part of the denominator, and the outer interval by its imaginary
part.  Thus the literal kernel, rather than an unspecified weight, is carried
through the estimate.
-/

open Complex MeasureTheory Set

namespace GafniTao

noncomputable section

private theorem norm_pintzGaussianKernel_equation47_even
    (lambda t : ℝ) (hlambda : 0 < lambda) :
    ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda (-t))‖ =
      ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖ := by
  unfold pintz2023Equation47Shift pintzGaussianKernel
  have hnumNeg :
      ‖pintzGaussianNumerator lambda
          (((1 / lambda : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
        Real.exp ((1 / lambda) ^ 2 / lambda + lambda * (1 / lambda)) *
          Real.exp (-(1 / lambda) * (-t) ^ 2) := by
    simpa only [mul_comm] using
      norm_pintzGaussianNumerator_vertical_factored
        lambda (1 / lambda) (-t) hlambda
  have hnumPos :
      ‖pintzGaussianNumerator lambda
          (((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I)‖ =
        Real.exp ((1 / lambda) ^ 2 / lambda + lambda * (1 / lambda)) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
    simpa only [mul_comm] using
      norm_pintzGaussianNumerator_vertical_factored
        lambda (1 / lambda) t hlambda
  have hden :
      ‖((1 / lambda : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ =
        ‖((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [norm_div, norm_div, hnumNeg, hnumPos, hden]
  simp only [neg_sq]

/-- Away from the central interval, the imaginary part of the denominator
gives the source `1/|t|` majorant. -/
theorem norm_pintzGaussianKernel_equation47_le_inv_abs
    {lambda t : ℝ} (hlambda : 1 ≤ lambda) (ht : t ≠ 0) :
    ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖ ≤
      Real.exp 2 / |t| := by
  have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hden : |t| ≤
      ‖((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    have him := Complex.abs_im_le_norm
      (((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I)
    simpa using him
  have htAbs : 0 < |t| := abs_pos.mpr ht
  have hdenPos : 0 < ‖((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    htAbs.trans_le hden
  have hinv :
      ‖((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I‖⁻¹ ≤ |t|⁻¹ :=
    (inv_le_inv₀ hdenPos htAbs).2 hden
  have hcubic : 1 / lambda ^ 3 ≤ 1 := by
    have hpow : 1 ≤ lambda ^ 3 := one_le_pow₀ hlambda
    exact (div_le_one (by positivity : (0 : ℝ) < lambda ^ 3)).2 hpow
  have hexponent :
      (1 / lambda) ^ 2 / lambda + lambda * (1 / lambda) -
          (1 / lambda) * t ^ 2 ≤ 2 := by
    have hnonneg : 0 ≤ (1 / lambda) * t ^ 2 := by positivity
    have hone : lambda * (1 / lambda) = 1 := by field_simp
    rw [show (1 / lambda) ^ 2 / lambda = 1 / lambda ^ 3 by field_simp,
      hone]
    nlinarith
  have hnum :
      ‖pintzGaussianNumerator lambda
          (((1 / lambda : ℝ) : ℂ) + (t : ℂ) * I)‖ =
        Real.exp ((1 / lambda) ^ 2 / lambda + lambda * (1 / lambda)) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
    simpa only [mul_comm] using
      norm_pintzGaussianNumerator_vertical_factored
        lambda (1 / lambda) t hlambdaPos
  have hexponent' :
      (1 / lambda) ^ 2 / lambda + lambda * (1 / lambda) +
          -(1 / lambda) * t ^ 2 ≤ 2 := by
    convert hexponent using 1
    ring
  unfold pintz2023Equation47Shift pintzGaussianKernel
  rw [norm_div, div_eq_mul_inv, hnum, ← Real.exp_add]
  calc
    _ ≤ Real.exp
          ((1 / lambda) ^ 2 / lambda + lambda * (1 / lambda) +
            -(1 / lambda) * t ^ 2) * |t|⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ Real.exp 2 * |t|⁻¹ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent') (by positivity)
    _ = Real.exp 2 / |t| := by rw [div_eq_mul_inv]

/-- The norm of the literal small-line kernel is even in the ordinate. -/
theorem integral_norm_pintzGaussianKernel_equation47_symmetric
    {lambda a : ℝ} (hlambda : 0 < lambda) :
    (∫ t in (-a)..a,
        ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖) =
      2 * ∫ t in 0..a,
        ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖ := by
  let f : ℝ → ℝ := fun t =>
    ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖
  have hf : Integrable f := by
    have h := (integrable_pintzGaussianKernel_vertical
      lambda (1 / lambda) hlambda (one_div_ne_zero hlambda.ne')).norm
    simpa only [f, pintz2023Equation47Shift, mul_comm I] using h
  have heven : ∀ t, f (-t) = f t := fun t =>
    norm_pintzGaussianKernel_equation47_even lambda t hlambda
  have hnegative : (∫ t in (-a)..0, f t) = ∫ t in 0..a, f t := by
    calc
      (∫ t in (-a)..0, f t) = ∫ t in 0..a, f (-t) := by
        symm
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (a := 0) (b := a) f)
      _ = ∫ t in 0..a, f t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact heven t
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hf.intervalIntegrable hf.intervalIntegrable, hnegative]
  ring

/-- Exact logarithmic mass estimate used in Pintz (4.12).  Constants are
kept explicit; `8 * exp 2` is harmless but avoids any hidden Vinogradov
constant. -/
theorem integral_norm_pintzGaussianKernel_equation47_le_log
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    (∫ t in (-2 * lambda)..(2 * lambda),
        ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖) ≤
      8 * Real.exp 2 * Real.log lambda := by
  have hlambdaPos : 0 < lambda := by linarith
  have hlambdaOne : 1 ≤ lambda := by linarith
  let f : ℝ → ℝ := fun t =>
    ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖
  have hf : Integrable f := by
    have h := (integrable_pintzGaussianKernel_vertical
      lambda (1 / lambda) hlambdaPos (one_div_ne_zero hlambdaPos.ne')).norm
    simpa only [f, pintz2023Equation47Shift, mul_comm I] using h
  have hcutPos : 0 < 1 / lambda := one_div_pos.mpr hlambdaPos
  have hcutUpper : 1 / lambda ≤ 2 * lambda := by
    have : 1 ≤ 2 * lambda ^ 2 := by nlinarith
    rw [div_le_iff₀ hlambdaPos]
    nlinarith
  have hcentral : (∫ t in 0..(1 / lambda), f t) ≤ 2 * Real.exp 2 := by
    have hmono := intervalIntegral.integral_mono_on hcutPos.le
      hf.intervalIntegrable intervalIntegrable_const
      (fun t _ht => norm_pintzGaussianKernel_equation47_le hlambdaOne)
    calc
      _ ≤ ∫ _t in 0..(1 / lambda), lambda * Real.exp 2 := hmono
      _ = Real.exp 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp [hlambdaPos.ne']
        ring
      _ ≤ 2 * Real.exp 2 := by nlinarith [Real.exp_pos 2]
  have houtside : (∫ t in (1 / lambda)..(2 * lambda), f t) ≤
      Real.exp 2 * Real.log (2 * lambda ^ 2) := by
    have hinvInt : IntervalIntegrable (fun t : ℝ => Real.exp 2 * (1 / t))
        volume (1 / lambda) (2 * lambda) := by
      exact (intervalIntegral.intervalIntegrable_one_div
        (fun t ht => by
          have htIcc : t ∈ Set.Icc (1 / lambda) (2 * lambda) := by
            rwa [Set.uIcc_of_le hcutUpper] at ht
          exact ne_of_gt (hcutPos.trans_le htIcc.1))
        (by fun_prop)).const_mul _
    have hmono := intervalIntegral.integral_mono_on hcutUpper
      hf.intervalIntegrable hinvInt (fun t ht => by
        have htPos : 0 < t := hcutPos.trans_le ht.1
        have hraw := norm_pintzGaussianKernel_equation47_le_inv_abs
          hlambdaOne htPos.ne'
        rw [abs_of_pos htPos, div_eq_mul_inv] at hraw
        simpa [f, one_div] using hraw)
    calc
      _ ≤ ∫ t in (1 / lambda)..(2 * lambda),
          Real.exp 2 * (1 / t) := hmono
      _ = Real.exp 2 * Real.log (2 * lambda ^ 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hcutPos (by positivity)]
        congr 2
        field_simp [hlambdaPos.ne']
  have hlogTwo : Real.log 2 ≤ Real.log lambda :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogNonneg : 0 ≤ Real.log lambda := Real.log_nonneg hlambdaOne
  have hlogProduct : Real.log (2 * lambda ^ 2) ≤ 3 * Real.log lambda := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hlambdaPos.ne'),
      Real.log_pow]
    norm_num
    linarith
  have hlogEight : Real.log 8 ≤ Real.log lambda :=
    Real.log_le_log (by norm_num) hlambda
  have hlogEightEq : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlogAtLeastTwo : 2 ≤ Real.log lambda := by
    rw [hlogEightEq] at hlogEight
    nlinarith [Real.log_two_gt_d9]
  have hpositive : (∫ t in 0..(2 * lambda), f t) ≤
      4 * Real.exp 2 * Real.log lambda := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      hf.intervalIntegrable hf.intervalIntegrable]
    calc
      (∫ t in 0..(1 / lambda), f t) +
          ∫ t in (1 / lambda)..(2 * lambda), f t ≤
        2 * Real.exp 2 + Real.exp 2 * Real.log (2 * lambda ^ 2) :=
          add_le_add hcentral houtside
      _ ≤ 4 * Real.exp 2 * Real.log lambda := by
        have houtMul := mul_le_mul_of_nonneg_left hlogProduct
          (Real.exp_pos 2).le
        have htwoMul := mul_le_mul_of_nonneg_left hlogAtLeastTwo
          (Real.exp_pos 2).le
        nlinarith
  have hsym := integral_norm_pintzGaussianKernel_equation47_symmetric
    (a := 2 * lambda) hlambdaPos
  change (∫ t in (-2 * lambda)..(2 * lambda), f t) ≤ _
  rw [show -2 * lambda = -(2 * lambda) by ring, hsym]
  nlinarith

/-- Pintz's equation (4.12), now with the source logarithmic loss.  The
polynomial and the ordinate window are exactly those of the finite equation
(4.7); no surrogate weight or sampled ordinate set is introduced. -/
theorem exists_large_pintz2023Equation47Polynomial_log
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 8 ≤ lambda) (hetaUpper : eta ≤ 1 / 24)
    (hX : 1 ≤ X) (hXC : X ≤ pintz2023Cutoff lambda)
    (hleft :
      ‖VerticalIntegral'
          (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
          (-eta)‖ ≤ 1 / 8)
    (hpole :
      ‖pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda‖ ≤ 1 / 8)
    (hremainder :
      ‖pintz2023Equation47TruncatedRemainder X
          (pintz2023Rho etaJ gamma) lambda‖ ≤ 1 / 8) :
    ∃ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
      1 / (32 * Real.exp 2 * Real.log lambda) ≤
        ‖pintz2023Equation47Polynomial X
          (pintz2023Rho etaJ gamma) lambda t‖ := by
  have hlambdaPos : 0 < lambda := by linarith
  have hlogPos : 0 < Real.log lambda := Real.log_pos (by linarith)
  have hlower := norm_pintz2023TruncatedSmallLineSum_ge_half
    hrhoZero hetaJPos hetaJ hlambda hetaUpper hX hXC hleft hpole hremainder
  have hsource := pintz2023_truncated_sum_eq_source_integral
    X (pintz2023Rho etaJ gamma) lambda hlambdaPos
  let P : ℝ → ℂ := fun t =>
    pintz2023Equation47Polynomial X (pintz2023Rho etaJ gamma) lambda t
  let K : ℝ → ℂ := fun t =>
    pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)
  let q : ℝ := 1 / (32 * Real.exp 2 * Real.log lambda)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hK : Integrable K := by
    have h := integrable_pintzGaussianKernel_vertical
      lambda (1 / lambda) hlambdaPos (one_div_ne_zero hlambdaPos.ne')
    simpa only [K, pintz2023Equation47Shift, mul_comm I] using h
  have hPK : Integrable (fun t => P t * K t) := by
    have hsum : Integrable (fun t : ℝ =>
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023TruncatedSmallLineVerticalTerm X
            (pintz2023Rho etaJ gamma) lambda n t) := by
      apply MeasureTheory.integrable_finsetSum
      intro n hn
      have hi := (integrable_pintz2023BareWeightIntegrand_vertical_pos
        (h := lambda - Real.log n) hlambdaPos
        (one_div_pos.mpr hlambdaPos)).const_mul
          (LSeries.term (pintz2023Coeff X) (pintz2023Rho etaJ gamma) n)
      simpa only [pintz2023TruncatedSmallLineVerticalTerm,
        pintz2023BareWeightIntegrand, mul_assoc] using hi
    apply hsum.congr
    filter_upwards with t
    exact pintz2023_vertical_sum_eq_polynomial_mul_kernel
      (X := X) (pintz2023Rho etaJ gamma) lambda t
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
      ‖P t * K t‖ ≤ q * ‖K t‖ := by
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hnot t ht).le (norm_nonneg _)
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -2 * lambda ≤ 2 * lambda)
    hPK.norm.intervalIntegrable
    (hK.norm.const_mul q).intervalIntegrable hpoint
  have hkernel := integral_norm_pintzGaussianKernel_equation47_le_log hlambda
  have hupper :
      ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X
          (pintz2023Rho etaJ gamma) lambda n‖ ≤ 1 / 4 := by
    rw [hsource, norm_mul]
    calc
      _ ≤ 1 * ‖∫ t in (-2 * lambda)..(2 * lambda), P t * K t‖ :=
        mul_le_mul norm_pintz2023_vertical_normalization_le_one le_rfl
          (norm_nonneg _) (by positivity)
      _ ≤ ∫ t in (-2 * lambda)..(2 * lambda), ‖P t * K t‖ := by
        simpa only [one_mul] using
          intervalIntegral.norm_integral_le_integral_norm
            (f := fun t => P t * K t)
            (by linarith : -2 * lambda ≤ 2 * lambda)
      _ ≤ ∫ t in (-2 * lambda)..(2 * lambda), q * ‖K t‖ := hmono
      _ = q * ∫ t in (-2 * lambda)..(2 * lambda), ‖K t‖ := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ q * (8 * Real.exp 2 * Real.log lambda) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hkernel) hq
      _ = 1 / 4 := by
        dsimp only [q]
        field_simp [Real.exp_ne_zero, hlogPos.ne']
        norm_num
  linarith

#print axioms norm_pintzGaussianKernel_equation47_le_inv_abs
#print axioms integral_norm_pintzGaussianKernel_equation47_le_log
#print axioms exists_large_pintz2023Equation47Polynomial_log

end

end GafniTao
