import GafniTao.Pintz2023Detection
import GafniTao.Pintz2023Equation42LeftIntegrable
import GafniTao.Pintz2023Equation47TruncationBound

/-!
# Pintz (2023), equations (4.2)--(4.12): finite integral extraction

This file contains the exact finite-dimensional extraction step.  It does
not assume Pintz's density conclusion.  Its hypotheses are the three
separate analytic errors which occur before (4.12): the displaced left
vertical integral, the pole residue, and the ordinate-truncation remainder.

The first extraction below deliberately records a polynomial lower bound in
`lambda`.  This is already sufficient for every later exponent calculation;
the sharper source estimate `c / log lambda` will be proved separately from
the literal Gaussian kernel before the final source crosswalk is closed.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- If each of the three errors in Pintz (4.2) and (4.7) is at most `1/8`,
then the literal finite small-line sum has norm at least `1/2`. -/
theorem norm_pintz2023TruncatedSmallLineSum_ge_half
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 8 ≤ lambda) (hetaUpper : eta ≤ 1 / 32)
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
    1 / 2 ≤
      ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X
          (pintz2023Rho etaJ gamma) lambda n‖ := by
  have hlambdaPos : 0 < lambda := by linarith
  have hetaQuarter : eta ≤ 1 / 4 := by linarith
  have hshift := pintz2023Equation42_source_shift
    (X := X) hrhoZero hetaJPos hetaJ hlambdaPos hetaQuarter
  have hfinite := pintz2023_equation_4_7_exact
    (X := X) (rho := pintz2023Rho etaJ gamma)
    (eta := eta) (lambda := lambda) (by simp [pintz2023Rho]; linarith)
    hlambda hetaUpper hX hXC
  let L : ℂ := VerticalIntegral'
    (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
    (-eta)
  let P : ℂ := pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda
  let S : ℂ := ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
    pintz2023TruncatedSmallLineTerm X
      (pintz2023Rho etaJ gamma) lambda n
  let R : ℂ := pintz2023Equation47TruncatedRemainder X
    (pintz2023Rho etaJ gamma) lambda
  have hone : (1 : ℂ) = L + P - S - R := by
    dsimp only [L, P, S, R]
    linear_combination hshift - hfinite
  have hnorm : (1 : ℝ) ≤ ‖L‖ + ‖P‖ + ‖S‖ + ‖R‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖L + P - S - R‖ := by rw [hone]
      _ ≤ ‖L‖ + ‖P‖ + ‖S‖ + ‖R‖ := by
        calc
          ‖L + P - S - R‖ ≤ ‖L + P - S‖ + ‖R‖ := norm_sub_le _ _
          _ ≤ (‖L + P‖ + ‖S‖) + ‖R‖ := by gcongr; exact norm_sub_le _ _
          _ ≤ (‖L‖ + ‖P‖ + ‖S‖) + ‖R‖ := by
            gcongr
            exact norm_add_le _ _
          _ = ‖L‖ + ‖P‖ + ‖S‖ + ‖R‖ := by ring
  dsimp only [L, P, S, R] at hnorm
  linarith

/-- A simple uniform bound for the literal equation-(4.7) kernel on its
finite ordinate window. -/
theorem norm_pintzGaussianKernel_equation47_le
    {lambda t : ℝ} (hlambda : 1 ≤ lambda) :
    ‖pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖ ≤
      lambda * Real.exp 2 := by
  have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hraw := norm_pintzGaussianKernel_vertical_le
    (lambda := lambda) (left := 1 / lambda) (u := t)
    hlambdaPos (one_div_ne_zero hlambdaPos.ne')
  have habs : |1 / lambda| = 1 / lambda :=
    abs_of_pos (one_div_pos.mpr hlambdaPos)
  have hinv : |1 / lambda|⁻¹ = lambda := by
    rw [habs]
    field_simp
  have hexponent :
      (1 / lambda) ^ 2 / lambda + lambda * (1 / lambda) -
          (1 / lambda) * t ^ 2 ≤ 2 := by
    have hcubic : 1 / lambda ^ 3 ≤ 1 := by
      have hpow : 1 ≤ lambda ^ 3 := one_le_pow₀ hlambda
      exact (div_le_one (by positivity : (0 : ℝ) < lambda ^ 3)).2 hpow
    have hnonneg : 0 ≤ (1 / lambda) * t ^ 2 := by positivity
    have hone : lambda * (1 / lambda) = 1 := by field_simp
    rw [show (1 / lambda) ^ 2 / lambda = 1 / lambda ^ 3 by field_simp,
      hone]
    nlinarith
  unfold pintz2023Equation47Shift at hraw ⊢
  rw [hinv] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponent) hlambdaPos.le)

theorem norm_pintz2023_vertical_normalization_le_one :
    ‖(1 / (2 * Real.pi * I) : ℂ) * I‖ ≤ 1 := by
  rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ Real.pi_pos).2 hpi
  nlinarith [mul_le_mul_of_nonneg_right hpiInv (show (0 : ℝ) ≤ 1 / 2 by norm_num)]

/-- Finite equation-(4.12) extraction with an explicit polynomial loss.
The stronger logarithmic kernel-mass estimate is intentionally a separate
obligation, so this theorem cannot conceal it in asymptotic notation. -/
theorem exists_large_pintz2023Equation47Polynomial
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 8 ≤ lambda) (hetaUpper : eta ≤ 1 / 32)
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
      1 / (16 * Real.exp 2 * lambda ^ 2) ≤
        ‖pintz2023Equation47Polynomial X
          (pintz2023Rho etaJ gamma) lambda t‖ := by
  have hlambdaPos : 0 < lambda := by linarith
  have hlower := norm_pintz2023TruncatedSmallLineSum_ge_half
    hrhoZero hetaJPos hetaJ hlambda hetaUpper hX hXC hleft hpole hremainder
  have hsource := pintz2023_truncated_sum_eq_source_integral
    X (pintz2023Rho etaJ gamma) lambda hlambdaPos
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ t ∈ Set.uIoc (-2 * lambda) (2 * lambda),
      ‖pintz2023Equation47Polynomial X (pintz2023Rho etaJ gamma) lambda t *
          pintzGaussianKernel lambda (pintz2023Equation47Shift lambda t)‖ ≤
        1 / (16 * lambda) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-2 * lambda) (2 * lambda) := by
      have ht' := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by linarith : -2 * lambda ≤ 2 * lambda)] at ht'
      exact ht'
    rw [norm_mul]
    have hpoly := (hnot t htIcc).le
    have hkernel := norm_pintzGaussianKernel_equation47_le
      (t := t) (by linarith : 1 ≤ lambda)
    calc
      _ ≤ (1 / (16 * Real.exp 2 * lambda ^ 2)) *
          (lambda * Real.exp 2) :=
        mul_le_mul hpoly hkernel (norm_nonneg _) (by positivity)
      _ = 1 / (16 * lambda) := by field_simp [hlambdaPos.ne']
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hupper :
      ‖∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
        pintz2023TruncatedSmallLineTerm X
          (pintz2023Rho etaJ gamma) lambda n‖ ≤ 1 / 4 := by
    rw [hsource, norm_mul]
    calc
      _ ≤ 1 * ((1 / (16 * lambda)) *
          |2 * lambda - (-2 * lambda)|) :=
        mul_le_mul norm_pintz2023_vertical_normalization_le_one hintegral
          (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by
        rw [abs_of_nonneg (by linarith : 0 ≤ 2 * lambda - (-2 * lambda))]
        field_simp [hlambdaPos.ne']
        ring
  linarith

#print axioms norm_pintz2023TruncatedSmallLineSum_ge_half
#print axioms norm_pintzGaussianKernel_equation47_le
#print axioms exists_large_pintz2023Equation47Polynomial

end

end GafniTao
