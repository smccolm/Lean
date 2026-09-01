import GafniTao.FordSourcePeak
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Ford's cubic sum in printed source form

This file converts the certified normalized integral to the numerical
coefficient `1.569` printed in Lemma 7.3 and rewrites the cubic peak as the
source power of `t`.
-/

namespace GafniTao

noncomputable section

theorem ford_integral_constant_div_log_two_le :
    (108754 / 100000 : ℝ) / Real.log 2 ≤ 1.569 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlogPos]
  norm_num at hlog ⊢
  linarith

theorem fordSourceScale_mul_integral_constant_le
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordSourceScale D t * (108754 / 100000 : ℝ) ≤
      1.569 * D ^ ((1 : ℝ) / 3) * Real.log t ^ ((2 : ℝ) / 3) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfactor :
      0 ≤ D ^ ((1 : ℝ) / 3) * Real.log t ^ ((2 : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg hD.le _)
      (Real.rpow_nonneg (Real.log_pos ht).le _)
  unfold fordSourceScale
  calc
    D ^ ((3 : ℝ)⁻¹) * Real.log t ^ ((2 : ℝ) / 3) /
          Real.log 2 * (108754 / 100000 : ℝ) =
        (D ^ ((1 : ℝ) / 3) * Real.log t ^ ((2 : ℝ) / 3)) *
          ((108754 / 100000 : ℝ) / Real.log 2) := by
      norm_num [inv_div]
      field_simp [hlogTwo.ne']
    _ ≤ (D ^ ((1 : ℝ) / 3) * Real.log t ^ ((2 : ℝ) / 3)) * 1.569 :=
      mul_le_mul_of_nonneg_left ford_integral_constant_div_log_two_le hfactor
    _ = 1.569 * D ^ ((1 : ℝ) / 3) *
          Real.log t ^ ((2 : ℝ) / 3) := by ring

/-- Ford's peak-plus-integral estimate with the exact printed `1.569`
coefficient and source exponent. -/
theorem fordCubicExpSum_le_source
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (r : ℕ) :
    (∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j)) ≤
      t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) *
        (1 + 1.569 * D ^ ((1 : ℝ) / 3) *
          Real.log t ^ ((2 : ℝ) / 3)) := by
  have hcert := fordCubicExpSum_le_certified hsigma hD ht r
  have hpeak := exp_two_mul_fordCubicY_cubed_eq_sourcePower hsigma hD ht
  have hscale := fordCubicScale_eq_sourceScale hD ht
  have hpower :
      0 ≤ t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg (zero_lt_one.trans ht).le _
  rw [hpeak, hscale] at hcert
  exact hcert.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl 1) (fordSourceScale_mul_integral_constant_le hD ht))
    hpower)

#print axioms ford_integral_constant_div_log_two_le
#print axioms fordSourceScale_mul_integral_constant_le
#print axioms fordCubicExpSum_le_source

end

end GafniTao
