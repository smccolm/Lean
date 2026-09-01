import GafniTao.FordRiemannZetaLemma73

/-!
# Ford Theorem 1 on its large-height, near-one range

This file performs the exact numerical reduction
`(2/9) * sqrt (3 * 133.66) ≤ 4.45` and applies monotonicity of real powers.
The only remaining premise is the source exponential-sum Theorem 2.
-/

namespace GafniTao

noncomputable section

theorem fordSourceB_133_66_le_4_45 :
    fordSourceB 133.66 ≤ (4.45 : ℝ) := by
  have harg : 0 ≤ (3 : ℝ) * 133.66 := by norm_num
  have hsqrtNonneg : 0 ≤ Real.sqrt ((3 : ℝ) * 133.66) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt ((3 : ℝ) * 133.66)) ^ 2 = 3 * 133.66 :=
    Real.sq_sqrt harg
  unfold fordSourceB
  nlinarith

theorem fordSourceExponent_le_4_45
    {sigma : ℝ} (hsigmaUpper : sigma ≤ 1) :
    fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ) ≤
      4.45 * (1 - sigma) ^ (3 / 2 : ℝ) := by
  exact mul_le_mul_of_nonneg_right fordSourceB_133_66_le_4_45
    (Real.rpow_nonneg (by linarith) _)

theorem norm_riemannZeta_le_ford_highRange
    (hFord : FordTheorem2) {sigma t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      76.2 * t ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ (2 / 3 : ℝ) := by
  have htOne : 1 ≤ t := by
    have : (1 : ℝ) ≤ (10 : ℝ) ^ 100 := by norm_num
    exact this.trans ht
  have h73 := norm_riemannZeta_le_76_2 hFord
    hsigmaLower hsigmaUpper ht
  have hpow :
      t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        t ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le htOne
      (fordSourceExponent_le_4_45 hsigmaUpper)
  have hlogPower : 0 ≤ Real.log t ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg htOne) _
  have hmajor :
      76.2 * t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ) ≤
        76.2 * t ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ (2 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by norm_num)) hlogPower
  simpa [fordComplexHeight, mul_comm] using h73.trans hmajor

#print axioms fordSourceB_133_66_le_4_45
#print axioms fordSourceExponent_le_4_45
#print axioms norm_riemannZeta_le_ford_highRange

end

end GafniTao
