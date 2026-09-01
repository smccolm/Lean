import GafniTao.FordDadaroRemainder

/-!
# Absorption of the Dadaro correction at Ford's large-height threshold

Ford's Lemma 7.2 uses `t >= 10^100` and `sigma >= 15/16`.  The exact Dadaro
correction obtained previously is far smaller than `10^-80` on this range.
-/

namespace GafniTao

noncomputable section

theorem ten_pow_hundred_rpow_nine_tenths :
    (((10 : ℝ) ^ 100) ^ (9 / 10 : ℝ)) = (10 : ℝ) ^ 90 := by
  calc
    (((10 : ℝ) ^ 100) ^ (9 / 10 : ℝ)) =
        ((10 : ℝ) ^ (100 : ℝ)) ^ (9 / 10 : ℝ) := by
          exact congrArg (fun x : ℝ => x ^ (9 / 10 : ℝ))
            (Real.rpow_natCast 10 100).symm
    _ = (10 : ℝ) ^ ((100 : ℝ) * (9 / 10 : ℝ)) := by
      rw [Real.rpow_mul (by positivity)]
    _ = (10 : ℝ) ^ (90 : ℝ) := by norm_num
    _ = (10 : ℝ) ^ 90 := Real.rpow_natCast 10 90

theorem fifteen_mul_rpow_neg_le_fordTinyRemainder
    {sigma t : ℝ} (hsigma : 15 / 16 ≤ sigma)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    15 * t ^ (-sigma) ≤ fordTinyRemainder := by
  have htOne : 1 ≤ t := by
    have : (1 : ℝ) ≤ (10 : ℝ) ^ 100 := by norm_num
    exact this.trans ht
  have hExponent :
      t ^ (-sigma) ≤ t ^ (-(9 / 10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le htOne
    linarith
  have hBasePower :
      (10 : ℝ) ^ 90 ≤ t ^ (9 / 10 : ℝ) := by
    rw [← ten_pow_hundred_rpow_nine_tenths]
    exact Real.rpow_le_rpow (by positivity) ht (by norm_num)
  have hNegPower :
      t ^ (-(9 / 10 : ℝ)) ≤ ((10 : ℝ) ^ 90)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    exact inv_anti₀ (by positivity) hBasePower
  calc
    15 * t ^ (-sigma) ≤ 15 * t ^ (-(9 / 10 : ℝ)) := by gcongr
    _ ≤ 15 * ((10 : ℝ) ^ 90)⁻¹ := by gcongr
    _ ≤ fordTinyRemainder := by
      unfold fordTinyRemainder
      norm_num

theorem norm_riemannZeta_sub_fordFiniteApproximation_le_tiny
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) -
        fordHurwitzFiniteApproximation sigma 1 t‖ ≤ fordTinyRemainder := by
  have htThree : 3 ≤ t := by
    have : (3 : ℝ) ≤ (10 : ℝ) ^ 100 := by norm_num
    exact this.trans ht
  exact (norm_riemannZeta_sub_fordFiniteApproximation_le_fifteen
      (by linarith) hsigmaUpper htThree).trans
    (fifteen_mul_rpow_neg_le_fordTinyRemainder hsigmaLower ht)

#print axioms ten_pow_hundred_rpow_nine_tenths
#print axioms fifteen_mul_rpow_neg_le_fordTinyRemainder
#print axioms norm_riemannZeta_sub_fordFiniteApproximation_le_tiny

end

end GafniTao
