import GafniTao.FordRiemannDadaroRemainder
import GafniTao.FordDadaroTinyRemainder

/-!
# Large-height absorption for the ordinary-zeta Dadaro remainder

The explicit factor `30` is still absorbed by Ford's `10^-80` remainder at
`t ≥ 10^100` and `sigma ≥ 15/16`.
-/

namespace GafniTao

noncomputable section

theorem thirty_mul_rpow_neg_le_fordTinyRemainder
    {sigma t : ℝ} (hsigma : 15 / 16 ≤ sigma)
    (ht : (10 : ℝ) ^ 100 ≤ t) :
    30 * t ^ (-sigma) ≤ fordTinyRemainder := by
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
    30 * t ^ (-sigma) ≤ 30 * t ^ (-(9 / 10 : ℝ)) := by gcongr
    _ ≤ 30 * ((10 : ℝ) ^ 90)⁻¹ := by gcongr
    _ ≤ fordTinyRemainder := by
      unfold fordTinyRemainder
      norm_num

theorem norm_riemannZeta_sub_fordPartialSum_le_tiny
    {sigma t : ℝ} (hsigmaLower : 15 / 16 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) (ht : (10 : ℝ) ^ 100 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) -
        (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℂ) ^ (-fordComplexHeight sigma t))‖ ≤
      fordTinyRemainder := by
  have htThree : 3 ≤ t := by
    have : (3 : ℝ) ≤ (10 : ℝ) ^ 100 := by norm_num
    exact this.trans ht
  exact (norm_riemannZeta_sub_fordPartialSum_le_thirty
      (by linarith) hsigmaUpper htThree).trans
    (thirty_mul_rpow_neg_le_fordTinyRemainder hsigmaLower ht)

#print axioms thirty_mul_rpow_neg_le_fordTinyRemainder
#print axioms norm_riemannZeta_sub_fordPartialSum_le_tiny

end

end GafniTao
