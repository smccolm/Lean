import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Expdb
open scoped NNReal
namespace TaoTrudgianYang2025.CubicJointCount

/-- The exact Trudgian--Yang input follows from the proved stronger refined
beta estimate, D(Bourgain), and Bourgain; no literature pair is postulated. -/
theorem exponentPair_trudgianYang_first :
    ExponentPair (4742/38463) (35731/51284) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  by_cases hlo : (α:ℝ)≤403/1000
  · have hh := exponentSumGrowthExponent_le_sargosD_bourgain
      (α:=α) (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,hlo]
  by_cases hhi : (α:ℝ)<3/7
  · have hh := exponentSumGrowthExponent_le_refined_bourgain
      (by linarith only [lt_of_not_ge hlo] : 2/5<(α:ℝ)) hhi
    apply hh.trans
    unfold exponentPairLine
    apply max_le <;> linarith only [lt_of_not_ge hlo,hhi]
  · have hh := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_bourgain α (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,le_of_not_gt hhi]

/-- The exact A-image used by the sixth public beta-table row. -/
theorem exponentPair_aTrudgianYang_first :
    ExponentPair (2371/43205) (280013/345640) := by
  have h := exponentPair_trudgianYang_first.aProcess
  norm_num at h
  exact h

/-- The sixth table row holds on the whole closed unit interval. -/
theorem exponentSumGrowthExponent_le_trudgianYang_sixthRow
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤ 2371/43205+52209*(α:ℝ)/69128 := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed
    exponentPair_aTrudgianYang_first α hα
  convert h using 1
  unfold exponentPairLine
  ring

#print axioms exponentPair_trudgianYang_first
#print axioms exponentPair_aTrudgianYang_first
#print axioms exponentSumGrowthExponent_le_trudgianYang_sixthRow
end TaoTrudgianYang2025.CubicJointCount
