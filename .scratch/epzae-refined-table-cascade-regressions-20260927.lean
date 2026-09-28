import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Expdb
open scoped NNReal
namespace TaoTrudgianYang2025.CubicJointCount
/-- Exact public table row from a stronger proved analytic beta bound. -/
theorem exponentSumGrowthExponent_le_huxley_thirteenthRow
    {α : ℝ≥0} (hlo : 62831/155153 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 143/349) :
    exponentSumGrowthExponent α ≤ 569/2800+1053*(α:ℝ)/2800 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

/-- Exact public table row, including both endpoints, from the refined source. -/
theorem exponentSumGrowthExponent_le_huxley_fourteenthRow
    {α : ℝ≥0} (hlo : 143/349 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 263/638) :
    exponentSumGrowthExponent α ≤ 491/5530+1812*(α:ℝ)/2765 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

/-- Exact public table row, including both endpoints, from the refined source. -/
theorem exponentSumGrowthExponent_le_huxley_fifteenthRow
    {α : ℝ≥0} (hlo : 263/638 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 1673/4038) :
    exponentSumGrowthExponent α ≤ 113/1345+897*(α:ℝ)/1345 := by
  have h := exponentSumGrowthExponent_le_refined_bourgain
    (by linarith only [hlo] : 2/5<(α:ℝ)) (by linarith only [hhi] : (α:ℝ)<3/7)
  apply h.trans
  apply max_le <;> linarith only [hlo,hhi]

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
end TaoTrudgianYang2025.CubicJointCount

section RefinedTableCascadeRegression
open Expdb TaoTrudgianYang2025 TaoTrudgianYang2025.CubicJointCount
open scoped NNReal

example
    {α : ℝ≥0} (hlo : 62831/155153 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 143/349) :
    exponentSumGrowthExponent α ≤ 569/2800+1053*(α:ℝ)/2800 :=
  exponentSumGrowthExponent_le_huxley_thirteenthRow hlo hhi

example
    {α : ℝ≥0} (hlo : 143/349 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 263/638) :
    exponentSumGrowthExponent α ≤ 491/5530+1812*(α:ℝ)/2765 :=
  exponentSumGrowthExponent_le_huxley_fourteenthRow hlo hhi

example
    {α : ℝ≥0} (hlo : 263/638 ≤ (α:ℝ)) (hhi : (α:ℝ) ≤ 1673/4038) :
    exponentSumGrowthExponent α ≤ 113/1345+897*(α:ℝ)/1345 :=
  exponentSumGrowthExponent_le_huxley_fifteenthRow hlo hhi

example :
    ExponentPair (4742/38463) (35731/51284) :=
  exponentPair_trudgianYang_first

example :
    ExponentPair (2371/43205) (280013/345640) :=
  exponentPair_aTrudgianYang_first

example
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤ 2371/43205+52209*(α:ℝ)/69128 :=
  exponentSumGrowthExponent_le_trudgianYang_sixthRow hα

example : exponentSumGrowthExponent (62831/155153) ≤ (569/2800:ℝ)+(1053/2800)*(62831/155153) := by
  have h := exponentSumGrowthExponent_le_huxley_thirteenthRow (α:=(62831/155153:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (143/349) ≤ (569/2800:ℝ)+(1053/2800)*(143/349) := by
  have h := exponentSumGrowthExponent_le_huxley_thirteenthRow (α:=(143/349:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (143/349) ≤ (491/5530:ℝ)+(1812/2765)*(143/349) := by
  have h := exponentSumGrowthExponent_le_huxley_fourteenthRow (α:=(143/349:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (263/638) ≤ (491/5530:ℝ)+(1812/2765)*(263/638) := by
  have h := exponentSumGrowthExponent_le_huxley_fourteenthRow (α:=(263/638:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (263/638) ≤ (113/1345:ℝ)+(897/1345)*(263/638) := by
  have h := exponentSumGrowthExponent_le_huxley_fifteenthRow (α:=(263/638:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : exponentSumGrowthExponent (1673/4038) ≤ (113/1345:ℝ)+(897/1345)*(1673/4038) := by
  have h := exponentSumGrowthExponent_le_huxley_fifteenthRow (α:=(1673/4038:ℝ≥0)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end RefinedTableCascadeRegression
