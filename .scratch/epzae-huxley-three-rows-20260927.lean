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

#print axioms exponentSumGrowthExponent_le_huxley_thirteenthRow
#print axioms exponentSumGrowthExponent_le_huxley_fourteenthRow
#print axioms exponentSumGrowthExponent_le_huxley_fifteenthRow
end TaoTrudgianYang2025.CubicJointCount
