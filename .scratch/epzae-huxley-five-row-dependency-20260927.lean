import TaoTrudgianYang2025.BourgainOptimizedTransfer
open Expdb TaoTrudgianYang2025 TaoTrudgianYang2025.CubicJointCount
open scoped NNReal
namespace HuxleyFiveRowDependencyTest

/- CONDITIONAL dependency test only. These are the five still-unproved
analytic inputs, on their exact public closed source intervals.
No theorem below claims that any of these inputs has been proved. -/
variable
    (h7 : ∀ (α : ℝ≥0), 861996/2811205 ≤ (α:ℝ) → (α:ℝ) ≤ 87/275 →
      exponentSumGrowthExponent α ≤ 13/146+47*(α:ℝ)/73)
    (h8 : ∀ (α : ℝ≥0), 87/275 ≤ (α:ℝ) → (α:ℝ) ≤ 423/1295 →
      exponentSumGrowthExponent α ≤ 11/244+191*(α:ℝ)/244)
    (h9 : ∀ (α : ℝ≥0), 423/1295 ≤ (α:ℝ) → (α:ℝ) ≤ 227/601 →
      exponentSumGrowthExponent α ≤ 89/1282+454*(α:ℝ)/641)
    (h10 : ∀ (α : ℝ≥0), 227/601 ≤ (α:ℝ) → (α:ℝ) ≤ 12/31 →
      exponentSumGrowthExponent α ≤ 29/280+173*(α:ℝ)/280)
    (h11 : ∀ (α : ℝ≥0), 12/31 ≤ (α:ℝ) → (α:ℝ) ≤ 1508/3825 →
      exponentSumGrowthExponent α ≤ 1/32+103*(α:ℝ)/128)

include h7 h8 h9 h10 h11

theorem first_public_pair : ExponentPair (89/1282) (997/1282) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := h7 α (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := h8 α (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := h9 α (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := h10 α (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := h11 α (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem second_public_pair : ExponentPair (652397/9713986) (7599781/9713986) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := h7 α (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := h8 α (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := h9 α (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := h10 α (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := h11 α (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem second_density_input : ExponentPair (391/4595) (3461/4595) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := h7 α (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := h8 α (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := h9 α (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := h10 α (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := h11 α (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

theorem third_density_input : ExponentPair (2779/38033) (58699/76066) := by
  apply exponentPair_of_beta_bound_half
    (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases h0 : (α:ℝ) ≤ 861996/2811205
  · have h := exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  by_cases hr0 : (α:ℝ) ≤ 87/275
  · have h := h7 α (by linarith only [lt_of_not_ge h0]) hr0
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge h0,hr0]
  by_cases hr1 : (α:ℝ) ≤ 423/1295
  · have h := h8 α (by linarith only [lt_of_not_ge hr0]) hr1
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr0,hr1]
  by_cases hr2 : (α:ℝ) ≤ 227/601
  · have h := h9 α (by linarith only [lt_of_not_ge hr1]) hr2
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr1,hr2]
  by_cases hr3 : (α:ℝ) ≤ 12/31
  · have h := h10 α (by linarith only [lt_of_not_ge hr2]) hr3
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr2,hr3]
  by_cases hr4 : (α:ℝ) ≤ 1508/3825
  · have h := h11 α (by linarith only [lt_of_not_ge hr3]) hr4
    unfold exponentPairLine
    linarith only [h,lt_of_not_ge hr3,hr4]
  have h := exponentSumGrowthExponent_le_sargosD_bourgain (α:=α) hα
  unfold exponentPairLine at h ⊢
  linarith only [h,lt_of_not_ge hr4]

#print axioms first_public_pair
#print axioms second_public_pair
#print axioms second_density_input
#print axioms third_density_input
end HuxleyFiveRowDependencyTest
