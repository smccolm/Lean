import TaoTrudgianYang2025.BetaCoherentLowerBound
import TaoTrudgianYang2025.BetaReflectionEnvelope

/-!
# Exact beta reflection on the whole closed unit interval

The source-sum reflection estimate and independent coherent lower bound
remove the nonnegative envelope. Applying the one-sided result in both
directions gives the paper's exact beta-reflect identity, endpoints included.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem isExponentSumBoundNonAsymptotic_reflect
    {α : ℝ≥0} {β : ℝ} (hα : (α : ℝ) ≤ 1)
    (hβ : IsExponentSumBoundNonAsymptotic α β) :
    IsExponentSumBoundNonAsymptotic (1-α) (β+1/2-(α : ℝ)) := by
  apply isExponentSumBoundNonAsymptotic_reflect_nonnegative hα hβ
  linarith [alpha_sub_half_le_of_exponentSumBoundNonAsymptotic hα hβ]

theorem exponentSumGrowthExponent_reflect_le
    {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent (1-α) ≤
      exponentSumGrowthExponent α+1/2-(α : ℝ) :=
  exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_reflect hα
      (exponentSumGrowthExponent_le_iff_nonAsymptotic.mp le_rfl))

theorem exponentSumGrowthExponent_reflection
    {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent (1-α) =
      1/2-(α : ℝ)+exponentSumGrowthExponent α := by
  have hαNN : α ≤ 1 := by exact_mod_cast hα
  have hcoe : ((1-α : ℝ≥0) : ℝ) = 1-(α : ℝ) := NNReal.coe_sub hαNN
  have hcomp : ((1-α : ℝ≥0) : ℝ) ≤ 1 := by
    rw [hcoe]
    linarith [α.coe_nonneg]
  have hcompNN : (1-α : ℝ≥0) ≤ 1 := by exact_mod_cast hcomp
  have hdouble : (1-(1-α) : ℝ≥0) = α := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hcompNN,hcoe]
    norm_num
  have hforward := exponentSumGrowthExponent_reflect_le hα
  have hbackward := exponentSumGrowthExponent_reflect_le hcomp
  rw [hdouble,hcoe] at hbackward
  linarith

end TaoTrudgianYang2025
