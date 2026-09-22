import TaoTrudgianYang2025.BetaClosedDuality

/-! The classical second-derivative exponent pair at the actual uniform
model-phase interface. This is a seed pair, not a proof of the full
dual-phase B transformation. -/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem isExponentPairEstimateNonAsymptotic_half_half :
    IsExponentPairEstimateNonAsymptotic ((1 : ℝ)/2) ((1 : ℝ)/2) := by
  intro ε hε σ hσ
  let δ := min (modelPhaseCurvatureLower σ) 1
  have hδ : 0 < δ := lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one
  let K := modelPhaseSumConstant σ
  have hK : 0 < K := modelPhaseSumConstant_pos hσ
  let C := max 1 (max (2*K) 3)
  have hC : 1 ≤ C := le_max_left _ _
  have hCK : 2*K ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCthree : 3 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ,hδ,1,le_rfl,C,hC,?_⟩
  intro T N F a b h
  have hT : 1 ≤ T := hC.trans h.threshold_le_param
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one h.one_le_scale
  have hspos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTp
  have hsone : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  have hsquare : (Real.sqrt T)^2 = T := Real.sq_sqrt hTp.le
  have hbound : ‖exponentialSumAt F T N a b‖ ≤ C*Real.sqrt T := by
    by_cases hscale : T ≤ N^2
    · have hf := norm_exponentialSumAt_le_secondDerivative hσ hT h.one_le_scale
        (le_rfl : δ ≤ min (modelPhaseCurvatureLower σ) 1)
        h.isApproximateModelPhase h.scale_le_start h.end_le_two_mul_scale hscale
      have hquot : N/Real.sqrt T ≤ Real.sqrt T :=
        (div_le_iff₀ hspos).2 (by nlinarith [h.scale_le_param])
      calc
        _ ≤ (2*K)*Real.sqrt T := by nlinarith
        _ ≤ C*Real.sqrt T := mul_le_mul_of_nonneg_right hCK hspos.le
    · have hNsqrt : N ≤ Real.sqrt T := by
        nlinarith
      have hf := norm_exponentialSumAt_le_add_one F T N a b
      calc
        _ ≤ 3*Real.sqrt T := by linarith [h.end_le_two_mul_scale]
        _ ≤ C*Real.sqrt T := mul_le_mul_of_nonneg_right hCthree hspos.le
  have hsbound : Real.sqrt T ≤ T^((1 : ℝ)/2+ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have heq : (T/N)^((1 : ℝ)/2+ε)*N^((1 : ℝ)/2+ε) =
      T^((1 : ℝ)/2+ε) := by
    rw [← Real.mul_rpow (div_nonneg hTp.le hNp.le) hNp.le,
      div_mul_cancel₀ T (ne_of_gt hNp)]
  calc
    _ ≤ C*T^((1 : ℝ)/2+ε) :=
      hbound.trans (mul_le_mul_of_nonneg_left hsbound (zero_le_one.trans hC))
    _ = C*(T/N)^((1 : ℝ)/2+ε)*N^((1 : ℝ)/2+ε) := by
      rw [mul_assoc,heq]

theorem exponentPair_half_half : ExponentPair ((1 : ℝ)/2) ((1 : ℝ)/2) :=
  ⟨by norm_num [InExponentPairTriangle],
    isExponentPairEstimate_iff_nonAsymptotic.mpr
      isExponentPairEstimateNonAsymptotic_half_half⟩

theorem exponentSumGrowthExponent_le_half {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ (1 : ℝ)/2 := by
  simpa [exponentPairLine] using
    exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_half_half α hα

theorem exponentSumGrowthExponent_le_min_self_half {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ min (α : ℝ) ((1 : ℝ)/2) :=
  le_min (exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_self α))
    (exponentSumGrowthExponent_le_half hα)

end TaoTrudgianYang2025
