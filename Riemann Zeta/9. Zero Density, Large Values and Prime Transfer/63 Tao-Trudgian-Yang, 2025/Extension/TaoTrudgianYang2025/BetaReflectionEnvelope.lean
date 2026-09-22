import TaoTrudgianYang2025.BetaSourceReflectionEstimate

/-!
# Nonasymptotic beta reflection with the necessary nonnegative envelope

The complete source estimate gives the reflected exponent after taking
its maximum with zero. The exact reflected exponent is obtained whenever
it is nonnegative. No lower bound needed to remove that maximum is
silently assumed in the unconditional statement.
-/

noncomputable section

open Set Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem isExponentSumBoundNonAsymptotic_reflect_max
    {α : ℝ≥0} {β : ℝ} (hα : (α : ℝ) ≤ 1)
    (hβ : IsExponentSumBoundNonAsymptotic α β) :
    IsExponentSumBoundNonAsymptotic (1-α) (max 0 (β+1/2-(α : ℝ))) := by
  have hβnonneg : 0 ≤ β :=
    (isExponentSumBound_exponentSumGrowthExponent α).nonneg.trans
      (exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr hβ)
  have hrefl : ((1-α : ℝ≥0) : ℝ) = 1-(α : ℝ) := by
    exact NNReal.coe_sub (by exact_mod_cast hα)
  intro ε hε σ hσ
  obtain ⟨d,hd,_hsmall,_hpos,P,hP,C,hC,hsource⟩ :=
    sourceExponentialSum_reflection_estimate hβ hσ (show 0 < ε/3 by positivity)
  let δ := min d (ε/3)
  have hδ : 0 < δ := lt_min hd (by positivity)
  have hδd : δ ≤ d := min_le_left _ _
  have hδε : δ ≤ ε/3 := min_le_right _ _
  have hC₃ : 1 ≤ 3*C := by linarith
  refine ⟨δ,hδ,P,le_trans (by norm_num) hP,3*C,hC₃,?_⟩
  intro T N F a b hs
  have hT₁ : 1 ≤ T := hC₃.trans hs.threshold_le_param
  have hT : 0 < T := zero_lt_one.trans_le hT₁
  have hγ : 0 ≤ max 0 (β+1/2-(α : ℝ)) := le_max_left _ _
  have htarget : 1 ≤ T^(max 0 (β+1/2-(α : ℝ))+ε) :=
    Real.one_le_rpow hT₁ (by linarith)
  by_cases hN : 1 ≤ N
  · have hlow : T^(1-(α : ℝ)-d) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le hT₁
        (by linarith : 1-(α : ℝ)-d ≤ 1-(α : ℝ)-δ)).trans
        (by simpa only [hrefl] using hs.rpow_sub_le_scale)
    have hhigh : N ≤ T^(1-(α : ℝ)+d) :=
      (show N ≤ T^(1-(α : ℝ)+δ) by
        simpa only [hrefl] using hs.scale_le_rpow_add).trans
          (Real.rpow_le_rpow_of_exponent_le hT₁
            (by linarith : 1-(α : ℝ)+δ ≤ 1-(α : ℝ)+d))
    have hbnd := hsource T N F a b
      (show C ≤ T by linarith [hs.threshold_le_param]) hN
      hs.scale_le_start hs.end_le_two_mul_scale hlow hhigh
      (approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδd)
    have hX : N/Real.sqrt T ≤ T^(1/2-(α : ℝ)+δ) := by
      calc
        N/Real.sqrt T ≤ T^(1-(α : ℝ)+δ)/Real.sqrt T :=
          div_le_div_of_nonneg_right
            (by simpa only [hrefl] using hs.scale_le_rpow_add) (by positivity)
        _ = T^(1/2-(α : ℝ)+δ) := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_sub hT]
          congr 1
          ring
    have hmain : (N/Real.sqrt T)*T^(β+ε/3) ≤
        T^(max 0 (β+1/2-(α : ℝ))+ε) := by
      calc
        _ ≤ T^(1/2-(α : ℝ)+δ)*T^(β+ε/3) :=
          mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hT.le _)
        _ = T^((1/2-(α : ℝ)+δ)+(β+ε/3)) := (Real.rpow_add hT _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT₁ (by
          linarith [le_max_right (0 : ℝ) (β+1/2-(α : ℝ))])
    have hfirst : N/Real.sqrt T ≤ T^(max 0 (β+1/2-(α : ℝ))+ε) :=
      hX.trans (Real.rpow_le_rpow_of_exponent_le hT₁ (by
        linarith [le_max_right (0 : ℝ) (β+1/2-(α : ℝ))]))
    have hsecond : T^(ε/3) ≤ T^(max 0 (β+1/2-(α : ℝ))+ε) :=
      Real.rpow_le_rpow_of_exponent_le hT₁ (by linarith)
    apply hbnd.trans
    nlinarith
  · have hbsmall : b < 2 := by
      have hbReal : (b : ℝ) < 2 := by linarith [hs.end_le_two_mul_scale]
      exact_mod_cast hbReal
    have hcard : (Finset.Icc a b).card ≤ 2 := by
      rw [Nat.card_Icc]
      omega
    have hnorm := (norm_exponentialSumAt_le_card F T N a b).trans
      (show ((Finset.Icc a b).card : ℝ) ≤ 2 by exact_mod_cast hcard)
    apply hnorm.trans
    nlinarith

theorem isExponentSumBoundNonAsymptotic_reflect_nonnegative
    {α : ℝ≥0} {β : ℝ} (hα : (α : ℝ) ≤ 1)
    (hβ : IsExponentSumBoundNonAsymptotic α β)
    (hreflect : 0 ≤ β+1/2-(α : ℝ)) :
    IsExponentSumBoundNonAsymptotic (1-α) (β+1/2-(α : ℝ)) := by
  simpa only [max_eq_right hreflect] using
    isExponentSumBoundNonAsymptotic_reflect_max hα hβ

theorem exponentSumGrowthExponent_reflect_le_max
    {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent (1-α) ≤
      max 0 (exponentSumGrowthExponent α+1/2-(α : ℝ)) :=
  exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_reflect_max hα
      (exponentSumGrowthExponent_le_iff_nonAsymptotic.mp le_rfl))

end TaoTrudgianYang2025
