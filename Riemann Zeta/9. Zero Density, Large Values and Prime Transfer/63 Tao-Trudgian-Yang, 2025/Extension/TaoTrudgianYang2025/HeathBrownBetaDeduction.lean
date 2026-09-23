import TaoTrudgianYang2025.HeathBrownSourceEstimate

/-!
# The complete beta deduction from Heath--Brown's source derivative theorem

The physical model-sum estimate supplies every original setup. The
positive scale exponent supplies N >= 1; empty intervals are included.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem isExponentSumBoundNonAsymptotic_heathBrown_of_derivative
    (hHB : GafniTao.HeathBrownKthDerivativeTheorem)
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0} (hα : 0 < (α : ℝ)) :
    IsExponentSumBoundNonAsymptotic α (heathBrownBetaBound k α) := by
  intro ε hε σ hσ
  obtain ⟨η,d,hη,hη₁,hd,_,hbudget⟩ := heathBrown_epsilon_budget hα.le hε
  obtain ⟨δ₀,hδ₀,P,hP,C,hC,hsource⟩ :=
    source_exponentialSum_heathBrown_bound_of_derivative hHB hk hσ hη
  let δ := min δ₀ (min d ((α : ℝ)/2))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hd (by positivity))
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδd : δ ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ (α : ℝ)/2 := (min_le_right _ _).trans (min_le_right _ _)
  let K := max 1 (3*C)
  have hK : 1 ≤ K := le_max_left _ _
  have hCK : 3*C ≤ K := le_max_right _ _
  refine ⟨δ,hδ,P,hP,K,hK,?_⟩
  intro T N F a b hs
  have hT : 1 ≤ T := hK.trans hs.threshold_le_param
  have hTpos := zero_lt_one.trans_le hT
  have hN : 1 ≤ N := (Real.one_le_rpow hT
    (show 0 ≤ (α : ℝ)-δ by linarith)).trans hs.rpow_sub_le_scale
  have hNpos := zero_lt_one.trans_le hN
  have hF := approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδ₀le
  have hwindow := heathBrownPowerMajorant_window hk hT hNpos hδ.le hη.le hη₁
    hs.scale_le_rpow_add
  have hLoss : ((α : ℝ)+1)*η+2*δ ≤ ε := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hT
    (show heathBrownBetaBound k α+((α : ℝ)+1)*η+2*δ ≤
      heathBrownBetaBound k α+ε by linarith)
  have hmain : heathBrownPowerMajorant k η T N ≤ 3*T^(heathBrownBetaBound k α+ε) :=
    hwindow.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  by_cases hab : a ≤ b
  · have he : a+(b-a) = b := Nat.add_sub_of_le hab
    have hb : (((a+(b-a)) : ℕ) : ℝ) ≤ 2*N := by
      rw [he]
      exact hs.end_le_two_mul_scale
    have hsum := hsource F T N a (b-a) hTpos hN hs.scale_le_start hb hF
    rw [he] at hsum
    calc
      ‖exponentialSumAt F T N a b‖ ≤ C*heathBrownPowerMajorant k η T N := hsum
      _ ≤ C*(3*T^(heathBrownBetaBound k α+ε)) :=
        mul_le_mul_of_nonneg_left hmain (zero_le_one.trans hC)
      _ = (3*C)*T^(heathBrownBetaBound k α+ε) := by ring
      _ ≤ K*T^(heathBrownBetaBound k α+ε) :=
        mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hTpos.le _)
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp only [exponentialSumAt,hempty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg hTpos.le _)

theorem exponentSumGrowthExponent_le_heathBrown_of_derivative
    (hHB : GafniTao.HeathBrownKthDerivativeTheorem)
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0} (hα : 0 < (α : ℝ)) :
    exponentSumGrowthExponent α ≤ heathBrownBetaBound k α :=
  exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (isExponentSumBoundNonAsymptotic_heathBrown_of_derivative hHB hk hα)

end TaoTrudgianYang2025
