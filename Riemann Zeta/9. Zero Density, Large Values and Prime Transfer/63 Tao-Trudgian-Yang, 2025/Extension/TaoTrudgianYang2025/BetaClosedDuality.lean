import TaoTrudgianYang2025.BetaModelSumBound

/-! The forward duality endpoint and the exact two-way beta criterion on
the full closed unit interval. The separate beta reflection identity is
not asserted by this module. -/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem exponentSumGrowthExponent_zero :
    exponentSumGrowthExponent 0 = 0 := by
  apply le_antisymm
  · exact exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_self 0)
  · exact (isExponentSumBound_exponentSumGrowthExponent 0).nonneg

theorem exponentSumGrowthExponent_one_le_half :
    exponentSumGrowthExponent 1 ≤ (1 : ℝ)/2 := by
  rw [exponentSumGrowthExponent_le_iff_nonAsymptotic]
  intro ε hε σ hσ
  let δ := min (min (modelPhaseCurvatureLower σ) 1) (min ((1 : ℝ)/2) ε)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
      (lt_min (by norm_num) hε)
  have hδphase : δ ≤ min (modelPhaseCurvatureLower σ) 1 := min_le_left _ _
  have hδhalf : δ ≤ (1 : ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  let K := modelPhaseSumConstant σ
  have hK : 0 < K := modelPhaseSumConstant_pos hσ
  let C := max 1 (2*K)
  refine ⟨δ,hδpos,1,le_rfl,C,le_max_left _ _,?_⟩
  intro T N F a b h
  have hT : 1 ≤ T := (le_max_left _ _).trans h.threshold_le_param
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNlow : Real.sqrt T ≤ N := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le hT (by norm_num; linarith : (1 : ℝ)/2 ≤
      (↑(1 : ℝ≥0) : ℝ)-δ)).trans h.rpow_sub_le_scale
  have hN : 1 ≤ N := (show 1 ≤ Real.sqrt T by
    simpa using Real.sqrt_le_sqrt hT).trans hNlow
  have hscale : T ≤ N^2 := by
    nlinarith [Real.sq_sqrt hTpos.le,Real.sqrt_nonneg T]
  have hfinite := norm_exponentialSumAt_le_secondDerivative hσ hT hN hδphase
    h.isApproximateModelPhase h.scale_le_start h.end_le_two_mul_scale hscale
  have hsqrtpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsqrtBound : Real.sqrt T ≤ T^((1 : ℝ)/2+ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hquotBound : N/Real.sqrt T ≤ T^((1 : ℝ)/2+ε) := by
    calc
      N/Real.sqrt T ≤ T^(1+δ)/Real.sqrt T :=
        div_le_div_of_nonneg_right h.scale_le_rpow_add hsqrtpos.le
      _ = T^((1 : ℝ)/2+δ) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_sub hTpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    _ ≤ K*(Real.sqrt T+N/Real.sqrt T) := hfinite
    _ ≤ (2*K)*T^((1 : ℝ)/2+ε) := by nlinarith
    _ ≤ C*T^((1 : ℝ)/2+ε) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hTpos.le _)

theorem exponentSumGrowthExponent_le_exponentPairLine_closed
    {k l : ℝ} (hkl : ExponentPair k l) (α : ℝ≥0)
    (hα : (α : ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ exponentPairLine k l α := by
  rcases lt_or_eq_of_le hα with hlt | heq
  · exact exponentSumGrowthExponent_le_exponentPairLine hkl α hlt
  · have hαone : α = 1 := NNReal.coe_injective heq
    rw [hαone]
    have hl : (1 : ℝ)/2 ≤ l := hkl.inTriangle.2.2.1
    have hline : exponentPairLine k l 1 = l := by
      unfold exponentPairLine
      ring
    simpa only [NNReal.coe_one,hline] using
      exponentSumGrowthExponent_one_le_half.trans hl

theorem exponentPair_iff_beta_bound {k l : ℝ}
    (htri : InExponentPairTriangle k l) :
    ExponentPair k l ↔
      ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
        exponentSumGrowthExponent α ≤ exponentPairLine k l α := by
  exact ⟨fun h α hα => exponentSumGrowthExponent_le_exponentPairLine_closed h α hα,
    exponentPair_of_beta_bound htri⟩

end TaoTrudgianYang2025
