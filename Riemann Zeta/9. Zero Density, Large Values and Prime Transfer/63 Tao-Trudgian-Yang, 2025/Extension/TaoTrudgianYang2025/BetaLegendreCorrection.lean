import TaoTrudgianYang2025.BetaCutoffEstimates

/-!
# Globally smooth corrections for actual Legendre phases

The correction uses the genuine anchored dual error on the cutoff support.
Its smoothness and all fixed-order uniform bounds are derived from the
original approximate-model hypothesis, not stipulated for an extension.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def legendreCutoffCorrection (χ F : ℝ → ℝ) (σ w v : ℝ) : ℝ :=
  χ v * anchoredLegendreError F σ w v

theorem anchoredLegendreError_contDiffAt
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) :
    ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v :=
  ((modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).sub
    (referenceModelPrimitive_contDiffAt σ⁻¹ hp)).sub contDiffAt_const

theorem anchoredLegendreError_iteratedDeriv
    {σ δ w v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hp : 0 < v) (n : ℕ) :
    iteratedDeriv (n+1) (anchoredLegendreError F σ w) v =
      iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
        iteratedDeriv n (modelPhase σ⁻¹) v := by
  have hN : ((n+1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
  have hG := (modelPhaseLegendreDual_contDiffAt hσ hδ hF hv).of_le hN
  have hR := (referenceModelPrimitive_contDiffAt σ⁻¹ hp).of_le hN
  unfold anchoredLegendreError
  rw [iteratedDeriv_fun_sub (hG.sub hR) contDiffAt_const,
    iteratedDeriv_fun_sub hG hR, referenceModelPrimitive_iteratedDeriv σ⁻¹ hp n]
  simp [iteratedDeriv_const]

theorem legendreCutoffCorrection_agrees {χ F : ℝ → ℝ} {σ w v : ℝ}
    (hχ : χ v = 1) :
    legendreCutoffCorrection χ F σ w v = anchoredLegendreError F σ w v := by
  simp only [legendreCutoffCorrection,hχ,one_mul]

theorem legendreCutoffCorrection_uniformity
    {σ c d w : ℝ} (hσ : 0 < σ)
    (hc : (2 : ℝ)^(-σ) < c) (hcd : c ≤ d) (hd : d < 1)
    (hw : w ∈ Icc c d) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Icc c d)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      Icc c d ⊆ modelPhaseSlopeRange F ∧
      ContDiff ℝ ∞ (legendreCutoffCorrection χ F σ w) ∧
        ∀ v : ℝ, ∀ n ≤ Q,
          |iteratedDeriv n (legendreCutoffCorrection χ F σ w) v| ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := smoothCutoff_uniform_derivative_bound hχ isCompact_Icc hs Q
  have hη : 0 < ε/C := div_pos hε hC
  obtain ⟨δ,hδ,hsmall,hall⟩ := modelPhaseLegendreDual_compact_anchored_uniformity
    hσ hc hcd hd Q hη
  refine ⟨δ,hδ,hsmall,?_⟩
  intro F hF
  have hP : 1 ≤ legendreFiniteInputOrder Q := by
    simpa only [inversePhaseDerivativeExpression,inversePhaseOrder,zero_add] using
      (legendreFiniteInputOrder_le (Nat.zero_le Q))
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hc₀ : 0 < c :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).trans hc
  have hH : ∀ v ∈ tsupport χ, ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v := by
    intro v hv
    exact anchoredLegendreError_contDiffAt hσ hsmall hF₁
      (hall F hF v (hs hv)).1 (hc₀.trans_le (hs hv).1)
  have he : ∀ v ∈ tsupport χ, ∀ j ≤ Q,
      |iteratedDeriv j (anchoredLegendreError F σ w) v| ≤ ε/C := by
    intro v hv j hj
    have hvI := hs hv
    have hdata := hall F hF v hvI
    cases j with
    | zero =>
      rw [iteratedDeriv_zero]
      have hdist : |v-w| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hvI.1,hvI.2,hw.1,hw.2]
      exact (hdata.2.2 w hw).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist hη.le)
    | succ n =>
      rw [anchoredLegendreError_iteratedDeriv hσ hsmall hF₁ hdata.1
        (hc₀.trans_le hvI.1) n]
      exact hdata.2.1 n (Nat.le_of_succ_le hj)
  refine ⟨fun v hv => (hall F hF v hv).1,smoothCutoff_mul_contDiff hχ hH,?_⟩
  intro v n hn
  have h := hbound (anchoredLegendreError F σ w) (ε/C) hη.le hH he v n hn
  simpa only [legendreCutoffCorrection,mul_div_cancel₀ _ hC.ne'] using h

end TaoTrudgianYang2025
