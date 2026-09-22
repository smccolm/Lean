import TaoTrudgianYang2025.BetaExpandedAllOrders
import TaoTrudgianYang2025.BetaLegendreCorrection

/-!
# Anchored dual errors on the whole moving slope image

The actual image is convex. Its fixed positive compact envelope gives a
uniform value estimate from the first derivative, and a single finite
original-model order controls every requested anchored derivative.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem modelPhaseLegendreDual_expanded_anchored_bound
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ 1 δ →
      ∀ v ∈ modelPhaseSlopeRange F, ∀ w ∈ modelPhaseSlopeRange F,
        |anchoredLegendreError F σ w v| ≤ C*δ := by
  obtain ⟨A,hA,hbound⟩ := modelPhaseInverseSlope_expanded_model_error hσ
  refine ⟨2*A+1,by linarith,?_⟩
  intro F δ hδ hpos hF v hv w hw
  have hd := approximateModelPhase_tolerance_nonneg hF
  have hlo : 0 < (2 : ℝ)^(-σ)/2 := by positivity
  have hconv : Convex ℝ (modelPhaseSlopeRange F) := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    exact convex_Ioo _ _
  have hj : ∀ x ∈ modelPhaseSlopeRange F,
      HasDerivWithinAt
        (fun y => modelPhaseLegendreDual F y-referenceModelPrimitive σ⁻¹ y)
        (modelPhaseInverseSlope F x-x^(-σ⁻¹)) (modelPhaseSlopeRange F) x := by
    intro x hx
    have hp : 0 < x := hlo.trans_le (modelPhaseSlopeRange_positive_window hσ hpos hF hx).1
    exact ((modelPhaseLegendreDual_hasDerivAt hσ hδ hF hx).sub
      (referenceModelPrimitive_hasDerivAt σ⁻¹ hp)).hasDerivWithinAt
  have he : ∀ x ∈ modelPhaseSlopeRange F, ‖modelPhaseInverseSlope F x-x^(-σ⁻¹)‖ ≤ A*δ := by
    intro x hx
    exact hbound F δ 1 hpos hF x hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hj he hconv hw hv
  have hV := modelPhaseSlopeRange_positive_window hσ hpos hF hv
  have hW := modelPhaseSlopeRange_positive_window hσ hpos hF hw
  have hdist : |v-w| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hV.1,hV.2,hW.1,hW.2]
  have h' : |anchoredLegendreError F σ w v| ≤ A*δ*|v-w| := h
  exact h'.trans ((mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (zero_le_one.trans hA) hd)).trans (by nlinarith))

theorem anchoredLegendreError_expanded_finite_uniformity
    {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      ∀ w ∈ modelPhaseSlopeRange F, ∀ v ∈ modelPhaseSlopeRange F,
        ∀ n ≤ Q, |iteratedDeriv n (anchoredLegendreError F σ w) v| ≤ C*δ := by
  obtain ⟨A,hA,hvalue⟩ := modelPhaseLegendreDual_expanded_anchored_bound hσ
  choose B hB hderiv using fun n => modelPhaseLegendreDual_expanded_allOrder_uniformity hσ n
  let S := ∑ n ∈ Finset.range (Q+1), B n
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ => zero_le_one.trans (hB n)
  refine ⟨A+S,by linarith,?_⟩
  intro F δ hδ hpos hF w hw v hv n hn
  have hd := approximateModelPhase_tolerance_nonneg hF
  have hP : 1 ≤ legendreFiniteInputOrder Q := by
    simpa only [inversePhaseDerivativeExpression,inversePhaseOrder,zero_add] using
      legendreFiniteInputOrder_le (Nat.zero_le Q)
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  cases n with
  | zero =>
      rw [iteratedDeriv_zero]
      exact (hvalue F δ hδ hpos hF₁ v hv w hw).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)
  | succ n =>
      have hnQ : n ≤ Q := Nat.le_of_succ_le hn
      have hsmall := approximateModelPhase_mono hF (legendreFiniteInputOrder_le hnQ) le_rfl
      have hp : 0 < v := (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
        (modelPhaseSlopeRange_positive_window hσ hpos hF hv).1
      rw [anchoredLegendreError_iteratedDeriv hσ hδ hF₁ hv hp n]
      have hsum : B n ≤ S := Finset.single_le_sum
        (fun k _ => zero_le_one.trans (hB k)) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnQ))
      exact (hderiv n F δ hδ hpos hsmall v hv).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)

end TaoTrudgianYang2025
