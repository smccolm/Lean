import TaoTrudgianYang2025.BetaExpandedJetBounds

/-!
# Uniform all-order inverse and Legendre errors on the full actual image

Every finite expression is applied to the genuine inverse jet and the
proved positive-axis reference jet. No fixed strict-interior reference
window is assumed.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem inversePhaseEval_modelPhaseInverseJet_expanded_error
    {σ : ℝ} (hσ : 0 < σ) (e : InversePhaseExpression) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ) (P : ℕ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      1 ≤ P → IsApproximateModelPhaseFunction F σ P δ →
      inversePhaseOrder e ≤ P → ∀ v ∈ modelPhaseSlopeRange F,
        |inversePhaseEval e (modelPhaseInverseJet F v)-
          inversePhaseEval e (expandedReferenceInverseJet σ v)| ≤ C*δ := by
  obtain ⟨R,hR,hreference⟩ := expandedReferenceInverseJet_uniform_bound hσ (inversePhaseOrder e)
  choose E hE herror using fun j => modelPhaseInverseJet_expanded_reference_error hσ j
  let S := ∑ j ∈ Finset.range (inversePhaseOrder e+1), E j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => zero_le_one.trans (hE j)
  let B := R+inverseJetMagnitudeBudget σ (inversePhaseOrder e)
  have hM := inverseJetMagnitudeBudget_nonneg hσ (inversePhaseOrder e)
  have hB : 0 ≤ B := add_nonneg (zero_le_one.trans hR) hM
  have hsen := inversePhaseSensitivity_nonneg e hB
  refine ⟨1+inversePhaseSensitivity e B*S,by nlinarith,?_⟩
  intro F δ P hδ hpos hP hF heP v hv
  have hd := approximateModelPhase_tolerance_nonneg hF
  have hx : ∀ j ≤ inversePhaseOrder e, |modelPhaseInverseJet F v j| ≤ B := by
    intro j hj
    have h := (modelPhaseInverseJet_abs_le hσ hδ hP hF hv j (hj.trans heP)).trans
      (inverseJetMagnitude_le_budget hσ hj)
    exact h.trans (by dsimp [B]; linarith)
  have hy : ∀ j ≤ inversePhaseOrder e, |expandedReferenceInverseJet σ v j| ≤ B := by
    intro j hj
    exact (hreference v (modelPhaseSlopeRange_positive_window hσ hpos hF hv) j hj).trans
      (by dsimp [B]; linarith)
  have he : ∀ j ≤ inversePhaseOrder e,
      |modelPhaseInverseJet F v j-expandedReferenceInverseJet σ v j| ≤ S*δ := by
    intro j hj
    have h := herror j F δ P hδ hpos hP hF (hj.trans heP) v hv
    have hsum : E j ≤ S := Finset.single_le_sum
      (fun k _ => zero_le_one.trans (hE k)) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact h.trans (mul_le_mul_of_nonneg_right hsum hd)
  have h := inversePhaseEval_difference_le e hB hx hy he
  apply h.trans
  nlinarith

theorem modelPhaseInverseSlope_expanded_allOrder_uniformity
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ
        (inversePhaseOrder (inversePhaseDerivativeExpression n)+1) δ →
      ∀ v ∈ modelPhaseSlopeRange F,
        |iteratedDeriv n (modelPhaseInverseSlope F) v-
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ C*δ := by
  obtain ⟨C,hC,hbound⟩ := inversePhaseEval_modelPhaseInverseJet_expanded_error hσ
    (inversePhaseDerivativeExpression n)
  refine ⟨C,hC,?_⟩
  intro F δ hδ hpos hF v hv
  have hw := modelPhaseSlopeRange_positive_window hσ hpos hF hv
  have hvpos : 0 < v := (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le hw.1
  have hP : 1 ≤ inversePhaseOrder (inversePhaseDerivativeExpression n)+1 := by omega
  rw [iteratedDeriv_modelPhaseInverseSlope_formula hσ hδ
    (approximateModelPhase_mono hF hP le_rfl) hv n,
    iteratedDeriv_modelPhase_expanded_inverseJet_formula hσ hvpos n]
  exact hbound F δ _ hδ hpos hP hF (by omega) v hv

theorem modelPhaseLegendreDual_expanded_allOrder_uniformity
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ
        (inversePhaseOrder (inversePhaseDerivativeExpression n)+1) δ →
      ∀ v ∈ modelPhaseSlopeRange F,
        |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v-
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ C*δ := by
  obtain ⟨C,hC,hbound⟩ := inversePhaseEval_modelPhaseInverseJet_expanded_error hσ
    (inversePhaseDerivativeExpression n)
  refine ⟨C,hC,?_⟩
  intro F δ hδ hpos hF v hv
  have hw := modelPhaseSlopeRange_positive_window hσ hpos hF hv
  have hvpos : 0 < v := (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le hw.1
  have hP : 1 ≤ inversePhaseOrder (inversePhaseDerivativeExpression n)+1 := by omega
  rw [iteratedDeriv_modelPhaseLegendreDual_formula hσ hδ
    (approximateModelPhase_mono hF hP le_rfl) hv n,
    iteratedDeriv_modelPhase_expanded_inverseJet_formula hσ hvpos n]
  exact hbound F δ _ hδ hpos hP hF (by omega) v hv

end TaoTrudgianYang2025
