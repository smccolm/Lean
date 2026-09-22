import TaoTrudgianYang2025.BetaLegendreCompact

/-!
# Anchored values of the actual Legendre phase

The original phase may contain an arbitrary additive constant. We remove
that constant by subtracting the dual/reference discrepancy at an anchor.
The value estimate is derived by mean value from the genuine first-derivative
error, uniformly along the entire compact interval.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def anchoredLegendreError (F : ℝ → ℝ) (σ w v : ℝ) : ℝ :=
  (modelPhaseLegendreDual F v - referenceModelPrimitive σ⁻¹ v) -
    (modelPhaseLegendreDual F w - referenceModelPrimitive σ⁻¹ w)

theorem modelPhaseLegendreDual_anchored_error
    {σ δ a b ε : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hJ : Icc a b ⊆ modelPhaseSlopeRange F)
    (ha : (2 : ℝ)^(-σ) < a)
    (he : ∀ v ∈ Icc a b,
      |deriv (modelPhaseLegendreDual F) v-v^(-σ⁻¹)| ≤ ε)
    {v w : ℝ} (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) :
    |anchoredLegendreError F σ w v| ≤ ε*|v-w| := by
  have hd : ∀ x ∈ Icc a b,
      HasDerivWithinAt
        (fun y => modelPhaseLegendreDual F y-referenceModelPrimitive σ⁻¹ y)
        (modelPhaseInverseSlope F x-x^(-σ⁻¹)) (Icc a b) x := by
    intro x hx
    have hp : 0 < x :=
      ((Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).trans ha).trans_le hx.1
    exact ((modelPhaseLegendreDual_hasDerivAt hσ hδ hF (hJ hx)).sub
      (referenceModelPrimitive_hasDerivAt σ⁻¹ hp)).hasDerivWithinAt
  have hb : ∀ x ∈ Icc a b, ‖modelPhaseInverseSlope F x-x^(-σ⁻¹)‖ ≤ ε := by
    intro x hx
    have h := he x hx
    rwa [deriv_modelPhaseLegendreDual hσ hδ hF (hJ hx)] at h
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc a b) hw hv

theorem modelPhaseLegendreDual_compact_anchored_uniformity
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      ∀ v ∈ Icc a b, v ∈ modelPhaseSlopeRange F ∧
        (∀ n ≤ Q, |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ ε) ∧
        ∀ w ∈ Icc a b, |anchoredLegendreError F σ w v| ≤ ε*|v-w| := by
  obtain ⟨δ,hd,hsmall,hall⟩ := modelPhaseLegendreDual_compact_uniformity
    hσ ha hab hb Q hε
  refine ⟨δ,hd,hsmall,?_⟩
  intro F hF v hv
  have hP : 1 ≤ legendreFiniteInputOrder Q := by
    simpa only [inversePhaseDerivativeExpression, inversePhaseOrder, zero_add] using
      (legendreFiniteInputOrder_le (Nat.zero_le Q))
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hJ : Icc a b ⊆ modelPhaseSlopeRange F := fun x hx => (hall F hF x hx).1
  have he : ∀ x ∈ Icc a b, |deriv (modelPhaseLegendreDual F) x-x^(-σ⁻¹)| ≤ ε := by
    intro x hx
    simpa only [Nat.zero_add, iteratedDeriv_one, iteratedDeriv_zero, modelPhase] using
      (hall F hF x hx).2 0 (Nat.zero_le Q)
  refine ⟨(hall F hF v hv).1,(hall F hF v hv).2,?_⟩
  intro w hw
  exact modelPhaseLegendreDual_anchored_error hσ hsmall hF₁ hJ ha he hv hw

end TaoTrudgianYang2025
