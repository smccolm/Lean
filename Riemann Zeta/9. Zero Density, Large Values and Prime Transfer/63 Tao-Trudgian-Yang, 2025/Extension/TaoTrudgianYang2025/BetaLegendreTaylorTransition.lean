import TaoTrudgianYang2025.BetaExpandedAnchoring
import TaoTrudgianYang2025.BetaTaylorTransitionBudget

/-!
# Actual anchored Legendre consumer of moving Taylor-transition estimates

All smoothness and Taylor derivative budgets are derived from the original
model phase. The transition width may shrink arbitrarily. This is a local
endpoint-correction theorem, not yet the full global canonical extension.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem anchoredLegendreError_transition_remainder_uniformity
    {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
      ∀ w ∈ modelPhaseSlopeRange F, ∀ a ∈ modelPhaseSlopeRange F,
      ∀ x ∈ modelPhaseSlopeRange F, ∀ h s t : ℝ,
        0 < h → h ≤ 1 → |s| ≤ 1 → |x-a| ≤ h → ∀ n ≤ Q,
          |iteratedDeriv n (fun y =>
            Real.smoothTransition (s*y/h+t)*
              (anchoredLegendreError F σ w y-
                finiteTaylorPolynomial (anchoredLegendreError F σ w) Q a y)) x| ≤ C*δ := by
  obtain ⟨A,hA,hjets⟩ := anchoredLegendreError_expanded_finite_uniformity hσ (Q+1)
  obtain ⟨B,hB,htransition⟩ := smoothTransition_taylor_remainder_uniform_jets Q
  refine ⟨B*A,by nlinarith,?_⟩
  intro F δ hδ hpos hF w hw a ha x hx h s t hh hh₁ hs hdist n hn
  have hP : 1 ≤ legendreFiniteInputOrder (Q+1) := by
    simpa only [inversePhaseDerivativeExpression,inversePhaseOrder,zero_add] using
      legendreFiniteInputOrder_le (Nat.zero_le (Q+1))
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hseg : uIcc a x ⊆ modelPhaseSlopeRange F := by
    have ha' := ha
    have hx' := hx
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF₁] at ha' hx' ⊢
    intro y hy
    exact ⟨(lt_min ha'.1 hx'.1).trans_le hy.1,
      hy.2.trans_lt (max_lt ha'.2 hx'.2)⟩
  have hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) y := by
    intro y hy
    have hp : 0 < y := (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
      (modelPhaseSlopeRange_positive_window hσ hpos hF (hseg hy)).1
    exact anchoredLegendreError_contDiffAt hσ hδ hF₁ (hseg hy) hp
  have hb : ∀ y ∈ uIcc a x,
      |iteratedDeriv (Q+1) (anchoredLegendreError F σ w) y| ≤ A*δ :=
    fun y hy => hjets F δ hδ hpos hF w hw y (hseg hy) (Q+1) le_rfl
  have hc := htransition (anchoredLegendreError F σ w) a x h s t (A*δ)
    hh hh₁ hs hdist hf hb n hn
  exact hc.trans_eq (by ring)

end TaoTrudgianYang2025
