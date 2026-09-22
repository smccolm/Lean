import TaoTrudgianYang2025.BetaExpandedEndpointGeometry

/-!
# A genuine globally smooth moving-image Legendre extension

The extension agrees with the anchored actual dual error on the retained
plateau. Its derivatives on the fixed observation window [0,4] are
O(delta), uniformly before the original phase and shrinking buffer width.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseTaylorExtension (F : ℝ → ℝ) (σ : ℝ) (Q : ℕ) (w h : ℝ) : ℝ → ℝ :=
  taylorPastedExtension (anchoredLegendreError F σ w) Q
    (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) h

theorem modelPhaseTaylorExtension_uniformity
    {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+1)) δ →
      ∀ w ∈ modelPhaseSlopeRange F, ∀ h : ℝ,
        0 < h → h ≤ 1 →
        modelPhaseClosedSlope F 2+4*h < modelPhaseClosedSlope F 1 →
        ContDiff ℝ ∞ (modelPhaseTaylorExtension F σ Q w h) ∧
        (∀ v ∈ Icc (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h),
          modelPhaseTaylorExtension F σ Q w h v = anchoredLegendreError F σ w v) ∧
        ∀ v ∈ Icc (0 : ℝ) 4, ∀ n ≤ Q,
          |iteratedDeriv n (modelPhaseTaylorExtension F σ Q w h) v| ≤ C*δ := by
  obtain ⟨A,hA,hjets⟩ := anchoredLegendreError_expanded_finite_uniformity hσ (Q+1)
  obtain ⟨B,hB,hpaste⟩ := taylorPastedExtension_uniform_jets Q (D := 4) (by norm_num)
  refine ⟨B*A,by nlinarith,?_⟩
  intro F δ hδ hpos hF w hw h hh hh₁ hgap
  have hP : 1 ≤ legendreFiniteInputOrder (Q+1) := by
    simpa only [inversePhaseDerivativeExpression,inversePhaseOrder,zero_add] using
      legendreFiniteInputOrder_le (Nat.zero_le (Q+1))
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hlow := modelPhaseClosedSlope_positive_window hσ hpos hF
    (u := 2) (by norm_num [phaseInterval])
  have hupp := modelPhaseClosedSlope_positive_window hσ hpos hF
    (u := 1) (by norm_num [phaseInterval])
  have hlo : 0 < (2 : ℝ)^(-σ)/2 := by positivity
  have himage : ∀ v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1),
      v ∈ modelPhaseSlopeRange F := by
    intro v hv
    rwa [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF₁]
  have hf : ∀ v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1),
      ContDiffAt ℝ ∞ (anchoredLegendreError F σ w) v := by
    intro v hv
    exact anchoredLegendreError_contDiffAt hσ hδ hF₁ (himage v hv)
      ((hlo.trans_le hlow.1).trans hv.1)
  have hb : ∀ v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1),
      ∀ n ≤ Q+1, |iteratedDeriv n (anchoredLegendreError F σ w) v| ≤ A*δ := by
    intro v hv n hn
    exact hjets F δ hδ hpos hF w hw v (himage v hv) n hn
  refine ⟨taylorPastedExtension_contDiff hh hf Q,
    fun v hv => taylorPastedExtension_agrees _ Q hh hv,?_⟩
  intro v hv n hn
  have hdistL : |v-(modelPhaseClosedSlope F 2+2*h)| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith [hlow.1,hupp.2,hv.1,hv.2]
  have hdistR : |v-(modelPhaseClosedSlope F 1-2*h)| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith [hlow.1,hupp.2,hv.1,hv.2]
  exact (hpaste (anchoredLegendreError F σ w) _ _ h v (A*δ)
    hh hh₁ hgap hf hb hdistL hdistR n hn).trans_eq (by ring)

end TaoTrudgianYang2025
