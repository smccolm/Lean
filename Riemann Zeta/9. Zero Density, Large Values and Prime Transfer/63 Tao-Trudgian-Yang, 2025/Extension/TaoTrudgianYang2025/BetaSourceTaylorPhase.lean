import TaoTrudgianYang2025.BetaTaylorRetainedCoverage

/-!
# Original-source consumer of the moving canonical Taylor phase

The buffer is chosen from T, the anchor from the original derivative,
and every retained stationary frequency is proved to lie in the exact
extension plateau. Membership in an individual multiplicative chart
remains the separate finite-cover/partition obligation.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

theorem modelPhase_source_canonicalTaylorPhase
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∀ (F : ℝ → ℝ),
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder (Q+2)) δ →
        ∀ (N T : ℝ) (a b : ℕ),
          0 < N → 0 < T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
          (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
          let w := deriv F ((3 : ℝ)/2)
          let h := modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹)
          IsApproximateModelPhaseFunction (canonicalTaylorLegendrePhase F σ A Q w h)
            σ⁻¹ Q ε ∧
          ∀ q ∈ modelPhaseSharpStationarySet F T N a b,
            canonicalTaylorLegendrePhase F σ A Q w h (((q : ℝ)*N/T)/A) =
              A^(σ⁻¹-1)*(modelPhaseLegendreDual F ((q : ℝ)*N/T)-modelPhaseLegendreDual F w)+
                referenceModelPrimitive σ⁻¹ (w/A) := by
  obtain ⟨δ,hd,hsmall,hpos,hcanonical⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ Q hε
  refine ⟨δ,hd,hsmall,hpos,?_⟩
  intro F hF N T a b hN hT ha hb hlong
  have hP : 1 ≤ legendreFiniteInputOrder (Q+2) := by
    simpa only [inversePhaseDerivativeExpression,inversePhaseOrder,zero_add] using
      legendreFiniteInputOrder_le (Nat.zero_le (Q+2))
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hw : deriv F ((3 : ℝ)/2) ∈ modelPhaseSlopeRange F :=
    ⟨(3 : ℝ)/2,by constructor <;> norm_num,rfl⟩
  have hadmissible := modelPhaseTaylorWidth_source_admissible hσ hsmall hF₁ hT hN ha hb hlong
  have hwpos : 0 < deriv F ((3 : ℝ)/2) :=
    (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
      (modelPhaseSlopeRange_positive_window hσ hpos hF hw).1
  refine ⟨hcanonical F hF _ hw _ hadmissible.1 hadmissible.2.1 hadmissible.2.2,?_⟩
  intro q hq
  have hgeom := modelPhaseSharpStationarySet_critical_geometry hσ hsmall hF₁ hT hN ha hb hq
  have hvpos : 0 < (q : ℝ)*N/T :=
    (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
      (modelPhaseSlopeRange_positive_window hσ hpos hF hgeom.1).1
  exact canonicalTaylorLegendrePhase_agrees Q hA hwpos hvpos hadmissible.1
    (modelPhaseSharpStationarySet_taylor_plateau hσ hsmall hF₁ hT hN ha hb hq)

end TaoTrudgianYang2025
