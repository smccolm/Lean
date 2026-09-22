import TaoTrudgianYang2025.BetaCoreNonstationary
import TaoTrudgianYang2025.BetaBufferedCoreExpansion

/-!
# Original source reduced to the actual stationary main terms

The nonstationary complement is now bounded, not retained in the expansion.
The original smoothing loss and stationary remainder are still explicit;
their sharp power-saving balance is a separate unresolved obligation.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhase_buffered_source_stationary_expansion
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N η : ℝ) (a b : ℕ),
        0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
          0 < T → 0 < ε →
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Ioo (modelPhaseEndpointLower F T N) (modelPhaseEndpointUpper F T N),
              (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
                (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
                  modelPhaseStationaryMainTerm F T N q‖ ≤
            4*N*η+2+ε+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(η⁻¹)^3*(1+N/T)+
              2*E*N/Real.sqrt T+(8/Real.pi)*(1+Real.log (3*(T/N)+3)) := by
  obtain ⟨C,hC,D,hD,hsource⟩ := modelPhase_buffered_source_core_expansion hσ
  obtain ⟨E,hE,hnonstationary⟩ := modelPhaseBufferedCoreNonstationary_uniform hσ
  refine ⟨C,hC,D,hD,E,hE,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T ε hδ hF hT hε A B R
  have hF₁ := approximateModelPhase_mono hF bufferedStationaryPhaseOrder_pos le_rfl
  have h₁ := hsource N η a b hN hη hη₁ ha hb F δ T ε hδ hF hT hε
  have h₂ := hnonstationary ((a : ℝ)/N) ((b : ℝ)/N) η
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb) hη F δ T N hδ hF₁ hT hN
  let main := ∑ q ∈ modelPhaseCoreStationarySet F σ δ T N,
    (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
      (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N q
  let expansion := modelPhaseBufferedCoreExpansion ((a : ℝ)/N) ((b : ℝ)/N) η F σ δ T N
  have hdiff : ‖expansion-main‖ ≤
      2*E*N/Real.sqrt T+(8/Real.pi)*(1+Real.log (3*(T/N)+3)) := by
    simpa only [expansion,modelPhaseBufferedCoreExpansion,main,add_sub_cancel_left] using h₂
  rw [← modelPhaseCoreStationarySet_eq_endpoint_Ioo hσ hδ hF₁ hT hN]
  change ‖exponentialSumAt F T N a b-main‖ ≤ _
  have he : exponentialSumAt F T N a b-main =
      (exponentialSumAt F T N a b-expansion)+(expansion-main) := by abel
  rw [he]
  have h := (norm_add_le _ _).trans (add_le_add h₁ hdiff)
  exact h.trans_eq (by ring)

end TaoTrudgianYang2025

