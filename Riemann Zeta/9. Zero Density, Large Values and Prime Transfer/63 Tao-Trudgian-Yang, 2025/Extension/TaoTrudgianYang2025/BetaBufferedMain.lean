import TaoTrudgianYang2025.BetaBufferedVariation
import TaoTrudgianYang2025.BetaAmplitudePartialSummation

/-!
# Actual cutoff-weighted stationary blocks and canonical prefix control

The original source cutoff remains at the actual stationary point.
Its variation is derived independently of its endpoints and width.
The separate canonical slope-chart cutoff only normalizes the phase.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

def modelPhaseBufferedStationaryBlock
    (F : ℝ → ℝ) (l r η T N : ℝ) (a L : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc a (a+L),
    (modelPhaseBufferedCutoff l r η (modelPhaseInverseSlope F ((q : ℝ)*N/T)) : ℂ)*
      modelPhaseStationaryMainTerm F T N q

theorem modelPhaseBufferedStationaryBlock_eq_range
    (F : ℝ → ℝ) (l r η T N : ℝ) (a L : ℕ) :
    modelPhaseBufferedStationaryBlock F l r η T N a L =
      ∑ i ∈ Finset.range (L+1),
        (modelPhaseBufferedCutoff l r η
          (modelPhaseInverseSlope F (((a : ℝ)+i)*N/T)) : ℂ)*
            modelPhaseStationaryMainTerm F T N ((a : ℝ)+i) := by
  rw [modelPhaseBufferedStationaryBlock,RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range _ a (a+L)
    (Nat.le_add_right a L)]
  simp only [Nat.add_sub_cancel_left,Nat.cast_add]

theorem norm_modelPhaseBufferedStationaryBlock_le_prefixMax
    {χ F : ℝ → ℝ} {σ δ A w T N η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hA : 0 < A) (hw : 0 < w) (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (l r : ℝ) (a L : ℕ)
    (hslope : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖modelPhaseBufferedStationaryBlock F l r η T N a L‖ ≤
      8*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
        exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L := by
  have hprefix : ∀ j ≤ L+1,
      ‖∑ i ∈ Finset.range j, modelPhaseStationaryCharacter F T N ((a : ℝ)+i)‖ ≤
        exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L := by
    intro j hj
    cases j with
    | zero =>
        simpa only [Finset.sum_range_zero,norm_zero] using
          exponentialSumAtPrefixMax_nonneg (canonicalLegendrePhase χ F σ A w)
            (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L
    | succ j =>
        have hjL : j ≤ L := by omega
        rw [norm_modelPhaseStationaryCharacter_range hA hw hT.ne' hN.ne' a j
          (fun i hi => hv i (hi.trans hjL)) (fun i hi => hχ i (hi.trans hjL))]
        exact norm_exponentialSumAt_le_prefixMax _ _ _ a L j hjL
  have h := norm_sum_range_succ_mul_le_of_finiteVariation
    (finiteVariationBound_modelPhaseBufferedAmplitude hσ hδ hF hT hN hη l r a L hslope)
    (exponentialSumAtPrefixMax_nonneg _ _ _ _ _) hprefix
  rw [modelPhaseBufferedStationaryBlock_eq_range]
  simp only [modelPhaseStationaryMainTerm,← mul_assoc]
  convert h using 1
  ring

end TaoTrudgianYang2025
