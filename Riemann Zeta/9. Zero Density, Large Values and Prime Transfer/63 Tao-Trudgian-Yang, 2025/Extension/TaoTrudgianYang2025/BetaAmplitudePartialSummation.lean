import TaoTrudgianYang2025.BetaStationaryMain

/-!
# Source-facing partial summation of the actual stationary main block

The real curvature weight is derived from the original model phase.
Its finite variation controls the literal canonical prefix maximum.
Neither variation nor a weighted exponential-sum estimate is assumed.
The approximation of Fourier integrals by these main terms remains separate.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

def modelPhaseStationaryBlock (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) : ℂ :=
  ∑ r ∈ Finset.Icc a (a+L), modelPhaseStationaryMainTerm F T N r

theorem modelPhaseStationaryBlock_eq_range (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    modelPhaseStationaryBlock F T N a L =
      ∑ i ∈ Finset.range (L+1), modelPhaseStationaryMainTerm F T N ((a : ℝ)+i) := by
  rw [modelPhaseStationaryBlock,RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range _ a (a+L)
    (Nat.le_add_right a L)]
  simp only [Nat.add_sub_cancel_left,Nat.cast_add]

theorem norm_modelPhaseStationaryBlock_le_prefixMax
    {χ F : ℝ → ℝ} {σ δ A w T N : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hA : 0 < A) (hw : 0 < w) (hT : 0 < T) (hN : 0 < N)
    (a L : ℕ)
    (hslope : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hχ : ∀ i : ℕ, i ≤ L → χ (((a : ℝ)+i)*N/T) = 1) :
    ‖modelPhaseStationaryBlock F T N a L‖ ≤
      2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
        exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A w)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L := by
  rw [modelPhaseStationaryBlock_eq_range]
  unfold modelPhaseStationaryMainTerm
  apply norm_sum_range_succ_mul_le_of_finiteVariation
    (finiteVariationBound_modelPhasePhysicalAmplitude hσ hδ hF hT hN a L hslope)
    (exponentialSumAtPrefixMax_nonneg _ _ _ _ _)
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

end TaoTrudgianYang2025
