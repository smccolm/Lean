import TaoTrudgianYang2025.BetaSourceChartPartition
import TaoTrudgianYang2025.BetaAmplitudePartialSummation

/-!
# Stationary main blocks in the moving Taylor chart

These identities retain the actual stationary character, its negative
curvature phase, and the actual physical curvature amplitude.
Plateau membership is supplied explicitly here and derived by the
original-source chart consumer.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem modelPhaseStationaryPoint_taylor_phase
    {F : ℝ → ℝ} {σ A w h T N r : ℝ} (Q : ℕ)
    (hA : 0 < A) (hw : 0 < w) (hh : 0 < h)
    (hT : T ≠ 0) (hN : N ≠ 0) (hv : 0 < r*N/T)
    (hplateau : r*N/T ∈ Icc
      (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      modelPhaseDualOffset F σ A w T -
        modelPhaseDualParameter σ A T *
          canonicalTaylorLegendrePhase F σ A Q w h (r/modelPhaseDualScale A T N) := by
  rw [modelPhaseStationaryPoint_phase hT hN,
    modelPhaseDualScale_coordinate hA.ne' hT hN,
    canonicalTaylorLegendrePhase_agrees Q hA hw hv hh hplateau]
  have hcancel := modelPhaseDualParameter_cancel σ hA T
  unfold modelPhaseDualOffset
  rw [mul_add,← mul_assoc,hcancel]
  ring

theorem modelPhaseStationaryCharacter_taylor
    {F : ℝ → ℝ} {σ A w h T N r : ℝ} (Q : ℕ)
    (hA : 0 < A) (hw : 0 < w) (hh : 0 < h)
    (hT : T ≠ 0) (hN : N ≠ 0) (hv : 0 < r*N/T)
    (hplateau : r*N/T ∈ Icc
      (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    modelPhaseStationaryCharacter F T N r =
      (𝐞 (modelPhaseDualOffset F σ A w T-1/8) : ℂ) *
        starRingEnd ℂ (𝐞 (modelPhaseDualParameter σ A T *
          canonicalTaylorLegendrePhase F σ A Q w h (r/modelPhaseDualScale A T N))) := by
  unfold modelPhaseStationaryCharacter
  rw [modelPhaseStationaryPoint_taylor_phase Q hA hw hh hT hN hv hplateau]
  rw [show modelPhaseDualOffset F σ A w T -
      modelPhaseDualParameter σ A T *
        canonicalTaylorLegendrePhase F σ A Q w h (r/modelPhaseDualScale A T N)-1/8 =
      (modelPhaseDualOffset F σ A w T-1/8) +
        -(modelPhaseDualParameter σ A T *
          canonicalTaylorLegendrePhase F σ A Q w h (r/modelPhaseDualScale A T N)) by ring]
  rw [AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]

theorem norm_modelPhaseStationaryCharacter_taylor_range
    {F : ℝ → ℝ} {σ A w h T N : ℝ} (Q : ℕ)
    (hA : 0 < A) (hw : 0 < w) (hh : 0 < h)
    (hT : T ≠ 0) (hN : N ≠ 0) (a L : ℕ)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hplateau : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ Icc
      (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    ‖∑ i ∈ Finset.range (L+1), modelPhaseStationaryCharacter F T N ((a : ℝ)+i)‖ =
      ‖exponentialSumAt (canonicalTaylorLegendrePhase F σ A Q w h)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a (a+L)‖ := by
  have he : (∑ i ∈ Finset.range (L+1),
      modelPhaseStationaryCharacter F T N ((a : ℝ)+i)) =
      (𝐞 (modelPhaseDualOffset F σ A w T-1/8) : ℂ) *
        starRingEnd ℂ (exponentialSumAt (canonicalTaylorLegendrePhase F σ A Q w h)
          (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a (a+L)) := by
    rw [exponentialSumAt_eq_range,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact modelPhaseStationaryCharacter_taylor Q hA hw hh hT hN
      (hv i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
      (hplateau i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  rw [he,norm_mul,Circle.norm_coe,one_mul]
  exact Complex.norm_conj _

theorem norm_modelPhaseStationaryBlock_le_taylor_prefixMax
    {F : ℝ → ℝ} {σ δ A w h T N : ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ modelPhaseAmplitudeTolerance σ)
    (hF : IsApproximateModelPhaseFunction F σ 2 δ)
    (hA : 0 < A) (hw : 0 < w) (hh : 0 < h) (hT : 0 < T) (hN : 0 < N)
    (a L : ℕ)
    (hslope : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F)
    (hv : ∀ i : ℕ, i ≤ L → 0 < ((a : ℝ)+i)*N/T)
    (hplateau : ∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ Icc
      (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    ‖modelPhaseStationaryBlock F T N a L‖ ≤
      2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
        exponentialSumAtPrefixMax (canonicalTaylorLegendrePhase F σ A Q w h)
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
      exponentialSumAtPrefixMax_nonneg (canonicalTaylorLegendrePhase F σ A Q w h)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L
  | succ j =>
    have hjL : j ≤ L := by omega
    rw [norm_modelPhaseStationaryCharacter_taylor_range Q hA hw hh hT.ne' hN.ne' a j
      (fun i hi => hv i (hi.trans hjL)) (fun i hi => hplateau i (hi.trans hjL))]
    exact norm_exponentialSumAt_le_prefixMax _ _ _ a L j hjL

end TaoTrudgianYang2025
