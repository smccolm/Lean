import GafniTao.FordShiftedLeftIntegrability
import GafniTao.FordShiftedPoleBound

/-!
# Ford's local detector with every contour term bounded

This theorem repeats the selected-contour construction once, so that the
local zero set, the horizontal tails, the Euler-product right edge, the zeta
pole, and the complete Ford-growth left edge all use the same selected shift
and the same selected heights.
-/

open Complex Finset Filter Set Topology MeasureTheory
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

private theorem fordPhysicalScale_mono
    {eta t : ℝ} (heta : 0 < eta) :
    Monotone (fordDetectorPhysicalScale eta t) := by
  intro x y hxy
  unfold fordDetectorPhysicalScale
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy t) Real.pi_pos.le)
    (mul_nonneg two_pos.le heta.le)

set_option maxHeartbeats 1200000 in
/-- Conditional on Ford's published zeta-growth theorem, the selected local
detector has no remaining contour integral or horizontal-remainder term. -/
theorem eventually_exists_fordLocalDisk_detector_growthBound
    (hFord : FordZetaGrowthBound)
    {t R : ℝ} (ht : 3 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T → 8 ≤ T →
        t + 2 * (3 * R) / Real.pi ≤ T →
        ∃ eta' RUpper RLower : ℝ,
          (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
          RUpper ∈ Set.Icc T (T + 1) ∧
          RLower ∈ Set.Icc T (T + 1) ∧
          -(fordDetectorZetaLogDeriv
              (fordShiftedDetectorCenter
                (1 + (6421 / 10000 : ℝ) * R) t)).re <
            -((fordLocalDiskZeroCount t R : ℝ) *
              (fordLocalCotUniformLowerConstant / R)) +
            eta' / (Real.pi * t ^ 2) +
            Real.log (1 + 1 / (3 * R)) / (2 * eta') +
            2 * fordShiftedLeftHighMajorant eta'
              (1 + (6421 / 10000 : ℝ) * R) t +
            fordShiftedLeftLowMajorant eta' t
              (eta' - (6421 / 10000 : ℝ) * R) + ε := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordShiftedDetector_selected_finite_abel_with_left_nonvanishing
  let eta0 : ℝ := (5 / 2 : ℝ) * R
  let etaMax : ℝ := (51 / 20 : ℝ) * R
  let sigma : ℝ := 1 + (6421 / 10000 : ℝ) * R
  have hsigma : 1 ≤ sigma := by dsimp [sigma]; nlinarith
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  have hetaRange : eta0 < etaMax := by dsimp [eta0, etaMax]; nlinarith
  have hPole : sigma - 1 ≤ eta0 := by dsimp [sigma, eta0]; nlinarith
  have hleftMax : -1 ≤ sigma - etaMax := by
    dsimp [sigma, etaMax]
    nlinarith
  have hetaMaxUpper : etaMax ≤ Real.pi / 4 := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    dsimp [etaMax]
    nlinarith
  have hleftLowerMax : 1 / 2 ≤ sigma - etaMax := by
    dsimp [sigma, etaMax]
    nlinarith
  have htPos : 0 < t := by linarith
  have heta0Max : eta0 ≤ etaMax := hetaRange.le
  intro ε hε
  obtain ⟨Ttail, htail⟩ :=
    eventually_fordShiftedDetector_horizontal_remainder_small
      (sigma := sigma) (eta := eta0) (etaMax := etaMax)
      (C := C) (t := t) heta0 heta0Max hC.le (ε / 2) (by positivity)
  refine ⟨max Ttail t, ?_⟩
  intro T hT0 hT hTlarge
  have hTtail : Ttail ≤ T := (le_max_left _ _).trans hT0
  have htT : t ≤ T := (le_max_right _ _).trans hT0
  have hTlargeNarrow : t + 2 * etaMax / Real.pi ≤ T := by
    have hscale : etaMax ≤ 3 * R := by dsimp [etaMax]; nlinarith
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 2))
      Real.pi_pos.le
    linarith
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
      habel, hremUpper, hremLower, hzLeft⟩ :=
    hselect hsigma heta0.le hetaRange hPole hleftMax
      htPos hT hTlargeNarrow
  have hetaPos : 0 < eta' := heta0.trans hetaLow
  have hetaUpperPi : eta' ≤ Real.pi / 4 :=
    hetaHigh.le.trans hetaMaxUpper
  have hy : -RLower ≤ RUpper := by linarith [hRU.1, hRL.1, hT]
  have hyLower : -RLower ≤ -3 := by linarith [hRL.1, hT]
  have hyUpper : 3 ≤ RUpper := by linarith [hRU.1, hT]
  have hd : 0 < eta' - (6421 / 10000 : ℝ) * R := by
    dsimp [eta0] at hetaLow
    nlinarith
  have hleftLower : 1 / 2 ≤ sigma - eta' :=
    hleftLowerMax.trans (sub_le_sub_left hetaHigh.le sigma)
  have hleftUpper :
      sigma - eta' ≤ 1 - (eta' - (6421 / 10000 : ℝ) * R) := by
    dsimp [sigma]
    have heq :
        1 + 6421 / 10000 * R - eta' =
          1 - (eta' - 6421 / 10000 * R) := by ring
    exact heq.le
  have hleftOne : sigma - eta' ≠ 1 := by linarith
  have hintFull : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta' sigma t) volume
      (fordDetectorPhysicalScale eta' t (-RLower))
      (fordDetectorPhysicalScale eta' t RUpper) := by
    apply intervalIntegrable_fordShiftedLeftCoordinateIntegrand hleftOne
    exact hzLeft
  have hscaleMono := fordPhysicalScale_mono (t := t) hetaPos
  have hscaleNeg3 : fordDetectorPhysicalScale eta' t (-RLower) ≤
      fordDetectorPhysicalScale eta' t (-3) :=
    hscaleMono hyLower
  have hscaleThree : fordDetectorPhysicalScale eta' t 3 ≤
      fordDetectorPhysicalScale eta' t RUpper :=
    hscaleMono hyUpper
  have hscaleNegThree : fordDetectorPhysicalScale eta' t (-3) ≤
      fordDetectorPhysicalScale eta' t 3 :=
    hscaleMono (by norm_num)
  have hnegMem : fordDetectorPhysicalScale eta' t (-3) ∈
      uIcc (fordDetectorPhysicalScale eta' t (-RLower))
        (fordDetectorPhysicalScale eta' t RUpper) :=
    mem_uIcc_of_le hscaleNeg3 (hscaleNegThree.trans hscaleThree)
  have hposMem : fordDetectorPhysicalScale eta' t 3 ∈
      uIcc (fordDetectorPhysicalScale eta' t (-RLower))
        (fordDetectorPhysicalScale eta' t RUpper) :=
    mem_uIcc_of_le (hscaleNeg3.trans hscaleNegThree) hscaleThree
  have hintNeg := hintFull.mono_set
    (uIcc_subset_uIcc left_mem_uIcc hnegMem)
  have hintLow := hintFull.mono_set
    (uIcc_subset_uIcc hnegMem hposMem)
  have hintPos := hintFull.mono_set
    (uIcc_subset_uIcc hposMem right_mem_uIcc)
  have hleft := fordShiftedDetectorPhysicalVerticalBulk_left_full_bound
    hFord hetaPos hetaUpperPi hd hleftLower hleftUpper ht
    hyLower hyUpper hintNeg hintLow hintPos
  have hsubset : fordLocalDiskZeros t R ⊆
      fordShiftedDetectorPhysicalZeros sigma eta' (-RLower) RUpper := by
    apply fordLocalDiskZeros_subset_physical
    · dsimp [sigma, eta0] at hetaLow ⊢
      nlinarith
    · dsimp [sigma]
      nlinarith
    · have hTR : t + R ≤ T := by
        have hpiSix : Real.pi < 6 := Real.pi_lt_four.trans (by norm_num)
        have hRScale : R ≤ 2 * (3 * R) / Real.pi := by
          rw [le_div_iff₀ Real.pi_pos]
          nlinarith
        linarith
      linarith [hRL.1]
    · have hTR : t + R ≤ T := by
        have hpiSix : Real.pi < 6 := Real.pi_lt_four.trans (by norm_num)
        have hRScale : R ≤ 2 * (3 * R) / Real.pi := by
          rw [le_div_iff₀ Real.pi_pos]
          nlinarith
        linarith
      exact hTR.trans hRU.1
  have hdet := fordShiftedDetector_finite_subset_inequality
    hsigma hetaPos hsubset habel
  have hsum := sum_fordLocalDisk_selected_zeroContribution_le
    (t := t) (eta' := eta') hR hetaLow.le
      (by dsimp [etaMax] at hetaHigh; nlinarith : eta' ≤ 3 * R)
  have hsigmaRight : 1 < sigma + eta' := by
    dsimp [sigma]
    nlinarith
  have hden : 3 * R ≤ sigma + eta' - 1 := by
    dsimp [sigma, eta0] at hetaLow ⊢
    nlinarith
  have hM : 1 + 1 / (sigma + eta' - 1) ≤
      1 + 1 / (3 * R) := by
    gcongr
  have hright := fordShiftedDetectorPhysicalVerticalBulk_right_lower
    (eta := eta') (sigma := sigma) (t := t)
    (yLower := -RLower) (yUpper := RUpper)
    (M := 1 + 1 / (3 * R)) hetaPos hsigmaRight hM hy
  have hrightNeg :
      -fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
          (eta' : ℂ) (-RLower) RUpper ≤
        Real.log (1 + 1 / (3 * R)) / (2 * eta') := by
    have hneg := neg_le_neg hright
    simpa only [neg_div, neg_neg] using hneg
  have hsigmaUpper : sigma ≤ 1 + eta' := by
    dsimp [sigma, eta0] at hetaLow ⊢
    nlinarith
  have hpole := fordShiftedDetector_poleCorrection_le_inv_sq
    (eta := eta') (sigma := sigma) (t := t)
    hetaPos hsigma hsigmaUpper htPos
  have hupperAbs : T - t ≤ |RUpper - t| := by
    rw [abs_of_nonneg (by linarith [hRU.1])]
    linarith [hRU.1]
  have hlowerAbs : T - t ≤ |-RLower - t| := by
    rw [abs_of_nonpos (by linarith [hRL.1, hT, htPos])]
    linarith [hRL.1, htPos]
  have htailUpper := htail hTtail (by linarith : 1 ≤ T) htT hetaLow.le
    hetaHigh.le hupperAbs hremUpper
  have htailLower := htail hTtail (by linarith : 1 ≤ T) htT hetaLow.le
    hetaHigh.le hlowerAbs hremLower
  refine ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL, ?_⟩
  dsimp only [sigma] at hdet hpole hleft ⊢
  linarith

#print axioms eventually_exists_fordLocalDisk_detector_growthBound

end

end GafniTao
