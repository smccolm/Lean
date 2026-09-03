import GafniTao.FordLocalDetectorGrowthBound

/-!
# An arbitrary-centre Ford detector with no retained zero

This is the empty-subset companion to `FordSingleZeroDetector`.  It consumes
the same selected contour and every edge term, but applies the exact finite
subset inequality with the empty zero subset.
-/

open Complex Set Finset MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

private theorem fordEmptyPhysicalScale_mono
    {eta t : ℝ} (heta : 0 < eta) :
    Monotone (fordDetectorPhysicalScale eta t) := by
  intro x y hxy
  unfold fordDetectorPhysicalScale
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy t) Real.pi_pos.le)
    (mul_nonneg two_pos.le heta.le)

set_option maxHeartbeats 1200000 in
theorem eventually_exists_fordEmpty_detector_general_growthBound
    {A B sigma eta etaMax t : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (hetaMax : eta < etaMax)
    (hPole : sigma - 1 ≤ eta)
    (hleftLowerMax : 1 / 2 ≤ sigma - etaMax)
    (hetaMaxUpper : etaMax ≤ Real.pi / 4)
    (ht : 3 ≤ t) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T → 8 ≤ T →
        t + 2 * etaMax / Real.pi ≤ T →
        ∃ eta' RUpper RLower : ℝ,
          eta < eta' ∧ eta' < etaMax ∧
          RUpper ∈ Set.Icc T (T + 1) ∧
          RLower ∈ Set.Icc T (T + 1) ∧
          -(fordDetectorZetaLogDeriv
              (fordShiftedDetectorCenter sigma t)).re <
            eta' / (Real.pi * t ^ 2) +
            Real.log (1 + 1 / (sigma + eta' - 1)) / (2 * eta') +
            2 * fordGeneralShiftedLeftHighMajorant A B eta' sigma t +
            fordShiftedLeftLowMajorant eta' t (eta' - (sigma - 1)) + ε := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordShiftedDetector_selected_finite_abel_with_left_nonvanishing
  have hleftMax : -1 ≤ sigma - etaMax := by linarith
  have htPos : 0 < t := by linarith
  intro ε hε
  obtain ⟨Ttail, htail⟩ :=
    eventually_fordShiftedDetector_horizontal_remainder_small
      (sigma := sigma) (eta := eta) (etaMax := etaMax)
      (C := C) (t := t) heta hetaMax.le hC.le (ε / 2) (by positivity)
  refine ⟨max Ttail t, ?_⟩
  intro T hT0 hT hTlarge
  have hTtail : Ttail ≤ T := (le_max_left _ _).trans hT0
  have htT : t ≤ T := (le_max_right _ _).trans hT0
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
      habel, hremUpper, hremLower, hzLeft⟩ :=
    hselect hsigma heta.le hetaMax hPole hleftMax htPos hT hTlarge
  have hetaPos : 0 < eta' := heta.trans hetaLow
  have hetaUpperPi : eta' ≤ Real.pi / 4 :=
    hetaHigh.le.trans hetaMaxUpper
  have hy : -RLower ≤ RUpper := by linarith [hRU.1, hRL.1, hT]
  have hyLower : -RLower ≤ -3 := by linarith [hRL.1, hT]
  have hyUpper : 3 ≤ RUpper := by linarith [hRU.1, hT]
  have hd : 0 < eta' - (sigma - 1) := by linarith
  have hleftLower : 1 / 2 ≤ sigma - eta' :=
    hleftLowerMax.trans (sub_le_sub_left hetaHigh.le sigma)
  have hleftUpper : sigma - eta' ≤ 1 - (eta' - (sigma - 1)) := by
    linarith
  have hleftOne : sigma - eta' ≠ 1 := by linarith
  have hintFull : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta' sigma t) volume
      (fordDetectorPhysicalScale eta' t (-RLower))
      (fordDetectorPhysicalScale eta' t RUpper) := by
    apply intervalIntegrable_fordShiftedLeftCoordinateIntegrand hleftOne
    exact hzLeft
  have hscaleMono := fordEmptyPhysicalScale_mono (t := t) hetaPos
  have hscaleNeg3 : fordDetectorPhysicalScale eta' t (-RLower) ≤
      fordDetectorPhysicalScale eta' t (-3) := hscaleMono hyLower
  have hscaleThree : fordDetectorPhysicalScale eta' t 3 ≤
      fordDetectorPhysicalScale eta' t RUpper := hscaleMono hyUpper
  have hscaleNegThree : fordDetectorPhysicalScale eta' t (-3) ≤
      fordDetectorPhysicalScale eta' t 3 := hscaleMono (by norm_num)
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
  have hleft := fordShiftedDetectorPhysicalVerticalBulk_left_general_full_bound
    hFord hA hB hetaPos hetaUpperPi hd hleftLower hleftUpper ht
      hyLower hyUpper hintNeg hintLow hintPos
  have hsubset : (∅ : Finset ℂ) ⊆
      fordShiftedDetectorPhysicalZeros sigma eta' (-RLower) RUpper :=
    empty_subset _
  have hdet := fordShiftedDetector_finite_subset_inequality
    hsigma hetaPos hsubset habel
  have hsigmaRight : 1 < sigma + eta' := by linarith
  have hright := fordShiftedDetectorPhysicalVerticalBulk_right_lower
    (eta := eta') (sigma := sigma) (t := t)
    (yLower := -RLower) (yUpper := RUpper)
    (M := 1 + 1 / (sigma + eta' - 1))
    hetaPos hsigmaRight le_rfl hy
  have hrightNeg :
      -fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
          (eta' : ℂ) (-RLower) RUpper ≤
        Real.log (1 + 1 / (sigma + eta' - 1)) / (2 * eta') := by
    have hneg := neg_le_neg hright
    simpa only [neg_div, neg_neg] using hneg
  have hsigmaUpper : sigma ≤ 1 + eta' := by linarith
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
  simp only [Finset.sum_empty] at hdet
  linarith

#print axioms eventually_exists_fordEmpty_detector_general_growthBound

end

end GafniTao
