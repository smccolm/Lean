import GafniTao.FordZeroDetectorGoodLeftShift

/-!
# Ford's finite Abel formula on fully selected edges

This is the first public detector theorem with no boundary-nonvanishing
hypothesis.  The upper and lower physical heights come from the actual Landau
zero set, while the left shift is selected arbitrarily close above the
prescribed `eta` by avoiding the actual finite zeta-zero set.  The conclusion
contains the exact finite residue identity and the literal exponential
majorants for both horizontal remainders.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordDetectorPhysicalScale_mono
    {eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hy : yLower ≤ yUpper) :
    fordDetectorPhysicalScale eta t yLower ≤
      fordDetectorPhysicalScale eta t yUpper := by
  unfold fordDetectorPhysicalScale
  have hk : 0 < Real.pi / (2 * eta) := by positivity
  rw [show Real.pi * (yLower - t) / (2 * eta) =
      (Real.pi / (2 * eta)) * (yLower - t) by ring,
    show Real.pi * (yUpper - t) / (2 * eta) =
      (Real.pi / (2 * eta)) * (yUpper - t) by ring]
  exact mul_le_mul_of_nonneg_left (by linarith) hk.le

theorem fordDetector_unscaled_mem_Icc
    {eta t yLower yUpper u : ℝ} (heta : 0 < eta)
    (hy : yLower ≤ yUpper)
    (hu : u ∈ uIcc (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t yUpper)) :
    t + 2 * eta * u / Real.pi ∈ Set.Icc yLower yUpper := by
  have hscale := fordDetectorPhysicalScale_mono (t := t) heta hy
  rw [uIcc_of_le hscale] at hu
  have hc : 0 ≤ 2 * eta / Real.pi := by positivity
  have hl := mul_le_mul_of_nonneg_left hu.1 hc
  have hr := mul_le_mul_of_nonneg_left hu.2 hc
  have hlId :
      (2 * eta / Real.pi) *
          fordDetectorPhysicalScale eta t yLower = yLower - t := by
    unfold fordDetectorPhysicalScale
    field_simp [heta.ne', Real.pi_ne_zero]
  have hrId :
      (2 * eta / Real.pi) *
          fordDetectorPhysicalScale eta t yUpper = yUpper - t := by
    unfold fordDetectorPhysicalScale
    field_simp [heta.ne', Real.pi_ne_zero]
  rw [hlId] at hl
  rw [hrId] at hr
  rw [show 2 * eta * u / Real.pi = (2 * eta / Real.pi) * u by ring]
  exact ⟨by linarith, by linarith⟩

theorem fordDetector_leftPoint_eq_unscaled
    (eta t u : ℝ) :
    fordDetectorCenter t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I =
      (((1 - eta : ℝ) : ℂ) +
        ((t + 2 * eta * u / Real.pi : ℝ) : ℂ) * I) := by
  unfold fordDetectorCenter
  apply Complex.ext
  · simp
    ring
  · simp

/-- Ford's finite physical detector identity with every contour edge selected
from the actual zeta function.  The selected `eta'` may be taken in any
prescribed interval `(eta, etaMax)`. -/
theorem exists_fordDetector_selected_finite_abel :
    ∃ C : ℝ, 0 < C ∧
      ∀ {eta etaMax t T : ℝ}
        (_heta : 0 ≤ eta) (_hetaMax : eta < etaMax)
        (_hetaMaxUpper : etaMax ≤ 1) (_ht : 0 < t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * etaMax / Real.pi ≤ T),
      ∃ eta' RUpper RLower : ℝ,
        eta < eta' ∧ eta' < etaMax ∧
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (fordDetectorPhysicalResidueMass eta' t (-RLower) RUpper).re =
          fordDetectorPhysicalVerticalBulk eta' t (eta' : ℂ)
              (-RLower) RUpper -
            fordDetectorPhysicalVerticalBulk eta' t (-eta' : ℂ)
              (-RLower) RUpper -
            (fordDetectorHorizontalRemainder eta' t (-RLower - t)).re +
            (fordDetectorHorizontalRemainder eta' t (RUpper - t)).re ∧
        ‖fordDetectorHorizontalRemainder eta' t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordDetectorHorizontalRemainder eta' t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (-RLower - t) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordDetector_independent_good_heights
  refine ⟨C, hC, ?_⟩
  intro eta etaMax t T _heta _hetaMax _hetaMaxUpper _ht _hT _hTlarge
  obtain ⟨RUpper, RLower, hRU, hRL, hzU, hzL, hlogU, hlogL⟩ :=
    hselect (T := T) (t := t) _hT
  have hy : -RLower ≤ RUpper := by linarith [hRU.1, hRL.1, _hT]
  obtain ⟨eta', hetaLow, hetaHigh, hzLeft⟩ :=
    exists_fordDetector_good_left_shift _heta _hetaMax
      _hetaMaxUpper hy
  have heta' : 0 < eta' := lt_of_le_of_lt _heta hetaLow
  have heta'Upper : eta' ≤ 1 := by linarith
  have hyLower : -RLower < 0 := by linarith [hRL.1, _hT]
  have hytLower : -RLower < t := by linarith [hRL.1, _hT, _ht]
  have hytUpper : t < RUpper := by
    have hetaMaxPos : 0 < etaMax := lt_of_le_of_lt _heta _hetaMax
    have hterm : 0 < 2 * etaMax / Real.pi := by positivity
    have htT : t < T := by linarith
    exact htT.trans_le hRU.1
  have hzLeftScaled : ∀ u ∈
      uIcc (fordDetectorPhysicalScale eta' t (-RLower))
        (fordDetectorPhysicalScale eta' t RUpper),
      riemannZeta (fordDetectorCenter t + (-eta' : ℂ) +
        (2 * eta' * u / Real.pi : ℝ) * I) ≠ 0 := by
    intro u hu
    rw [fordDetector_leftPoint_eq_unscaled]
    exact hzLeft (t + 2 * eta' * u / Real.pi)
      (fordDetector_unscaled_mem_Icc heta' hy hu)
  have hboundary := fordDetectorPhysicalZeros_strict_of_edge_nonvanishing
    heta' hzLeft
      (fun x _hx => by simpa [fordHorizontalPoint] using hzU x)
      (fun x _hx => by simpa [fordHorizontalPoint] using hzL x)
  have habel := re_fordDetectorPhysicalResidueMass_eq_finite_abel
    heta' heta'Upper _ht hyLower hytLower hytUpper hboundary
      hzLeftScaled hzU hzL
  have hetaScale : 2 * eta' / Real.pi ≤ 2 * etaMax / Real.pi := by
    gcongr
  have hUpperDiff : 2 * eta' / Real.pi ≤ RUpper - t := by
    linarith [hRU.1, _hTlarge, hetaScale]
  have hLowerDiff : 2 * eta' / Real.pi ≤ RLower + t := by
    linarith [hRL.1, _hTlarge, hetaScale, _ht]
  have hUpperNonneg : 0 ≤ RUpper - t := by
    have : 0 < 2 * eta' / Real.pi := by positivity
    linarith
  have hLowerNeg : -RLower - t < 0 := by linarith [hRL.1, _hT, _ht]
  have hscaleId :
      (Real.pi / (2 * eta')) * (2 * eta' / Real.pi) = 1 := by
    field_simp [heta'.ne', Real.pi_ne_zero]
  have hUpperHeight :
      1 ≤ (Real.pi / (2 * eta')) * |RUpper - t| := by
    rw [abs_of_nonneg hUpperNonneg, ← hscaleId]
    exact mul_le_mul_of_nonneg_left hUpperDiff (by positivity)
  have hLowerHeight :
      1 ≤ (Real.pi / (2 * eta')) * |-RLower - t| := by
    rw [abs_of_neg hLowerNeg]
    rw [show -(-RLower - t) = RLower + t by ring, ← hscaleId]
    exact mul_le_mul_of_nonneg_left hLowerDiff (by positivity)
  have hM : 0 ≤ C * Real.log T ^ 2 :=
    mul_nonneg hC.le (sq_nonneg _)
  have hremUpper :
      ‖fordDetectorHorizontalRemainder eta' t (RUpper - t)‖ ≤
        fordDetectorHorizontalRemainderMajorant eta'
          (C * Real.log T ^ 2) (RUpper - t) := by
    apply norm_fordDetectorHorizontalRemainder_le_majorant
      heta' hM hUpperHeight
    intro x hx
    exact hlogU x (by linarith [hx.1, heta'Upper])
  have hremLower :
      ‖fordDetectorHorizontalRemainder eta' t (-RLower - t)‖ ≤
        fordDetectorHorizontalRemainderMajorant eta'
          (C * Real.log T ^ 2) (-RLower - t) := by
    apply norm_fordDetectorHorizontalRemainder_le_majorant
      heta' hM hLowerHeight
    intro x hx
    exact hlogL x (by linarith [hx.1, heta'Upper])
  exact ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
    habel, hremUpper, hremLower⟩

end

end GafniTao
