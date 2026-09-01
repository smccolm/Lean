import GafniTao.FordShiftedZeroDetectorGoodLeftShift
import GafniTao.FordShiftedZeroDetectorHorizontalBound
import GafniTao.FordZeroDetectorSelectedAbel

/-!
# Fully selected finite Abel formula for the shifted detector

The upper and lower heights and the nearby left shift are selected from the
actual zeta function.  The conclusion contains the exact pole-corrected
residue identity and literal exponential majorants.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordShiftedDetector_leftPoint_eq_unscaled
    (sigma eta t u : ℝ) :
    fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I =
      (((sigma - eta : ℝ) : ℂ) +
        ((t + 2 * eta * u / Real.pi : ℝ) : ℂ) * I) := by
  unfold fordShiftedDetectorCenter
  apply Complex.ext
  · simp
    ring
  · simp

/-- The shifted finite detector identity with every contour edge selected
from the actual zeta function. -/
theorem exists_fordShiftedDetector_selected_finite_abel_with_left_nonvanishing :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma eta etaMax t T : ℝ}
        (_hsigma : 1 ≤ sigma)
        (_heta : 0 ≤ eta) (_hetaMax : eta < etaMax)
        (_hPole : sigma - 1 ≤ eta)
        (_hleftMax : -1 ≤ sigma - etaMax)
        (_ht : 0 < t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * etaMax / Real.pi ≤ T),
      ∃ eta' RUpper RLower : ℝ,
        eta < eta' ∧ eta' < etaMax ∧
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (fordShiftedDetectorPhysicalResidueMass
            sigma eta' t (-RLower) RUpper).re =
          fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (eta' : ℂ) (-RLower) RUpper -
            fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (-eta' : ℂ) (-RLower) RUpper -
            (fordShiftedHorizontalRemainder
              sigma eta' t (-RLower - t)).re +
            (fordShiftedHorizontalRemainder
              sigma eta' t (RUpper - t)).re ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (-RLower - t) ∧
        (∀ u ∈ uIcc (fordDetectorPhysicalScale eta' t (-RLower))
            (fordDetectorPhysicalScale eta' t RUpper),
          riemannZeta
            (fordShiftedDetectorCenter sigma t + (-eta' : ℂ) +
              (2 * eta' * u / Real.pi : ℝ) * I) ≠ 0) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordDetector_independent_good_heights
  refine ⟨C, hC, ?_⟩
  intro sigma eta etaMax t T _hsigma _heta _hetaMax _hPole
    _hleftMax _ht _hT _hTlarge
  obtain ⟨RUpper, RLower, hRU, hRL, hzU, hzL, hlogU, hlogL⟩ :=
    hselect (T := T) (t := t) _hT
  have hy : -RLower ≤ RUpper := by
    linarith [hRU.1, hRL.1, _hT]
  obtain ⟨eta', hetaLow, hetaHigh, hzLeft⟩ :=
    exists_fordShiftedDetector_good_left_shift
      _heta _hetaMax _hleftMax hy
  have heta' : 0 < eta' := lt_of_le_of_lt _heta hetaLow
  have hPole' : sigma - 1 < eta' := by linarith
  have hleft' : -1 ≤ sigma - eta' := by linarith
  have hleftOne : sigma - eta' ≠ 1 := by linarith
  have hyLower : -RLower < 0 := by
    linarith [hRL.1, _hT]
  have hytLower : -RLower < t := by
    linarith [hRL.1, _hT, _ht]
  have hytUpper : t < RUpper := by
    have hetaMaxPos : 0 < etaMax :=
      lt_of_le_of_lt _heta _hetaMax
    have hterm : 0 < 2 * etaMax / Real.pi := by positivity
    have htT : t < T := by linarith
    exact htT.trans_le hRU.1
  have hzLeftScaled : ∀ u ∈
      uIcc (fordDetectorPhysicalScale eta' t (-RLower))
        (fordDetectorPhysicalScale eta' t RUpper),
      riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta' : ℂ) +
          (2 * eta' * u / Real.pi : ℝ) * I) ≠ 0 := by
    intro u hu
    rw [fordShiftedDetector_leftPoint_eq_unscaled]
    exact hzLeft (t + 2 * eta' * u / Real.pi)
      (fordDetector_unscaled_mem_Icc heta' hy hu)
  have hboundary :=
    fordShiftedDetectorPhysicalZeros_strict_of_edge_nonvanishing
      _hsigma heta' hzLeft
        (fun x _hx => by
          simpa [fordHorizontalPoint] using hzU x)
        (fun x _hx => by
          simpa [fordHorizontalPoint] using hzL x)
  have habel :=
    re_fordShiftedDetectorPhysicalResidueMass_eq_finite_abel
      _hsigma heta' _ht hPole' hyLower hytLower hytUpper
      hleft' hleftOne hboundary hzLeftScaled hzU hzL
  have hetaScale :
      2 * eta' / Real.pi ≤ 2 * etaMax / Real.pi := by
    gcongr
  have hUpperDiff : 2 * eta' / Real.pi ≤ RUpper - t := by
    linarith [hRU.1, _hTlarge, hetaScale]
  have hLowerDiff : 2 * eta' / Real.pi ≤ RLower + t := by
    linarith [hRL.1, _hTlarge, hetaScale, _ht]
  have hUpperNonneg : 0 ≤ RUpper - t := by
    have : 0 < 2 * eta' / Real.pi := by positivity
    linarith
  have hLowerNeg : -RLower - t < 0 := by
    linarith [hRL.1, _hT, _ht]
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
      ‖fordShiftedHorizontalRemainder
          sigma eta' t (RUpper - t)‖ ≤
        fordDetectorHorizontalRemainderMajorant eta'
          (C * Real.log T ^ 2) (RUpper - t) := by
    simpa [fordDetectorHorizontalRemainderMajorant] using
      (norm_fordShiftedHorizontalRemainder_le
        (sigma := sigma) heta' hM hUpperHeight
        (fun x hx => hlogU x
          (by linarith [hx.1, hleft'])))
  have hremLower :
      ‖fordShiftedHorizontalRemainder
          sigma eta' t (-RLower - t)‖ ≤
        fordDetectorHorizontalRemainderMajorant eta'
          (C * Real.log T ^ 2) (-RLower - t) := by
    simpa [fordDetectorHorizontalRemainderMajorant] using
      (norm_fordShiftedHorizontalRemainder_le
        (sigma := sigma) heta' hM hLowerHeight
        (fun x hx => hlogL x
          (by linarith [hx.1, hleft'])))
  exact ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
    habel, hremUpper, hremLower, hzLeftScaled⟩

/-- Regression projection retaining the original selected finite-Abel public
interface. -/
theorem exists_fordShiftedDetector_selected_finite_abel :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma eta etaMax t T : ℝ}
        (_hsigma : 1 ≤ sigma)
        (_heta : 0 ≤ eta) (_hetaMax : eta < etaMax)
        (_hPole : sigma - 1 ≤ eta)
        (_hleftMax : -1 ≤ sigma - etaMax)
        (_ht : 0 < t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * etaMax / Real.pi ≤ T),
      ∃ eta' RUpper RLower : ℝ,
        eta < eta' ∧ eta' < etaMax ∧
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (fordShiftedDetectorPhysicalResidueMass
            sigma eta' t (-RLower) RUpper).re =
          fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (eta' : ℂ) (-RLower) RUpper -
            fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (-eta' : ℂ) (-RLower) RUpper -
            (fordShiftedHorizontalRemainder
              sigma eta' t (-RLower - t)).re +
            (fordShiftedHorizontalRemainder
              sigma eta' t (RUpper - t)).re ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (-RLower - t) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordShiftedDetector_selected_finite_abel_with_left_nonvanishing
  refine ⟨C, hC, ?_⟩
  intro sigma eta etaMax t T _hsigma _heta _hetaMax _hPole
    _hleftMax _ht _hT _hTlarge
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
      habel, hremUpper, hremLower, _hzLeft⟩ :=
    hselect _hsigma _heta _hetaMax _hPole _hleftMax
      _ht _hT _hTlarge
  exact ⟨eta', RUpper, RLower, hetaLow, hetaHigh, hRU, hRL,
    habel, hremUpper, hremLower⟩

#print axioms exists_fordShiftedDetector_selected_finite_abel_with_left_nonvanishing
#print axioms exists_fordShiftedDetector_selected_finite_abel

end

end GafniTao
