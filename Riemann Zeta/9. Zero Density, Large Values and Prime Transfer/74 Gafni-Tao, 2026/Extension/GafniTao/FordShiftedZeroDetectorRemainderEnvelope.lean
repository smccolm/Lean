import GafniTao.FordShiftedZeroDetectorSelectedAbel
import GafniTao.FordZeroDetectorRemainderEnvelope

/-!
# Uniform tail envelope for the shifted Ford detector
-/

open Complex Filter Set Topology
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem eventually_fordShiftedDetector_horizontal_remainder_small
    {sigma eta etaMax C t : ℝ} (heta : 0 < eta)
    (hetaMax : eta ≤ etaMax) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ {T eta' y : ℝ}, T0 ≤ T →
        1 ≤ T → t ≤ T → eta ≤ eta' → eta' ≤ etaMax →
        T - t ≤ |y| →
        ‖fordShiftedHorizontalRemainder sigma eta' t y‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) y →
        ‖fordShiftedHorizontalRemainder sigma eta' t y‖ < ε := by
  have hetaMaxPos : 0 < etaMax := heta.trans_le hetaMax
  intro ε hε
  have htend := tendsto_fordDetector_poly_exp_envelope
    (C := C) (t := t) hetaMaxPos
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨T0, hT0⟩ := htend ε hε
  refine ⟨T0, ?_⟩
  intro T eta' y hT0T hT htT hetaLow hetaHigh hy hrem
  have heta' : 0 < eta' := heta.trans_le hetaLow
  have henv :=
    fordDetectorHorizontalRemainderMajorant_le_poly_exp
      heta' hetaHigh hC hT htT hy
  have hsmall := hT0 T hT0T
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hsmall
  · exact lt_of_le_of_lt (hrem.trans henv) hsmall
  · positivity

theorem re_fordShiftedDetectorPhysicalResidueMass_expanded
    (sigma eta t yLower yUpper : ℝ) :
    (fordShiftedDetectorPhysicalResidueMass
        sigma eta t yLower yUpper).re =
      (fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter sigma t)).re -
      (fordCotKernel eta
        (1 - fordShiftedDetectorCenter sigma t)).re +
      ∑ rho ∈ fordShiftedDetectorPhysicalZeros
          sigma eta yLower yUpper,
        ((analyticVanishingOrder riemannZeta rho : ℂ) *
          fordCotKernel eta
            (rho - fordShiftedDetectorCenter sigma t)).re := by
  classical
  unfold fordShiftedDetectorPhysicalResidueMass
  simp

/-- Selected finite Abel identity with the pole and multiplicity-weighted
zero sum exposed in the public conclusion. -/
theorem exists_fordShiftedDetector_selected_finite_abel_expanded :
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
        (fordDetectorZetaLogDeriv
            (fordShiftedDetectorCenter sigma t)).re -
          (fordCotKernel eta'
            (1 - fordShiftedDetectorCenter sigma t)).re +
          ∑ rho ∈ fordShiftedDetectorPhysicalZeros
              sigma eta' (-RLower) RUpper,
            ((analyticVanishingOrder riemannZeta rho : ℂ) *
              fordCotKernel eta'
                (rho - fordShiftedDetectorCenter sigma t)).re =
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
  obtain ⟨C, hC, hselected⟩ :=
    exists_fordShiftedDetector_selected_finite_abel
  refine ⟨C, hC, ?_⟩
  intro sigma eta etaMax t T _hsigma _heta _hetaMax _hPole
    _hleftMax _ht _hT _hTlarge
  obtain ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
      habel, hremUpper, hremLower⟩ :=
    hselected _hsigma _heta _hetaMax _hPole _hleftMax
      _ht _hT _hTlarge
  refine ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
    ?_, hremUpper, hremLower⟩
  rw [← re_fordShiftedDetectorPhysicalResidueMass_expanded]
  exact habel

end

end GafniTao
