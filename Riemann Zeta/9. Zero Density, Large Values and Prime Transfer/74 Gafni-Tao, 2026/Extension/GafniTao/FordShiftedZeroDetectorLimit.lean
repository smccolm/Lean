import GafniTao.FordShiftedZeroDetectorInequality

/-!
# Uniform disappearance of the selected horizontal edges
-/

open Complex Set Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Epsilon form of the selected finite detector inequality.  The two
horizontal edges have been absorbed into the displayed epsilon, uniformly
for the nearby shift. -/
theorem eventually_exists_fordShiftedDetector_selected_subset_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma eta etaMax t : ℝ}
        (_hsigma : 1 ≤ sigma)
        (_heta : 0 < eta) (_hetaMax : eta < etaMax)
        (_hPole : sigma - 1 ≤ eta)
        (_hleftMax : -1 ≤ sigma - etaMax)
        (_ht : 0 < t),
      ∀ ε : ℝ, 0 < ε →
        ∃ T0 : ℝ, ∀ {T : ℝ}, T0 ≤ T → 8 ≤ T →
          t + 2 * etaMax / Real.pi ≤ T →
          ∃ eta' RUpper RLower : ℝ,
            eta < eta' ∧ eta' < etaMax ∧
            RUpper ∈ Set.Icc T (T + 1) ∧
            RLower ∈ Set.Icc T (T + 1) ∧
            ∀ S : Finset ℂ, S ⊆
                fordShiftedDetectorPhysicalZeros
                  sigma eta' (-RLower) RUpper →
              -(fordDetectorZetaLogDeriv
                  (fordShiftedDetectorCenter sigma t)).re <
                (∑ rho ∈ S,
                  ((analyticVanishingOrder riemannZeta rho : ℂ) *
                    fordCotKernel eta'
                      (rho - fordShiftedDetectorCenter sigma t)).re) -
                (fordCotKernel eta'
                  (1 - fordShiftedDetectorCenter sigma t)).re -
                fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
                  (eta' : ℂ) (-RLower) RUpper +
                fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
                  (-eta' : ℂ) (-RLower) RUpper + ε := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_fordShiftedDetector_selected_subset_inequality
  refine ⟨C, hC, ?_⟩
  intro sigma eta etaMax t _hsigma _heta _hetaMax _hPole
    _hleftMax _ht ε hε
  obtain ⟨T0, hsmall⟩ :=
    eventually_fordShiftedDetector_horizontal_remainder_small
      (sigma := sigma) _heta _hetaMax.le hC.le (ε / 2)
      (by linarith)
  refine ⟨T0, ?_⟩
  intro T hT0 hT hTlarge
  obtain ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
      hineq, hremUpper, hremLower⟩ :=
    hselected _hsigma _heta.le _hetaMax _hPole _hleftMax
      _ht hT hTlarge
  have htT : t ≤ T := by
    have hetaMaxPos : 0 < etaMax := _heta.trans _hetaMax
    have hterm : 0 < 2 * etaMax / Real.pi := by positivity
    linarith
  have hUpperAbs : T - t ≤ |RUpper - t| := by
    have hnonneg : 0 ≤ RUpper - t := by linarith [hRU.1]
    rw [abs_of_nonneg hnonneg]
    linarith [hRU.1]
  have hLowerAbs : T - t ≤ |-RLower - t| := by
    have hneg : -RLower - t < 0 := by
      linarith [hRL.1, hT, _ht]
    rw [abs_of_neg hneg]
    linarith [hRL.1, _ht]
  have hUpperSmall :
      ‖fordShiftedHorizontalRemainder
        sigma eta' t (RUpper - t)‖ < ε / 2 :=
    hsmall hT0 (by linarith [hT]) htT heta'.le heta'Max.le
      hUpperAbs hremUpper
  have hLowerSmall :
      ‖fordShiftedHorizontalRemainder
        sigma eta' t (-RLower - t)‖ < ε / 2 :=
    hsmall hT0 (by linarith [hT]) htT heta'.le heta'Max.le
      hLowerAbs hremLower
  refine ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL, ?_⟩
  intro S hS
  have hbase := hineq S hS
  linarith

end

end GafniTao
