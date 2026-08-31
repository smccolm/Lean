import GafniTao.FordZeroDetectorSelectedPhysicalHeights

/-!
# Exponentially small Ford remainders at the selected physical heights

The majorant is the literal bound obtained from the differentiated cotangent
kernel and the normalized logarithm lift.  No unspecified `O`-term is used.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

def fordDetectorHorizontalRemainderMajorant
    (eta M y : ℝ) : ℝ :=
  ((1 / (2 * Real.pi)) *
    (16 * (Real.pi / (2 * eta)) ^ 2 *
      Real.exp (-2 * ((Real.pi / (2 * eta)) * |y|))) *
    (2 * eta * M)) * (2 * eta)

theorem norm_fordDetectorHorizontalRemainder_le_majorant
    {eta t y M : ℝ} (heta : 0 < eta) (hM : 0 ≤ M)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * |y|)
    (hL : ∀ x ∈ Set.Icc (1 - eta) (1 + eta),
      ‖fordHorizontalLogDeriv t y x‖ ≤ M) :
    ‖fordDetectorHorizontalRemainder eta t y‖ ≤
      fordDetectorHorizontalRemainderMajorant eta M y := by
  exact norm_fordDetectorHorizontalRemainder_le
    heta hM hheight hL

/-- The two independently selected physical edges, together with the exact
exponential majorants for both surviving Abel remainders. -/
theorem exists_fordDetector_good_heights_remainder_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ {eta t T : ℝ} (_heta : 0 < eta) (_hetaUpper : eta ≤ 2)
        (_ht : 0 ≤ t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * eta / Real.pi ≤ T),
      ∃ RUpper RLower : ℝ,
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (∀ x : ℝ,
          riemannZeta (fordHorizontalPoint t (RUpper - t) x) ≠ 0) ∧
        (∀ x : ℝ,
          riemannZeta (fordHorizontalPoint t (-RLower - t) x) ≠ 0) ∧
        ‖fordDetectorHorizontalRemainder eta t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordDetectorHorizontalRemainder eta t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta
            (C * Real.log T ^ 2) (-RLower - t) := by
  obtain ⟨C, hC, hselect⟩ :=
    exists_fordDetector_independent_good_heights
  refine ⟨C, hC, ?_⟩
  intro eta t T _heta _hetaUpper _ht _hT _hTlarge
  obtain ⟨RUpper, RLower, hRU, hRL, hzU, hzL, hlogU, hlogL⟩ :=
    hselect _hT
  refine ⟨RUpper, RLower, hRU, hRL, hzU, hzL, ?_, ?_⟩
  · have hscale :
        (Real.pi / (2 * eta)) * (2 * eta / Real.pi) = 1 := by
      field_simp [_heta.ne', Real.pi_ne_zero]
    have hdiff : 2 * eta / Real.pi ≤ RUpper - t := by
      linarith [hRU.1, _hTlarge]
    have hdiff0 : 0 ≤ RUpper - t := by
      have hsmall : 0 < 2 * eta / Real.pi := by positivity
      linarith
    have hheight :
        1 ≤ (Real.pi / (2 * eta)) * |RUpper - t| := by
      rw [abs_of_nonneg hdiff0, ← hscale]
      exact mul_le_mul_of_nonneg_left hdiff
        (by positivity)
    have hM : 0 ≤ C * Real.log T ^ 2 :=
      mul_nonneg hC.le (sq_nonneg _)
    apply norm_fordDetectorHorizontalRemainder_le_majorant
      _heta hM hheight
    intro x hx
    exact hlogU x (by linarith [hx.1])
  · have hscale :
        (Real.pi / (2 * eta)) * (2 * eta / Real.pi) = 1 := by
      field_simp [_heta.ne', Real.pi_ne_zero]
    have hdiff : 2 * eta / Real.pi ≤ RLower + t := by
      linarith [hRL.1, _hTlarge, _ht]
    have hneg : -RLower - t < 0 := by linarith [hRL.1, _hT]
    have hheight :
        1 ≤ (Real.pi / (2 * eta)) * |-RLower - t| := by
      rw [abs_of_neg hneg]
      rw [show -(-RLower - t) = RLower + t by ring, ← hscale]
      exact mul_le_mul_of_nonneg_left hdiff
        (by positivity)
    have hM : 0 ≤ C * Real.log T ^ 2 :=
      mul_nonneg hC.le (sq_nonneg _)
    apply norm_fordDetectorHorizontalRemainder_le_majorant
      _heta hM hheight
    intro x hx
    exact hlogL x (by linarith [hx.1])

end

end GafniTao
