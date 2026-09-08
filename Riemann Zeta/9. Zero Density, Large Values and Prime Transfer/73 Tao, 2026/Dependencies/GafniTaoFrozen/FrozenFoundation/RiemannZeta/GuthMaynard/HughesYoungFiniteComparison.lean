import RiemannZeta.GuthMaynard.HughesYoungMomentTransfer

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative transfer to the exact finite Hughes--Young rectangle

This module combines the opening-line truncation and finite-height contour
truncation.  Its right-hand arithmetic object is literally the finite
four-index rectangle decomposed by the diagonal and DFI modules.
-/

theorem exists_norm_hughesYoungSmoothedMoment_sub_finiteRect_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ C K L : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧
      ∀ {T H : ℝ} {M : ℕ},
        Real.exp 1 ≤ T → 0 ≤ H → 0 < M →
        ‖(hughesYoungSmoothedMoment T : ℂ) -
            hughesYoungFiniteRectIntegratedMoment T
              (hughesYoungSmallContour T) H M M‖ ≤
          (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
              (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
                (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) +
            (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
              ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
                ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
                (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η) * L) := by
  obtain ⟨C, K, hC, hK, hfinite⟩ :=
    exists_norm_integral_hughesYoungWholeFiniteSmallTwistedSquare_sub_finite_le
  obtain ⟨L, hL, hhigh⟩ :=
    exists_norm_integral_weight_mul_hughesYoungWholeHighTwistedTail_le
      q hq η hη0 hη
  refine ⟨C, K, L, hC, hK, hL, ?_⟩
  intro T H M hT hH hM
  let W : ℂ := ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungWholeFiniteSmallTwistedSquare T t M
  let F : ℂ := ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungFiniteSmallTwistedSquare T t H M
  let R : ℂ := ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungWholeHighTwistedTail q T t M
  have hW : W = (hughesYoungSmoothedMoment T : ℂ) - R := by
    simpa only [W, R] using
      integral_hughesYoungWholeFiniteSmallTwistedSquare_eq_smoothed_sub_highTail
        hq η hη0 hη hT hM
  have hfiniteBound := hfinite hT hH hM
  have hhighBound := hhigh hT hM
  have hF : F = hughesYoungFiniteRectIntegratedMoment T
      (hughesYoungSmallContour T) H M M := by
    simpa only [F] using
      integral_hughesYoungFiniteSmallTwistedSquare_eq_finiteRect hT H M
  have hrearr : (hughesYoungSmoothedMoment T : ℂ) = W + R := by
    rw [hW]
    ring
  rw [← hF, hrearr]
  calc
    ‖W + R - F‖ = ‖(W - F) + R‖ := by ring_nf
    _ ≤ ‖W - F‖ + ‖R‖ := norm_add_le _ _
    _ ≤
        (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) +
          (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
            ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
              (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
              hughesYoungReferenceDivisorPairMass η) * L) :=
      add_le_add (by simpa only [W, F] using hfiniteBound)
        (by simpa only [R] using hhighBound)

end RiemannZeta.GuthMaynard
