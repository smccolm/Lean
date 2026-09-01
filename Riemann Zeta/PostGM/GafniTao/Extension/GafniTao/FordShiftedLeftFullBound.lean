import GafniTao.FordShiftedLeftLowBound

/-!
# Complete shifted left-edge bound for Ford's detector

This file joins the two high-ordinate pieces controlled by Ford's zeta-growth
estimate to the compact low-ordinate piece controlled by Abel continuation.
The splitting is at the physical ordinates `-3` and `3`; no part of the
vertical edge is discarded.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

def fordShiftedLeftCoordinateIntegrand
    (eta sigma t : ℝ) (u : ℝ) : ℝ :=
  Real.log ‖riemannZeta
      (((sigma - eta : ℝ) : ℂ) +
        I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
    Real.cosh u ^ 2

def fordShiftedLeftHighMajorant (eta sigma t : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    (2 * (Real.log 76.2 +
      fordAffineGrowthCoefficient (sigma - eta) * Real.log t) +
    fordAffineGrowthCoefficient (sigma - eta) * fordSechLogMoment)

def fordShiftedLeftLowMajorant (eta t d : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    ((24 * Real.pi / (2 * eta)) *
      Real.log (4 / d + 8) *
      Real.exp (2 * fordDetectorPhysicalScale eta t 3))

private def fordShiftedLeftIntegrand
    (eta sigma t : ℝ) (u : ℝ) : ℝ :=
  Real.log ‖riemannZeta
      (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
        (2 * eta * u / Real.pi : ℝ) * I)‖ /
    Real.cosh u ^ 2

theorem fordShiftedDetectorPhysicalVerticalBulk_left_add
    {eta sigma t y₁ y₂ y₃ : ℝ}
    (h₁₂ : IntervalIntegrable (fordShiftedLeftIntegrand eta sigma t)
      volume
      (fordDetectorPhysicalScale eta t y₁)
      (fordDetectorPhysicalScale eta t y₂))
    (h₂₃ : IntervalIntegrable (fordShiftedLeftIntegrand eta sigma t)
      volume
      (fordDetectorPhysicalScale eta t y₂)
      (fordDetectorPhysicalScale eta t y₃)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) y₁ y₃ =
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) y₁ y₂ +
        fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) y₂ y₃ := by
  unfold fordShiftedDetectorPhysicalVerticalBulk
  change
    (1 / (4 * eta)) *
        (∫ u in fordDetectorPhysicalScale eta t y₁..
          fordDetectorPhysicalScale eta t y₃,
          fordShiftedLeftIntegrand eta sigma t u) =
      (1 / (4 * eta)) *
          (∫ u in fordDetectorPhysicalScale eta t y₁..
            fordDetectorPhysicalScale eta t y₂,
            fordShiftedLeftIntegrand eta sigma t u) +
        (1 / (4 * eta)) *
          (∫ u in fordDetectorPhysicalScale eta t y₂..
            fordDetectorPhysicalScale eta t y₃,
            fordShiftedLeftIntegrand eta sigma t u)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₁₂ h₂₃
  rw [← hadd]
  ring

private theorem fordShiftedLeftIntegrand_eq_expanded
    {eta sigma t u : ℝ} :
    fordShiftedLeftIntegrand eta sigma t u =
      Real.log ‖riemannZeta
        (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I)‖ /
        Real.cosh u ^ 2 := by
  unfold fordShiftedLeftIntegrand
  rfl

private theorem fordShiftedLeftIntegrand_eq_coordinates
    {eta sigma t u : ℝ} :
    fordShiftedLeftIntegrand eta sigma t u =
      fordShiftedLeftCoordinateIntegrand eta sigma t u := by
  unfold fordShiftedLeftIntegrand
  unfold fordShiftedLeftCoordinateIntegrand
  have hpoint :
      fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I =
        (((sigma - eta : ℝ) : ℂ) +
          I * (t + (2 * eta / Real.pi) * u : ℝ)) := by
    simp only [fordShiftedDetectorCenter]
    push_cast
    ring
  rw [hpoint]

theorem fordShiftedDetectorPhysicalVerticalBulk_left_high_bound_compact
    {eta sigma t yLower yUpper : ℝ}
    (hFord : FordZetaGrowthBound)
    (heta : 0 < eta) (hetaUpper : eta ≤ Real.pi / 4)
    (hy : yLower ≤ yUpper)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1)
    (ht : 3 ≤ t)
    (hheight : ∀ u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t yUpper),
      3 ≤ |t + (2 * eta / Real.pi) * u|)
    (hint : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t yUpper)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) yLower yUpper ≤
      fordShiftedLeftHighMajorant eta sigma t := by
  unfold fordShiftedLeftHighMajorant
  exact fordShiftedDetectorPhysicalVerticalBulk_left_high_bound
    hFord heta hetaUpper hleftLower hleftUpper ht hy hheight
      (by simpa only [fordShiftedLeftCoordinateIntegrand] using hint)

theorem fordShiftedDetectorPhysicalVerticalBulk_left_low_bound_compact
    {eta sigma t d : ℝ}
    (heta : 0 < eta) (hd : 0 < d)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1 - d)
    (ht : 3 ≤ t)
    (hint : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t (-3))
      (fordDetectorPhysicalScale eta t 3)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) (-3) 3 ≤
      fordShiftedLeftLowMajorant eta t d := by
  unfold fordShiftedLeftLowMajorant
  exact fordShiftedDetectorPhysicalVerticalBulk_left_low_bound
    heta hd hleftLower hleftUpper ht
      (by simpa only [fordShiftedLeftCoordinateIntegrand] using hint)

private theorem fordPhysicalHeight_le_neg_three
    {eta t yLower u : ℝ} (heta : 0 < eta)
    (hu : u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3))) :
    t + (2 * eta / Real.pi) * u ≤ -3 := by
  have hscale : 0 ≤ 2 * eta / Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hu.2 hscale
  have hunscale := fordDetector_physicalScale_unscale
    (eta := eta) (t := t) (y := (-3 : ℝ)) heta
  rw [← hunscale]
  convert add_le_add_left hmul t using 1 <;> ring

private theorem fordThree_le_physicalHeight
    {eta t yUpper u : ℝ} (heta : 0 < eta)
    (hu : u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper)) :
    3 ≤ t + (2 * eta / Real.pi) * u := by
  have hscale : 0 ≤ 2 * eta / Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hu.1 hscale
  have hunscale := fordDetector_physicalScale_unscale
    (eta := eta) (t := t) (y := (3 : ℝ)) heta
  rw [← hunscale]
  convert add_le_add_left hmul t using 1 <;> ring

set_option maxHeartbeats 800000 in
/-- The complete left edge, including both high-height tails and the compact
middle segment.  The hypotheses expose precisely the three interval
integrability obligations used by the adjacent-interval identities. -/
theorem fordShiftedDetectorPhysicalVerticalBulk_left_full_bound
    {eta sigma t d yLower yUpper : ℝ}
    (hFord : FordZetaGrowthBound)
    (heta : 0 < eta) (hetaUpper : eta ≤ Real.pi / 4)
    (hd : 0 < d)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1 - d)
    (ht : 3 ≤ t)
    (hyLower : yLower ≤ -3) (hyUpper : 3 ≤ yUpper)
    (hintNeg : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t)
      volume
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3)))
    (hintLow : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t)
      volume
      (fordDetectorPhysicalScale eta t (-3))
      (fordDetectorPhysicalScale eta t 3))
    (hintPos : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t)
      volume
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) yLower yUpper ≤
      2 * fordShiftedLeftHighMajorant eta sigma t +
        fordShiftedLeftLowMajorant eta t d := by
  have hnegHeight : ∀ u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3)),
      3 ≤ |t + (2 * eta / Real.pi) * u| := by
    intro u hu
    have h := fordPhysicalHeight_le_neg_three heta hu
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hposHeight : ∀ u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper),
      3 ≤ |t + (2 * eta / Real.pi) * u| := by
    intro u hu
    have h := fordThree_le_physicalHeight heta hu
    rw [abs_of_nonneg (by linarith)]
    exact h
  have hleftUpperOne : sigma - eta ≤ 1 := by linarith
  have hneg := fordShiftedDetectorPhysicalVerticalBulk_left_high_bound_compact
    hFord heta hetaUpper hyLower hleftLower hleftUpperOne ht hnegHeight
    hintNeg
  have hlow := fordShiftedDetectorPhysicalVerticalBulk_left_low_bound_compact
    heta hd hleftLower hleftUpper ht hintLow
  have hpos := fordShiftedDetectorPhysicalVerticalBulk_left_high_bound_compact
    hFord heta hetaUpper hyUpper hleftLower hleftUpperOne ht hposHeight
    hintPos
  have hintNegCenter : IntervalIntegrable
      (fordShiftedLeftIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3)) :=
    hintNeg.congr fun u _ =>
      fordShiftedLeftIntegrand_eq_coordinates.symm
  have hintLowCenter : IntervalIntegrable
      (fordShiftedLeftIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t (-3))
      (fordDetectorPhysicalScale eta t 3) :=
    hintLow.congr fun u _ =>
      fordShiftedLeftIntegrand_eq_coordinates.symm
  have hintPosCenter : IntervalIntegrable
      (fordShiftedLeftIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper) :=
    hintPos.congr fun u _ =>
      fordShiftedLeftIntegrand_eq_coordinates.symm
  have hsplitNegLow :=
    fordShiftedDetectorPhysicalVerticalBulk_left_add
      (eta := eta) (sigma := sigma) (t := t)
      (y₁ := yLower) (y₂ := -3) (y₃ := 3)
      hintNegCenter hintLowCenter
  have hsplitAll :=
    fordShiftedDetectorPhysicalVerticalBulk_left_add
      (eta := eta) (sigma := sigma) (t := t)
      (y₁ := yLower) (y₂ := 3) (y₃ := yUpper)
      (by
        apply IntervalIntegrable.trans (b := fordDetectorPhysicalScale eta t (-3))
        · exact hintNegCenter
        · exact hintLowCenter)
      hintPosCenter
  rw [hsplitAll, hsplitNegLow]
  linarith

#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_add
#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_high_bound_compact
#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_low_bound_compact
#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_full_bound

end

end GafniTao
