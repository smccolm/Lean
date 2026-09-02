import GafniTao.FordGeneralGrowthConsumer
import GafniTao.FordShiftedLeftFullBound

/-!
# The shifted detector left edge under a general Ford bound

This is the constant-parameter version of the existing numerical left-edge
consumer.  It keeps the same physical contour, compact middle segment, and
two high-ordinate pieces.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

noncomputable def fordGeneralAffineGrowthEnvelope
    (A B sigma t u : ℝ) : ℝ :=
  (Real.log A +
      (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
      (2 / 3 : ℝ) * Real.log (Real.log t)) *
      (1 / Real.cosh u ^ 2) +
    fordGeneralAffineGrowthCoefficient B sigma *
      (Real.log (|u| + 2) / Real.cosh u ^ 2)

def fordGeneralShiftedLeftHighMajorant
    (A B eta sigma t : ℝ) : ℝ :=
  (1 / (4 * eta)) *
    (2 * (Real.log A +
      (B * (1 - (sigma - eta)) ^ (3 / 2 : ℝ)) * Real.log t +
      (2 / 3 : ℝ) * Real.log (Real.log t)) +
    fordGeneralAffineGrowthCoefficient B (sigma - eta) *
      fordSechLogMoment)

/-- The sharp general majorant is no larger than the older coarse majorant
that replaces `log log t` by `log t`. -/
theorem fordGeneralShiftedLeftHighMajorant_le_coarse
    {A B eta sigma t : ℝ} (heta : 0 < eta) (ht : 3 ≤ t) :
    fordGeneralShiftedLeftHighMajorant A B eta sigma t ≤
      (1 / (4 * eta)) *
        (2 * (Real.log A +
          fordGeneralAffineGrowthCoefficient B (sigma - eta) * Real.log t) +
        fordGeneralAffineGrowthCoefficient B (sigma - eta) *
          fordSechLogMoment) := by
  have hlogtPos : 0 < Real.log t :=
    Real.log_pos (by linarith)
  have hloglog : Real.log (Real.log t) ≤ Real.log t := by
    have h := Real.log_le_sub_one_of_pos hlogtPos
    linarith
  have hfac : 0 ≤ 1 / (4 * eta) := by positivity
  have h23 : 0 ≤ (2 / 3 : ℝ) := by norm_num
  unfold fordGeneralShiftedLeftHighMajorant
  unfold fordGeneralAffineGrowthCoefficient
  apply mul_le_mul_of_nonneg_left _ hfac
  nlinarith

theorem intervalIntegrable_fordGeneralAffineGrowthEnvelope
    {A B sigma t a b : ℝ} :
    IntervalIntegrable
      (fordGeneralAffineGrowthEnvelope A B sigma t) volume a b := by
  have hsech : IntervalIntegrable
      (fun u : ℝ => 1 / Real.cosh u ^ 2) volume a b :=
    (continuous_const.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b
  have hlog : IntervalIntegrable
      (fun u : ℝ => Real.log (|u| + 2) / Real.cosh u ^ 2) volume a b :=
    integrable_log_abs_add_two_div_cosh_sq.intervalIntegrable
  unfold fordGeneralAffineGrowthEnvelope
  exact (hsech.const_mul
    (Real.log A +
      (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
      (2 / 3 : ℝ) * Real.log (Real.log t))).add
      (hlog.const_mul (fordGeneralAffineGrowthCoefficient B sigma))

theorem intervalIntegral_fordGeneralAffineGrowthEnvelope_eq
    {A B sigma t a b : ℝ} :
    (∫ u in a..b, fordGeneralAffineGrowthEnvelope A B sigma t u) =
      (Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t)) *
        (∫ u in a..b, 1 / Real.cosh u ^ 2) +
      fordGeneralAffineGrowthCoefficient B sigma *
        (∫ u in a..b, Real.log (|u| + 2) / Real.cosh u ^ 2) := by
  let C : ℝ := Real.log A +
    (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
    (2 / 3 : ℝ) * Real.log (Real.log t)
  let q : ℝ := fordGeneralAffineGrowthCoefficient B sigma
  have hsech : IntervalIntegrable
      (fun u : ℝ => 1 / Real.cosh u ^ 2) volume a b :=
    (continuous_const.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b
  have hlog : IntervalIntegrable
      (fun u : ℝ => Real.log (|u| + 2) / Real.cosh u ^ 2) volume a b :=
    integrable_log_abs_add_two_div_cosh_sq.intervalIntegrable
  calc
    (∫ u in a..b, fordGeneralAffineGrowthEnvelope A B sigma t u) =
        ∫ u in a..b,
          C * (1 / Real.cosh u ^ 2) +
            q * (Real.log (|u| + 2) / Real.cosh u ^ 2) := by rfl
    _ = (∫ u in a..b, C * (1 / Real.cosh u ^ 2)) +
          ∫ u in a..b,
            q * (Real.log (|u| + 2) / Real.cosh u ^ 2) :=
      intervalIntegral.integral_add (hsech.const_mul C) (hlog.const_mul q)
    _ = C * (∫ u in a..b, 1 / Real.cosh u ^ 2) +
          q * (∫ u in a..b,
            Real.log (|u| + 2) / Real.cosh u ^ 2) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = _ := by rfl

theorem intervalIntegral_fordGeneralAffineGrowthEnvelope_le
    {A B sigma t a b : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hsigma : sigma ≤ 1) (ht : 3 ≤ t) (hab : a ≤ b) :
    (∫ u in a..b, fordGeneralAffineGrowthEnvelope A B sigma t u) ≤
      2 * (Real.log A +
        (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
        (2 / 3 : ℝ) * Real.log (Real.log t)) +
      fordGeneralAffineGrowthCoefficient B sigma * fordSechLogMoment := by
  have hq : 0 ≤ fordGeneralAffineGrowthCoefficient B sigma :=
    fordGeneralAffineGrowthCoefficient_nonneg hB hsigma
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hloglogt : 0 ≤ Real.log (Real.log t) := by
    apply Real.log_nonneg
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans_le (by norm_num)
    exact hlogThree.le.trans
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < t by linarith) ht)
  have hC : 0 ≤ Real.log A +
      (B * (1 - sigma) ^ (3 / 2 : ℝ)) * Real.log t +
      (2 / 3 : ℝ) * Real.log (Real.log t) := by
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
    positivity
  have hmass := intervalIntegral_one_div_cosh_sq_le_two (a := a) (b := b)
  have hmoment := intervalIntegral_log_abs_add_two_div_cosh_sq_le hab
  rw [intervalIntegral_fordGeneralAffineGrowthEnvelope_eq]
  have hfirst := mul_le_mul_of_nonneg_left hmass hC
  have hsecond := mul_le_mul_of_nonneg_left hmoment hq
  nlinarith

theorem fordShiftedDetectorPhysicalVerticalBulk_left_general_high_bound
    {A B eta sigma t yLower yUpper : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (heta : 0 < eta) (hetaUpper : eta ≤ Real.pi / 4)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1)
    (ht : 3 ≤ t) (hy : yLower ≤ yUpper)
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
      fordGeneralShiftedLeftHighMajorant A B eta sigma t := by
  let a : ℝ := fordDetectorPhysicalScale eta t yLower
  let b : ℝ := fordDetectorPhysicalScale eta t yUpper
  let f : ℝ → ℝ := fun u =>
    Real.log ‖riemannZeta
      (((sigma - eta : ℝ) : ℂ) +
        I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
      Real.cosh u ^ 2
  let g : ℝ → ℝ := fordGeneralAffineGrowthEnvelope A B (sigma - eta) t
  have hab : a ≤ b := by
    dsimp only [a, b, fordDetectorPhysicalScale]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hy t) Real.pi_pos.le)
      (mul_nonneg two_pos.le heta.le)
  have hscale0 : 0 ≤ 2 * eta / Real.pi := by positivity
  have hscaleUpper : 2 * eta / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  have hfg : ∀ u ∈ Set.Icc a b, f u ≤ g u := by
    intro u hu
    have hraw := log_norm_riemannZeta_affine_le_fordGeneralEnvelope
      hFord hA hB hleftLower hleftUpper ht hscale0 hscaleUpper
        (hheight u hu)
    have hcoshSq : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
    have hdiv := div_le_div_of_nonneg_right hraw hcoshSq.le
    dsimp only [f, g, fordGeneralAffineGrowthEnvelope]
    simpa only [div_eq_mul_inv, mul_add, add_mul, mul_assoc,
      mul_left_comm, mul_comm, one_mul, add_assoc] using hdiv
  have hgint : IntervalIntegrable g volume a b :=
    intervalIntegrable_fordGeneralAffineGrowthEnvelope
  have hmono := intervalIntegral.integral_mono_on hab hint hgint hfg
  have henv := intervalIntegral_fordGeneralAffineGrowthEnvelope_le
    (A := A) (B := B) (sigma := sigma - eta) (a := a) (b := b)
      hA hB hleftUpper ht hab
  have hbulkEq :
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) yLower yUpper =
        (1 / (4 * eta)) * ∫ u in a..b, f u := by
    unfold fordShiftedDetectorPhysicalVerticalBulk
    dsimp only [a, b, f]
    apply congrArg (fun z : ℝ => (1 / (4 * eta)) * z)
    apply intervalIntegral.integral_congr
    intro u _hu
    change
      Real.log ‖riemannZeta
          (fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I)‖ / Real.cosh u ^ 2 =
        Real.log ‖riemannZeta
          (((sigma - eta : ℝ) : ℂ) +
            I * (t + (2 * eta / Real.pi) * u : ℝ))‖ / Real.cosh u ^ 2
    have hpoint :
        fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
            (2 * eta * u / Real.pi : ℝ) * I =
          (((sigma - eta : ℝ) : ℂ) +
            I * (t + (2 * eta / Real.pi) * u : ℝ)) := by
      simp only [fordShiftedDetectorCenter]
      push_cast
      ring
    rw [hpoint]
  rw [hbulkEq]
  unfold fordGeneralShiftedLeftHighMajorant
  exact mul_le_mul_of_nonneg_left (hmono.trans henv) (by positivity)

private theorem fordGeneralPhysicalHeight_le_neg_three
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

private theorem fordGeneralThree_le_physicalHeight
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

theorem fordShiftedDetectorPhysicalVerticalBulk_left_add_coordinates
    {eta sigma t y₁ y₂ y₃ : ℝ}
    (h₁₂ : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t y₁)
      (fordDetectorPhysicalScale eta t y₂))
    (h₂₃ : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t y₂)
      (fordDetectorPhysicalScale eta t y₃)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) y₁ y₃ =
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) y₁ y₂ +
        fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) y₂ y₃ := by
  have hpoint (u : ℝ) :
      fordShiftedDetectorCenter sigma t + (-eta : ℂ) +
          (2 * eta * u / Real.pi : ℝ) * I =
        (((sigma - eta : ℝ) : ℂ) +
          I * (t + (2 * eta / Real.pi) * u : ℝ)) := by
    simp only [fordShiftedDetectorCenter]
    push_cast
    ring
  unfold fordShiftedDetectorPhysicalVerticalBulk
  simp_rw [hpoint]
  change
    (1 / (4 * eta)) *
        (∫ u in fordDetectorPhysicalScale eta t y₁..
          fordDetectorPhysicalScale eta t y₃,
          fordShiftedLeftCoordinateIntegrand eta sigma t u) =
      (1 / (4 * eta)) *
          (∫ u in fordDetectorPhysicalScale eta t y₁..
            fordDetectorPhysicalScale eta t y₂,
            fordShiftedLeftCoordinateIntegrand eta sigma t u) +
        (1 / (4 * eta)) *
          (∫ u in fordDetectorPhysicalScale eta t y₂..
            fordDetectorPhysicalScale eta t y₃,
            fordShiftedLeftCoordinateIntegrand eta sigma t u)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₁₂ h₂₃
  rw [← hadd]
  ring

set_option maxHeartbeats 800000 in
theorem fordShiftedDetectorPhysicalVerticalBulk_left_general_full_bound
    {A B eta sigma t d yLower yUpper : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (heta : 0 < eta) (hetaUpper : eta ≤ Real.pi / 4)
    (hd : 0 < d)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1 - d)
    (ht : 3 ≤ t)
    (hyLower : yLower ≤ -3) (hyUpper : 3 ≤ yUpper)
    (hintNeg : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3)))
    (hintLow : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t (-3))
      (fordDetectorPhysicalScale eta t 3))
    (hintPos : IntervalIntegrable
      (fordShiftedLeftCoordinateIntegrand eta sigma t) volume
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) yLower yUpper ≤
      2 * fordGeneralShiftedLeftHighMajorant A B eta sigma t +
        fordShiftedLeftLowMajorant eta t d := by
  have hnegHeight : ∀ u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t (-3)),
      3 ≤ |t + (2 * eta / Real.pi) * u| := by
    intro u hu
    have h := fordGeneralPhysicalHeight_le_neg_three heta hu
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hposHeight : ∀ u ∈ Set.Icc
      (fordDetectorPhysicalScale eta t 3)
      (fordDetectorPhysicalScale eta t yUpper),
      3 ≤ |t + (2 * eta / Real.pi) * u| := by
    intro u hu
    have h := fordGeneralThree_le_physicalHeight heta hu
    rw [abs_of_nonneg (by linarith)]
    exact h
  have hleftUpperOne : sigma - eta ≤ 1 := by linarith
  have hneg := fordShiftedDetectorPhysicalVerticalBulk_left_general_high_bound
    hFord hA hB heta hetaUpper hleftLower hleftUpperOne ht hyLower
      hnegHeight hintNeg
  have hlow := fordShiftedDetectorPhysicalVerticalBulk_left_low_bound_compact
    heta hd hleftLower hleftUpper ht hintLow
  have hpos := fordShiftedDetectorPhysicalVerticalBulk_left_general_high_bound
    hFord hA hB heta hetaUpper hleftLower hleftUpperOne ht hyUpper
      hposHeight hintPos
  have hsplitNegLow :=
    fordShiftedDetectorPhysicalVerticalBulk_left_add_coordinates
      (eta := eta) (sigma := sigma) (t := t)
      (y₁ := yLower) (y₂ := -3) (y₃ := 3)
      hintNeg hintLow
  have hsplitAll :=
    fordShiftedDetectorPhysicalVerticalBulk_left_add_coordinates
      (eta := eta) (sigma := sigma) (t := t)
      (y₁ := yLower) (y₂ := 3) (y₃ := yUpper)
      (by
        apply IntervalIntegrable.trans
          (b := fordDetectorPhysicalScale eta t (-3))
        · exact hintNeg
        · exact hintLow)
      hintPos
  rw [hsplitAll, hsplitNegLow]
  linarith

#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_general_high_bound
#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_general_full_bound

end

end GafniTao
