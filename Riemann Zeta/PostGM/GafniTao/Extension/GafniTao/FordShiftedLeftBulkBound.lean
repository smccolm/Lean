import GafniTao.FordSechLogIntegral
import GafniTao.FordShiftedRightBulkBound

/-!
# Ford-growth bound for the shifted detector's left vertical bulk

This file connects the literal Ford zeta-growth theorem to the actual finite
left-edge integral produced by the shifted zero detector.  The only analytic
input supplied separately is interval integrability of the concrete zeta-log
integrand; the selected zero-avoiding edge derives that fact in the contour
module.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

noncomputable def fordAffineGrowthCoefficient (sigma : ℝ) : ℝ :=
  4.45 * (1 - sigma) ^ (3 / 2 : ℝ) + 2 / 3

noncomputable def fordAffineGrowthEnvelope
    (sigma t u : ℝ) : ℝ :=
  (Real.log 76.2 + fordAffineGrowthCoefficient sigma * Real.log t) *
      (1 / Real.cosh u ^ 2) +
    fordAffineGrowthCoefficient sigma *
      (Real.log (|u| + 2) / Real.cosh u ^ 2)

theorem fordAffineGrowthCoefficient_nonneg
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    0 ≤ fordAffineGrowthCoefficient sigma := by
  unfold fordAffineGrowthCoefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (sub_nonneg.mpr hsigma) _)) (by norm_num)

theorem intervalIntegrable_fordAffineGrowthEnvelope
    {sigma t a b : ℝ} :
    IntervalIntegrable (fordAffineGrowthEnvelope sigma t) volume a b := by
  have hsech : IntervalIntegrable
      (fun u : ℝ => 1 / Real.cosh u ^ 2) volume a b :=
    (continuous_const.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b
  have hlog : IntervalIntegrable
      (fun u : ℝ => Real.log (|u| + 2) / Real.cosh u ^ 2) volume a b :=
    integrable_log_abs_add_two_div_cosh_sq.intervalIntegrable
  unfold fordAffineGrowthEnvelope
  exact (hsech.const_mul
    (Real.log 76.2 + fordAffineGrowthCoefficient sigma * Real.log t)).add
      (hlog.const_mul (fordAffineGrowthCoefficient sigma))

theorem intervalIntegral_fordAffineGrowthEnvelope_eq
    {sigma t a b : ℝ} :
    (∫ u in a..b, fordAffineGrowthEnvelope sigma t u) =
      (Real.log 76.2 + fordAffineGrowthCoefficient sigma * Real.log t) *
        (∫ u in a..b, 1 / Real.cosh u ^ 2) +
      fordAffineGrowthCoefficient sigma *
        (∫ u in a..b,
          Real.log (|u| + 2) / Real.cosh u ^ 2) := by
  let C : ℝ := Real.log 76.2 +
    fordAffineGrowthCoefficient sigma * Real.log t
  let q : ℝ := fordAffineGrowthCoefficient sigma
  have hsech : IntervalIntegrable
      (fun u : ℝ => 1 / Real.cosh u ^ 2) volume a b :=
    (continuous_const.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).intervalIntegrable a b
  have hlog : IntervalIntegrable
      (fun u : ℝ => Real.log (|u| + 2) / Real.cosh u ^ 2) volume a b :=
    integrable_log_abs_add_two_div_cosh_sq.intervalIntegrable
  calc
    (∫ u in a..b, fordAffineGrowthEnvelope sigma t u) =
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

theorem intervalIntegral_fordAffineGrowthEnvelope_le
    {sigma t a b : ℝ} (hsigma : sigma ≤ 1)
    (ht : 3 ≤ t) (hab : a ≤ b) :
    (∫ u in a..b, fordAffineGrowthEnvelope sigma t u) ≤
      2 * (Real.log 76.2 +
        fordAffineGrowthCoefficient sigma * Real.log t) +
      fordAffineGrowthCoefficient sigma * fordSechLogMoment := by
  have hq : 0 ≤ fordAffineGrowthCoefficient sigma :=
    fordAffineGrowthCoefficient_nonneg hsigma
  have hlogt : 0 ≤ Real.log t :=
    Real.log_nonneg (by linarith)
  have hC : 0 ≤ Real.log 76.2 +
      fordAffineGrowthCoefficient sigma * Real.log t := by
    have hlogA : 0 ≤ Real.log 76.2 := Real.log_nonneg (by norm_num)
    positivity
  have hmass := intervalIntegral_one_div_cosh_sq_le_two (a := a) (b := b)
  have hmoment := intervalIntegral_log_abs_add_two_div_cosh_sq_le hab
  rw [intervalIntegral_fordAffineGrowthEnvelope_eq]
  have hfirst := mul_le_mul_of_nonneg_left hmass hC
  have hsecond := mul_le_mul_of_nonneg_left hmoment hq
  nlinarith

/-- Finite-interval left-edge bound in the exact physical parametrization of
the shifted detector.  It applies Ford's growth theorem at every high point
on the selected edge and records the fixed low-complexity `sech²` moment
explicitly. -/
theorem fordShiftedDetectorPhysicalVerticalBulk_left_high_bound
    (hFord : FordZetaGrowthBound)
    {eta sigma t yLower yUpper : ℝ}
    (heta : 0 < eta) (hetaUpper : eta ≤ Real.pi / 4)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1)
    (ht : 3 ≤ t) (hy : yLower ≤ yUpper)
    (hheight : ∀ u ∈ Set.Icc
        (fordDetectorPhysicalScale eta t yLower)
        (fordDetectorPhysicalScale eta t yUpper),
      3 ≤ |t + (2 * eta / Real.pi) * u|)
    (hint : IntervalIntegrable
      (fun u : ℝ =>
        Real.log ‖riemannZeta
          (((sigma - eta : ℝ) : ℂ) +
            I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
          Real.cosh u ^ 2)
      volume
      (fordDetectorPhysicalScale eta t yLower)
      (fordDetectorPhysicalScale eta t yUpper)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) yLower yUpper ≤
      (1 / (4 * eta)) *
        (2 * (Real.log 76.2 +
          fordAffineGrowthCoefficient (sigma - eta) * Real.log t) +
        fordAffineGrowthCoefficient (sigma - eta) * fordSechLogMoment) := by
  let a : ℝ := fordDetectorPhysicalScale eta t yLower
  let b : ℝ := fordDetectorPhysicalScale eta t yUpper
  let f : ℝ → ℝ := fun u =>
    Real.log ‖riemannZeta
      (((sigma - eta : ℝ) : ℂ) +
        I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
      Real.cosh u ^ 2
  let g : ℝ → ℝ := fordAffineGrowthEnvelope (sigma - eta) t
  have hab : a ≤ b := by
    dsimp only [a, b, fordDetectorPhysicalScale]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hy t) Real.pi_pos.le)
      (mul_nonneg two_pos.le heta.le)
  have hscale0 : 0 ≤ 2 * eta / Real.pi :=
    (div_pos (mul_pos two_pos heta) Real.pi_pos).le
  have hscaleUpper : 2 * eta / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  have hfg : ∀ u ∈ Set.Icc a b, f u ≤ g u := by
    intro u hu
    have hraw := log_norm_riemannZeta_affine_le_fordEnvelope hFord
      hleftLower hleftUpper ht hscale0 hscaleUpper (hheight u hu)
    have hcoshSq : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
    have hdiv := div_le_div_of_nonneg_right hraw hcoshSq.le
    dsimp only [f, g, fordAffineGrowthEnvelope,
      fordAffineGrowthCoefficient]
    simpa only [div_eq_mul_inv, mul_add, add_mul, mul_assoc,
      mul_left_comm, mul_comm, one_mul, add_assoc] using hdiv
  have hgint : IntervalIntegrable g volume a b :=
    intervalIntegrable_fordAffineGrowthEnvelope
  have hmono := intervalIntegral.integral_mono_on hab hint hgint hfg
  have henv := intervalIntegral_fordAffineGrowthEnvelope_le
    (sigma := sigma - eta) (a := a) (b := b) hleftUpper ht hab
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
            (2 * eta * u / Real.pi : ℝ) * I)‖ /
          Real.cosh u ^ 2 =
        Real.log ‖riemannZeta
          (((sigma - eta : ℝ) : ℂ) +
            I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
          Real.cosh u ^ 2
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
  have hcoeff : 0 ≤ 1 / (4 * eta) := by positivity
  exact mul_le_mul_of_nonneg_left (hmono.trans henv) hcoeff

#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_high_bound

end

end GafniTao
