import GafniTao.FordShiftedLeftBulkBound
import RiemannZeta.GuthMaynard.ZetaBounds

/-!
# Low-height part of Ford's shifted left edge

The published proof treats the short segment where the physical ordinate is
smaller than three by Abel's continuation formula.  This file supplies that
bound with an explicit distance from the pole and then combines it with the
exponential `sech²` decay at the translated height.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem norm_riemannZeta_low_height_le
    {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hreLower : 1 / 2 ≤ s.re) (hreUpper : s.re ≤ 1 - d)
    (him : |s.im| ≤ 3) :
    ‖riemannZeta s‖ ≤ 4 / d + 8 := by
  have hrePos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  have hreAbs : |s.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hnormS : ‖s‖ ≤ 4 := by
    exact (Complex.norm_le_abs_re_add_abs_im s).trans (by linarith)
  have hden : d ≤ ‖s - 1‖ := by
    have hreSub : (s - 1).re = s.re - 1 := by simp
    have habs : d ≤ |(s - 1).re| := by
      rw [hreSub, abs_of_nonpos (by linarith)]
      linarith
    exact habs.trans (Complex.abs_re_le_norm (s - 1))
  have hdenPos : 0 < ‖s - 1‖ := lt_of_lt_of_le hd hden
  have hdiv : ‖s‖ / ‖s - 1‖ ≤ 4 / d := by
    calc
      ‖s‖ / ‖s - 1‖ ≤ 4 / ‖s - 1‖ :=
        div_le_div_of_nonneg_right hnormS hdenPos.le
      _ ≤ 4 / d := div_le_div_of_nonneg_left (by norm_num) hd hden
  have hrem : ‖abelZetaRemainder s‖ ≤ 2 := by
    calc
      ‖abelZetaRemainder s‖ ≤ 1 / s.re :=
        norm_abelZetaRemainder_le hrePos
      _ ≤ 2 := by
        rw [div_le_iff₀ hrePos]
        nlinarith
  rw [riemannZeta_eq_abel hrePos hs1]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖ ≤
        ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by
      rw [norm_div, norm_mul]
    _ ≤ 4 / d + 4 * 2 := add_le_add hdiv
      (mul_le_mul hnormS hrem (norm_nonneg _) (by norm_num))
    _ = 4 / d + 8 := by ring

theorem log_norm_riemannZeta_low_height_le
    {s : ℂ} {d : ℝ} (hd : 0 < d)
    (hreLower : 1 / 2 ≤ s.re) (hreUpper : s.re ≤ 1 - d)
    (him : |s.im| ≤ 3) :
    Real.log ‖riemannZeta s‖ ≤ Real.log (4 / d + 8) := by
  have hMPos : 0 < 4 / d + 8 := by positivity
  have hMOne : 1 ≤ 4 / d + 8 := by
    have : 0 < 4 / d := div_pos (by norm_num) hd
    linarith
  by_cases hzeta : riemannZeta s = 0
  · simp [hzeta, Real.log_nonneg hMOne]
  · exact Real.strictMonoOn_log.monotoneOn
      (norm_pos_iff.mpr hzeta) hMPos
      (norm_riemannZeta_low_height_le hd hreLower hreUpper him)

theorem one_div_cosh_sq_le_four_mul_exp_two_of_nonpos
    {u : ℝ} (hu : u ≤ 0) :
    1 / Real.cosh u ^ 2 ≤ 4 * Real.exp (2 * u) := by
  have h := one_div_cosh_sq_le_four_mul_exp_neg_two_abs u
  rw [abs_of_nonpos hu] at h
  have harg : -2 * -u = 2 * u := by ring
  rwa [harg] at h

/-- The low physical ordinate segment contributes only an exponentially
small translated-edge term. -/
theorem fordShiftedDetectorPhysicalVerticalBulk_left_low_bound
    {eta sigma t d : ℝ}
    (heta : 0 < eta) (hd : 0 < d)
    (hleftLower : 1 / 2 ≤ sigma - eta)
    (hleftUpper : sigma - eta ≤ 1 - d)
    (ht : 3 ≤ t)
    (hint : IntervalIntegrable
      (fun u : ℝ =>
        Real.log ‖riemannZeta
          (((sigma - eta : ℝ) : ℂ) +
            I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
          Real.cosh u ^ 2)
      volume
      (fordDetectorPhysicalScale eta t (-3))
      (fordDetectorPhysicalScale eta t 3)) :
    fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) (-3) 3 ≤
      (1 / (4 * eta)) *
        ((24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) *
          Real.exp (2 * fordDetectorPhysicalScale eta t 3)) := by
  let a : ℝ := fordDetectorPhysicalScale eta t (-3)
  let b : ℝ := fordDetectorPhysicalScale eta t 3
  let f : ℝ → ℝ := fun u =>
    Real.log ‖riemannZeta
      (((sigma - eta : ℝ) : ℂ) +
        I * (t + (2 * eta / Real.pi) * u : ℝ))‖ /
      Real.cosh u ^ 2
  let M : ℝ := Real.log (4 / d + 8) *
    (4 * Real.exp (2 * b))
  have hscale : 0 < 2 * eta / Real.pi :=
    div_pos (mul_pos two_pos heta) Real.pi_pos
  have hab : a ≤ b := by
    dsimp only [a, b, fordDetectorPhysicalScale]
    apply div_le_div_of_nonneg_right
    · nlinarith [Real.pi_pos]
    · positivity
  have hbNonpos : b ≤ 0 := by
    dsimp only [b, fordDetectorPhysicalScale]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [Real.pi_pos]
    · positivity
  have hlogMNonneg : 0 ≤ Real.log (4 / d + 8) := by
    have hMOne : 1 ≤ 4 / d + 8 := by
      have : 0 < 4 / d := div_pos (by norm_num) hd
      linarith
    exact Real.log_nonneg hMOne
  have hfM : ∀ u ∈ Set.Icc a b, f u ≤ M := by
    intro u hu
    have huNonpos : u ≤ 0 := hu.2.trans hbNonpos
    have hy : |t + (2 * eta / Real.pi) * u| ≤ 3 := by
      have hscaled : t + (2 * eta / Real.pi) * u ∈ Set.Icc (-3 : ℝ) 3 := by
        have hunscaleNeg := fordDetector_physicalScale_unscale
          (eta := eta) (t := t) (y := (-3 : ℝ)) heta
        have hunscalePos := fordDetector_physicalScale_unscale
          (eta := eta) (t := t) (y := (3 : ℝ)) heta
        have hscaleNonneg : 0 ≤ 2 * eta / Real.pi := hscale.le
        constructor
        · have ha := mul_le_mul_of_nonneg_left hu.1 hscaleNonneg
          dsimp only [a] at ha
          rw [← hunscaleNeg]
          convert add_le_add_left ha t using 1 <;> ring
        · have hb := mul_le_mul_of_nonneg_left hu.2 hscaleNonneg
          dsimp only [b] at hb
          rw [← hunscalePos]
          convert add_le_add_left hb t using 1 <;> ring
      exact abs_le.mpr hscaled
    have hzeta := log_norm_riemannZeta_low_height_le
      (s := (((sigma - eta : ℝ) : ℂ) +
        I * (t + (2 * eta / Real.pi) * u : ℝ))) hd
      (by simpa using hleftLower) (by simpa using hleftUpper)
      (by simpa using hy)
    have hsech := one_div_cosh_sq_le_four_mul_exp_two_of_nonpos huNonpos
    have hexpMono : Real.exp (2 * u) ≤ Real.exp (2 * b) := by
      exact Real.exp_le_exp.mpr (by linarith [hu.2])
    have hsechB : 1 / Real.cosh u ^ 2 ≤ 4 * Real.exp (2 * b) :=
      hsech.trans (mul_le_mul_of_nonneg_left hexpMono (by norm_num))
    have hcoshSq : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
    dsimp only [f, M]
    calc
      Real.log ‖riemannZeta
          (↑(sigma - eta) + I * ↑(t + 2 * eta / Real.pi * u))‖ /
          Real.cosh u ^ 2 =
        Real.log ‖riemannZeta
          (↑(sigma - eta) + I * ↑(t + 2 * eta / Real.pi * u))‖ *
          (1 / Real.cosh u ^ 2) := by ring
      _ ≤ Real.log (4 / d + 8) * (1 / Real.cosh u ^ 2) :=
        mul_le_mul_of_nonneg_right hzeta (by positivity)
      _ ≤ Real.log (4 / d + 8) * (4 * Real.exp (2 * b)) :=
        mul_le_mul_of_nonneg_left hsechB hlogMNonneg
  have hconstInt : IntervalIntegrable (fun _u : ℝ => M) volume a b :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hint hconstInt hfM
  have hlen : b - a = 6 * Real.pi / (2 * eta) := by
    dsimp only [a, b, fordDetectorPhysicalScale]
    field_simp [heta.ne', Real.pi_ne_zero]
    ring
  have hbulkEq :
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
          (-eta : ℂ) (-3) 3 =
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
  have hconstEq : (∫ _u in a..b, M) = (b - a) * M := by
    rw [intervalIntegral.integral_const]
    simp
  rw [hconstEq, hlen] at hmono
  have hcoeff : 0 ≤ 1 / (4 * eta) := by positivity
  have hMEq :
      6 * Real.pi / (2 * eta) * M =
        (24 * Real.pi / (2 * eta)) *
          Real.log (4 / d + 8) *
          Real.exp (2 * fordDetectorPhysicalScale eta t 3) := by
    dsimp only [M, b]
    ring
  rw [hMEq] at hmono
  exact mul_le_mul_of_nonneg_left hmono hcoeff

#print axioms norm_riemannZeta_low_height_le
#print axioms fordShiftedDetectorPhysicalVerticalBulk_left_low_bound

end

end GafniTao
