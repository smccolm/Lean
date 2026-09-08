import RiemannZeta.GuthMaynard.HughesYoungActiveComplementGlobalContour
import RiemannZeta.GuthMaynard.HughesYoungNativeMoment

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative global bound for the active product complement

This file supplies the quantitative estimates for the exact finite-rectangle
identity.  The opening-line order is deliberately chosen after epsilon; this
quantifier order is essential because the finite DFI shift family has a
fixed polynomial cost.
-/

/-- The epsilon-dependent physical radius has the extra `sqrt 2` of slack
required by the lower-boundary-removed complement. -/
theorem hughesYoungEpsilonRadius_cover_with_ratio
    {delta T : ℝ} (hT : 2 ≤ T) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) {h k : ℕ}
    (hh : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hk : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) *
            hughesYoungEpsilonRadius delta T : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
  have hbase := hughesYoungEpsilonRadius_cover hT hdelta0 hdelta1 hh hk
  have hT1 : 1 ≤ T := by linarith
  have hcut := detectorCutoff_le_three_mul T hT1
  have hrr := hughesYoungEpsilonRadius_le_two_mul_cube hT1 hdelta0 hdelta1
  have hh' : (h : ℝ) ≤ (3 * T) ^ 2 := by
    have hhcast : (h : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact hhcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have hk' : (k : ℝ) ≤ (3 * T) ^ 2 := by
    have hkcast : (k : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hkcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have hraw :
      (hughesYoungReducedLeft h k : ℝ) *
          (hughesYoungReducedRight h k : ℝ) *
            (hughesYoungEpsilonRadius delta T : ℝ) ≤
        162 * T ^ (7 : ℝ) := by
    calc
      _ ≤ ((3 * T) ^ 2) * ((3 * T) ^ 2) * (2 * T ^ (3 : ℝ)) := by
        gcongr
        · exact ha.trans hh'
        · exact hb.trans hk'
      _ = 162 * T ^ (7 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  have hratio : hughesYoungDyadicRatio ≤ 2 :=
    hughesYoungDyadicRatio_lt_two.le
  have hscaled :
      hughesYoungDyadicRatio *
          ((hughesYoungReducedLeft h k : ℝ) *
            (hughesYoungReducedRight h k : ℝ) *
              (hughesYoungEpsilonRadius delta T : ℝ)) ≤
        324 * T ^ (7 : ℝ) := by
    calc
      _ ≤ 2 * (162 * T ^ (7 : ℝ)) := by gcongr
      _ = 324 * T ^ (7 : ℝ) := by ring
  have hpow : (324 : ℝ) * T ^ (7 : ℝ) ≤ T ^ (30 : ℝ) := by
    have hcoef : (324 : ℝ) ≤ T ^ (23 : ℝ) := by
      calc
        (324 : ℝ) ≤ 2 ^ (23 : ℕ) := by norm_num
        _ ≤ T ^ (23 : ℕ) := by gcongr
        _ = T ^ (23 : ℝ) := by simp
    rw [show T ^ (30 : ℝ) = T ^ (23 : ℝ) * T ^ (7 : ℝ) by
      rw [← Real.rpow_add (by positivity)]
      norm_num]
    gcongr
  simp only [Nat.cast_mul]
  exact hscaled.trans (hpow.trans (rpow_thirty_le_globalDepth hT1))

/-- Exact cancellation of the two reduced arithmetic coordinates on an
even opening line.  This is the algebraic reason the contour order can beat
the fixed polynomial size of the finite DFI family. -/
theorem reducedProduct_evenOpening_cancel
    {a b R : ℕ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (p : ℝ) :
    (a : ℝ) ^ p * (b : ℝ) ^ p * ((a * b * R : ℕ) : ℝ) ^ (-p) =
      (R : ℝ) ^ (-p) := by
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hR0 : (0 : ℝ) ≤ R := by positivity
  push_cast
  rw [Real.mul_rpow (mul_nonneg ha0 hb0) hR0, Real.mul_rpow ha0 hb0]
  have haCancel : (a : ℝ) ^ p * (a : ℝ) ^ (-p) = 1 := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < a)]
    simp
  have hbCancel : (b : ℝ) ^ p * (b : ℝ) ^ (-p) = 1 := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < b)]
    simp
  calc
    _ = ((a : ℝ) ^ p * (a : ℝ) ^ (-p)) *
        ((b : ℝ) ^ p * (b : ℝ) ^ (-p)) * (R : ℝ) ^ (-p) := by ring
    _ = _ := by simp [haCancel, hbCancel]

/-- Arithmetic coefficient left by one positive signed shift after the two
reduced coordinates cancel against the conductor power on the opening
line. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenShiftCoefficient
    (T : ℝ) (Q h k R r : ℕ) : ℝ :=
  ‖hughesYoungLocalizedStaticScalar T h k‖ *
    (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2)) * (r : ℝ) *
    (((hughesYoungReducedLeft h k) *
      (hughesYoungReducedRight h k) : ℕ) : ℝ) *
    (2312 * max 1
        (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) + 72) *
    (hughesYoungEquation84LogBudget
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r ^ 2 *
      hughesYoungEquation84LogProfileMass)

theorem hughesYoungNonLowerActiveComplementEvenShiftCoefficient_nonneg
    (T : ℝ) (Q h k R r : ℕ) :
    0 ≤ hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q h k R r := by
  have hmass : 0 ≤ hughesYoungEquation84LogProfileMass :=
    hughesYoungEquation84LogProfileMass_pos.le
  unfold hughesYoungNonLowerActiveComplementEvenShiftCoefficient
  positivity

/-- The beta-integral loss attached to a positive signed shift grows at
most linearly in that shift.  The source exponent is only `3/4`; the
linear majorant is chosen because it composes cleanly with the finite DFI
window. -/
theorem hughesYoungComplementBetaLoss_le_fiveThousand_mul
    {r : ℕ} (hr : 0 < r) :
    2312 * max 1
        (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) + 72 ≤
      5000 * (r : ℝ) := by
  let x : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ : 1 ≤ hughesYoungDyadicRatio := by
    unfold hughesYoungDyadicRatio
    rw [Real.one_le_sqrt]
    norm_num
  have hρ0 : 0 < hughesYoungDyadicRatio := hughesYoungDyadicRatio_pos
  have hx0 : 0 < x := by
    dsimp only [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    rw [div_le_one (by positivity)]
    calc
      1 / hughesYoungDyadicRatio ≤ 1 := (div_le_one hρ0).2 hρ
      _ ≤ (r : ℝ) := by exact_mod_cast hr
  have hpow : x ^ (-(3 / 4 : ℝ)) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by norm_num)
  have hinv : x ^ (-1 : ℝ) = hughesYoungDyadicRatio * (r : ℝ) := by
    rw [Real.rpow_neg_one]
    dsimp only [x]
    field_simp
  have hρ2 : hughesYoungDyadicRatio ≤ 2 :=
    hughesYoungDyadicRatio_lt_two.le
  have hpow' : x ^ (-(3 / 4 : ℝ)) ≤ 2 * (r : ℝ) := by
    rw [hinv] at hpow
    exact hpow.trans (mul_le_mul_of_nonneg_right hρ2 hrR.le)
  have hr1 : (1 : ℝ) ≤ 2 * (r : ℝ) := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hmax : max 1 (x ^ (-(3 / 4 : ℝ))) ≤ 2 * (r : ℝ) :=
    max_le hr1 hpow'
  dsimp only [x] at hmax ⊢
  nlinarith

/-- One positive signed shift on the even line, with the Mellin ordinate
and the physical-height weight separated from the arithmetic coefficient. -/
theorem hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_profile_le_scalar
    {T : ℝ} (z : ℂ) {h k R r : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hr : 0 < r) (Q : ℕ) (t u : ℝ) :
    hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          z T t u Q h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r +
            4 * Real.log (q : ℝ)) ^ 2) ≤
      ‖z‖ *
        ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
          hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q h k R r := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let p : ℝ := 2 * (Q : ℝ) - 1 / 2
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hbudget : 1 ≤ hughesYoungEquation84LogBudget a b r :=
    one_le_hughesYoungEquation84LogBudget a b r
  have hprofile := tsum_natCast_inv_sq_mul_four_log_profile_sq_le hbudget
  have hstatic :=
    norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
      hh hk T t (2 * (Q : ℝ)) u
  have hscale :
      ‖(((a : ℕ) : ℂ) * (b : ℕ))⁻¹‖ *
          ‖hughesYoungReducedMellinScaleConstantComplex T t
            ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I) h k‖ =
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ p * (b : ℝ) ^ p *
            ‖hughesYoungRightContourWeight t (2 * Q) u‖ := by
    rw [hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour,
      norm_mul]
    calc
      _ = (‖(((a : ℕ) : ℂ) * (b : ℕ))⁻¹‖ *
            ‖hughesYoungReducedMellinStaticComplex T t h k
              ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I)‖) *
            ‖hughesYoungRightContourWeightComplex t
              ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I)‖ := by ring
      _ = ‖((((a : ℕ) : ℂ) * (b : ℕ))⁻¹ *
            hughesYoungReducedMellinStaticComplex T t h k
              ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I))‖ *
            ‖hughesYoungRightContourWeightComplex t
              ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I)‖ := by rw [norm_mul]
      _ = _ := by
        rw [hughesYoungRightContourWeightComplex_vertical]
        simpa only [a, b, p, Nat.cast_mul, Nat.cast_ofNat] using
          congrArg (fun x : ℝ => x *
            ‖hughesYoungRightContourWeight t (2 * (Q : ℝ)) u‖) hstatic
  have hcoords := reducedProduct_evenOpening_cancel ha hb hR p
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrCancel :
      (r : ℝ) ^ (2 : ℕ) * (r : ℝ) * (r : ℝ) ^ (-2 : ℝ) = (r : ℝ) := by
    rw [Real.rpow_neg hrR.le, Real.rpow_two]
    field_simp
  have hnonneg : 0 ≤
      hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
        z T t u Q h k a b R r :=
    hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_nonneg
      z T t u Q h k a b R r
  calc
    _ ≤ hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          z T t u Q h k a b R r *
        (hughesYoungEquation84LogBudget a b r ^ 2 *
          hughesYoungEquation84LogProfileMass) :=
      mul_le_mul_of_nonneg_left hprofile hnonneg
    _ = _ := by
      unfold hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
        hughesYoungNonLowerActiveComplementEvenShiftCoefficient
      simp only [a, b, p] at hscale hcoords ⊢
      calc
        _ =
            (‖(((a : ℕ) : ℂ) * (b : ℕ))⁻¹‖ *
              ‖hughesYoungReducedMellinScaleConstantComplex T t
                ((((2 * Q : ℕ) : ℝ) : ℂ) + (u : ℂ) * I) h k‖) *
            (((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) *
              ‖z‖ *
              ((a * b * R : ℕ) : ℝ) ^ (-p) * (r : ℝ) ^ (-2 : ℝ) *
              (2312 * max 1
                (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ))) + 72) *
              (hughesYoungEquation84LogBudget a b r ^ 2 *
                hughesYoungEquation84LogProfileMass)) := by
                  dsimp only [a, b, p]
                  push_cast
                  ring
        _ =
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              (a : ℝ) ^ p * (b : ℝ) ^ p *
                ‖hughesYoungRightContourWeight t (2 * Q) u‖) *
            (((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) *
              ‖z‖ *
              ((a * b * R : ℕ) : ℝ) ^ (-p) * (r : ℝ) ^ (-2 : ℝ) *
              (2312 * max 1
                (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ))) + 72) *
              (hughesYoungEquation84LogBudget a b r ^ 2 *
                hughesYoungEquation84LogProfileMass)) := by rw [hscale]
        _ =
            ‖z‖ *
              ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
              ‖hughesYoungLocalizedStaticScalar T h k‖ *
              ((a : ℝ) ^ p * (b : ℝ) ^ p *
                ((a * b * R : ℕ) : ℝ) ^ (-p)) *
              ((r : ℝ) ^ (2 : ℕ) * (r : ℝ) * (r : ℝ) ^ (-2 : ℝ)) *
              ((a * b : ℕ) : ℝ) *
              (2312 * max 1
                (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ))) + 72) *
              (hughesYoungEquation84LogBudget a b r ^ 2 *
                hughesYoungEquation84LogProfileMass) := by
                  dsimp only [a, b]
                  push_cast
                  ring
        _ = _ := by rw [hcoords, hrCancel]; ring

/-- Height-weight specialization of the scalar opening-line coefficient
bound. -/
theorem hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_profile_le
    {T : ℝ} {h k R r : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hr : 0 < r) (Q : ℕ) (t u : ℝ) :
    hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T t u Q h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r +
            4 * Real.log (q : ℝ)) ^ 2) ≤
      ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
          hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q h k R r := by
  simpa using
    hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_profile_le_scalar
      (hughesYoungHeightWeight T t : ℂ) hh hk hR hr Q t u

/-- Polynomial domination of the cancelled opening-line coefficient for one
positive shift in the literal finite DFI window.  The decisive conductor
factor is retained rather than discarded. -/
theorem hughesYoungNonLowerActiveComplementEvenShiftCoefficient_le_polynomial
    {T ell B : ℝ} {Q h k R M r : ℕ}
    (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (hMB : (M : ℝ) ≤ B) (hr : 0 < r)
    (hrM : r ≤ hughesYoungReducedLeft h k * M) :
    hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q h k R r ≤
      (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2)) *
        (5000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ)) := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let p : ℝ := 2 * (Q : ℝ) - 1 / 2
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haCast : (a : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hbCast : (b : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have haell : (a : ℝ) ≤ ell := haCast.trans hhle
  have hbell : (b : ℝ) ≤ ell := hbCast.trans hkle
  have hrCast : (r : ℝ) ≤ ell * B := by
    calc
      (r : ℝ) ≤ ((a * M : ℕ) : ℝ) := by exact_mod_cast hrM
      _ = (a : ℝ) * (M : ℝ) := by norm_cast
      _ ≤ ell * B := mul_le_mul haell hMB (by positivity) (by positivity)
  have hE : 1 ≤ ell * B := by nlinarith
  have haE : (a : ℝ) ≤ ell * B := haell.trans (by nlinarith)
  have hbE : (b : ℝ) ≤ ell * B := hbell.trans (by nlinarith)
  have hbudget := hughesYoungEquation84LogBudget_le_commonScale
    ha hb hr hE haE hbE hrCast
  have hscalar := norm_hughesYoungLocalizedStaticScalar_le_coefficients
    (T := T) hh hk
  have hdivh : ((h.divisors.card : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self h
  have hdivk : ((k.divisors.card : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self k
  have hcoeffh : ‖shortMobiusSquareCoeff T h‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hh).trans (hdivh.trans hhle)
  have hcoeffk : ‖shortMobiusSquareCoeff T k‖ ≤ ell :=
    (norm_shortMobiusSquareCoeff_le_divisors T hk).trans (hdivk.trans hkle)
  have hscalarEll : ‖hughesYoungLocalizedStaticScalar T h k‖ ≤ ell ^ (2 : ℕ) := by
    calc
      _ ≤ ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ := hscalar
      _ ≤ ell * ell := mul_le_mul hcoeffh hcoeffk (norm_nonneg _)
        (zero_le_one.trans hell)
      _ = ell ^ (2 : ℕ) := by ring
  have hab : (((a * b : ℕ) : ℝ)) ≤ ell ^ (2 : ℕ) := by
    push_cast
    calc
      (a : ℝ) * (b : ℝ) ≤ ell * ell :=
        mul_le_mul haell hbell (by positivity) (by positivity)
      _ = ell ^ (2 : ℕ) := by ring
  have hbeta := hughesYoungComplementBetaLoss_le_fiveThousand_mul hr
  have hbeta' :
      2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) + 72 ≤
        5000 * (ell * B) := hbeta.trans (by gcongr)
  have hmass := hughesYoungEquation84LogProfileMass_pos.le
  have hbudget0 : 0 ≤ hughesYoungEquation84LogBudget a b r :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hRp : 0 ≤ (R : ℝ) ^ (-p) := Real.rpow_nonneg (by positivity) _
  unfold hughesYoungNonLowerActiveComplementEvenShiftCoefficient
  dsimp only [a, b, p] at hRp ⊢
  calc
    _ ≤ ell ^ (2 : ℕ) * (R : ℝ) ^ (-p) * (ell * B) *
        ell ^ (2 : ℕ) * (5000 * (ell * B)) *
        (((5 + 4 * |Real.eulerMascheroniConstant|) * (ell * B)) ^ 2 *
          hughesYoungEquation84LogProfileMass) := by gcongr
    _ = (R : ℝ) ^ (-p) *
        (5000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ)) := by
      ring

/-- Coordinate-aware cancelled coefficient for a signed DFI shift.  The
negative branch uses the exact `h ↔ k` source symmetry. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
    (T : ℝ) (Q h k R : ℕ) : ℤ → ℝ
  | Int.ofNat n =>
      if n = 0 then 0 else
        hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q h k R n
  | Int.negSucc m =>
      hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q k h R (m + 1)

theorem hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient_nonneg
    (T : ℝ) (Q h k R : ℕ) (r : ℤ) :
    0 ≤ hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
      T Q h k R r := by
  cases r with
  | ofNat n =>
      simp only [hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient]
      split_ifs
      · exact le_rfl
      · exact hughesYoungNonLowerActiveComplementEvenShiftCoefficient_nonneg
          T Q h k R n
  | negSucc m =>
      exact hughesYoungNonLowerActiveComplementEvenShiftCoefficient_nonneg
        T Q k h R (m + 1)

set_option maxRecDepth 10000 in
/-- One nonzero signed source shift is bounded by the common physical-height
kernel and its cancelled arithmetic coefficient. -/
theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_even_le_cancelled
    {T : ℝ} {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) {r : ℤ} (hr₀ : r ≠ 0) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K r‖ ≤
      ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
          hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
            T Q h k R r := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hbase :=
    norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_even_le
      (T := T) ha hb hR hstrong hQ t u h k hr₀
  refine hbase.trans ?_
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      simpa only [hughesYoungNonLowerActiveComplementEvenSignedMajorant,
        hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient, hn.ne', if_false,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungHeightWeight_nonneg T t), a, b] using
          hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_profile_le_scalar
            (T := T) (hughesYoungHeightWeight T t : ℂ) hh hk hR hn Q t u
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hright :
          ‖hughesYoungRightContourWeight (-t) (2 * Q) u‖ =
            ‖hughesYoungRightContourWeight t (2 * Q) u‖ := by
        have heq := hughesYoungRightContourWeightComplex_neg t
          (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        rw [hughesYoungRightContourWeightComplex_vertical,
          hughesYoungRightContourWeightComplex_vertical] at heq
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg norm heq.symm
      have hswap :=
        hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor_profile_le_scalar
          (T := T) (hughesYoungHeightWeight T t : ℂ) hk hh hR hn Q (-t) u
      rw [hright] at hswap
      rw [hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k] at hswap
      change
        hughesYoungScalarNonLowerActiveComplementEvenPositivePrefactor
            (hughesYoungHeightWeight T t : ℂ) T (-t) u Q k h b a R n *
          (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
            (hughesYoungEquation84LogBudget b a n +
              4 * Real.log (q : ℝ)) ^ 2) ≤
        ‖hughesYoungHeightWeight T t‖ *
          ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
            hughesYoungNonLowerActiveComplementEvenShiftCoefficient T Q k h R n
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)] using hswap

/-- The complete finite signed source on the even opening line is bounded
by the common analytic kernel times the sum of cancelled coefficients. -/
theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le_cancelled
    {T : ℝ} {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) (t u : ℝ) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
            h k (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K‖ ≤
      ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
          (∑ r ∈ hughesYoungShiftInterval
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound (K + 1))
              (hughesYoungFullDyadicBound (K + 1)),
            hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
              T Q h k R r) := by
  classical
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        ‖(hughesYoungHeightWeight T t : ℂ) *
          (if r = 0 then 0 else
            hughesYoungNonLowerActiveComplementSignedCentralComplex
              T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                h k (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K r)‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        ‖hughesYoungHeightWeight T t‖ *
          ‖hughesYoungRightContourWeight t (2 * Q) u‖ *
            hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
              T Q h k R r := by
      apply Finset.sum_le_sum
      intro r _hr
      by_cases hr₀ : r = 0
      · subst r
        simp [hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient]
      · simp only [hr₀, if_false]
        exact
          norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_even_le_cancelled
            hh hk hR hstrong hQ t u hr₀
    _ = _ := by
      simp_rw [← Finset.mul_sum]

/-- Total cancelled signed-shift mass for one pair of mollifier indices. -/
noncomputable def hughesYoungFiniteActiveComplementEvenShiftMass
    (T : ℝ) (Q h k R K : ℕ) : ℝ :=
  ∑ r ∈ hughesYoungShiftInterval
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      (hughesYoungFullDyadicBound (K + 1))
      (hughesYoungFullDyadicBound (K + 1)),
    hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
      T Q h k R r

theorem hughesYoungFiniteActiveComplementEvenShiftMass_nonneg
    (T : ℝ) (Q h k R K : ℕ) :
    0 ≤ hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K := by
  unfold hughesYoungFiniteActiveComplementEvenShiftMass
  apply Finset.sum_nonneg
  intro r _hr
  exact hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient_nonneg
    T Q h k R r

/-- Uniform polynomial bound for the complete signed window, retaining the
opening-line conductor saving. -/
theorem hughesYoungFiniteActiveComplementEvenShiftMass_le_polynomial
    {T ell B : ℝ} {Q h k R K : ℕ}
    (hell : 1 ≤ ell) (hB : 1 ≤ B)
    (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hhle : (h : ℝ) ≤ ell) (hkle : (k : ℝ) ≤ ell)
    (hKB : (hughesYoungFullDyadicBound (K + 1) : ℝ) ≤ B) :
    hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K ≤
      (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2)) *
        (15000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungEquation84LogProfileMass * ell ^ (9 : ℕ) * B ^ (5 : ℕ)) := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let M := hughesYoungFullDyadicBound (K + 1)
  let E : ℝ := (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2)) *
    (5000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungEquation84LogProfileMass * ell ^ (8 : ℕ) * B ^ (4 : ℕ))
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haCast : (a : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hbCast : (b : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have haell : (a : ℝ) ≤ ell := haCast.trans hhle
  have hbell : (b : ℝ) ≤ ell := hbCast.trans hkle
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hmass := hughesYoungEquation84LogProfileMass_pos.le
    positivity
  have hterm : ∀ r ∈ hughesYoungShiftInterval a b M M,
      hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
        T Q h k R r ≤ E := by
    intro r hrmem
    simp only [hughesYoungShiftInterval, Finset.mem_Icc] at hrmem
    cases r with
    | ofNat n =>
        by_cases hn0 : n = 0
        · subst n
          simpa only [hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient,
            if_pos rfl] using hE
        · have hn : 0 < n := Nat.pos_of_ne_zero hn0
          have hnM : n ≤ a * M := by
            exact Int.ofNat_le.mp (by
              simpa only [Int.natCast_mul] using hrmem.2)
          simpa only [hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient,
            hn0, if_false, E, a, b, M] using
            hughesYoungNonLowerActiveComplementEvenShiftCoefficient_le_polynomial
              (T := T) (Q := Q) hell hB hh hk hR hhle hkle hKB hn hnM
    | negSucc m =>
        let n : ℕ := m + 1
        have hn : 0 < n := by dsimp only [n]; omega
        have hrEq : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
        have hnM : n ≤ b * M := by
          have hlower : (-(b * M : ℕ) : ℤ) ≤ -(n : ℤ) := by
            simpa only [hrEq] using hrmem.1
          exact_mod_cast (neg_le_neg_iff.mp hlower)
        have hswap :=
          hughesYoungNonLowerActiveComplementEvenShiftCoefficient_le_polynomial
            (T := T) (Q := Q) (h := k) (k := h) (R := R) (M := M)
            (r := n) hell hB hk hh hR hkle hhle hKB hn
            (by simpa only [hughesYoungReducedLeft_swap h k] using hnM)
        rw [hrEq]
        simpa only [hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient,
          n, E] using hswap
  have hcardEq : (hughesYoungShiftInterval a b M M).card =
      a * M + b * M + 1 := by
    unfold hughesYoungShiftInterval
    rw [Int.card_Icc]
    norm_num
    omega
  have hcard : ((hughesYoungShiftInterval a b M M).card : ℝ) ≤
      3 * ell * B := by
    rw [hcardEq]
    push_cast
    have haM : (a : ℝ) * (M : ℝ) ≤ ell * B :=
      mul_le_mul haell hKB (by positivity) (by positivity)
    have hbM : (b : ℝ) * (M : ℝ) ≤ ell * B :=
      mul_le_mul hbell hKB (by positivity) (by positivity)
    nlinarith [mul_le_mul hell hB]
  unfold hughesYoungFiniteActiveComplementEvenShiftMass
  change ∑ r ∈ hughesYoungShiftInterval a b M M,
      hughesYoungNonLowerActiveComplementEvenSignedShiftCoefficient
        T Q h k R r ≤ _
  calc
    _ ≤ ∑ _r ∈ hughesYoungShiftInterval a b M M, E :=
      Finset.sum_le_sum hterm
    _ = ((hughesYoungShiftInterval a b M M).card : ℝ) * E := by simp
    _ ≤ (3 * ell * B) * E := mul_le_mul_of_nonneg_right hcard hE
    _ = _ := by dsimp only [E]; ring

/-- Complete mollifier- and shift-index mass on the even opening line. -/
noncomputable def hughesYoungActiveComplementEvenTotalMass
    (T : ℝ) (Q R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K

theorem hughesYoungActiveComplementEvenTotalMass_nonneg
    (T : ℝ) (Q R K : ℕ) :
    0 ≤ hughesYoungActiveComplementEvenTotalMass T Q R K := by
  unfold hughesYoungActiveComplementEvenTotalMass
  apply Finset.sum_nonneg
  intro h _hh
  apply Finset.sum_nonneg
  intro k _hk
  exact hughesYoungFiniteActiveComplementEvenShiftMass_nonneg T Q h k R K

/-- The whole finite arithmetic family has fixed polynomial cost `T^522`;
the opening-line conductor factor remains outside that cost. -/
theorem hughesYoungActiveComplementEvenTotalMass_le_pow_fiveHundredTwentyTwo
    {T : ℝ} (hT : Real.exp 4 ≤ T) (Q : ℕ) {R : ℕ} (hR : 0 < R) :
    hughesYoungActiveComplementEvenTotalMass
        T Q R (hughesYoungGlobalDepth T) ≤
      (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2)) *
        ((15000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)) *
            T ^ (522 : ℕ)) := by
  let ell : ℝ := 9 * T ^ (2 : ℕ)
  let B : ℝ := 7 * T ^ (100 : ℕ)
  let P : ℝ := (R : ℝ) ^ (-(2 * (Q : ℝ) - 1 / 2))
  let E : ℝ := P *
    (15000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungEquation84LogProfileMass * ell ^ (9 : ℕ) * B ^ (5 : ℕ))
  have hT1 : 1 ≤ T := by
    have hexp : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, hexp.trans hT]
  have hTexp1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hcut := detectorCutoff_le_three_mul T hT1
  have hcutSq : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ ell := by
    dsimp only [ell]
    push_cast
    calc
      (detectorCutoff T : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = 9 * T ^ (2 : ℕ) := by ring
  have hpow2 : 1 ≤ T ^ (2 : ℕ) := one_le_pow₀ hT1
  have hpow100 : 1 ≤ T ^ (100 : ℕ) := one_le_pow₀ hT1
  have hell : 1 ≤ ell := by dsimp only [ell]; nlinarith
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith
  have hterminal :
      (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ≤ B := by
    simpa only [B] using
      hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hTexp1
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    have hmass := hughesYoungEquation84LogProfileMass_pos.le
    positivity
  have hterm : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        hughesYoungFiniteActiveComplementEvenShiftMass
          T Q h k R (hughesYoungGlobalDepth T) ≤ E := by
    intro h hhmem k hkmem
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hhCast : (h : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hhmem).2
    have hkCast : (k : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
      exact_mod_cast (Finset.mem_Icc.mp hkmem).2
    have hhle : (h : ℝ) ≤ ell := hhCast.trans hcutSq
    have hkle : (k : ℝ) ≤ ell := hkCast.trans hcutSq
    simpa only [E, P] using
      hughesYoungFiniteActiveComplementEvenShiftMass_le_polynomial
        (T := T) (Q := Q) (R := R) hell hB hh hk hR hhle hkle hterminal
  have hcardNat : (Finset.Icc 1 ((detectorCutoff T) ^ 2)).card ≤
      (detectorCutoff T) ^ 2 := by simp
  have hcardCast : ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ≤
      (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hcard : ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ≤ ell :=
    hcardCast.trans hcutSq
  unfold hughesYoungActiveComplementEvenTotalMass
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ _k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2), E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      exact hterm h hhmem k hkmem
    _ = ((Finset.Icc 1 ((detectorCutoff T) ^ 2)).card : ℝ) ^ 2 * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ell ^ (2 : ℕ) * E :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard 2) hE
    _ = _ := by dsimp only [E, P, ell, B]; ring

/-- The explicit analytic factor multiplying the Gaussian ordinate profile
on an even opening line. -/
noncomputable def hughesYoungActiveComplementEvenAnalyticFactor
    (Q : ℕ) (T : ℝ) : ℝ :=
  160000 * (2 * (Q : ℝ) + 1) ^ 8 * Real.exp (400 * (Q : ℝ) ^ 2) *
    ((7 + 2 * (Q : ℝ)) * T) ^ (4 * Q + 8)

theorem hughesYoungActiveComplementEvenAnalyticFactor_nonneg
    (Q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ hughesYoungActiveComplementEvenAnalyticFactor Q T := by
  unfold hughesYoungActiveComplementEvenAnalyticFactor
  positivity

/-- Source-uniform Gaussian bound for the completed-zeta factor on the
chosen even opening line. -/
theorem norm_hughesYoungRightContourWeight_even_le_factor_mul_gaussian
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {Q : ℕ} (hQ : 0 < Q) (u : ℝ) :
    ‖hughesYoungRightContourWeight t (2 * Q) u‖ ≤
      hughesYoungActiveComplementEvenAnalyticFactor Q T *
        hughesYoungNonLowerActiveComplementEvenGaussian Q u := by
  have hright := norm_hughesYoungRightContourWeight_even_le_on_height_support
    hT ht hQ u
  calc
    _ ≤ 160000 * (2 * (Q : ℝ) + 1) ^ 8 *
        Real.exp (400 * (Q : ℝ) ^ 2 - 84 * u ^ 2) *
        ((7 + 2 * (Q : ℝ)) * T * (1 + |u|)) ^ (4 * Q + 8) *
        (1 + |u|) ^ 8 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hright
    _ = hughesYoungActiveComplementEvenAnalyticFactor Q T *
        hughesYoungNonLowerActiveComplementEvenGaussian Q u := by
      rw [show Real.exp (400 * (Q : ℝ) ^ 2 - 84 * u ^ 2) =
          Real.exp (400 * (Q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) by
        rw [← Real.exp_add]
        congr 1
        ring,
        mul_pow]
      unfold hughesYoungActiveComplementEvenAnalyticFactor
        hughesYoungNonLowerActiveComplementEvenGaussian
      rw [show 4 * Q + 16 = (4 * Q + 8) + 8 by omega, pow_add]
      ring

/-- Total Gaussian mass of the even opening-line profile. -/
noncomputable def hughesYoungActiveComplementEvenGaussianMass (Q : ℕ) : ℝ :=
  ∫ u : ℝ, hughesYoungNonLowerActiveComplementEvenGaussian Q u

theorem hughesYoungActiveComplementEvenGaussianMass_nonneg (Q : ℕ) :
    0 ≤ hughesYoungActiveComplementEvenGaussianMass Q := by
  unfold hughesYoungActiveComplementEvenGaussianMass
  apply integral_nonneg_of_ae
  filter_upwards with u
  unfold hughesYoungNonLowerActiveComplementEvenGaussian
  positivity

/-- One mollifier pair, integrated over the full physical-height line and
the full even opening line, is bounded by its cancelled finite shift mass. -/
theorem norm_integral_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le
    {T : ℝ} (hT : 1 ≤ T) {h k R K : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) :
    ‖∫ t : ℝ, ∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K‖ ≤
      (15 * T / 4) *
        (hughesYoungActiveComplementEvenAnalyticFactor Q T *
          hughesYoungActiveComplementEvenGaussianMass Q *
          hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K) := by
  let A : ℝ := hughesYoungActiveComplementEvenAnalyticFactor Q T
  let M : ℝ := hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K
  let G : ℝ := hughesYoungActiveComplementEvenGaussianMass Q
  let C : ℝ := A * G * M
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact hughesYoungActiveComplementEvenAnalyticFactor_nonneg Q (zero_le_one.trans hT)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact hughesYoungFiniteActiveComplementEvenShiftMass_nonneg T Q h k R K
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact hughesYoungActiveComplementEvenGaussianMass_nonneg Q
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hinner (t : ℝ) :
      ‖∫ u : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementSignedSourceComplex
              T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                h k (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K‖ ≤
        (Set.Icc (T / 4) (4 * T)).indicator (fun _ : ℝ => C) t := by
    by_cases ht : t ∈ Set.Icc (T / 4) (4 * T)
    · rw [Set.indicator_of_mem ht]
      let D : ℝ := ‖hughesYoungHeightWeight T t‖ * A * M
      have hD : 0 ≤ D := by dsimp only [D]; positivity
      have hmajor : Integrable (fun u : ℝ =>
          D * hughesYoungNonLowerActiveComplementEvenGaussian Q u) :=
        (integrable_hughesYoungNonLowerActiveComplementEvenGaussian Q).const_mul D
      calc
        _ ≤ ∫ u : ℝ, D *
            hughesYoungNonLowerActiveComplementEvenGaussian Q u := by
          apply MeasureTheory.norm_integral_le_of_norm_le hmajor
          filter_upwards with u
          have hsource :=
            norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le_cancelled
              (T := T) hh hk hR hstrong hQ t u
          have hright :=
            norm_hughesYoungRightContourWeight_even_le_factor_mul_gaussian
              hT ht hQ u
          calc
            ‖(hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedSourceComplex
                  T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                    h k (hughesYoungReducedLeft h k)
                      (hughesYoungReducedRight h k) R K‖ ≤
                ‖hughesYoungHeightWeight T t‖ *
                  ‖hughesYoungRightContourWeight t (2 * Q) u‖ * M := hsource
            _ ≤ ‖hughesYoungHeightWeight T t‖ *
                  (A * hughesYoungNonLowerActiveComplementEvenGaussian Q u) * M := by
              gcongr
            _ = D * hughesYoungNonLowerActiveComplementEvenGaussian Q u := by
              dsimp only [D]
              ring
        _ = ‖hughesYoungHeightWeight T t‖ * A * M * G := by
          rw [MeasureTheory.integral_const_mul]
          rfl
        _ ≤ C := by
          have hw := hughesYoungHeightWeight_le_one T t
          have hw0 := hughesYoungHeightWeight_nonneg T t
          rw [Real.norm_eq_abs, abs_of_nonneg hw0]
          dsimp only [C]
          nlinarith [mul_nonneg hA hG, hM]
    · have hind :
          (Set.Icc (T / 4) (4 * T)).indicator (fun _ : ℝ => C) t = 0 := by
          simp [Set.indicator, ht]
      rw [hind]
      have hw : hughesYoungHeightWeight T t = 0 := by
        by_contra hwne
        exact ht (hughesYoungHeightWeight_support hT0 hwne)
      simp [hw]
  have hmajorOuter : Integrable
      ((Set.Icc (T / 4) (4 * T)).indicator (fun _ : ℝ => C)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  calc
    _ ≤ ∫ t : ℝ, (Set.Icc (T / 4) (4 * T)).indicator
        (fun _ : ℝ => C) t := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajorOuter
      exact Filter.Eventually.of_forall hinner
    _ = (15 * T / 4) * C := by
      rw [show (∫ t : ℝ, (Set.Icc (T / 4) (4 * T)).indicator
          (fun _ : ℝ => C) t) = ∫ _t in Set.Icc (T / 4) (4 * T), C by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 4 * T - T / 4)]
      ring
    _ = _ := by dsimp only [C, A, G, M]

/-- The complete mollifier-weighted complement on the literal whole even
opening line.  Both integrals and both arithmetic sums are the source
objects; the definition contains no estimate. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenOpeningWhole
    (Q : ℕ) (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
              h k (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K

/-- The pairwise cancellation estimate summed over the actual mollifier
range. -/
theorem norm_hughesYoungNonLowerActiveComplementEvenOpeningWhole_le
    {T : ℝ} (hT : Real.exp 4 ≤ T) {R K : ℕ} (hR : 0 < R)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        hughesYoungDyadicRatio *
            (((hughesYoungReducedLeft h k) *
              (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
          hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) :
    ‖hughesYoungNonLowerActiveComplementEvenOpeningWhole Q T R K‖ ≤
      (15 * T / 4) *
        (hughesYoungActiveComplementEvenAnalyticFactor Q T *
          hughesYoungActiveComplementEvenGaussianMass Q *
          hughesYoungActiveComplementEvenTotalMass T Q R K) := by
  have hT1 : 1 ≤ T := by
    have h14 : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h14.trans hT]
  unfold hughesYoungNonLowerActiveComplementEvenOpeningWhole
    hughesYoungActiveComplementEvenTotalMass
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖∫ t : ℝ, ∫ u : ℝ,
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedSourceComplex
                T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
                  h k (hughesYoungReducedLeft h k)
                    (hughesYoungReducedRight h k) R K‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _hh =>
        (norm_sum_le _ _))
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (15 * T / 4) *
            (hughesYoungActiveComplementEvenAnalyticFactor Q T *
              hughesYoungActiveComplementEvenGaussianMass Q *
              hughesYoungFiniteActiveComplementEvenShiftMass T Q h k R K) := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
      have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
      exact
        norm_integral_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_even_le
          hT1 hh hk hR (hcover h hhmem k hkmem) hQ
    _ = _ := by
      simp only [Finset.mul_sum]

/-- At the conductor radius, order `60000` supplies more than the exact
`T^120531` needed to cancel the physical-height, completed-zeta, and finite
arithmetic costs. -/
theorem hughesYoungConductorRadius_evenOpening_rpow_le
    {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungConductorRadius T : ℝ) ^
        (-(2 * (30000 : ℝ) - 1 / 2)) ≤
      T ^ (-120531 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hbase : T ^ (201 / 100 : ℝ) ≤
      (hughesYoungConductorRadius T : ℝ) :=
    hughesYoungConductorRadius_lower T
  calc
    (hughesYoungConductorRadius T : ℝ) ^
          (-(2 * (30000 : ℝ) - 1 / 2)) ≤
        (T ^ (201 / 100 : ℝ)) ^
          (-(2 * (30000 : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hT0 _) hbase (by norm_num)
    _ = T ^ ((201 / 100 : ℝ) *
          (-(2 * (30000 : ℝ) - 1 / 2))) := by
      rw [Real.rpow_mul hT0.le]
    _ ≤ T ^ (-120531 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      norm_num

/-- The whole even-line complement is uniformly bounded at the conductor
radius.  This is stronger than the `T^(1+ε)` estimate ultimately consumed
by the Hughes--Young moment. -/
theorem exists_norm_hughesYoungConductorNonLowerActiveComplementEvenOpeningWhole_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 4 ≤ T →
      ‖hughesYoungNonLowerActiveComplementEvenOpeningWhole
          30000 T (hughesYoungConductorRadius T)
            (hughesYoungGlobalDepth T)‖ ≤ C := by
  let A₀ : ℝ := 160000 * (60001 : ℝ) ^ (8 : ℕ) *
    Real.exp (400 * (30000 : ℝ) ^ 2) * (60007 : ℝ) ^ (120008 : ℕ)
  let B₀ : ℝ :=
    15000 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
      hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)
  let G : ℝ := hughesYoungActiveComplementEvenGaussianMass 30000
  let C : ℝ := (15 / 4) * A₀ * (G + 1) * B₀
  have hA₀ : 0 < A₀ := by
    dsimp only [A₀]
    positivity
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀]
    have hmass := hughesYoungEquation84LogProfileMass_pos
    positivity
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact hughesYoungActiveComplementEvenGaussianMass_nonneg 30000
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by
    have h14 : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h14.trans hT]
  have hT2 : 2 ≤ T := by
    have h24 : Real.exp 2 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    have he2 : 3 < Real.exp 2 := by
      calc
        (3 : ℝ) = 2 + 1 := by norm_num
        _ < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
    linarith [h24.trans hT]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hwhole :=
    norm_hughesYoungNonLowerActiveComplementEvenOpeningWhole_le
      hT hR (fun h hh k hk => hughesYoungConductor_cover_with_ratio hT2 hh hk)
        (Q := 30000) (by norm_num)
  have hmass :=
    hughesYoungActiveComplementEvenTotalMass_le_pow_fiveHundredTwentyTwo
      hT 30000 hR
  have hradius := hughesYoungConductorRadius_evenOpening_rpow_le hT1
  have hAeq :
      hughesYoungActiveComplementEvenAnalyticFactor 30000 T =
        A₀ * T ^ (120008 : ℕ) := by
    unfold hughesYoungActiveComplementEvenAnalyticFactor
    dsimp only [A₀]
    norm_num1
    rw [mul_pow]
    ac_rfl
  have hcollapse :
      T * T ^ (120008 : ℕ) * T ^ (522 : ℕ) *
          T ^ (-120531 : ℝ) = 1 := by
    have hpos : T * T ^ (120008 : ℕ) * T ^ (522 : ℕ) =
        T ^ (120531 : ℕ) := by
      calc
        _ = T ^ (1 : ℕ) * T ^ (120008 : ℕ) * T ^ (522 : ℕ) := by
          rw [pow_one]
        _ = T ^ ((1 : ℕ) + 120008 + 522) := by
          rw [pow_add, pow_add]
        _ = T ^ (120531 : ℕ) := by norm_num
    calc
      _ = T ^ (120531 : ℕ) * T ^ (-120531 : ℝ) := by rw [hpos]
      _ = T ^ (120531 : ℝ) * T ^ (-120531 : ℝ) := by
        exact congrArg (fun x : ℝ => x * T ^ (-120531 : ℝ))
          (Real.rpow_natCast T 120531).symm
      _ = T ^ ((120531 : ℝ) + (-120531 : ℝ)) :=
        (Real.rpow_add hT0 120531 (-120531)).symm
      _ = 1 := by norm_num
  calc
    _ ≤ (15 * T / 4) *
        (hughesYoungActiveComplementEvenAnalyticFactor 30000 T *
          hughesYoungActiveComplementEvenGaussianMass 30000 *
          hughesYoungActiveComplementEvenTotalMass T 30000
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)) := hwhole
    _ ≤ (15 * T / 4) *
        ((A₀ * T ^ (120008 : ℕ)) * (G + 1) *
          (((hughesYoungConductorRadius T : ℝ) ^
              (-(2 * (30000 : ℝ) - 1 / 2))) *
            (B₀ * T ^ (522 : ℕ)))) := by
      rw [hAeq]
      dsimp only [G, B₀]
      gcongr
      · exact hughesYoungActiveComplementEvenTotalMass_nonneg T 30000
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
      · linarith [hG]
      · simpa only using hmass
    _ ≤ (15 * T / 4) *
        ((A₀ * T ^ (120008 : ℕ)) * (G + 1) *
          (T ^ (-120531 : ℝ) * (B₀ * T ^ (522 : ℕ)))) := by
      gcongr
    _ = C := by
      calc
        _ = C * (T * T ^ (120008 : ℕ) * T ^ (522 : ℕ) *
            T ^ (-120531 : ℝ)) := by
          dsimp only [C]
          rw [show (15 * T / 4) = (15 / 4) * T by ring]
          ac_rfl
        _ = C := by rw [hcollapse, mul_one]

/-- The complete even opening-line complement has the native
Hughes--Young `T^(1+ε)` strength. -/
theorem hughesYoungConductorNonLowerActiveComplementEvenOpeningWhole_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungNonLowerActiveComplementEvenOpeningWhole
        30000 T (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungConductorNonLowerActiveComplementEvenOpeningWhole_le
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (Real.exp 4)] with T hT
  have hT1 : 1 ≤ T := by
    have h14 : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h14.trans hT]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hpow : 1 ≤ T ^ (1 + ε) :=
    Real.one_le_rpow hT1 (by linarith)
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  conv_lhs =>
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (norm_nonneg _)]
  rw [htarget]
  calc
    _ ≤ C := hbound hT
    _ = C * 1 := by ring
    _ ≤ C * T ^ (1 + ε) := mul_le_mul_of_nonneg_left hpow hC.le

end RiemannZeta.GuthMaynard
