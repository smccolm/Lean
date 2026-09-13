import Tao2026.BadIntervalLargePrimeErrorSource

/-!
# Power normalization of the large-prime source errors

This module absorbs fixed constants and logarithmic powers in the explicit
source envelopes.  It then compares those `z`-power savings with the dyadic
modulus selectors occurring in Propositions 6.7 and 6.8.
-/

namespace Tao2026

open Filter Topology

noncomputable section

set_option maxRecDepth 10000

/-- A fixed power of `z` absorbs any fixed nonnegative multiple of a fixed
real logarithmic power. -/
theorem eventually_const_mul_log_rpow_taoZ_div_rpow_le
    {C k a b : ℝ} (hC : 0 ≤ C) (hgap : b < a) :
    ∀ᶠ x : ℕ in atTop,
      C * Real.log (taoZ x) ^ k / (taoZ x) ^ a ≤
        1 / (taoZ x) ^ b := by
  have hgapPos : 0 < a - b := sub_pos.mpr hgap
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop k hgapPos).const_mul_left C
  have hdenPositive : ∀ᶠ z : ℝ in atTop,
      0 < ‖z ^ (a - b)‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz _)]
    exact Real.rpow_pos_of_pos hz _
  have hreal : ∀ᶠ z : ℝ in atTop,
      C * Real.log z ^ k ≤ z ^ (a - b) := by
    filter_upwards
      [hsmall.eventuallyLT_norm_of_eventually_pos hdenPositive,
        eventually_ge_atTop (1 : ℝ)] with z hzSmall hzOne
    have hzPos : 0 < z := zero_lt_one.trans_le hzOne
    have hlogNonneg : 0 ≤ Real.log z := Real.log_nonneg hzOne
    have hleftNonneg : 0 ≤ C * Real.log z ^ k :=
      mul_nonneg hC (Real.rpow_nonneg hlogNonneg _)
    rw [Real.norm_of_nonneg hleftNonneg, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hzPos _)] at hzSmall
    exact hzSmall.le
  filter_upwards [tendsto_taoZ_atTop.eventually hreal] with x hx
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hza : 0 < (taoZ x) ^ a := Real.rpow_pos_of_pos hzPos _
  have hzb : 0 < (taoZ x) ^ b := Real.rpow_pos_of_pos hzPos _
  apply (div_le_div_iff₀ hza hzb).2
  calc
    (C * Real.log (taoZ x) ^ k) * (taoZ x) ^ b ≤
        (taoZ x) ^ (a - b) * (taoZ x) ^ b :=
      mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hzPos.le _)
    _ = 1 * (taoZ x) ^ a := by
      rw [one_mul, ← Real.rpow_add hzPos]
      exact congrArg (fun t : ℝ => (taoZ x) ^ t) (by ring)

/-- The complete reciprocal-band envelope saves `z^(4/5)`. -/
theorem eventually_taoLargePrimeSourceBandReciprocalEnvelope_le_rpow :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceBandReciprocalEnvelope x ≤
        (taoZ x) ^ (-(4 / 5 : ℝ)) := by
  have h := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := (4004 : ℝ)) (k := (1 : ℝ)) (a := (9 / 10 : ℝ))
      (b := (4 / 5 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [h] with x hx
  have hzPos := taoZ_pos x
  rw [Real.rpow_one] at hx
  rw [taoLargePrimeSourceBandReciprocalEnvelope]
  have hx' : 1001 * (4 * Real.log (taoZ x) /
      (taoZ x) ^ (9 / 10 : ℝ)) ≤
      1 / (taoZ x) ^ (4 / 5 : ℝ) := by
    calc
      1001 * (4 * Real.log (taoZ x) /
          (taoZ x) ^ (9 / 10 : ℝ)) =
          4004 * Real.log (taoZ x) /
            (taoZ x) ^ (9 / 10 : ℝ) := by ring
      _ ≤ 1 / (taoZ x) ^ (4 / 5 : ℝ) := hx
  simpa only [Real.rpow_neg hzPos.le, one_div] using hx'

/-- The complete eighth-power envelope saves `z^7`. -/
theorem eventually_taoLargePrimeSourceEighthPowerEnvelope_le_rpow :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceEighthPowerEnvelope x ≤
        (taoZ x) ^ (-(7 : ℝ)) := by
  have h := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := (1000 : ℝ)) (k := (0 : ℝ)) (a := (36 / 5 : ℝ))
      (b := (7 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [h] with x hx
  have hzPos := taoZ_pos x
  rw [Real.rpow_zero] at hx
  rw [taoLargePrimeSourceEighthPowerEnvelope]
  rw [show ((taoZ x) ^ (9 / 10 : ℝ)) ^ (-(8 : ℝ)) =
      ((taoZ x) ^ (36 / 5 : ℝ))⁻¹ by
    rw [← Real.rpow_mul hzPos.le]
    norm_num
    rw [Real.rpow_neg hzPos.le]]
  simpa only [Real.rpow_neg hzPos.le, one_div, div_eq_mul_inv,
    one_mul, mul_one] using hx

/-- The 1000th-power change-level envelope has far more than the `z^7`
saving needed by the two-prime error. -/
theorem eventually_taoLargePrimeSourceChangeLevelEnvelope_le_rpow :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceChangeLevelEnvelope x ≤
        (taoZ x) ^ (-(7 : ℝ)) := by
  have h := eventually_const_mul_log_rpow_taoZ_div_rpow_le
    (C := (1000 : ℝ) * (16 : ℝ) ^ (1000 : ℕ))
      (k := (1000 : ℝ)) (a := (900 : ℝ)) (b := (7 : ℝ))
      (by positivity) (by norm_num)
  filter_upwards [h] with x hx
  have hzPos := taoZ_pos x
  rw [taoLargePrimeSourceChangeLevelEnvelope]
  have hden : ((taoZ x) ^ (9 / 10 : ℝ)) ^ (1000 : ℕ) =
      (taoZ x) ^ (900 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hzPos.le]
    norm_num
  have hlog : Real.log (taoZ x) ^ (1000 : ℕ) =
      Real.log (taoZ x) ^ ((1000 : ℕ) : ℝ) :=
    (Real.rpow_natCast (Real.log (taoZ x)) 1000).symm
  have hx' : ((1000 : ℝ) * (16 : ℝ) ^ (1000 : ℕ)) *
      Real.log (taoZ x) ^ (1000 : ℕ) /
        (taoZ x) ^ (900 : ℝ) ≤
      1 / (taoZ x) ^ (7 : ℝ) := by
    calc
      ((1000 : ℝ) * (16 : ℝ) ^ (1000 : ℕ)) *
          Real.log (taoZ x) ^ (1000 : ℕ) /
            (taoZ x) ^ (900 : ℝ) =
          ((1000 : ℝ) * (16 : ℝ) ^ (1000 : ℕ)) *
            Real.log (taoZ x) ^ (1000 : ℝ) /
              (taoZ x) ^ (900 : ℝ) :=
        congrArg (fun t : ℝ =>
          ((1000 : ℝ) * (16 : ℝ) ^ (1000 : ℕ)) * t /
            (taoZ x) ^ (900 : ℝ)) hlog
      _ ≤ 1 / (taoZ x) ^ (7 : ℝ) := hx
  rw [div_pow, mul_pow, hden]
  simpa only [Real.rpow_neg hzPos.le, one_div,
    div_eq_mul_inv, one_mul, mul_assoc] using hx'

/-- A dyadic modulus selector in the source large-prime range, with harmless
fixed power margins around `z^(1/100) ≪ R ≪ z^(1+o(1))`. -/
structure TaoLargePrimeSourceBandSelector (R : ℕ → ℕ) : Prop where
  lower : ∀ᶠ x : ℕ in atTop,
    (taoZ x) ^ (1 / 200 : ℝ) ≤ (R x : ℝ)
  upper : ∀ᶠ x : ℕ in atTop,
    (R x : ℝ) ≤ (taoZ x) ^ (11 / 10 : ℝ)

theorem TaoLargePrimeSourceBandSelector.eventually_two_le
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R) :
    ∀ᶠ x : ℕ in atTop, 2 ≤ R x := by
  have hpowTop : Tendsto (fun z : ℝ => z ^ (1 / 200 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [hR.lower,
    (hpowTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with x hlower htwo
  exact_mod_cast hlower.trans' htwo

private theorem taoZ_rpow_neg_four_fifths_le_selector
    {x R : ℕ} (hz : 1 ≤ taoZ x) (hR : 0 < R)
    (hupper : (R : ℝ) ≤ (taoZ x) ^ (11 / 10 : ℝ)) :
    (taoZ x) ^ (-(4 / 5 : ℝ)) ≤ (R : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hzPos : 0 < taoZ x := taoZ_pos x
  calc
    (taoZ x) ^ (-(4 / 5 : ℝ)) ≤
        (taoZ x) ^ (-(11 / 10000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
    _ = ((taoZ x) ^ (11 / 10 : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
      rw [← Real.rpow_mul hzPos.le]
      congr 1
      norm_num
    _ ≤ (R : ℝ) ^ (-(1 / 1000 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hR) hupper (by norm_num)

private theorem taoZ_rpow_neg_seven_le_selector
    {x R : ℕ} (hz : 1 ≤ taoZ x) (hR : 0 < R)
    (hupper : (R : ℝ) ≤ (taoZ x) ^ (11 / 10 : ℝ)) :
    (taoZ x) ^ (-(7 : ℝ)) ≤ (R : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
  have hzPos : 0 < taoZ x := taoZ_pos x
  calc
    (taoZ x) ^ (-(7 : ℝ)) ≤
        (taoZ x) ^ (-(11011 / 10000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
    _ = ((taoZ x) ^ (11 / 10 : ℝ)) ^ (-(1001 / 1000 : ℝ)) := by
      rw [← Real.rpow_mul hzPos.le]
      congr 1
      norm_num
    _ ≤ (R : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hR) hupper (by norm_num)

/-- Source power form of Proposition 6.7(ii)'s uniform improved error
envelope.  The fixed factor three is an explicit `O(1)` witness. -/
theorem eventually_taoLargePrimeSourceSingleErrorEnvelope_le_power
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R) :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceSingleErrorEnvelope x (R x) ≤
        3 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeSourceBandReciprocalEnvelope_le_rpow,
    eventually_taoLargePrimeSourceEighthPowerEnvelope_le_rpow,
    hR.upper, hR.eventually_two_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hU hV hupper hRtwo hz
  have hRpos : 0 < R x := by omega
  have hU' : taoLargePrimeSourceBandReciprocalEnvelope x ≤
      (R x : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    hU.trans (taoZ_rpow_neg_four_fifths_le_selector hz hRpos hupper)
  have hV' : taoLargePrimeSourceEighthPowerEnvelope x ≤
      (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    hV.trans (taoZ_rpow_neg_seven_le_selector hz hRpos hupper)
  have hfirst : 2 / (R x : ℝ) *
      taoLargePrimeSourceBandReciprocalEnvelope x ≤
      2 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
    calc
      2 / (R x : ℝ) * taoLargePrimeSourceBandReciprocalEnvelope x ≤
          2 / (R x : ℝ) * (R x : ℝ) ^ (-(1 / 1000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hU' (by positivity)
      _ = 2 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
        have hRreal : (0 : ℝ) < R x := by exact_mod_cast hRpos
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        rw [show 2 * (R x : ℝ) ^ (-1 : ℝ) *
            (R x : ℝ) ^ (-(1 / 1000 : ℝ)) =
            2 * ((R x : ℝ) ^ (-1 : ℝ) *
              (R x : ℝ) ^ (-(1 / 1000 : ℝ))) by ring]
        rw [← Real.rpow_add hRreal]
        congr 1
        norm_num
  rw [taoLargePrimeSourceSingleErrorEnvelope]
  nlinarith [hfirst, hV']

private theorem taoZ_rpow_neg_seven_le_selector_product
    {x R S : ℕ} (hz : 1 ≤ taoZ x) (hR : 0 < R) (hS : 0 < S)
    (hRupper : (R : ℝ) ≤ (taoZ x) ^ (11 / 10 : ℝ))
    (hSupper : (S : ℝ) ≤ (taoZ x) ^ (11 / 10 : ℝ)) :
    (taoZ x) ^ (-(7 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := by
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hRcomp : ((taoZ x) ^ (11 / 10 : ℝ)) ^
      (-(1001 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hRreal hRupper (by norm_num)
  have hScomp : ((taoZ x) ^ (11 / 10 : ℝ)) ^ (-(1 : ℝ)) ≤
      (S : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hSreal hSupper (by norm_num)
  have hprod := mul_le_mul hRcomp hScomp
    (Real.rpow_nonneg (Real.rpow_nonneg hzPos.le _) _)
    (Real.rpow_nonneg hRreal.le _)
  calc
    (taoZ x) ^ (-(7 : ℝ)) ≤
        (taoZ x) ^ (-(22011 / 10000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
    _ = ((taoZ x) ^ (11 / 10 : ℝ)) ^
          (-(1001 / 1000 : ℝ)) *
        ((taoZ x) ^ (11 / 10 : ℝ)) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add (Real.rpow_pos_of_pos hzPos _)]
      rw [← Real.rpow_mul hzPos.le]
      congr 1
      norm_num
    _ ≤ (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := hprod

/-- An explicit constant witnessing the source `O(R^-1.001 S^-1)` joint
error. -/
def taoLargePrimeSourceJointPowerConstant : ℝ :=
  8 + 5 * (2 : ℝ) ^ (999 : ℕ)

/-- Source power form of Proposition 6.8(ii)'s joint improved error envelope.
The smaller band is placed in the `1.001` exponent. -/
theorem eventually_taoLargePrimeSourceJointErrorEnvelope_le_power
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S) :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceJointErrorEnvelope x (R x) (S x) ≤
        taoLargePrimeSourceJointPowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeSourceBandReciprocalEnvelope_le_rpow,
    eventually_taoLargePrimeSourceEighthPowerEnvelope_le_rpow,
    eventually_taoLargePrimeSourceChangeLevelEnvelope_le_rpow,
    hR.upper, hS.upper, hR.eventually_two_le, hS.eventually_two_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hU hV hW hRupper hSupper hRtwo hStwo hz
  have hRpos : 0 < R x := by omega
  have hSpos : 0 < S x := by omega
  have hRreal : (0 : ℝ) < R x := by exact_mod_cast hRpos
  have hSreal : (0 : ℝ) < S x := by exact_mod_cast hSpos
  let T : ℝ := (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
    (S x : ℝ) ^ (-(1 : ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU' : taoLargePrimeSourceBandReciprocalEnvelope x ≤
      (R x : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    hU.trans (taoZ_rpow_neg_four_fifths_le_selector hz hRpos hRupper)
  have hVWTarget : (taoZ x) ^ (-(7 : ℝ)) ≤ T := by
    exact taoZ_rpow_neg_seven_le_selector_product
      hz hRpos hSpos hRupper hSupper
  have hV' : taoLargePrimeSourceEighthPowerEnvelope x ≤ T :=
    hV.trans hVWTarget
  have hW' : taoLargePrimeSourceChangeLevelEnvelope x ≤ T :=
    hW.trans hVWTarget
  have hfirst : (4 / ((R x : ℝ) * (S x : ℝ))) *
      (2 * taoLargePrimeSourceBandReciprocalEnvelope x) ≤ 8 * T := by
    calc
      (4 / ((R x : ℝ) * (S x : ℝ))) *
          (2 * taoLargePrimeSourceBandReciprocalEnvelope x) ≤
        (4 / ((R x : ℝ) * (S x : ℝ))) *
          (2 * (R x : ℝ) ^ (-(1 / 1000 : ℝ))) := by
            gcongr
      _ = 8 * T := by
        dsimp [T]
        rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_neg_one]
        rw [show 4 * ((R x : ℝ) ^ (-1 : ℝ) *
              (S x : ℝ) ^ (-1 : ℝ)) *
              (2 * (R x : ℝ) ^ (-(1 / 1000 : ℝ))) =
            8 * ((R x : ℝ) ^ (-1 : ℝ) *
              (R x : ℝ) ^ (-(1 / 1000 : ℝ))) *
              (S x : ℝ) ^ (-1 : ℝ) by ring]
        rw [← Real.rpow_add hRreal]
        rw [show (-1 : ℝ) + -(1 / 1000 : ℝ) =
          -(1001 / 1000 : ℝ) by norm_num]
        ring
  let c : ℝ := (2 : ℝ) ^ (999 : ℕ)
  have hsecond : c *
      (4 * taoLargePrimeSourceEighthPowerEnvelope x +
        taoLargePrimeSourceChangeLevelEnvelope x) ≤ c * (5 * T) := by
    apply mul_le_mul_of_nonneg_left _ (by dsimp [c]; positivity)
    nlinarith
  rw [taoLargePrimeSourceJointErrorEnvelope]
  calc
    _ ≤ 8 * T + c * (5 * T) := add_le_add hfirst hsecond
    _ = taoLargePrimeSourceJointPowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
      have hc : taoLargePrimeSourceJointPowerConstant = 8 + 5 * c := rfl
      have hfactor (a b : ℝ) : 8 * b + a * (5 * b) = (8 + 5 * a) * b := by
        ring
      have hassoc (a b d : ℝ) : (8 + 5 * a) * (b * d) =
          (8 + 5 * a) * b * d := by
        ring
      rw [hc]
      calc
        8 * T + c * (5 * T) = (8 + 5 * c) * T := hfactor c T
        _ = (8 + 5 * c) *
              (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
              (S x : ℝ) ^ (-(1 : ℝ)) := by
          exact hassoc c _ _

private theorem selector_cross_power_le
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) :
    (R : ℝ) ^ (-(1 : ℝ)) *
        (S : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hRSreal : (R : ℝ) ≤ S := by exact_mod_cast hRS
  have hdelta : (S : ℝ) ^ (-(1 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hRreal hRSreal (by norm_num)
  have hRsplit : (R : ℝ) ^ (-(1001 / 1000 : ℝ)) =
      (R : ℝ) ^ (-(1 : ℝ)) *
        (R : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hRreal]
    congr 1
    norm_num
  have hSsplit : (S : ℝ) ^ (-(1001 / 1000 : ℝ)) =
      (S : ℝ) ^ (-(1 : ℝ)) *
        (S : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hSreal]
    congr 1
    norm_num
  rw [hRsplit, hSsplit]
  calc
    (R : ℝ) ^ (-(1 : ℝ)) *
        ((S : ℝ) ^ (-(1 : ℝ)) *
          (S : ℝ) ^ (-(1 / 1000 : ℝ))) =
      ((R : ℝ) ^ (-(1 : ℝ)) * (S : ℝ) ^ (-(1 : ℝ))) *
        (S : ℝ) ^ (-(1 / 1000 : ℝ)) := by ring
    _ ≤ ((R : ℝ) ^ (-(1 : ℝ)) * (S : ℝ) ^ (-(1 : ℝ))) *
        (R : ℝ) ^ (-(1 / 1000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdelta (by positivity)
    _ = ((R : ℝ) ^ (-(1 : ℝ)) *
          (R : ℝ) ^ (-(1 / 1000 : ℝ))) *
        (S : ℝ) ^ (-(1 : ℝ)) := by ring

private theorem selector_rpow_neg_alpha_le_neg_one
    {S : ℕ} (hS : 1 ≤ S) :
    (S : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (S : ℝ) ^ (-(1 : ℝ)) := by
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hS) (by norm_num)

/-- An explicit constant witnessing the source covariance
`O(R^-1.001 S^-1)` error when `R ≤ S`. -/
def taoLargePrimeSourceCovariancePowerConstant : ℝ :=
  taoLargePrimeSourceJointPowerConstant + 21

/-- Source power form of Proposition 6.8(ii)'s covariance error.  Under the
ordered-band convention `R ≤ S`, the extra `0.001` decay is attached to
the smaller scale. -/
theorem eventually_taoLargePrimeSourceCovarianceErrorEnvelope_le_power
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceCovarianceErrorEnvelope x (R x) (S x) ≤
        taoLargePrimeSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeSourceJointErrorEnvelope_le_power hR hS,
    eventually_taoLargePrimeSourceSingleErrorEnvelope_le_power hR,
    eventually_taoLargePrimeSourceSingleErrorEnvelope_le_power hS,
    hR.eventually_two_le, hS.eventually_two_le, hRS] with
      x hjoint hsingleR hsingleS hRtwo hStwo horder
  have hRpos : 0 < R x := by omega
  have hSpos : 0 < S x := by omega
  let T : ℝ := (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
    (S x : ℝ) ^ (-(1 : ℝ))
  have hcross : (R x : ℝ) ^ (-(1 : ℝ)) *
      (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤ T := by
    exact selector_cross_power_le hRpos hSpos horder
  have hSdecay : (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (S x : ℝ) ^ (-(1 : ℝ)) :=
    selector_rpow_neg_alpha_le_neg_one (by omega)
  have htermR : (2 / (R x : ℝ)) *
      taoLargePrimeSourceSingleErrorEnvelope x (S x) ≤ 6 * T := by
    calc
      (2 / (R x : ℝ)) *
          taoLargePrimeSourceSingleErrorEnvelope x (S x) ≤
        (2 / (R x : ℝ)) *
          (3 * (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsingleS (by positivity)
      _ = 6 * ((R x : ℝ) ^ (-(1 : ℝ)) *
          (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        ring
      _ ≤ 6 * T := mul_le_mul_of_nonneg_left hcross (by norm_num)
  have htermS : (2 / (S x : ℝ)) *
      taoLargePrimeSourceSingleErrorEnvelope x (R x) ≤ 6 * T := by
    calc
      (2 / (S x : ℝ)) *
          taoLargePrimeSourceSingleErrorEnvelope x (R x) ≤
        (2 / (S x : ℝ)) *
          (3 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsingleR (by positivity)
      _ = 6 * T := by
        dsimp [T]
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        ring
  have hproduct : taoLargePrimeSourceSingleErrorEnvelope x (R x) *
      taoLargePrimeSourceSingleErrorEnvelope x (S x) ≤ 9 * T := by
    calc
      taoLargePrimeSourceSingleErrorEnvelope x (R x) *
          taoLargePrimeSourceSingleErrorEnvelope x (S x) ≤
        (3 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ))) *
          (3 * (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) :=
        mul_le_mul hsingleR hsingleS
          (taoLargePrimeSourceSingleErrorEnvelope_nonneg x (S x))
          (by positivity)
      _ = 9 * ((R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) := by ring
      _ ≤ 9 * T := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        dsimp [T]
        exact mul_le_mul_of_nonneg_left hSdecay (by positivity)
  have hjointT : taoLargePrimeSourceJointErrorEnvelope x (R x) (S x) ≤
      taoLargePrimeSourceJointPowerConstant * T := by
    calc
      taoLargePrimeSourceJointErrorEnvelope x (R x) (S x) ≤
          taoLargePrimeSourceJointPowerConstant *
            (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
            (S x : ℝ) ^ (-(1 : ℝ)) := hjoint
      _ = taoLargePrimeSourceJointPowerConstant * T := by
        have hassoc (a b d : ℝ) : a * b * d = a * (b * d) := by ring
        exact hassoc _ _ _
  rw [taoLargePrimeSourceCovarianceErrorEnvelope]
  calc
    _ ≤ taoLargePrimeSourceJointPowerConstant * T + 6 * T + 6 * T + 9 * T :=
      add_le_add (add_le_add (add_le_add hjointT htermR) htermS) hproduct
    _ = taoLargePrimeSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
      have hcombine (a b : ℝ) : a * b + 6 * b + 6 * b + 9 * b =
          (a + 21) * b := by ring
      have hassoc (a b d : ℝ) : a * (b * d) = a * b * d := by ring
      rw [hcombine]
      rw [taoLargePrimeSourceCovariancePowerConstant]
      exact hassoc _ _ _

/-- The literal one-prime error in Proposition 6.7(ii) has the required
`O(R^-1.001)` power form, uniformly over the selected dyadic band. -/
theorem eventually_taoLargePrimeImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R) :
    ∀ᶠ x : ℕ in atTop, ∀ p : ℕ,
      p ∈ taoDyadicPrimeBand (R x) →
      taoLargePrimeImprovedError (P x) p ≤
        3 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
  filter_upwards [eventually_taoLargePrimeImprovedError_le_sourceEnvelope hscale,
    eventually_taoLargePrimeSourceSingleErrorEnvelope_le_power hR,
    hR.eventually_two_le] with x hsource hpower hRtwo
  intro p hp
  exact (hsource (R x) p hRtwo hp).trans hpower

/-- The literal two-prime joint error in Proposition 6.8(ii) has the required
`O(R^-1.001 S^-1)` power form on source-scale dyadic bands. -/
theorem eventually_taoLargePrimeJointImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S) :
    ∀ᶠ x : ℕ in atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeJointImprovedError (P x) p q ≤
        taoLargePrimeSourceJointPowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeJointImprovedError_le_sourceEnvelope hscale,
    eventually_taoLargePrimeSourceJointErrorEnvelope_le_power hR hS,
    hR.eventually_two_le, hS.eventually_two_le] with
      x hsource hpower hRtwo hStwo
  intro p q hp hq hpq
  exact (hsource (R x) (S x) p q hRtwo hStwo hp hq hpq).trans hpower

/-- The literal covariance error in Proposition 6.8(ii) has the required
ordered-band `O(R^-1.001 S^-1)` power form. -/
theorem eventually_taoLargePrimeCovarianceImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeCovarianceImprovedError (P x) p q ≤
        taoLargePrimeSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeCovarianceImprovedError_le_sourceEnvelope hscale,
    eventually_taoLargePrimeSourceCovarianceErrorEnvelope_le_power hR hS hRS,
    hR.eventually_two_le, hS.eventually_two_le] with
      x hsource hpower hRtwo hStwo
  intro p q hp hq hpq
  exact (hsource (R x) (S x) p q hRtwo hStwo hp hq hpq).trans hpower

end

end Tao2026
