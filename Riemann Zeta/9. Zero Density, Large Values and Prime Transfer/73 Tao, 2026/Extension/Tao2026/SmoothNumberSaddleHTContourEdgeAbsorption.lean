import Tao2026.SmoothNumberSaddleHTContourEdgeAnalytic
import Tao2026.SmoothNumberSaddleHTPerronAbsorption

/-!
# Absorption of the HT contour-edge majorant

The contour displacement contains two copies of the requested stretched
exponential saving.  This module bounds all logarithmic-derivative and
geometric losses by fixed powers of `log y`, then spends one copy to absorb
those powers.
-/

open Complex Filter Set Topology

namespace Tao2026

noncomputable section

/-- A deliberately coarse fixed envelope for all constants in the two
logarithmic-derivative majorants. -/
noncomputable def smoothSaddleHTEdgeLogConstant (C : ℝ) : ℝ :=
  1000 * (1 + C + GafniTao.sharpLandauPartialFractionConstant +
    GafniTao.sharpLandauMassConstant)

theorem smoothSaddleHTEdgeLogConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ smoothSaddleHTEdgeLogConstant C := by
  unfold smoothSaddleHTEdgeLogConstant
  have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
  have hM := GafniTao.sharpLandauMassConstant_pos.le
  positivity

/-- Eventually the explicit high-height Landau majorant is at most a fixed
coefficient times the cube of the source logarithm. -/
theorem eventually_smoothSaddleHTHighLogDerivativeMajorant_le_log_cube
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTHighLogDerivativeMajorant y ε ≤
        smoothSaddleHTEdgeLogConstant C * (Real.log y) ^ (3 : ℕ) := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with y hL hy
  let L := Real.log (y : ℝ)
  let eta := smoothSaddleHTContourShift y ε
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have ha : 0 ≤ ε / 2 := by positivity
  have hLa : 1 ≤ L ^ (ε / 2) :=
    Real.one_le_rpow hL ha
  have hetaL : 1 ≤ eta * L := by
    rw [show eta * L = 2 * L ^ (ε / 2) by
      simpa [eta, L] using smoothSaddleHTContourShift_mul_log hy ε]
    linarith
  have hinvEta : 1 / eta ≤ L := by
    rw [div_le_iff₀ heta]
    nlinarith
  have hq : 0 ≤ (3 : ℝ) / 2 - ε := by linarith
  have hqTwo : (3 : ℝ) / 2 - ε ≤ 2 := by linarith
  have hLq : L ^ ((3 : ℝ) / 2 - ε) ≤ L ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL hqTwo
  have hlogThree : Real.log 3 ≤ 2 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≠ 1)
    linarith
  have hlogY : Real.log (3 * smoothSaddleHTFrequencyCeiling y ε) ≤
      3 * L ^ (2 : ℝ) := by
    unfold smoothSaddleHTFrequencyCeiling
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_pos _).ne',
      Real.log_exp]
    have hLsq : 1 ≤ L ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith
    linarith
  have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
  have hM := GafniTao.sharpLandauMassConstant_pos.le
  have hlogYNonneg :
      0 ≤ Real.log (3 * smoothSaddleHTFrequencyCeiling y ε) := by
    apply Real.log_nonneg
    have hYone : 1 ≤ smoothSaddleHTFrequencyCeiling y ε := by
      unfold smoothSaddleHTFrequencyCeiling
      exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
    nlinarith
  have hinside :
      202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant ≤
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / 4) * GafniTao.sharpLandauMassConstant) * L := by
    have hfirst : 202 * GafniTao.sharpLandauPartialFractionConstant ≤
        202 * GafniTao.sharpLandauPartialFractionConstant * L := by
      nlinarith
    have hsecond : (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant ≤
        ((7 / 4) * GafniTao.sharpLandauMassConstant) * L := by
      rw [show (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant =
        ((7 / 4) * GafniTao.sharpLandauMassConstant) * (1 / eta) by ring]
      gcongr
    linarith
  have hcoeff :
      (12 / 7 : ℝ) *
          (202 * GafniTao.sharpLandauPartialFractionConstant +
            (7 / 4) * GafniTao.sharpLandauMassConstant) ≤
        smoothSaddleHTEdgeLogConstant C := by
    unfold smoothSaddleHTEdgeLogConstant
    nlinarith
  unfold smoothSaddleHTHighLogDerivativeMajorant
  calc
    (4 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / (4 * eta)) * GafniTao.sharpLandauMassConstant) *
          Real.log (3 * smoothSaddleHTFrequencyCeiling y ε) ≤
      (4 / 7 : ℝ) *
        ((202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / 4) * GafniTao.sharpLandauMassConstant) * L) *
          (3 * L ^ (2 : ℝ)) := by gcongr
    _ = ((12 / 7 : ℝ) *
        (202 * GafniTao.sharpLandauPartialFractionConstant +
          (7 / 4) * GafniTao.sharpLandauMassConstant)) * L ^ (3 : ℕ) := by
      simp only [Real.rpow_two]
      ring
    _ ≤ smoothSaddleHTEdgeLogConstant C * L ^ (3 : ℕ) := by
      gcongr

/-- The max majorant on the complete left edge obeys the same cubic-log
envelope. -/
theorem eventually_smoothSaddleHTLeftLogDerivativeMajorant_le_log_cube
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop,
      smoothSaddleHTLeftLogDerivativeMajorant y ε C ≤
        smoothSaddleHTEdgeLogConstant C * (Real.log y) ^ (3 : ℕ) := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_smoothSaddleHTHighLogDerivativeMajorant_le_log_cube
      hC hε hεOne,
     hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
     eventually_ge_atTop (2 : ℕ)] with y hhigh hL hy
  let L := Real.log (y : ℝ)
  let eta := smoothSaddleHTContourShift y ε
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have ha : 0 ≤ ε / 2 := by positivity
  have hLa : 1 ≤ L ^ (ε / 2) := Real.one_le_rpow hL ha
  have hetaL : 1 ≤ eta * L := by
    rw [show eta * L = 2 * L ^ (ε / 2) by
      simpa [eta, L] using smoothSaddleHTContourShift_mul_log hy ε]
    linarith
  have hinvEta : 1 / eta ≤ L := by
    rw [div_le_iff₀ heta]
    nlinarith
  have hcube : C + 1 / eta ≤
      smoothSaddleHTEdgeLogConstant C * L ^ (3 : ℕ) := by
    have hK : C + 1 ≤ smoothSaddleHTEdgeLogConstant C := by
      unfold smoothSaddleHTEdgeLogConstant
      have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
      have hM := GafniTao.sharpLandauMassConstant_pos.le
      nlinarith
    have hLcube : L ≤ L ^ (3 : ℕ) := by
      have hLsq : 1 ≤ L ^ (2 : ℕ) := by nlinarith
      calc
        L = L * 1 := by ring
        _ ≤ L * L ^ (2 : ℕ) := by gcongr
        _ = L ^ (3 : ℕ) := by ring
    calc
      C + 1 / eta ≤ C + L := by linarith
      _ ≤ (C + 1) * L := by nlinarith
      _ ≤ smoothSaddleHTEdgeLogConstant C * L := by gcongr
      _ ≤ smoothSaddleHTEdgeLogConstant C * L ^ (3 : ℕ) := by
        gcongr
        exact smoothSaddleHTEdgeLogConstant_nonneg hC
  unfold smoothSaddleHTLeftLogDerivativeMajorant
  exact max_le hcube hhigh

/-- In the large-beta branch, the reciprocal-distance integral contributes
at most a quadratic power of the source logarithm. -/
theorem eventually_smoothSaddleHT_verticalWeightLog_le_log_sq
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta : ℝ,
      2 * smoothSaddleHTContourShift y ε ≤ beta →
      Real.log
          (((beta - smoothSaddleHTContourShift y ε) +
              smoothSaddleHTContourHeight y ε) /
            (beta - smoothSaddleHTContourShift y ε)) ≤
        4 * (Real.log y) ^ (2 : ℕ) := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with y hL hy
  intro beta hbeta
  let L := Real.log (y : ℝ)
  let eta := smoothSaddleHTContourShift y ε
  let Y := smoothSaddleHTFrequencyCeiling y ε
  let T := smoothSaddleHTContourHeight y ε
  let a := beta - eta
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have haEta : eta ≤ a := by dsimp [a, eta] at hbeta ⊢; linarith
  have ha : 0 < a := heta.trans_le haEta
  have hY : 0 < Y := by
    dsimp [Y]
    exact smoothSaddleHTFrequencyCeiling_pos y ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hLa : 1 ≤ L ^ (ε / 2) :=
    Real.one_le_rpow hL (by positivity)
  have hetaL : 1 ≤ eta * L := by
    rw [show eta * L = 2 * L ^ (ε / 2) by
      simpa [eta, L] using smoothSaddleHTContourShift_mul_log hy ε]
    linarith
  have hinvEta : 1 / eta ≤ L := by
    rw [div_le_iff₀ heta]
    nlinarith
  have hToverEta : T / eta ≤ 2 * Y * L := by
    have h := mul_le_mul_of_nonneg_left hinvEta (show 0 ≤ T from hT.le)
    simpa [div_eq_mul_inv, T, smoothSaddleHTContourHeight, Y] using h
  have hToverA : T / a ≤ T / eta :=
    div_le_div_of_nonneg_left hT.le heta haEta
  have hYLone : 1 ≤ Y * L := by
    have hYone : 1 ≤ Y := by
      dsimp [Y, smoothSaddleHTFrequencyCeiling]
      exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
    nlinarith
  have hratio : (a + T) / a ≤ 3 * Y * L := by
    rw [show (a + T) / a = 1 + T / a by field_simp]
    calc
      1 + T / a ≤ 1 + T / eta := by linarith
      _ ≤ 1 + 2 * Y * L := by linarith
      _ ≤ 3 * Y * L := by nlinarith
  have hratioPos : 0 < (a + T) / a := div_pos (add_pos ha hT) ha
  have hlogRatio : Real.log ((a + T) / a) ≤ Real.log (3 * Y * L) :=
    Real.log_le_log hratioPos hratio
  have hlogThree : Real.log 3 ≤ 2 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≠ 1)
    linarith
  have hlogY : Real.log Y = L ^ ((3 : ℝ) / 2 - ε) := by
    dsimp [Y, smoothSaddleHTFrequencyCeiling, L]
    rw [Real.log_exp]
  have hLq : L ^ ((3 : ℝ) / 2 - ε) ≤ L ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hlogL : Real.log L ≤ L := by
    by_cases hL1 : L = 1
    · simp [hL1]
    · have h := Real.log_lt_sub_one_of_pos hLpos hL1
      linarith
  have hLsq : 1 ≤ L ^ (2 : ℕ) := by nlinarith
  have hLleSq : L ≤ L ^ (2 : ℕ) := by nlinarith
  have hlogProduct : Real.log (3 * Y * L) ≤ 4 * L ^ (2 : ℕ) := by
    rw [Real.log_mul (by positivity : 3 * Y ≠ 0) hLpos.ne',
      Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hY.ne', hlogY]
    rw [Real.rpow_two] at hLq
    nlinarith
  simpa [a, T, eta, L] using hlogRatio.trans hlogProduct

/-- In the branch `2*eta <= beta`, the complete weighted edge majorant is
absorbed by the requested equation-(3.10) stretched exponential. -/
theorem eventually_smoothSaddleHTContourEdgeWeightedMajorant_le_target
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta : ℝ,
      2 * smoothSaddleHTContourShift y ε ≤ beta →
      smoothSaddleHTContourEdgeWeightedMajorant y beta ε
          (smoothSaddleHTHorizontalIntegrandMajorant y beta ε)
          (smoothSaddleHTVerticalIntegrandNumerator y beta ε C) ≤
        (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) := by
  let K := smoothSaddleHTEdgeLogConstant C
  have hK : 0 ≤ K := by
    dsimp [K]
    exact smoothSaddleHTEdgeLogConstant_nonneg hC
  have ha : 0 < ε / 2 := by positivity
  have hq : 0 < (3 : ℝ) / 2 - ε := by linarith
  have haq : ε / 2 < (3 : ℝ) / 2 - ε :=
    smoothSaddleHT_decayExponent_lt_heightExponent hεOne
  have hHorizontalAbsorb :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 24 * K) (α := ε / 2) (β := (3 : ℝ) / 2 - ε)
      hq haq 3
  have hVerticalAbsorb :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := 32 * K) (α := 0) (β := ε / 2) ha ha 5
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_smoothSaddleHTHighLogDerivativeMajorant_le_log_cube
      hC hε hεOne,
     eventually_smoothSaddleHTLeftLogDerivativeMajorant_le_log_cube
      hC hε hεOne,
     eventually_smoothSaddleHT_verticalWeightLog_le_log_sq hε hεOne,
     eventually_smoothSaddleHTContourShift_le_one hεOne,
     hHorizontalAbsorb,
     hVerticalAbsorb,
     hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
     eventually_ge_atTop (2 : ℕ)] with
      y hhigh hleft hweight hetaOne hHabs hVabs hL hy
  intro beta hbeta
  let L := Real.log (y : ℝ)
  let eta := smoothSaddleHTContourShift y ε
  let Y := smoothSaddleHTFrequencyCeiling y ε
  let T := smoothSaddleHTContourHeight y ε
  let E := Real.exp (L ^ (ε / 2))
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have heta : 0 < eta := by
    dsimp [eta]
    exact smoothSaddleHTContourShift_pos hy ε
  have hY : 0 < Y := by
    dsimp [Y]
    exact smoothSaddleHTFrequencyCeiling_pos y ε
  have hT : 0 < T := by
    dsimp [T]
    exact smoothSaddleHTContourHeight_pos y ε
  have hE : 0 < E := by dsimp [E]; positivity
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyPow : 0 ≤ (y : ℝ) ^ beta := Real.rpow_nonneg hyPos.le _
  have hInvLog : 1 / L ≤ 1 := (div_le_one hLpos).2 hL
  have hLength : eta + 1 / L ≤ 2 := by
    dsimp [eta, L] at hetaOne ⊢
    linarith
  have hHighNonneg : 0 ≤ smoothSaddleHTHighLogDerivativeMajorant y ε := by
    unfold smoothSaddleHTHighLogDerivativeMajorant
    have hlogNonneg :
        0 ≤ Real.log (3 * smoothSaddleHTFrequencyCeiling y ε) := by
      apply Real.log_nonneg
      have hYone : 1 ≤ smoothSaddleHTFrequencyCeiling y ε := by
        unfold smoothSaddleHTFrequencyCeiling
        exact Real.one_le_exp (Real.rpow_nonneg hLpos.le _)
      nlinarith
    have hA := GafniTao.sharpLandauPartialFractionConstant_pos.le
    have hM := GafniTao.sharpLandauMassConstant_pos.le
    positivity
  have hLeftNonneg : 0 ≤ smoothSaddleHTLeftLogDerivativeMajorant y ε C :=
    hHighNonneg.trans (le_max_right _ _)
  have hHorizontal : smoothSaddleHTHorizontalIntegrandMajorant y beta ε ≤
      3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y := by
    unfold smoothSaddleHTHorizontalIntegrandMajorant
    rw [rpow_smoothSaddleHTContourRight hy beta]
    have hnum :
        smoothSaddleHTHighLogDerivativeMajorant y ε *
            ((y : ℝ) ^ beta * Real.exp 1) ≤
          3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta := by
      calc
        smoothSaddleHTHighLogDerivativeMajorant y ε *
            ((y : ℝ) ^ beta * Real.exp 1) ≤
          (K * L ^ (3 : ℕ)) * ((y : ℝ) ^ beta * Real.exp 1) := by
            gcongr
        _ ≤ (K * L ^ (3 : ℕ)) * ((y : ℝ) ^ beta * 3) := by
            gcongr
            exact Real.exp_one_lt_three.le
        _ = 3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta := by ring
    calc
      smoothSaddleHTHighLogDerivativeMajorant y ε *
          ((y : ℝ) ^ beta * Real.exp 1) /
          smoothSaddleHTContourHeight y ε ≤
        (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta) /
          smoothSaddleHTContourHeight y ε :=
        div_le_div_of_nonneg_right hnum hT.le
      _ ≤ (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta) / Y := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hY
        · dsimp [T, Y]
          unfold smoothSaddleHTContourHeight
          linarith
  have hVertical : smoothSaddleHTVerticalIntegrandNumerator y beta ε C ≤
      K * L ^ (3 : ℕ) * (y : ℝ) ^ beta *
        Real.exp (-2 * L ^ (ε / 2)) := by
    unfold smoothSaddleHTVerticalIntegrandNumerator
    rw [Real.rpow_sub hyPos, div_eq_mul_inv,
      ← Real.rpow_neg hyPos.le,
      rpow_neg_smoothSaddleHTContourShift hy ε]
    have hleft' : smoothSaddleHTLeftLogDerivativeMajorant y ε C ≤
        K * L ^ (3 : ℕ) := by simpa [K, L] using hleft
    have htail : 0 ≤ (y : ℝ) ^ beta *
        Real.exp (-2 * L ^ (ε / 2)) := by positivity
    calc
      smoothSaddleHTLeftLogDerivativeMajorant y ε C *
          ((y : ℝ) ^ beta *
            Real.exp (-2 * (Real.log y) ^ (ε / 2))) ≤
        (K * L ^ (3 : ℕ)) *
          ((y : ℝ) ^ beta * Real.exp (-2 * L ^ (ε / 2))) := by
            simpa [L] using mul_le_mul_of_nonneg_right hleft' htail
      _ = K * L ^ (3 : ℕ) * (y : ℝ) ^ beta *
          Real.exp (-2 * L ^ (ε / 2)) := by ring
  have hBracket :
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
          (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
        4 * smoothSaddleHTVerticalIntegrandNumerator y beta ε C *
          Real.log
            (((beta - smoothSaddleHTContourShift y ε) +
                smoothSaddleHTContourHeight y ε) /
              (beta - smoothSaddleHTContourShift y ε)) ≤
      12 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
        16 * K * L ^ (5 : ℕ) * (y : ℝ) ^ beta *
          Real.exp (-2 * L ^ (ε / 2)) := by
    have hweight' := hweight beta hbeta
    have hHorizontalNonneg :
        0 ≤ smoothSaddleHTHorizontalIntegrandMajorant y beta ε := by
      unfold smoothSaddleHTHorizontalIntegrandMajorant
      positivity
    have hVerticalNonneg :
        0 ≤ smoothSaddleHTVerticalIntegrandNumerator y beta ε C := by
      unfold smoothSaddleHTVerticalIntegrandNumerator
      positivity
    have hweightNonneg : 0 ≤ Real.log
          (((beta - smoothSaddleHTContourShift y ε) +
              smoothSaddleHTContourHeight y ε) /
            (beta - smoothSaddleHTContourShift y ε)) := by
      apply Real.log_nonneg
      have hleft : 0 < beta - smoothSaddleHTContourShift y ε := by
        dsimp [eta] at hbeta heta ⊢
        linarith
      rw [one_le_div hleft]
      linarith [hT]
    calc
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTVerticalIntegrandNumerator y beta ε C *
            Real.log
              (((beta - smoothSaddleHTContourShift y ε) +
                  smoothSaddleHTContourHeight y ε) /
                (beta - smoothSaddleHTContourShift y ε)) ≤
        2 * (3 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y) * 2 +
          4 * (K * L ^ (3 : ℕ) * (y : ℝ) ^ beta *
            Real.exp (-2 * L ^ (ε / 2))) * (4 * L ^ (2 : ℕ)) := by
              gcongr
      _ = 12 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
          16 * K * L ^ (5 : ℕ) * (y : ℝ) ^ beta *
            Real.exp (-2 * L ^ (ε / 2)) := by ring
  have hHabs' : 24 * K * L ^ (3 : ℕ) * E ≤ Y := by
    have h := hHabs
    rw [Real.rpow_natCast] at h
    simpa [L, E, Y, smoothSaddleHTFrequencyCeiling] using h
  have hVabs' : 32 * K * L ^ (5 : ℕ) ≤ E := by
    have hExpZero : Real.exp (L ^ (0 : ℝ)) = Real.exp 1 := by
      rw [Real.rpow_zero]
    have hExpOne : 1 ≤ Real.exp (L ^ (0 : ℝ)) := by
      rw [hExpZero]
      exact Real.one_le_exp (by norm_num)
    have h := hVabs
    rw [Real.rpow_natCast] at h
    dsimp [K, L, E] at h ⊢
    calc
      32 * smoothSaddleHTEdgeLogConstant C *
          Real.log (y : ℝ) ^ (5 : ℕ) ≤
        32 * smoothSaddleHTEdgeLogConstant C *
          Real.log (y : ℝ) ^ (5 : ℕ) *
            Real.exp (Real.log (y : ℝ) ^ (0 : ℝ)) := by
              have hbase : 0 ≤ 32 * smoothSaddleHTEdgeLogConstant C *
                  Real.log (y : ℝ) ^ (5 : ℕ) := by positivity
              calc
                32 * smoothSaddleHTEdgeLogConstant C *
                    Real.log (y : ℝ) ^ (5 : ℕ) =
                  (32 * smoothSaddleHTEdgeLogConstant C *
                    Real.log (y : ℝ) ^ (5 : ℕ)) * 1 := by ring
                _ ≤ (32 * smoothSaddleHTEdgeLogConstant C *
                    Real.log (y : ℝ) ^ (5 : ℕ)) *
                      Real.exp (Real.log (y : ℝ) ^ (0 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hExpOne hbase
      _ ≤ Real.exp (Real.log (y : ℝ) ^ (ε / 2)) := by
        exact h
  have hHalfHorizontal :
      12 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y ≤
        ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / 2 := by
    rw [Real.exp_neg]
    rw [div_le_div_iff₀ hY (by positivity : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_right hHabs' hyPow
    dsimp [E] at hmul
    field_simp [ne_of_gt hE] at hmul ⊢
    nlinarith
  have hHalfVertical :
      16 * K * L ^ (5 : ℕ) * (y : ℝ) ^ beta *
          Real.exp (-2 * L ^ (ε / 2)) ≤
        ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hVabs' hyPow
    dsimp [E] at hmul
    rw [show Real.exp (-2 * L ^ (ε / 2)) =
        (Real.exp (L ^ (ε / 2)))⁻¹ ^ 2 by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      ring,
      Real.exp_neg]
    field_simp [ne_of_gt hE] at hmul ⊢
    nlinarith
  unfold smoothSaddleHTContourEdgeWeightedMajorant
  have hfactor : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hfactorOne : (1 / (2 * Real.pi) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith [Real.pi_gt_three]
  have hbracketNonneg : 0 ≤
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
          (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
        4 * smoothSaddleHTVerticalIntegrandNumerator y beta ε C *
          Real.log
            (((beta - smoothSaddleHTContourShift y ε) +
                smoothSaddleHTContourHeight y ε) /
              (beta - smoothSaddleHTContourShift y ε)) := by
    have hweightNonneg : 0 ≤ Real.log
          (((beta - smoothSaddleHTContourShift y ε) +
              smoothSaddleHTContourHeight y ε) /
            (beta - smoothSaddleHTContourShift y ε)) := by
      apply Real.log_nonneg
      have hleft : 0 < beta - smoothSaddleHTContourShift y ε := by
        dsimp [eta] at hbeta heta ⊢
        linarith
      rw [one_le_div hleft]
      linarith [hT]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (by
          unfold smoothSaddleHTHorizontalIntegrandMajorant
          positivity))
        (add_nonneg heta.le (one_div_nonneg.mpr hLpos.le)))
      (mul_nonneg
        (mul_nonneg (by positivity) (by
          unfold smoothSaddleHTVerticalIntegrandNumerator
          positivity))
        hweightNonneg)
  calc
    (1 / (2 * Real.pi)) *
        (2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTVerticalIntegrandNumerator y beta ε C *
            Real.log
              (((beta - smoothSaddleHTContourShift y ε) +
                  smoothSaddleHTContourHeight y ε) /
                (beta - smoothSaddleHTContourShift y ε))) ≤
      2 * smoothSaddleHTHorizontalIntegrandMajorant y beta ε *
            (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
          4 * smoothSaddleHTVerticalIntegrandNumerator y beta ε C *
            Real.log
              (((beta - smoothSaddleHTContourShift y ε) +
                  smoothSaddleHTContourHeight y ε) /
                (beta - smoothSaddleHTContourShift y ε)) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfactorOne hbracketNonneg
    _ ≤ 12 * K * L ^ (3 : ℕ) * (y : ℝ) ^ beta / Y +
        16 * K * L ^ (5 : ℕ) * (y : ℝ) ^ beta *
          Real.exp (-2 * L ^ (ε / 2)) := hBracket
    _ ≤ ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / 2 +
        ((y : ℝ) ^ beta * Real.exp (-L ^ (ε / 2))) / 2 :=
      add_le_add hHalfHorizontal hHalfVertical
    _ = (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) := by
      dsimp [L]
      ring

theorem tendsto_smoothSaddleHTContourShift_atTop_zero
    {ε : ℝ} (hεOne : ε < 1) :
    Tendsto (fun y : ℕ => smoothSaddleHTContourShift y ε)
      atTop (𝓝 0) := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : 0 < 1 - ε / 2 := by linarith
  have h := ((tendsto_rpow_neg_atTop hp).const_mul 2).comp hlogTop
  convert h using 1
  · funext y
    unfold smoothSaddleHTContourShift
    rw [show ε / 2 - 1 = -(1 - ε / 2) by ring]
    rfl
  · simp

/-- Combining the VK-specialized pointwise theorem with scalar absorption
closes the complete displaced contour edge in the large-beta branch. -/
theorem eventually_norm_smoothSaddleHTContourEdgeContribution_le_target_of_vK
    {c H C ε : ℝ}
    (hc : 0 < c)
    (hHbase : Real.exp (Real.exp 1) ≤ H) (hEightH : 8 ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hClow : ∀ {eta R : ℝ},
      0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) +
            (R : ℂ) * Complex.I)‖ ≤ C + 1 / eta)
    (hC : 0 ≤ C) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ (beta t : ℝ),
      2 * smoothSaddleHTContourShift y ε ≤ beta →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ ≤
        (y : ℝ) ^ beta * Real.exp (-(Real.log y) ^ (ε / 2)) := by
  have ha : 0 < (3 : ℝ) / 2 - ε := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto (fun y : ℕ => smoothSaddleHTFrequencyCeiling y ε)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  have hshiftZero := tendsto_smoothSaddleHTContourShift_atTop_zero hεOne
  have hD : 0 < GafniTao.vinogradovKorobovDenominator H :=
    GafniTao.vinogradovKorobovDenominator_pos hHbase
  have hfixed : 0 < c /
      (2 * GafniTao.vinogradovKorobovDenominator H) := by positivity
  filter_upwards
    [eventually_smoothSaddleHTContourEdgeWeightedMajorant_le_target
      hC hε hεOne,
     eventually_two_mul_smoothSaddleHTContourShift_le_vk_nine_frequency
      hc hε hεOne,
     hYTop.eventually
      (eventually_ge_atTop (Real.exp (Real.exp 1))),
     hYTop.eventually (eventually_ge_atTop (8 : ℝ)),
     hYTop.eventually (eventually_ge_atTop H),
     hshiftZero.eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
     hshiftZero.eventually (eventually_le_nhds hfixed),
     hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
     eventually_ge_atTop (2 : ℕ)] with
      y habsorb hwidth hYbase hY8 hHY hetaHalf hetaFixed hlogOne hy
  intro beta t hbeta ht
  have heta := smoothSaddleHTContourShift_pos hy ε
  have hbetaShift : smoothSaddleHTContourShift y ε < beta := by linarith
  have hedge :=
    norm_smoothSaddleHTContourEdgeContribution_le_analyticMajorant_of_vK
      hZeroFree hHbase hEightH hClow hy hYbase hY8 hHY hwidth hetaHalf
      hetaFixed hbetaShift hlogOne ht
  exact hedge.trans (habsorb beta hbeta)

end

end Tao2026
