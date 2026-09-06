import GafniTao.DyadicZeroShellHeight
import GafniTao.HeathBrownFullyUniformMixedSelfReduction
import GafniTao.HeathBrownLongSourceThreshold
import GafniTao.HeathBrownSourceLossAbsorption
import GafniTao.ReflectedExtractionLoss
import GafniTao.HeathBrownActualSourceColorPhysicalCells

/-!
# Quantitative bound for the four-colour selection loss

The global Heath--Brown source reduction carries four detector-colour counts,
four displacement windows, four local multiplicity caps, and one doubled-floor
defect window.  This file bounds that literal product.  Its only polynomial
cost is `5 * d`; all binary logarithms and local-zero logarithms are assigned
the explicit reserve `v`.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The natural local-multiplicity cap is eventually smaller than any positive
power of its physical shell height. -/
theorem eventually_sharpShellLocalMultiplicityCap_cast_le_rpow
    {v : Real} (hv : 0 < v) :
    ∀ᶠ U : Real in atTop,
      (sharpShellLocalMultiplicityCap U : Real) <= U ^ v := by
  let D : Real := 2 * globalLocalZeroLogConstant + 1
  have hD : 0 <= D := by
    dsimp only [D]
    nlinarith [globalLocalZeroLogConstant_pos]
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := D) (p := 1) (q := v) (b := 1) hD hv zero_lt_one
  filter_upwards [hSmall, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop 2] with U hSmallU hExp hTwo
  have hUPos : 0 < U := (Real.exp_pos 1).trans_le hExp
  have hLogOne : 1 <= Real.log U := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExp
  have hLogTwoU : Real.log (2 * U) <= 2 * Real.log U := by
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hUPos.ne']
    have hLogTwo : Real.log 2 <= Real.log U :=
      Real.log_le_log (by norm_num) hTwo
    linarith
  have hCeilRaw := Nat.ceil_lt_add_one
    (show 0 <= globalLocalZeroLogConstant * Real.log (2 * U) by
      have : 1 <= 2 * U := by nlinarith
      exact mul_nonneg globalLocalZeroLogConstant_pos.le
        (Real.log_nonneg this))
  have hCap : (sharpShellLocalMultiplicityCap U : Real) <=
      D * Real.log U := by
    unfold sharpShellLocalMultiplicityCap
    calc
      (Nat.ceil (globalLocalZeroLogConstant * Real.log (2 * U)) : Real) <=
          globalLocalZeroLogConstant * Real.log (2 * U) + 1 := hCeilRaw.le
      _ <= globalLocalZeroLogConstant * (2 * Real.log U) + 1 := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hLogTwoU
            globalLocalZeroLogConstant_pos.le) 1
      _ <= D * Real.log U := by
        dsimp only [D]
        nlinarith
  have hPowerPos : 0 < U ^ v := Real.rpow_pos_of_pos hUPos v
  have hCancel : U ^ (-v) * U ^ v = 1 := by
    rw [← Real.rpow_add hUPos]
    norm_num
  have hScaled : D * Real.log U <= U ^ v := by
    simp only [Real.rpow_one] at hSmallU
    have hMul := mul_le_mul_of_nonneg_right hSmallU hPowerPos.le
    calc
      D * Real.log U =
          (D * Real.log U * U ^ (-v)) * U ^ v := by
        rw [mul_assoc, hCancel, mul_one]
      _ <= 1 * U ^ v := hMul
      _ = U ^ v := one_mul _
  exact hCap.trans hScaled

/-- The exact signed Type-I/Type-II detector-colour count is eventually
bounded by `8 * U^v`. -/
theorem eventually_classicalBinary_color_count_cast_le
    {delta1 v : Real} (hdelta1 : 0 < delta1) (hv : 0 < v) :
    ∀ᶠ U : Real in atTop,
      ∀ {D : ClassicalBinaryShellDetectorData (1 / 2) U 0
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta1 / 2)))
          (Nat.floor (sharpZetaCutoff U)) 1},
        (((D.kI * 2 + D.kII * 2) * 2 : Nat) : Real) <= 8 * U ^ v := by
  have hI := eventually_const_mul_sharp_cutoff_clog_le_rpow
    (D := 1) (zeta := v) (by norm_num) hv
  have hII := eventually_const_mul_clog_floor_rpow_le_rpow
    (D := 1) (delta := delta1) (zeta := v) (by norm_num) hdelta1 hv
  filter_upwards [hI, hII] with U hIU hIIU
  intro D
  have hkI : (D.kI : Real) <= U ^ v := by
    rw [D.hkI_eq]
    simpa only [one_mul] using hIU
  have hkII : (D.kII : Real) <= U ^ v := by
    simpa only [one_mul] using hIIU D.kII (by rw [D.hkII_eq])
  push_cast
  linarith

/-- Parameter-generic form of the preceding colour-count estimate.  The
detector's `sigma`, displacement exponent, threshold and secondary exponent
do not affect its two exact binary-logarithmic cardinalities. -/
theorem eventually_classicalBinary_color_count_cast_le_general
    {delta1 v : Real} (hdelta1 : 0 < delta1) (hv : 0 < v) :
    ∀ᶠ U : Real in atTop,
      ∀ {sigma d delta2 : Real}
        {D : ClassicalBinaryShellDetectorData sigma U d
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))},
        (((D.kI * 2 + D.kII * 2) * 2 : Nat) : Real) <= 8 * U ^ v := by
  have hI := eventually_const_mul_sharp_cutoff_clog_le_rpow
    (D := 1) (zeta := v) (by norm_num) hv
  have hII := eventually_const_mul_clog_floor_rpow_le_rpow
    (D := 1) (delta := delta1) (zeta := v) (by norm_num) hdelta1 hv
  filter_upwards [hI, hII] with U hIU hIIU
  intro sigma d delta2 D
  have hkI : (D.kI : Real) <= U ^ v := by
    rw [D.hkI_eq]
    simpa only [one_mul] using hIU
  have hkII : (D.kII : Real) <= U ^ v := by
    simpa only [one_mul] using hIIU D.kII (by rw [D.hkII_eq])
  push_cast
  linarith

/-- The exact displacement-window cardinality has its advertised physical
power and no additional polynomial loss. -/
theorem detector_displacement_window_cast_le
    {U d : Real} (hU : 1 <= U) (hd : 0 <= d) :
    ((2 * Nat.ceil (U ^ d + 1) + 1 : Nat) : Real) <= 8 * U ^ d := by
  have hPow : 1 <= U ^ d := Real.one_le_rpow hU hd
  have hCeil := Nat.ceil_lt_add_one
    (show 0 <= U ^ d + 1 by positivity)
  push_cast
  linarith

set_option maxHeartbeats 800000 in
/-- Exact polynomial ledger for the fully uniform four-colour selection
loss.  Each of the eight logarithmic factors receives reserve `v`; the four
displacement windows and the final defect window contribute `5*d`. -/
theorem heathBrownUniformMixedSelectionLoss_le_physical
    {sigma delta delta1 delta2 eta epsilon C0 C2 C4 : Real}
    {U0 U1 U2 U3 T v : Real}
    {d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2))}
    {d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2))}
    {d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2))}
    {d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))}
    (output : HeathBrownUniformMixedSourceOutput sigma delta delta1 delta2
      eta epsilon C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3)
    (hT : 1 <= T) (hdelta : 0 <= delta) (hv : 0 <= v)
    (hU0One : 1 <= U0) (hU1One : 1 <= U1)
    (hU2One : 1 <= U2) (hU3One : 1 <= U3)
    (hU0 : U0 <= 2 * T) (hU1 : U1 <= 2 * T)
    (hU2 : U2 <= 2 * T) (hU3 : U3 <= 2 * T)
    (hColor0 : (((d0.kI * 2 + d0.kII * 2) * 2 : Nat) : Real) <=
      8 * U0 ^ v)
    (hColor1 : (((d1.kI * 2 + d1.kII * 2) * 2 : Nat) : Real) <=
      8 * U1 ^ v)
    (hColor2 : (((d2.kI * 2 + d2.kII * 2) * 2 : Nat) : Real) <=
      8 * U2 ^ v)
    (hColor3 : (((d3.kI * 2 + d3.kII * 2) * 2 : Nat) : Real) <=
      8 * U3 ^ v)
    (hCap0 : (sharpShellLocalMultiplicityCap U0 : Real) <= U0 ^ v)
    (hCap1 : (sharpShellLocalMultiplicityCap U1 : Real) <= U1 ^ v)
    (hCap2 : (sharpShellLocalMultiplicityCap U2 : Real) <= U2 ^ v)
    (hCap3 : (sharpShellLocalMultiplicityCap U3 : Real) <= U3 ^ v) :
    (heathBrownUniformMixedSelectionLoss output : Real) <=
      (64 ^ 4 * 43 : Real) * (2 * T) ^ (5 * delta + 8 * v) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hTwoTPos : 0 < 2 * T := by positivity
  have hDisp0 := detector_displacement_window_cast_le hU0One hdelta
  have hDisp1 := detector_displacement_window_cast_le hU1One hdelta
  have hDisp2 := detector_displacement_window_cast_le hU2One hdelta
  have hDisp3 := detector_displacement_window_cast_le hU3One hdelta
  have hCoord0 :
      (((d0.kI * 2 + d0.kII * 2) * 2 : Nat) : Real) *
        (((2 * Nat.ceil (U0 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U0 : Nat) : Real) <=
        64 * U0 ^ (delta + 2 * v) := by
    have hLocal :
        ((((2 * Nat.ceil (U0 ^ delta + 1) + 1) *
          sharpShellLocalMultiplicityCap U0 : Nat) : Real)) <=
          8 * U0 ^ (delta + v) := by
      rw [Nat.cast_mul]
      calc
        ((2 * Nat.ceil (U0 ^ delta + 1) + 1 : Nat) : Real) *
            (sharpShellLocalMultiplicityCap U0 : Real) <=
          (8 * U0 ^ delta) * U0 ^ v := by gcongr
        _ = 8 * (U0 ^ delta * U0 ^ v) := by ring
        _ = 8 * U0 ^ (delta + v) := by
          rw [Real.rpow_add (by positivity : 0 < U0)]
    calc
      (((d0.kI * 2 + d0.kII * 2) * 2 : Nat) : Real) *
          (((2 * Nat.ceil (U0 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U0 : Nat) : Real) <=
        (8 * U0 ^ v) * (8 * U0 ^ (delta + v)) := by gcongr
      _ = 64 * U0 ^ (delta + 2 * v) := by
        calc
          (8 * U0 ^ v) * (8 * U0 ^ (delta + v)) =
              64 * (U0 ^ v * U0 ^ (delta + v)) := by ring
          _ = 64 * U0 ^ (v + (delta + v)) := by
            rw [← Real.rpow_add (by positivity : 0 < U0)]
          _ = 64 * U0 ^ (delta + 2 * v) := by ring_nf
  have hCoord1 :
      (((d1.kI * 2 + d1.kII * 2) * 2 : Nat) : Real) *
        (((2 * Nat.ceil (U1 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U1 : Nat) : Real) <=
        64 * U1 ^ (delta + 2 * v) := by
    have hLocal :
        ((((2 * Nat.ceil (U1 ^ delta + 1) + 1) *
          sharpShellLocalMultiplicityCap U1 : Nat) : Real)) <=
          8 * U1 ^ (delta + v) := by
      rw [Nat.cast_mul]
      calc
        ((2 * Nat.ceil (U1 ^ delta + 1) + 1 : Nat) : Real) *
            (sharpShellLocalMultiplicityCap U1 : Real) <=
          (8 * U1 ^ delta) * U1 ^ v := by gcongr
        _ = 8 * (U1 ^ delta * U1 ^ v) := by ring
        _ = 8 * U1 ^ (delta + v) := by
          rw [Real.rpow_add (by positivity : 0 < U1)]
    calc
      (((d1.kI * 2 + d1.kII * 2) * 2 : Nat) : Real) *
          (((2 * Nat.ceil (U1 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U1 : Nat) : Real) <=
        (8 * U1 ^ v) * (8 * U1 ^ (delta + v)) := by gcongr
      _ = 64 * U1 ^ (delta + 2 * v) := by
        calc
          (8 * U1 ^ v) * (8 * U1 ^ (delta + v)) =
              64 * (U1 ^ v * U1 ^ (delta + v)) := by ring
          _ = 64 * U1 ^ (v + (delta + v)) := by
            rw [← Real.rpow_add (by positivity : 0 < U1)]
          _ = 64 * U1 ^ (delta + 2 * v) := by ring_nf
  have hCoord2 :
      (((d2.kI * 2 + d2.kII * 2) * 2 : Nat) : Real) *
        (((2 * Nat.ceil (U2 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U2 : Nat) : Real) <=
        64 * U2 ^ (delta + 2 * v) := by
    have hLocal :
        ((((2 * Nat.ceil (U2 ^ delta + 1) + 1) *
          sharpShellLocalMultiplicityCap U2 : Nat) : Real)) <=
          8 * U2 ^ (delta + v) := by
      rw [Nat.cast_mul]
      calc
        ((2 * Nat.ceil (U2 ^ delta + 1) + 1 : Nat) : Real) *
            (sharpShellLocalMultiplicityCap U2 : Real) <=
          (8 * U2 ^ delta) * U2 ^ v := by gcongr
        _ = 8 * (U2 ^ delta * U2 ^ v) := by ring
        _ = 8 * U2 ^ (delta + v) := by
          rw [Real.rpow_add (by positivity : 0 < U2)]
    calc
      (((d2.kI * 2 + d2.kII * 2) * 2 : Nat) : Real) *
          (((2 * Nat.ceil (U2 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U2 : Nat) : Real) <=
        (8 * U2 ^ v) * (8 * U2 ^ (delta + v)) := by gcongr
      _ = 64 * U2 ^ (delta + 2 * v) := by
        calc
          (8 * U2 ^ v) * (8 * U2 ^ (delta + v)) =
              64 * (U2 ^ v * U2 ^ (delta + v)) := by ring
          _ = 64 * U2 ^ (v + (delta + v)) := by
            rw [← Real.rpow_add (by positivity : 0 < U2)]
          _ = 64 * U2 ^ (delta + 2 * v) := by ring_nf
  have hCoord3 :
      (((d3.kI * 2 + d3.kII * 2) * 2 : Nat) : Real) *
        (((2 * Nat.ceil (U3 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U3 : Nat) : Real) <=
        64 * U3 ^ (delta + 2 * v) := by
    have hLocal :
        ((((2 * Nat.ceil (U3 ^ delta + 1) + 1) *
          sharpShellLocalMultiplicityCap U3 : Nat) : Real)) <=
          8 * U3 ^ (delta + v) := by
      rw [Nat.cast_mul]
      calc
        ((2 * Nat.ceil (U3 ^ delta + 1) + 1 : Nat) : Real) *
            (sharpShellLocalMultiplicityCap U3 : Real) <=
          (8 * U3 ^ delta) * U3 ^ v := by gcongr
        _ = 8 * (U3 ^ delta * U3 ^ v) := by ring
        _ = 8 * U3 ^ (delta + v) := by
          rw [Real.rpow_add (by positivity : 0 < U3)]
    calc
      (((d3.kI * 2 + d3.kII * 2) * 2 : Nat) : Real) *
          (((2 * Nat.ceil (U3 ^ delta + 1) + 1) *
            sharpShellLocalMultiplicityCap U3 : Nat) : Real) <=
        (8 * U3 ^ v) * (8 * U3 ^ (delta + v)) := by gcongr
      _ = 64 * U3 ^ (delta + 2 * v) := by
        calc
          (8 * U3 ^ v) * (8 * U3 ^ (delta + v)) =
              64 * (U3 ^ v * U3 ^ (delta + v)) := by ring
          _ = 64 * U3 ^ (v + (delta + v)) := by
            rw [← Real.rpow_add (by positivity : 0 < U3)]
          _ = 64 * U3 ^ (delta + 2 * v) := by ring_nf
  have hExponent : 0 <= delta + 2 * v := by linarith
  have hCoord0T : 64 * U0 ^ (delta + 2 * v) <=
      64 * (2 * T) ^ (delta + 2 * v) := by
    gcongr
  have hCoord1T : 64 * U1 ^ (delta + 2 * v) <=
      64 * (2 * T) ^ (delta + 2 * v) := by
    gcongr
  have hCoord2T : 64 * U2 ^ (delta + 2 * v) <=
      64 * (2 * T) ^ (delta + 2 * v) := by
    gcongr
  have hCoord3T : 64 * U3 ^ (delta + 2 * v) <=
      64 * (2 * T) ^ (delta + 2 * v) := by
    gcongr
  have hWindowRaw := doubleFloorDefectWindow_card_cast_le
    (show 0 <= 5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta by
      positivity)
  have hPow0 : U0 ^ delta <= (2 * T) ^ delta := by gcongr
  have hPow1 : U1 ^ delta <= (2 * T) ^ delta := by gcongr
  have hPow2 : U2 ^ delta <= (2 * T) ^ delta := by gcongr
  have hPow3 : U3 ^ delta <= (2 * T) ^ delta := by gcongr
  have hTwoTPow : 1 <= (2 * T) ^ delta :=
    Real.one_le_rpow (by nlinarith) hdelta
  have hWindow :
      ((doubleFloorDefectWindow
        (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card :
          Real) <= 43 * (2 * T) ^ delta := by
    calc
      ((doubleFloorDefectWindow
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card :
            Real) <=
          4 * (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta) + 7 :=
        hWindowRaw
      _ <= 43 * (2 * T) ^ delta := by
        have hSum : U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta <=
            4 * (2 * T) ^ delta := by
          linarith only [hPow0, hPow1, hPow2, hPow3]
        nlinarith only [hSum, hTwoTPow]
  let Q0 : Real := (((d0.kI * 2 + d0.kII * 2) * 2 : Nat) : Real)
  let Q1 : Real := (((d1.kI * 2 + d1.kII * 2) * 2 : Nat) : Real)
  let Q2 : Real := (((d2.kI * 2 + d2.kII * 2) * 2 : Nat) : Real)
  let Q3 : Real := (((d3.kI * 2 + d3.kII * 2) * 2 : Nat) : Real)
  let L0 : Real := (((2 * Nat.ceil (U0 ^ delta + 1) + 1) *
    sharpShellLocalMultiplicityCap U0 : Nat) : Real)
  let L1 : Real := (((2 * Nat.ceil (U1 ^ delta + 1) + 1) *
    sharpShellLocalMultiplicityCap U1 : Nat) : Real)
  let L2 : Real := (((2 * Nat.ceil (U2 ^ delta + 1) + 1) *
    sharpShellLocalMultiplicityCap U2 : Nat) : Real)
  let L3 : Real := (((2 * Nat.ceil (U3 ^ delta + 1) + 1) *
    sharpShellLocalMultiplicityCap U3 : Nat) : Real)
  let W : Real := ((doubleFloorDefectWindow
    (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card : Real)
  have hQ0L0 : Q0 * L0 <= 64 * U0 ^ (delta + 2 * v) := by
    simpa only [Q0, L0] using hCoord0
  have hQ1L1 : Q1 * L1 <= 64 * U1 ^ (delta + 2 * v) := by
    simpa only [Q1, L1] using hCoord1
  have hQ2L2 : Q2 * L2 <= 64 * U2 ^ (delta + 2 * v) := by
    simpa only [Q2, L2] using hCoord2
  have hQ3L3 : Q3 * L3 <= 64 * U3 ^ (delta + 2 * v) := by
    simpa only [Q3, L3] using hCoord3
  have hW : W <= 43 * (2 * T) ^ delta := by
    simpa only [W] using hWindow
  have hLossEq : (heathBrownUniformMixedSelectionLoss output : Real) =
      (Q0 * Q1 * Q2 * Q3) * (L0 * L1 * L2 * L3) * W := by
    simp only [heathBrownUniformMixedSelectionLoss, Q0, Q1, Q2, Q3,
      L0, L1, L2, L3, W, Nat.cast_mul]
  rw [hLossEq]
  calc
    (Q0 * Q1 * Q2 * Q3) * (L0 * L1 * L2 * L3) * W =
        (Q0 * L0) * (Q1 * L1) * (Q2 * L2) * (Q3 * L3) * W := by ring
    _ <= (64 * U0 ^ (delta + 2 * v)) *
        (64 * U1 ^ (delta + 2 * v)) *
        (64 * U2 ^ (delta + 2 * v)) *
        (64 * U3 ^ (delta + 2 * v)) * W := by gcongr
    _ <= (64 * (2 * T) ^ (delta + 2 * v)) *
        (64 * (2 * T) ^ (delta + 2 * v)) *
        (64 * (2 * T) ^ (delta + 2 * v)) *
        (64 * (2 * T) ^ (delta + 2 * v)) * W := by gcongr
    _ <= (64 * (2 * T) ^ (delta + 2 * v)) ^ 4 *
        (43 * (2 * T) ^ delta) := by
      have hBaseNonneg : 0 <= 64 * (2 * T) ^ (delta + 2 * v) := by
        positivity
      calc
        (64 * (2 * T) ^ (delta + 2 * v)) *
            (64 * (2 * T) ^ (delta + 2 * v)) *
            (64 * (2 * T) ^ (delta + 2 * v)) *
            (64 * (2 * T) ^ (delta + 2 * v)) * W =
          (64 * (2 * T) ^ (delta + 2 * v)) ^ 4 * W := by ring
        _ <= (64 * (2 * T) ^ (delta + 2 * v)) ^ 4 *
            (43 * (2 * T) ^ delta) := by gcongr
    _ = (64 ^ 4 * 43 : Real) * (2 * T) ^ (5 * delta + 8 * v) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hTwoTPos.le]
      calc
        64 ^ 4 * (2 * T) ^ ((delta + 2 * v) * (4 : Nat)) *
            (43 * (2 * T) ^ delta) =
          (64 ^ 4 * 43) *
            ((2 * T) ^ ((delta + 2 * v) * (4 : Nat)) *
              (2 * T) ^ delta) := by ring
        _ = (64 ^ 4 * 43) *
            (2 * T) ^ ((delta + 2 * v) * (4 : Nat) + delta) := by
          rw [Real.rpow_add hTwoTPos]
        _ = (64 ^ 4 * 43) * (2 * T) ^ (5 * delta + 8 * v) := by
          norm_num
          ring_nf

/-- Adding one to a positive integer costs at most one additional binary
ceiling-logarithm. -/
theorem clog_two_add_one_le_succ_clog {A : Nat} (hA : 1 <= A) :
    Nat.clog 2 (A + 1) <= Nat.clog 2 A + 1 := by
  apply Nat.clog_le_of_le_pow
  calc
    A + 1 <= 2 * A := by omega
    _ <= 2 * (2 ^ Nat.clog 2 A) :=
      Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by omega) A)
    _ = 2 ^ (Nat.clog 2 A + 1) := by
      rw [pow_succ]
      omega

/-- Both exact Type-I reassembly factors are logarithmic and are therefore
eventually absorbed by any prescribed positive power.  They remain separate
in the conclusion because their source definitions use different `clog`
expressions. -/
theorem eventually_heathBrown_reassembly_factors_le_rpow
    {v : Real} (hv : 0 < v) :
    ∀ᶠ U : Real in atTop,
      heathBrownSourceReassemblyFactor U <= U ^ v ∧
      heathBrownLongTailReassemblyFactor U <= U ^ v := by
  let w : Real := v / 8
  have hw : 0 < w := by dsimp only [w]; positivity
  have hClog := eventually_const_mul_sharp_cutoff_clog_le_rpow
    (D := 1) (zeta := w) (by norm_num) hw
  let D : Real := 16 * (doubleFloorDefectWindow 1).card
  have hConst := eventually_const_le_rpow
    (D := D) (zeta := v / 2) (by positivity)
  filter_upwards [hClog, hConst, eventually_ge_atTop 8] with U hClogU hConstU hU
  let A := Nat.floor (sharpZetaCutoff U)
  have hUPos : 0 < U := by linarith
  have hAOne : 1 <= A := by
    dsimp only [A]
    have hATwo : 2 <= Nat.floor (sharpZetaCutoff U) := by
      apply Nat.le_floor
      exact (show (2 : Real) <= 4 * U by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff U).le
    omega
  have hClogA : (Nat.clog 2 A : Real) <= U ^ w := by
    simpa only [one_mul, A] using hClogU
  have hPowOne : 1 <= U ^ w := Real.one_le_rpow (by linarith) hw.le
  have hLongBase : ((Nat.clog 2 A + 1 : Nat) : Real) <= 2 * U ^ w := by
    push_cast
    linarith
  have hSourceBase : (Nat.clog 2 (A + 1) : Real) <= 2 * U ^ w := by
    have hNat := clog_two_add_one_le_succ_clog hAOne
    have hCast : (Nat.clog 2 (A + 1) : Real) <=
        ((Nat.clog 2 A + 1 : Nat) : Real) := by exact_mod_cast hNat
    exact hCast.trans hLongBase
  have hLongPow : (((Nat.clog 2 A + 1) ^ 4 : Nat) : Real) <=
      16 * U ^ (v / 2) := by
    calc
      (((Nat.clog 2 A + 1) ^ 4 : Nat) : Real) =
          (((Nat.clog 2 A + 1 : Nat) : Real)) ^ 4 := by norm_num
      _ <= (2 * U ^ w) ^ 4 := by gcongr
      _ = 16 * U ^ (v / 2) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_mul_natCast hUPos.le w 4]
        dsimp only [w]
        congr 1
        ring
  have hSourcePow : (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) <=
      16 * U ^ (v / 2) := by
    calc
      (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) =
          ((Nat.clog 2 (A + 1) : Real)) ^ 4 := by norm_num
      _ <= (2 * U ^ w) ^ 4 := by gcongr
      _ = 16 * U ^ (v / 2) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_mul_natCast hUPos.le w 4]
        dsimp only [w]
        congr 1
        ring
  have hAssemble (Q : Real) (hQ : Q <= 16 * U ^ (v / 2)) :
      Q * (doubleFloorDefectWindow 1).card <= U ^ v := by
    have hWindowNonneg :
        0 <= ((doubleFloorDefectWindow 1).card : Real) := by positivity
    calc
      Q * (doubleFloorDefectWindow 1).card <=
          (16 * U ^ (v / 2)) * (doubleFloorDefectWindow 1).card := by
        gcongr
      _ = D * U ^ (v / 2) := by dsimp only [D]; ring
      _ <= U ^ (v / 2) * U ^ (v / 2) := by gcongr
      _ = U ^ v := by
        rw [← Real.rpow_add hUPos]
        congr 1
        ring
  constructor
  · unfold heathBrownSourceReassemblyFactor
    simpa only [A] using hAssemble _ hSourcePow
  · unfold heathBrownLongTailReassemblyFactor
    simpa only [A] using hAssemble _ hLongPow

/-- Uniform cutoff form used by the global shell assembly.  Above one common
inner-height threshold, and for every four independently selected shells
below `2*T`, the exact mixed-selection loss is absorbed by `T^zeta` whenever
`zeta` strictly exceeds its explicit cost `5*delta + 8*v`. -/
theorem exists_heathBrown_mixed_selection_loss_cutoff
    {delta delta1 v zeta : Real}
    (hdelta : 0 <= delta) (hdelta1 : 0 < delta1) (hv : 0 < v)
    (hCost : 5 * delta + 8 * v < zeta) :
    ∃ Umin T0 : Real, 1 <= Umin ∧ 1 <= T0 ∧
      ∀ {sigma delta2 eta epsilon C0 C2 C4 : Real}
        {U0 U1 U2 U3 T : Real}
        {d0 : ClassicalBinaryShellDetectorData sigma U0 delta
          (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2))}
        {d1 : ClassicalBinaryShellDetectorData sigma U1 delta
          (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2))}
        {d2 : ClassicalBinaryShellDetectorData sigma U2 delta
          (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2))}
        {d3 : ClassicalBinaryShellDetectorData sigma U3 delta
          (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))}
        (output : HeathBrownUniformMixedSourceOutput sigma delta delta1 delta2
          eta epsilon C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3),
        T0 <= T -> Umin <= U0 -> Umin <= U1 -> Umin <= U2 -> Umin <= U3 ->
        U0 <= 2 * T -> U1 <= 2 * T -> U2 <= 2 * T -> U3 <= 2 * T ->
        (heathBrownUniformMixedSelectionLoss output : Real) <= T ^ zeta := by
  have hColor := eventually_classicalBinary_color_count_cast_le_general
    hdelta1 hv
  have hCap := eventually_sharpShellLocalMultiplicityCap_cast_le_rpow hv
  have hPrimitive :
      ∀ᶠ U : Real in atTop,
        1 <= U ∧
        (∀ {sigma d delta2 : Real}
          {D : ClassicalBinaryShellDetectorData sigma U d
            (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
            (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))},
          (((D.kI * 2 + D.kII * 2) * 2 : Nat) : Real) <= 8 * U ^ v) ∧
        (sharpShellLocalMultiplicityCap U : Real) <= U ^ v := by
    filter_upwards [eventually_ge_atTop 1, hColor, hCap] with U hU hColorU hCapU
    exact ⟨hU, hColorU, hCapU⟩
  obtain ⟨Umin, hUmin⟩ := (eventually_atTop.1 hPrimitive)
  let p : Real := 5 * delta + 8 * v
  have hp : 0 <= p := by dsimp only [p]; positivity
  have hMargin : 0 < zeta - p := by dsimp only [p]; linarith
  let Dconst : Real := (64 ^ 4 * 43 : Real) * 2 ^ p
  have hAbsorb := eventually_const_le_rpow (D := Dconst) hMargin
  have hLargeT : ∀ᶠ T : Real in atTop, 1 <= T ∧
      Dconst <= T ^ (zeta - p) := by
    filter_upwards [eventually_ge_atTop 1, hAbsorb] with T hT hD
    exact ⟨hT, hD⟩
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hLargeT
  let Ucut := max 1 Umin
  let Tcut := max 1 T0
  refine ⟨Ucut, Tcut, le_max_left _ _, le_max_left _ _, ?_⟩
  intro sigma delta2 eta epsilon C0 C2 C4 U0 U1 U2 U3 T
    d0 d1 d2 d3 output hT hU0 hU1 hU2 hU3 hU0T hU1T hU2T hU3T
  have hTData := hT0 T ((le_max_right _ _).trans hT)
  have hData0 := hUmin U0 ((le_max_right _ _).trans hU0)
  have hData1 := hUmin U1 ((le_max_right _ _).trans hU1)
  have hData2 := hUmin U2 ((le_max_right _ _).trans hU2)
  have hData3 := hUmin U3 ((le_max_right _ _).trans hU3)
  have hPhysical := heathBrownUniformMixedSelectionLoss_le_physical output
    hTData.1 hdelta hv.le hData0.1 hData1.1 hData2.1 hData3.1
    hU0T hU1T hU2T hU3T hData0.2.1 hData1.2.1 hData2.2.1 hData3.2.1
    hData0.2.2 hData1.2.2 hData2.2.2 hData3.2.2
  have hTPos : 0 < T := zero_lt_one.trans_le hTData.1
  have hRewrite :
      (64 ^ 4 * 43 : Real) * (2 * T) ^ p = Dconst * T ^ p := by
    dsimp only [Dconst]
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hTPos.le]
    ring
  calc
    (heathBrownUniformMixedSelectionLoss output : Real) <=
        (64 ^ 4 * 43 : Real) * (2 * T) ^ p := by
      simpa only [p] using hPhysical
    _ = Dconst * T ^ p := hRewrite
    _ <= T ^ (zeta - p) * T ^ p :=
      mul_le_mul_of_nonneg_right hTData.2 (Real.rpow_nonneg hTPos.le _)
    _ = T ^ zeta := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring

#print axioms eventually_sharpShellLocalMultiplicityCap_cast_le_rpow
#print axioms eventually_classicalBinary_color_count_cast_le_general
#print axioms detector_displacement_window_cast_le
#print axioms heathBrownUniformMixedSelectionLoss_le_physical
#print axioms clog_two_add_one_le_succ_clog
#print axioms eventually_heathBrown_reassembly_factors_le_rpow
#print axioms exists_heathBrown_mixed_selection_loss_cutoff

end

end GafniTao
