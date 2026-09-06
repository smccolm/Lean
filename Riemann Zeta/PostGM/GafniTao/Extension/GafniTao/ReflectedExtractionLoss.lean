import GafniTao.ReflectedWideEnergyBound
import GafniTao.HeathBrownPoweredThresholdLower

/-!
# Explicit loss from reflected energy extraction

The four-coordinate displacement and dyadic colourings have a finite loss.
This file bounds that literal loss rather than replacing it by an unnamed
`T^epsilon` factor.
-/

open Filter

namespace GafniTao

noncomputable section

/-- Cardinality of the doubled-floor defect window, as a real inequality. -/
theorem doubleFloorDefectWindow_card_cast_le
    {eta : Real} (heta : 0 <= eta) :
    ((doubleFloorDefectWindow eta).card : Real) <= 4 * eta + 7 := by
  let C : Int := ⌈2 * eta + 2⌉
  have hC : (0 : Int) <= C := by
    apply Int.ceil_nonneg
    linarith
  have hCard : (doubleFloorDefectWindow eta).card = (2 * C + 1).toNat := by
    simp only [doubleFloorDefectWindow, Int.card_Icc, C]
    congr 1
    ring
  have hToNat : ((2 * C + 1).toNat : Int) = 2 * C + 1 := by
    rw [Int.toNat_of_nonneg]
    omega
  have hCeil : (C : Real) < 2 * eta + 3 := by
    dsimp only [C]
    have h := Int.ceil_lt_add_one (2 * eta + 2)
    linarith
  rw [hCard]
  have hCast : (((2 * C + 1).toNat : Nat) : Real) = 2 * (C : Real) + 1 := by
    exact_mod_cast hToNat
  rw [hCast]
  linarith

/-- The literal dyadic/displacement extraction factor has exponent
`4*v + 5*d` when the dyadic count is at most `T^v`. -/
theorem reflectedDyadicExtractionFactor_le
    {T d v : Real} {k : Nat}
    (hT : 1 <= T) (hd : 0 <= d)
    (hk : (k : Real) <= T ^ v) :
    reflectedDyadicExtractionFactor (T ^ d) k <=
      (16 * 4096 * 43 : Real) * T ^ (4 * v + 5 * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hH : 1 <= T ^ d := Real.one_le_rpow hT hd
  have hK : ((2 * k : Nat) : Real) <= 2 * T ^ v := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_left hk (by norm_num : (0 : Real) <= 2)
  have hCeil : ((2 * ⌈T ^ d + 1⌉₊ + 1 : Nat) : Real) <=
      8 * T ^ d := by
    have hCeilRaw := Nat.ceil_lt_add_one
      (show 0 <= T ^ d + 1 by positivity)
    push_cast
    linarith
  have hWindow := doubleFloorDefectWindow_card_cast_le
    (show 0 <= 1 + 4 * (T ^ d + 1) by positivity)
  have hWindow' :
      ((doubleFloorDefectWindow (1 + 4 * (T ^ d + 1))).card : Real) <=
        43 * T ^ d := by
    calc
      ((doubleFloorDefectWindow (1 + 4 * (T ^ d + 1))).card : Real) <=
          4 * (1 + 4 * (T ^ d + 1)) + 7 := hWindow
      _ <= 43 * T ^ d := by nlinarith
  have hKPow : (((2 * k : Nat) : Real) ^ 4) <=
      16 * T ^ (4 * v) := by
    calc
      (((2 * k : Nat) : Real) ^ 4) <= (2 * T ^ v) ^ 4 := by
        gcongr
      _ = 16 * T ^ (4 * v) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        ring
  have hCeilPow : (((2 * ⌈T ^ d + 1⌉₊ + 1 : Nat) : Real) ^ 4) <=
      4096 * T ^ (4 * d) := by
    calc
      (((2 * ⌈T ^ d + 1⌉₊ + 1 : Nat) : Real) ^ 4) <=
          (8 * T ^ d) ^ 4 := by gcongr
      _ = 4096 * T ^ (4 * d) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        ring
  unfold reflectedDyadicExtractionFactor
  calc
    (((2 * k : Nat) : Real) ^ 4) *
          (((2 * ⌈T ^ d + 1⌉₊ + 1 : Nat) : Real) ^ 4) *
          (doubleFloorDefectWindow (1 + 4 * (T ^ d + 1))).card <=
        (16 * T ^ (4 * v)) * (4096 * T ^ (4 * d)) *
          (43 * T ^ d) := by gcongr
    _ = (16 * 4096 * 43 : Real) *
        (T ^ (4 * v) * T ^ (4 * d) * T ^ d) := by ring
    _ = (16 * 4096 * 43 : Real) * T ^ (4 * v + 5 * d) := by
      rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
      congr 1
      ring_nf

/-- After also including the sign split, the complete reflected extraction
loss is eventually absorbed by one explicitly supplied positive power. -/
theorem eventually_reflectedExtractionLoss_le_rpow
    {d v zeta : Real} (hd : 0 <= d)
    (hzeta : 4 * v + 5 * d < zeta) :
    ∀ᶠ T : Real in atTop,
      ∀ (k : Nat), (k : Real) <= T ^ v ->
      16 * ((doubleFloorDefectWindow 1).card : Real) *
          reflectedDyadicExtractionFactor (T ^ d) k <= T ^ zeta := by
  have hMargin : 0 < zeta - (4 * v + 5 * d) := by linarith
  have hConst := eventually_const_le_rpow
    (D := 16 * ((doubleFloorDefectWindow 1).card : Real) *
      (16 * 4096 * 43 : Real)) hMargin
  filter_upwards [hConst, eventually_ge_atTop (1 : Real)] with T hConstT hT
  intro k hk
  have hFactor := reflectedDyadicExtractionFactor_le hT hd
    (k := k) hk
  have hNonneg : 0 <= 16 * ((doubleFloorDefectWindow 1).card : Real) := by
    positivity
  calc
    16 * ((doubleFloorDefectWindow 1).card : Real) *
        reflectedDyadicExtractionFactor (T ^ d) k <=
      16 * ((doubleFloorDefectWindow 1).card : Real) *
        ((16 * 4096 * 43 : Real) * T ^ (4 * v + 5 * d)) := by
          gcongr
    _ = (16 * ((doubleFloorDefectWindow 1).card : Real) *
        (16 * 4096 * 43 : Real)) * T ^ (4 * v + 5 * d) := by ring
    _ <= T ^ (zeta - (4 * v + 5 * d)) * T ^ (4 * v + 5 * d) := by
      gcongr
    _ = T ^ zeta := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
      congr 1
      ring

#print axioms doubleFloorDefectWindow_card_cast_le
#print axioms reflectedDyadicExtractionFactor_le
#print axioms eventually_reflectedExtractionLoss_le_rpow

end

end GafniTao
