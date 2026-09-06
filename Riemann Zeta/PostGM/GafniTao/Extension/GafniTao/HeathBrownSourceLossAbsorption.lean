import GafniTao.HeathBrownUniformPowerConstants
import GafniTao.Pintz2023DetectorEventually

/-!
# Eventual absorption of source shell and normalization losses

The Type-II detector loses its number of dyadic shells.  That integer is at
most a binary logarithm of `floor (U ^ delta)`, so it is genuinely
sub-polynomial.  The theorem below proves the exact real inequality needed
to absorb it into an arbitrary positive power of `U`.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A fixed constant times every admissible binary-shell count is eventually
bounded by an arbitrary positive power of the physical height. -/
theorem eventually_const_mul_clog_floor_rpow_le_rpow
    {D delta zeta : Real} (hD : 0 ≤ D) (hdelta : 0 < delta)
    (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      ∀ k : Nat, k ≤ Nat.clog 2 (Nat.floor (U ^ delta)) →
        D * (k : Real) ≤ U ^ zeta := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let E : Real := D * (1 + delta / Real.log 2)
  have hE : 0 ≤ E := by
    dsimp only [E]
    have : 0 ≤ delta / Real.log 2 := by positivity
    positivity
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := E) (p := 1) (q := zeta) (b := 1)
    hE hzeta (by norm_num)
  filter_upwards [hSmall, eventually_ge_atTop (Real.exp 1)] with U hSmallU hU
  intro k hk
  have hUPos : 0 < U := (Real.exp_pos 1).trans_le hU
  have hUOne : 1 ≤ U := by
    have hExpOne : (1 : Real) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr zero_lt_one).le
    exact hExpOne.trans hU
  have hlogU : 1 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 1) hU
    simpa using this
  have hPowOne : 1 ≤ U ^ delta :=
    Real.one_le_rpow hUOne hdelta.le
  have hFloorOne : 1 ≤ Nat.floor (U ^ delta) := by
    rw [Nat.le_floor_iff (Real.rpow_nonneg hUPos.le delta)]
    exact_mod_cast hPowOne
  have hClogRaw := natCast_clog_two_le_one_add_log
    (Nat.floor (U ^ delta)) hFloorOne
  have hFloorPos : (0 : Real) < Nat.floor (U ^ delta) := by
    exact_mod_cast (show 0 < Nat.floor (U ^ delta) by omega)
  have hFloorUpper : (Nat.floor (U ^ delta) : Real) ≤ U ^ delta :=
    Nat.floor_le (Real.rpow_nonneg hUPos.le delta)
  have hLogFloor : Real.log (Nat.floor (U ^ delta) : Real) ≤
      delta * Real.log U := by
    calc
      Real.log (Nat.floor (U ^ delta) : Real) ≤ Real.log (U ^ delta) :=
        Real.log_le_log hFloorPos hFloorUpper
      _ = delta * Real.log U := by
        rw [Real.log_rpow hUPos]
  have hkR : (k : Real) ≤
      (1 + delta / Real.log 2) * Real.log U := by
    have hkClog : (k : Real) ≤
        (Nat.clog 2 (Nat.floor (U ^ delta)) : Real) := by
      exact_mod_cast hk
    calc
      (k : Real) ≤
          (Nat.clog 2 (Nat.floor (U ^ delta)) : Real) := hkClog
      _ ≤ 1 + Real.log (Nat.floor (U ^ delta) : Real) /
          Real.log 2 := hClogRaw
      _ ≤ 1 + (delta * Real.log U) / Real.log 2 := by gcongr
      _ ≤ (1 + delta / Real.log 2) * Real.log U := by
        field_simp [hlogTwo.ne']
        nlinarith
  have hFront : D * (k : Real) ≤ E * Real.log U := by
    dsimp only [E]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hkR hD
  have hCancel : U ^ zeta * U ^ (-zeta) = 1 := by
    rw [← Real.rpow_add hUPos]
    norm_num
  have hScaled : D * (k : Real) * U ^ (-zeta) ≤ 1 := by
    calc
      D * (k : Real) * U ^ (-zeta) ≤
          (E * Real.log U) * U ^ (-zeta) :=
        mul_le_mul_of_nonneg_right hFront (Real.rpow_nonneg hUPos.le _)
      _ ≤ 1 := by simpa only [Real.rpow_one] using hSmallU
  have hPowerPos : 0 < U ^ zeta := Real.rpow_pos_of_pos hUPos zeta
  calc
    D * (k : Real) =
        (D * (k : Real) * U ^ (-zeta)) * U ^ zeta := by
      rw [mul_assoc, mul_comm (U ^ (-zeta)) (U ^ zeta),
        ← Real.rpow_add hUPos]
      norm_num
    _ ≤ 1 * U ^ zeta :=
      mul_le_mul_of_nonneg_right hScaled hPowerPos.le
    _ = U ^ zeta := one_mul _

/-- Reciprocal form of the exact Type-II coefficient loss. -/
theorem rpow_neg_le_typeII_normalization_coefficient
    {U C eta zeta : Real} {k : Nat}
    (hU : 0 < U) (hC : 0 < C) (hk : 0 < k)
    (hLoss : (16 * C * (2 : Real) ^ eta / 9) * (k : Real) ≤
      U ^ zeta) :
    U ^ (-zeta) ≤ 9 / (16 * (k : Real) * C * (2 : Real) ^ eta) := by
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have hTwo : 0 < (2 : Real) ^ eta := Real.rpow_pos_of_pos (by norm_num) _
  have hUPow : 0 < U ^ zeta := Real.rpow_pos_of_pos hU _
  have hDen : 0 < 16 * (k : Real) * C * (2 : Real) ^ eta := by positivity
  rw [Real.rpow_neg hU.le, inv_eq_one_div]
  rw [div_le_div_iff₀ hUPow hDen]
  calc
    1 * (16 * (k : Real) * C * (2 : Real) ^ eta) =
        9 * ((16 * C * (2 : Real) ^ eta / 9) * (k : Real)) := by ring
    _ ≤ 9 * U ^ zeta := mul_le_mul_of_nonneg_left hLoss (by norm_num)

/-- The exact selected Type-II threshold loses only an arbitrary small
power of `U`, uniformly over every admissible shell index. -/
theorem eventually_typeII_selectedThreshold_lower
    {delta eta zeta C : Real}
    (hdelta : 0 < delta) (hzeta : 0 < zeta) (hC : 0 < C) :
    ∀ᶠ U : Real in atTop,
      ∀ (Y X kI kII : Nat) (sigma q0 : Real)
          (q : Fin (kI * 2 + kII * 2)) (r : Fin (kII * 2)),
        kII ≤ Nat.clog 2 (Nat.floor (U ^ delta)) →
        0 < kII →
        binaryScaleLabel q = Sum.inr r →
        0 < classicalBinarySelectedN Y X kI kII q →
        U ^ (-zeta) *
            (classicalBinarySelectedN Y X kI kII q : Real) ^
              (sigma - eta) ≤
          classicalBinarySelectedThreshold
            Y X kI kII sigma q0 eta C q := by
  let D : Real := 16 * C * (2 : Real) ^ eta / 9
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hAbsorb := eventually_const_mul_clog_floor_rpow_le_rpow
    hD hdelta hzeta
  filter_upwards [hAbsorb, eventually_gt_atTop 0] with U hAbsorbU hU
  intro Y X kI kII sigma q0 q r hkII hkIIPos hq hN
  have hLoss : D * (kII : Real) ≤ U ^ zeta := hAbsorbU kII hkII
  have hCoefficient := rpow_neg_le_typeII_normalization_coefficient
    hU hC hkIIPos (by simpa only [D] using hLoss)
  have hNPower : 0 ≤
      (classicalBinarySelectedN Y X kI kII q : Real) ^
        (sigma - eta) := Real.rpow_nonneg (by positivity) _
  rw [classicalBinarySelectedThreshold_typeII_selected_normalized
    hq hN hkIIPos hC]
  exact mul_le_mul_of_nonneg_right hCoefficient hNPower

#print axioms eventually_const_mul_clog_floor_rpow_le_rpow
#print axioms rpow_neg_le_typeII_normalization_coefficient
#print axioms eventually_typeII_selectedThreshold_lower

end

end GafniTao
