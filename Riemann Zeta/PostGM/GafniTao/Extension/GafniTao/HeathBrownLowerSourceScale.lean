import GafniTao.HeathBrownSelectedScaleTwo
import GafniTao.HeathBrownFiniteLossAbsorption

/-!
# Physical powering of a lower classified Type-I source block

The lower alternative in the frozen smooth-source classification has source
index `r < 2`.  After the energy-safe dyadic extraction its literal length is
still large enough to bound the chosen power uniformly, while its square is
below the physical height.  This file proves those comparisons without
identifying a floor with a real power.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_heathBrown_lower_source_scale
    {delta1 delta2 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1) :
    ∀ᶠ U : Real in atTop,
      let Y := Nat.floor (U ^ delta1)
      ∀ {r P : Nat}, r < 2 ->
        P < 2 * (2 ^ r * Y) -> 2 ^ r * Y < 4 * P ->
        let p := heathBrownSourcePower P U
        1 < P /\ U ^ (delta1 / 2) <= (P : Real) /\
        2 <= p /\ (P : Real) ^ p <= U /\
        U < (P : Real) ^ (p + 1) /\
        U ^ 2 <= ((P : Real) ^ p) ^ 3 /\
        p <= Nat.ceil (4 / delta2) := by
  obtain ⟨Ufloor, _hUfloor, hFloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := 3 * delta1 / 4) (b := delta1) (by positivity) (by nlinarith)
  have hLowerAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (4 : Real)) (a := delta1 / 2) (b := 3 * delta1 / 4)
      (by nlinarith)
  have hdelta1Twice : 2 * delta1 < 1 := by nlinarith
  have hUpperAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (16 : Real)) (a := 2 * delta1) (b := 1) hdelta1Twice
  filter_upwards [eventually_ge_atTop Ufloor, hLowerAbsorb, hUpperAbsorb,
      eventually_ge_atTop (8 : Real)]
    with U hUfloor hLowerAbsorbU hUpperAbsorbU hUEight
  dsimp only
  intro r P hr hPUpper hPLower
  let Y := Nat.floor (U ^ delta1)
  let Q := 2 ^ r * Y
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hYLower : U ^ (3 * delta1 / 4) <= (Y : Real) := by
    simpa only [Y] using hFloor U hUfloor
  have hYPosReal : (0 : Real) < Y :=
    (Real.rpow_pos_of_pos hUPos _).trans_le hYLower
  have hYPos : 0 < Y := by exact_mod_cast hYPosReal
  have hYQ : Y <= Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega : 0 < (2 : Nat)) r)
  have hYFourP : Y < 4 * P := hYQ.trans_lt (by simpa only [Q] using hPLower)
  have hPLowerReal : U ^ (delta1 / 2) <= (P : Real) := by
    have hFourLower : 4 * U ^ (delta1 / 2) <= (Y : Real) :=
      hLowerAbsorbU.trans hYLower
    have hYFourPReal : (Y : Real) < 4 * (P : Real) := by exact_mod_cast hYFourP
    linarith
  have hPOne : 1 < P := by
    have hPowOne : (1 : Real) < U ^ (delta2 / 4) :=
      Real.one_lt_rpow (by linarith) (by positivity)
    exact_mod_cast hPowOne.trans_le hPLowerReal
  have hrLe : r <= 1 := by omega
  have hPowR : 2 ^ r <= 2 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hrLe
  have hYUpper : (Y : Real) <= U ^ delta1 := by
    simpa only [Y] using Nat.floor_le (Real.rpow_nonneg hUPos.le delta1)
  have hPBound : (P : Real) < 4 * U ^ delta1 := by
    have hPUpperQ : P < 2 * Q := by simpa only [Q, Y] using hPUpper
    have hPUpperReal : (P : Real) < 2 * ((2 ^ r : Nat) : Real) * (Y : Real) := by
      have hCast : (P : Real) < ((2 * Q : Nat) : Real) := by
        exact_mod_cast hPUpperQ
      simpa only [Q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        mul_assoc] using hCast
    calc
      (P : Real) < 2 * ((2 ^ r : Nat) : Real) * (Y : Real) := hPUpperReal
      _ <= 4 * (Y : Real) := by
        have hCast : (((2 ^ r : Nat) : Real)) <= 2 := by exact_mod_cast hPowR
        nlinarith
      _ <= 4 * U ^ delta1 := by gcongr
  have hPSquare : (P : Real) ^ 2 <= U := by
    have hRpowSquare : (U ^ delta1) ^ (2 : Nat) = U ^ (2 * delta1) := by
      calc
        (U ^ delta1) ^ (2 : Nat) = (U ^ delta1) ^ (2 : Real) :=
          (Real.rpow_natCast (U ^ delta1) 2).symm
        _ = U ^ (delta1 * 2) :=
          (Real.rpow_mul hUPos.le delta1 2).symm
        _ = U ^ (2 * delta1) := by ring_nf
    have hSquareStrict : (P : Real) ^ 2 < 16 * (U ^ delta1) ^ 2 := by
      have hPNonneg : 0 <= (P : Real) := by positivity
      have hPowNonneg : 0 <= U ^ delta1 := Real.rpow_nonneg hUPos.le _
      nlinarith [hPBound]
    rw [hRpowSquare] at hSquareStrict
    exact hSquareStrict.le.trans (hUpperAbsorbU.trans_eq (Real.rpow_one U))
  have hPower := heathBrownSourcePower_spec_two hPOne hUPos hPSquare
  dsimp only at hPower
  let p := heathBrownSourcePower P U
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlogP : 0 < Real.log (P : Real) := Real.log_pos (by exact_mod_cast hPOne)
  have hLogLower : (delta1 / 2) * Real.log U <= Real.log (P : Real) := by
    have hLog := Real.log_le_log (Real.rpow_pos_of_pos hUPos _)
      hPLowerReal
    rw [Real.log_rpow hUPos] at hLog
    exact hLog
  have hRatioUpper : Real.log U / Real.log (P : Real) <= 2 / delta1 := by
    apply (div_le_iff₀ hlogP).2
    calc
      Real.log U = (2 / delta1) * ((delta1 / 2) * Real.log U) := by
        field_simp [hdelta1.ne']
      _ <= (2 / delta1) * Real.log (P : Real) := by gcongr
  have hpReal : (p : Real) <= 4 / delta2 := by
    have hRatioCap : 2 / delta1 <= 4 / delta2 := by
      calc
        2 / delta1 = (2 * delta2) / (delta1 * delta2) := by
          field_simp [hdelta1.ne', hdelta2.ne']
        _ <= (4 * delta1) / (delta1 * delta2) := by
          apply div_le_div_of_nonneg_right
          · nlinarith [hdeltaOrder]
          · positivity
        _ = 4 / delta2 := by
          field_simp [hdelta1.ne', hdelta2.ne']
    exact (Nat.floor_le (by positivity : 0 <=
      Real.log U / Real.log (P : Real))).trans (hRatioUpper.trans hRatioCap)
  have hpBound : p <= Nat.ceil (4 / delta2) := by
    exact_mod_cast hpReal.trans (Nat.le_ceil (4 / delta2))
  exact ⟨hPOne, hPLowerReal, hPower.1, hPower.2.1,
    hPower.2.2.1, hPower.2.2.2, hpBound⟩

#print axioms eventually_heathBrown_lower_source_scale

end

end GafniTao
