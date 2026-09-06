import GafniTao.HeathBrownCardinalityExponent
import GafniTao.HeathBrownCommonLogarithmicRelation

/-!
# Transfer between the consecutive common logarithmic bases

The two cardinality packets live at `2^P N^p` and `2^P N^(p+1)`.
For `p >= 2`, the latter base has logarithmic size at most `3/2` times
the former.  This file proves that statement directly from the exact finite
powers and transfers cardinality exponents without an asymptotic equality.
-/

namespace GafniTao

noncomputable section

/-- Exact square/cube comparison for consecutive common source bases. -/
theorem heathBrown_consecutive_common_base_sq_le_cube
    {N p P : Nat} (hN : 0 < N) (hp : 2 <= p) :
    (((2 ^ P * N ^ (p + 1) : Nat) : Real)) ^ 2 <=
      (((2 ^ P * N ^ p : Nat) : Real)) ^ 3 := by
  have hNone : (1 : Nat) <= N := hN
  have hNtwo : N ^ 2 <= N ^ p := Nat.pow_le_pow_right hNone hp
  have hD : (1 : Nat) <= 2 ^ P :=
    pow_pos (by norm_num : (0 : Nat) < 2) P
  have hDsq : (2 ^ P : Nat) ^ 2 <= (2 ^ P : Nat) ^ 3 :=
    Nat.pow_le_pow_right hD (by omega)
  have hNtwoReal : (N : Real) ^ 2 <= (N : Real) ^ p := by
    exact_mod_cast hNtwo
  have hDsqReal : ((2 ^ P : Nat) : Real) ^ 2 <=
      ((2 ^ P : Nat) : Real) ^ 3 := by exact_mod_cast hDsq
  calc
    (((2 ^ P * N ^ (p + 1) : Nat) : Real)) ^ 2 =
        ((2 ^ P : Nat) : Real) ^ 2 *
          ((N : Real) ^ p) ^ 2 * (N : Real) ^ 2 := by
      norm_num [pow_succ]
      ring
    _ <= ((2 ^ P : Nat) : Real) ^ 2 *
          ((N : Real) ^ p) ^ 2 * (N : Real) ^ p := by
      gcongr
    _ <= ((2 ^ P : Nat) : Real) ^ 3 *
          ((N : Real) ^ p) ^ 2 * (N : Real) ^ p := by
      gcongr
    _ = ((2 ^ P : Nat) : Real) ^ 3 *
          ((N : Real) ^ p) ^ 3 := by ring
    _ = (((2 ^ P * N ^ p : Nat) : Real)) ^ 3 := by
      norm_num
      ring

/-- Logarithmic exponents of the same positive quantity transfer from a
base whose square is at most the cube of the smaller base. -/
theorem heathBrown_logExponent_transfer_three_halves
    {x x' y : Real} (hx : 1 < x) (hx' : 1 < x') (hy : 1 <= y)
    (hScale : (x') ^ 2 <= x ^ 3) :
    heathBrownLogExponent x y <=
      (3 / 2 : Real) * heathBrownLogExponent x' y := by
  let q := heathBrownLogExponent x' y
  have hx'pos : 0 < x' := zero_lt_one.trans hx'
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hq : 0 <= q := by
    apply (Real.strictMono_rpow_of_base_gt_one hx').le_iff_le.mp
    simpa only [Real.rpow_zero, q, rpow_heathBrownLogExponent hx' hypos]
  have hxPow : x ^ heathBrownLogExponent x y = y :=
    rpow_heathBrownLogExponent hx hypos
  have hx'Pow : (x') ^ q = y := rpow_heathBrownLogExponent hx' hypos
  have hTau := heathBrownLogExponent_le_three_halves hx hx'pos hScale
  have hBase : x' <= x ^ (3 / 2 : Real) := by
    calc
      x' = x ^ heathBrownLogExponent x x' :=
        (rpow_heathBrownLogExponent hx hx'pos).symm
      _ <= x ^ (3 / 2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hx.le hTau
  have hPower : y <= x ^ ((3 / 2 : Real) * q) := by
    calc
      y = (x') ^ q := hx'Pow.symm
      _ <= (x ^ (3 / 2 : Real)) ^ q :=
        Real.rpow_le_rpow (zero_lt_one.trans hx').le hBase hq
      _ = x ^ ((3 / 2 : Real) * q) := by
        rw [Real.rpow_mul (zero_lt_one.trans hx).le]
  apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
  simpa only [hxPow] using hPower

/-- Specialization of the base-transfer inequality to the two exact common
Heath--Brown lengths. -/
theorem heathBrown_common_cardinality_base_transfer
    {N p P : Nat} {card : Real} (hN : 1 < N) (hp : 2 <= p)
    (hcard : 1 <= card) :
    heathBrownLogExponent (((2 ^ P * N ^ p : Nat) : Real)) card <=
      (3 / 2 : Real) *
        heathBrownLogExponent
          (((2 ^ P * N ^ (p + 1) : Nat) : Real)) card := by
  have hNpos : 0 < N := by omega
  have hNpOne : 1 < N ^ p := one_lt_pow₀ hN (by omega)
  have hNpNextOne : 1 < N ^ (p + 1) := one_lt_pow₀ hN (by omega)
  have hxNat : 1 < 2 ^ P * N ^ p := by
    exact hNpOne.trans_le
      (Nat.le_mul_of_pos_left (N ^ p) (pow_pos (by omega) P))
  have hxNextNat : 1 < 2 ^ P * N ^ (p + 1) := by
    exact hNpNextOne.trans_le
      (Nat.le_mul_of_pos_left (N ^ (p + 1)) (pow_pos (by omega) P))
  apply heathBrown_logExponent_transfer_three_halves
  · exact_mod_cast hxNat
  · exact_mod_cast hxNextNat
  · exact hcard
  · exact heathBrown_consecutive_common_base_sq_le_cube hNpos hp

#print axioms heathBrown_consecutive_common_base_sq_le_cube
#print axioms heathBrown_logExponent_transfer_three_halves
#print axioms heathBrown_common_cardinality_base_transfer

end

end GafniTao
