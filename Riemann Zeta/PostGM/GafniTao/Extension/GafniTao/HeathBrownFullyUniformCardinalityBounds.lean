import GafniTao.HeathBrownFullyUniformColorBound

/-!
# Common physical cardinality bounds

The two consecutive powered packets may choose different dyadic blocks.  The
following exact bounds replace both choices by a fixed common factor `2^P`
while retaining the same globally selected `Cp` and `Cmv`.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

private theorem meanValueExpression_mono_length
    {B V M M' : Real} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hMM' : M ≤ M') :
    M ^ 2 / V ^ 2 + B * M / V ^ 2 ≤
      M' ^ 2 / V ^ 2 + B * M' / V ^ 2 := by
  have hM' : 0 ≤ M' := hM.trans hMM'
  have hden : 0 ≤ V ^ 2 := sq_nonneg V
  gcongr

/-- The `p`-packet cardinality bound with its variable dyadic block replaced
by the fixed common length `(2^P) N^p`. -/
theorem HeathBrownFullyUniformOutputs.card_le_common
    {epsilon B R eta L : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hpP : p ≤ P) (hCmv : 0 ≤ Cmv) (hB : 0 ≤ B) :
    (W.card : Real) ≤
      P * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ p : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ p : Nat)) /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2) := by
  have hRaw := full.card.card_le_bound
  unfold HeathBrownPoweredCardinalityPacket.bound at hRaw
  rw [full.card_Cp, full.card_Cmv] at hRaw
  have hrP : full.card.r ≤ P :=
    (Finset.mem_range.mp full.card.hr).le.trans hpP
  have hTwoNat : 2 ^ full.card.r ≤ 2 ^ P :=
    Nat.pow_le_pow_right (by omega) hrP
  have hLengthNat : 2 ^ full.card.r * N ^ p ≤ 2 ^ P * N ^ p :=
    Nat.mul_le_mul_right (N ^ p) hTwoNat
  have hLength : ((2 ^ full.card.r * N ^ p : Nat) : Real) ≤
      ((2 ^ P : Nat) : Real) * (N ^ p : Nat) := by
    exact_mod_cast hLengthNat
  have hExpr := meanValueExpression_mono_length
    (V := heathBrownPoweredThreshold N p L Cp eta) hB
    (Nat.cast_nonneg (2 ^ full.card.r * N ^ p)) hLength
  have hpReal : (p : Real) ≤ P := by exact_mod_cast hpP
  have hExprNonneg : 0 ≤
      (((2 ^ P : Nat) : Real) * (N ^ p : Nat)) ^ 2 /
          (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
        B * (((2 ^ P : Nat) : Real) * (N ^ p : Nat)) /
          (heathBrownPoweredThreshold N p L Cp eta) ^ 2 := by positivity
  calc
    (W.card : Real) ≤ p * Cmv *
        (((2 ^ full.card.r * N ^ p : Nat) : Real) ^ 2 /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
          B * ((2 ^ full.card.r * N ^ p : Nat) : Real) /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2) := hRaw
    _ ≤ p * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ p : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ p : Nat)) /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hExpr (mul_nonneg (Nat.cast_nonneg _) hCmv)
    _ ≤ P * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ p : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ p : Nat)) /
            (heathBrownPoweredThreshold N p L Cp eta) ^ 2) := by
      gcongr

/-- The `(p+1)` packet with its variable block replaced by
`(2^P) N^(p+1)`. -/
theorem HeathBrownFullyUniformOutputs.next_le_common
    {epsilon B R eta L : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hpP : p ≤ P) (hCmv : 0 ≤ Cmv) (hB : 0 ≤ B) :
    (W.card : Real) ≤
      ((P + 1 : Nat) : Real) * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2) := by
  have hRaw := full.next.card_le_bound
  unfold HeathBrownPoweredCardinalityPacket.bound at hRaw
  rw [full.next_Cp, full.next_Cmv] at hRaw
  have hrP : full.next.r ≤ P := by
    have hr : full.next.r < p + 1 := Finset.mem_range.mp full.next.hr
    omega
  have hTwoNat : 2 ^ full.next.r ≤ 2 ^ P :=
    Nat.pow_le_pow_right (by omega) hrP
  have hLengthNat : 2 ^ full.next.r * N ^ (p + 1) ≤
      2 ^ P * N ^ (p + 1) := Nat.mul_le_mul_right _ hTwoNat
  have hLength : ((2 ^ full.next.r * N ^ (p + 1) : Nat) : Real) ≤
      ((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat) := by
    exact_mod_cast hLengthNat
  have hExpr := meanValueExpression_mono_length
    (V := heathBrownPoweredThreshold N (p + 1) L Cp eta) hB
    (Nat.cast_nonneg (2 ^ full.next.r * N ^ (p + 1))) hLength
  have hpNat : p + 1 ≤ P + 1 := Nat.add_le_add_right hpP 1
  have hpReal : ((p + 1 : Nat) : Real) ≤ ((P + 1 : Nat) : Real) := by
    exact_mod_cast hpNat
  have hExprNonneg : 0 ≤
      (((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) ^ 2 /
          (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 +
        B * (((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) /
          (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 := by positivity
  calc
    (W.card : Real) ≤ ((p + 1 : Nat) : Real) * Cmv *
        (((2 ^ full.next.r * N ^ (p + 1) : Nat) : Real) ^ 2 /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 +
          B * ((2 ^ full.next.r * N ^ (p + 1) : Nat) : Real) /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2) := hRaw
    _ ≤ ((p + 1 : Nat) : Real) * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hExpr
        (mul_nonneg (Nat.cast_nonneg _) hCmv)
    _ ≤ ((P + 1 : Nat) : Real) * Cmv *
        ((((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) ^ 2 /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2 +
          B * (((2 ^ P : Nat) : Real) * (N ^ (p + 1) : Nat)) /
            (heathBrownPoweredThreshold N (p + 1) L Cp eta) ^ 2) := by
      gcongr

#print axioms HeathBrownFullyUniformOutputs.card_le_common
#print axioms HeathBrownFullyUniformOutputs.next_le_common

end

end GafniTao
