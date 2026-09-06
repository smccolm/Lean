import GafniTao.HeathBrownFullyUniformCardinalityBounds
import GafniTao.HeathBrownMeanValueSimplification

/-!
# Physical bounds for the two common cardinality packets

The fully uniform packets have exact mean-value bounds at lengths
`2^P N^p` and `2^P N^(p+1)`.  This file removes only that fixed dyadic
factor.  The threshold, source power, height term, and both alternatives of
the classical mean-value expression remain visible.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The linear quotient accompanying `quotient_sq_le_rpow_sub`. -/
theorem quotient_linear_le_rpow_sub
    {x V sigma : Real} (hx : 0 < x) (hV : x ^ sigma ≤ V) :
    x / V ^ 2 ≤ x ^ (1 - 2 * sigma) := by
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hx sigma
  have hVPos : 0 < V := hxSigmaPos.trans_le hV
  have hSq : (x ^ sigma) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ hxSigmaPos.le hV 2
  have hDiv : x / V ^ 2 ≤ x / (x ^ sigma) ^ 2 :=
    div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hxSigmaPos) hSq
  calc
    x / V ^ 2 ≤ x / (x ^ sigma) ^ 2 := hDiv
    _ = x ^ (1 - 2 * sigma) := by
      have hDen : (x ^ sigma) ^ 2 = x ^ (sigma * 2) := by
        calc
          (x ^ sigma) ^ 2 = (x ^ sigma) ^ (2 : Real) :=
            (Real.rpow_natCast (x ^ sigma) 2).symm
          _ = x ^ (sigma * 2) := (Real.rpow_mul hx.le sigma 2).symm
      calc
        x / (x ^ sigma) ^ 2 =
            x ^ (1 : Real) / x ^ (sigma * 2) := by
          rw [Real.rpow_one, hDen]
        _ = x ^ (1 - sigma * 2) := by rw [← Real.rpow_sub hx]
        _ = x ^ (1 - 2 * sigma) := by congr 1; ring

/-- A fixed multiplicative length factor is exposed only as a coefficient;
the two physical powers are exactly those in the classical mean-value
estimate. -/
theorem scaledMeanValueExpression_le_physical
    {D B x V sigma : Real} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hx : 0 < x) (hV : x ^ sigma ≤ V) :
    (D * x) ^ 2 / V ^ 2 + B * (D * x) / V ^ 2 ≤
      D ^ 2 * x ^ (2 - 2 * sigma) +
        D * B * x ^ (1 - 2 * sigma) := by
  have hquad := quotient_sq_le_rpow_sub hx hV
  have hlin := quotient_linear_le_rpow_sub hx hV
  calc
    (D * x) ^ 2 / V ^ 2 + B * (D * x) / V ^ 2 =
        D ^ 2 * (x ^ 2 / V ^ 2) +
          (D * B) * (x / V ^ 2) := by ring
    _ ≤ D ^ 2 * x ^ (2 - 2 * sigma) +
          (D * B) * x ^ (1 - 2 * sigma) := by
      gcongr
    _ = D ^ 2 * x ^ (2 - 2 * sigma) +
          D * B * x ^ (1 - 2 * sigma) := by ring

/-- Physical cardinality bound for the actual `p` packet. -/
theorem HeathBrownFullyUniformOutputs.card_le_physical
    {epsilon B R eta L sigma : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hN : 0 < N) (hpP : p ≤ P) (hCmv : 0 ≤ Cmv) (hB : 0 ≤ B)
    (hThreshold : ((N ^ p : Nat) : Real) ^ sigma ≤
      heathBrownPoweredThreshold N p L Cp eta) :
    (W.card : Real) ≤
      P * Cmv *
        (((2 ^ P : Nat) : Real) ^ 2 *
            ((N ^ p : Nat) : Real) ^ (2 - 2 * sigma) +
          ((2 ^ P : Nat) : Real) * B *
            ((N ^ p : Nat) : Real) ^ (1 - 2 * sigma)) := by
  have hCommon := full.card_le_common hpP hCmv hB
  have hPhysical := scaledMeanValueExpression_le_physical
    (D := ((2 ^ P : Nat) : Real)) (B := B)
    (x := ((N ^ p : Nat) : Real))
    (V := heathBrownPoweredThreshold N p L Cp eta)
    (sigma := sigma) (by positivity) hB (by positivity) hThreshold
  exact hCommon.trans
    (mul_le_mul_of_nonneg_left hPhysical
      (mul_nonneg (Nat.cast_nonneg P) hCmv))

/-- Physical cardinality bound for the actual `(p+1)` companion packet. -/
theorem HeathBrownFullyUniformOutputs.next_le_physical
    {epsilon B R eta L sigma : Real} {N p P : Nat}
    {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hN : 0 < N) (hpP : p ≤ P) (hCmv : 0 ≤ Cmv) (hB : 0 ≤ B)
    (hThreshold : ((N ^ (p + 1) : Nat) : Real) ^ sigma ≤
      heathBrownPoweredThreshold N (p + 1) L Cp eta) :
    (W.card : Real) ≤
      ((P + 1 : Nat) : Real) * Cmv *
        (((2 ^ P : Nat) : Real) ^ 2 *
            ((N ^ (p + 1) : Nat) : Real) ^ (2 - 2 * sigma) +
          ((2 ^ P : Nat) : Real) * B *
            ((N ^ (p + 1) : Nat) : Real) ^ (1 - 2 * sigma)) := by
  have hCommon := full.next_le_common hpP hCmv hB
  have hPhysical := scaledMeanValueExpression_le_physical
    (D := ((2 ^ P : Nat) : Real)) (B := B)
    (x := ((N ^ (p + 1) : Nat) : Real))
    (V := heathBrownPoweredThreshold N (p + 1) L Cp eta)
    (sigma := sigma) (by positivity) hB (by positivity) hThreshold
  exact hCommon.trans
    (mul_le_mul_of_nonneg_left hPhysical
      (mul_nonneg (Nat.cast_nonneg (P + 1)) hCmv))

#print axioms quotient_linear_le_rpow_sub
#print axioms scaledMeanValueExpression_le_physical
#print axioms HeathBrownFullyUniformOutputs.card_le_physical
#print axioms HeathBrownFullyUniformOutputs.next_le_physical

end

end GafniTao
