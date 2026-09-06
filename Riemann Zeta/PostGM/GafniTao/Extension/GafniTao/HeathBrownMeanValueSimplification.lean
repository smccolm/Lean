import GafniTao.HeathBrownPoweredCardinality

/-!
# Physical simplification of the powered mean-value bound

The companion power in Heath--Brown's low and middle cells is estimated by
the classical mean-value theorem.  This file records the two exact physical
inequalities corresponding to the alternatives that the powered polynomial
length lies below or above the height.  No logarithmic exponent notation or
asymptotic loss is used here.
-/

namespace GafniTao

noncomputable section

/-- A large-value threshold `V >= x^sigma` converts the quadratic quotient
in the mean-value theorem into the source power `x^(2-2*sigma)`. -/
theorem quotient_sq_le_rpow_sub
    {x V sigma : Real} (hx : 0 < x) (hV : x ^ sigma ≤ V) :
    x ^ 2 / V ^ 2 ≤ x ^ (2 - 2 * sigma) := by
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hx sigma
  have hVPos : 0 < V := hxSigmaPos.trans_le hV
  have hSq : (x ^ sigma) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ hxSigmaPos.le hV 2
  have hDiv : x ^ 2 / V ^ 2 ≤ x ^ 2 / (x ^ sigma) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg x) (sq_pos_of_pos hxSigmaPos) hSq
  have hNum : x ^ 2 = x ^ (2 : Real) := (Real.rpow_natCast x 2).symm
  have hDen : (x ^ sigma) ^ 2 = x ^ (sigma * 2) := by
    calc
      (x ^ sigma) ^ 2 = (x ^ sigma) ^ (2 : Real) :=
        (Real.rpow_natCast (x ^ sigma) 2).symm
      _ = x ^ (sigma * 2) := (Real.rpow_mul hx.le sigma 2).symm
  calc
    x ^ 2 / V ^ 2 ≤ x ^ 2 / (x ^ sigma) ^ 2 := hDiv
    _ = x ^ (2 - 2 * sigma) := by
      rw [hNum, hDen, ← Real.rpow_sub hx]
      congr 1
      ring

/-- Below the height, both terms of the classical mean-value expression are
bounded by the height term. -/
theorem meanValueShape_le_two_mul_height
    {x B V sigma : Real} (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hxB : x ≤ B) (hV : x ^ sigma ≤ V) :
    x ^ 2 / V ^ 2 + B * x / V ^ 2 ≤
      2 * B * x ^ (1 - 2 * sigma) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hxPos sigma
  have hVPos : 0 < V := hxSigmaPos.trans_le hV
  have hSq : (x ^ sigma) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ hxSigmaPos.le hV 2
  have hFirst : x ^ 2 / V ^ 2 ≤ B * x ^ (1 - 2 * sigma) := by
    calc
      x ^ 2 / V ^ 2 ≤ x ^ (2 - 2 * sigma) :=
        quotient_sq_le_rpow_sub hxPos hV
      _ = x * x ^ (1 - 2 * sigma) := by
        calc
          x ^ (2 - 2 * sigma) = x ^ (1 + (1 - 2 * sigma)) := by
            congr 1
            ring
          _ = x ^ (1 : Real) * x ^ (1 - 2 * sigma) :=
            Real.rpow_add hxPos 1 (1 - 2 * sigma)
          _ = x * x ^ (1 - 2 * sigma) := by rw [Real.rpow_one]
      _ ≤ B * x ^ (1 - 2 * sigma) :=
        mul_le_mul_of_nonneg_right hxB (Real.rpow_nonneg hxPos.le _)
  have hSecond : B * x / V ^ 2 ≤ B * x ^ (1 - 2 * sigma) := by
    have hQuot : x / V ^ 2 ≤ x / (x ^ sigma) ^ 2 :=
      div_le_div_of_nonneg_left hxPos.le (sq_pos_of_pos hxSigmaPos) hSq
    calc
      B * x / V ^ 2 = B * (x / V ^ 2) := by ring
      _ ≤ B * (x / (x ^ sigma) ^ 2) :=
        mul_le_mul_of_nonneg_left hQuot hB
      _ = B * x ^ (1 - 2 * sigma) := by
        congr 1
        have hDen : (x ^ sigma) ^ 2 = x ^ (sigma * 2) := by
          calc
            (x ^ sigma) ^ 2 = (x ^ sigma) ^ (2 : Real) :=
              (Real.rpow_natCast (x ^ sigma) 2).symm
            _ = x ^ (sigma * 2) :=
              (Real.rpow_mul hxPos.le sigma 2).symm
        calc
          x / (x ^ sigma) ^ 2 =
              x ^ (1 : Real) / x ^ (sigma * 2) := by
            rw [Real.rpow_one, hDen]
          _ = x ^ (1 - 2 * sigma) := by
            rw [← Real.rpow_sub hxPos]
            congr 1
            ring
  linarith

/-- Above the height, both terms of the classical mean-value expression are
bounded by the length-squared term. -/
theorem meanValueShape_le_two_mul_length
    {x B V sigma : Real} (hx : 1 ≤ x)
    (hBx : B ≤ x) (hV : x ^ sigma ≤ V) :
    x ^ 2 / V ^ 2 + B * x / V ^ 2 ≤
      2 * x ^ (2 - 2 * sigma) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hFirst := quotient_sq_le_rpow_sub hxPos hV
  have hVNonneg : 0 ≤ V ^ 2 := sq_nonneg V
  have hSecondLe : B * x / V ^ 2 ≤ x ^ 2 / V ^ 2 := by
    apply div_le_div_of_nonneg_right _ hVNonneg
    have hMul : B * x ≤ x * x := mul_le_mul_of_nonneg_right hBx hxPos.le
    simpa [pow_two] using hMul
  linarith

#print axioms quotient_sq_le_rpow_sub
#print axioms meanValueShape_le_two_mul_height
#print axioms meanValueShape_le_two_mul_length

end

end GafniTao
