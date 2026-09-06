import GafniTao.HeathBrownGenericGMCardinality
import GafniTao.HeathBrownMHHExponent

/-!
# Logarithmic form of the Guth--Maynard powered-packet estimate

This file converts the three literal monomials in the frozen
Guth--Maynard large-values theorem into a logarithmic cardinality cap.  The
coefficient, epsilon, and three-term losses remain explicit.
-/

namespace GafniTao

noncomputable section

/-- The exponent supplied by the three Guth--Maynard monomials. -/
def heathBrownGMCardinalityCap (sigma tau : Real) : Real :=
  max (2 - 2 * sigma)
    (max (18 / 5 - 4 * sigma) (tau + 12 / 5 - 4 * sigma))

/-- A fourth inverse power of a threshold `V >= x^sigma` contributes
`-4*sigma` to any numerator exponent. -/
theorem rpow_mul_threshold_neg_four_le
    {x V sigma a : Real} (hx : 0 < x) (hV : x ^ sigma <= V) :
    x ^ a * V ^ (-4 : Real) <= x ^ (a - 4 * sigma) := by
  have hxSigmaPos : 0 < x ^ sigma := Real.rpow_pos_of_pos hx sigma
  have hVPos : 0 < V := hxSigmaPos.trans_le hV
  have hFour : (x ^ sigma) ^ 4 <= V ^ 4 :=
    pow_le_pow_left₀ hxSigmaPos.le hV 4
  have hDiv : x ^ a / V ^ 4 <= x ^ a / (x ^ sigma) ^ 4 :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _)
      (pow_pos hxSigmaPos 4) hFour
  have hNegV : V ^ (-4 : Real) = 1 / V ^ 4 := by
    rw [Real.rpow_neg hVPos.le]
    simpa only [one_div] using congrArg Inv.inv (Real.rpow_natCast V 4)
  have hDen : (x ^ sigma) ^ 4 = x ^ (sigma * 4) := by
    calc
      (x ^ sigma) ^ 4 = (x ^ sigma) ^ (4 : Real) :=
        (Real.rpow_natCast (x ^ sigma) 4).symm
      _ = x ^ (sigma * 4) := (Real.rpow_mul hx.le sigma 4).symm
  calc
    x ^ a * V ^ (-4 : Real) = x ^ a / V ^ 4 := by
      rw [hNegV]
      ring_nf
    _ <= x ^ a / (x ^ sigma) ^ 4 := hDiv
    _ = x ^ (a - 4 * sigma) := by
      rw [hDen, ← Real.rpow_sub hx]
      congr 1
      ring_nf

/-- The analogous inverse-square conversion for the first GM monomial. -/
theorem rpow_two_mul_threshold_neg_two_le
    {x V sigma : Real} (hx : 0 < x) (hV : x ^ sigma <= V) :
    x ^ 2 * V ^ (-2 : Real) <= x ^ (2 - 2 * sigma) := by
  have hVPos : 0 < V := (Real.rpow_pos_of_pos hx sigma).trans_le hV
  have hRewrite : V ^ (-2 : Real) = 1 / V ^ 2 := by
    rw [Real.rpow_neg hVPos.le]
    simpa only [one_div] using congrArg Inv.inv (Real.rpow_natCast V 2)
  rw [hRewrite]
  simpa only [div_eq_mul_inv, one_mul] using
    quotient_sq_le_rpow_sub hx hV

/-- Three powers of a base at least one are bounded by three times the
largest of their exponents. -/
theorem add_three_rpow_le_three_mul_max
    {x a b c : Real} (hx : 1 <= x) :
    x ^ a + x ^ b + x ^ c <= 3 * x ^ max a (max b c) := by
  have ha : x ^ a <= x ^ max a (max b c) :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  have hb : x ^ b <= x ^ max a (max b c) :=
    Real.rpow_le_rpow_of_exponent_le hx
      ((le_max_left _ _).trans (le_max_right _ _))
  have hc : x ^ c <= x ^ max a (max b c) :=
    Real.rpow_le_rpow_of_exponent_le hx
      ((le_max_right _ _).trans (le_max_right _ _))
  linarith

/-- Exact logarithmic consequence of the frozen Guth--Maynard estimate on
a common powered block. -/
theorem heathBrown_gm_card_log_le
    {x B V card C sigma tau epsilonGM zeta : Real}
    (hx : 1 < x) (hB : 0 < B) (hcard : 0 < card)
    (hC : 0 <= C)
    (hThreshold : x ^ sigma <= V)
    (hBExact : x ^ tau = B)
    (hCardBound : card <= C * B ^ epsilonGM *
      (x ^ 2 * V ^ (-2 : Real) +
        x ^ (18 / 5 : Real) * V ^ (-4 : Real) +
        B * x ^ (12 / 5 : Real) * V ^ (-4 : Real)))
    (hCoeff : 3 * C <= x ^ zeta) :
    heathBrownLogExponent x card <=
      zeta + epsilonGM * tau + heathBrownGMCardinalityCap sigma tau := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : 1 <= x := hx.le
  have hfirst := rpow_two_mul_threshold_neg_two_le hx0 hThreshold
  have hsecond := rpow_mul_threshold_neg_four_le
    (a := (18 / 5 : Real)) hx0 hThreshold
  have hthirdCore := rpow_mul_threshold_neg_four_le
    (a := (12 / 5 : Real)) hx0 hThreshold
  have hthird : B * x ^ (12 / 5 : Real) * V ^ (-4 : Real) <=
      x ^ (tau + 12 / 5 - 4 * sigma) := by
    calc
      B * x ^ (12 / 5 : Real) * V ^ (-4 : Real) =
          B * (x ^ (12 / 5 : Real) * V ^ (-4 : Real)) := by ring_nf
      _ <= B * x ^ (12 / 5 - 4 * sigma) := by gcongr
      _ = x ^ tau * x ^ (12 / 5 - 4 * sigma) := by rw [hBExact]
      _ = x ^ (tau + 12 / 5 - 4 * sigma) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring_nf
  let q := heathBrownGMCardinalityCap sigma tau
  have hsum :
      x ^ 2 * V ^ (-2 : Real) +
          x ^ (18 / 5 : Real) * V ^ (-4 : Real) +
          B * x ^ (12 / 5 : Real) * V ^ (-4 : Real) <=
        3 * x ^ q := by
    calc
      _ <= x ^ (2 - 2 * sigma) + x ^ (18 / 5 - 4 * sigma) +
          x ^ (tau + 12 / 5 - 4 * sigma) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ <= 3 * x ^ q := by
        exact add_three_rpow_le_three_mul_max hx1
  have hBEpsilon : B ^ epsilonGM = x ^ (epsilonGM * tau) := by
    rw [← hBExact]
    calc
      (x ^ tau) ^ epsilonGM = x ^ (tau * epsilonGM) :=
        (Real.rpow_mul hx0.le tau epsilonGM).symm
      _ = x ^ (epsilonGM * tau) := by ring_nf
  have hPower : card <= x ^ (zeta + epsilonGM * tau + q) := by
    calc
      card <= C * B ^ epsilonGM *
          (x ^ 2 * V ^ (-2 : Real) +
            x ^ (18 / 5 : Real) * V ^ (-4 : Real) +
            B * x ^ (12 / 5 : Real) * V ^ (-4 : Real)) := hCardBound
      _ <= C * B ^ epsilonGM * (3 * x ^ q) := by gcongr
      _ = (3 * C) * B ^ epsilonGM * x ^ q := by ring_nf
      _ <= x ^ zeta * B ^ epsilonGM * x ^ q := by gcongr
      _ = x ^ zeta * x ^ (epsilonGM * tau) * x ^ q := by rw [hBEpsilon]
      _ = x ^ (zeta + epsilonGM * tau + q) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
  have hExact : x ^ heathBrownLogExponent x card = card :=
    rpow_heathBrownLogExponent hx hcard
  apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
  simpa only [hExact] using hPower

#print axioms rpow_mul_threshold_neg_four_le
#print axioms rpow_two_mul_threshold_neg_two_le
#print axioms add_three_rpow_le_three_mul_max
#print axioms heathBrown_gm_card_log_le

end

end GafniTao
