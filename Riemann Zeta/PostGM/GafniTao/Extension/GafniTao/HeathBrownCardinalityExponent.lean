import GafniTao.HeathBrownCommonThresholdExponent
import GafniTao.HeathBrownFullyUniformCardinalityBounds
import GafniTao.HeathBrownCommonCardinalityPhysical

/-!
# Logarithmic cardinality exponents for the common packets

This is the exact finite form of the mean-value estimates used to obtain
Heath--Brown's two bounds for `rho`.  A literal coefficient loss is exposed;
later source consumers absorb it uniformly because the power bound is fixed.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The sum of two powers is bounded by twice the larger power. -/
theorem add_two_rpow_le_two_mul_max
    {x a b : Real} (hx : 1 <= x) :
    x ^ a + x ^ b <= 2 * x ^ max a b := by
  have ha : x ^ a <= x ^ max a b :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  have hb : x ^ b <= x ^ max a b :=
    Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
  linarith

/-- A classical mean-value cardinality bound, expressed at an exact
logarithmic base. -/
theorem heathBrown_card_log_le
    {x B V card C sigma tau zeta : Real}
    (hx : 1 < x) (hB : 0 < B) (hcard : 0 < card)
    (hC : 0 <= C)
    (hThreshold : x ^ sigma <= V)
    (hBExact : x ^ tau = B)
    (hCardBound : card <= C * (x ^ 2 / V ^ 2 + B * x / V ^ 2))
    (hCoeff : 2 * C <= x ^ zeta) :
    heathBrownLogExponent x card <=
      zeta + max (2 - 2 * sigma) (tau + 1 - 2 * sigma) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : 1 <= x := hx.le
  have hquad := quotient_sq_le_rpow_sub hx0 hThreshold
  have hlin := quotient_linear_le_rpow_sub hx0 hThreshold
  have hlinear : B * (x / V ^ 2) <= x ^ (tau + 1 - 2 * sigma) := by
    calc
      B * (x / V ^ 2) <= B * x ^ (1 - 2 * sigma) := by
        gcongr
      _ = x ^ tau * x ^ (1 - 2 * sigma) := by rw [hBExact]
      _ = x ^ (tau + 1 - 2 * sigma) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
  let q := max (2 - 2 * sigma) (tau + 1 - 2 * sigma)
  have hsum : x ^ 2 / V ^ 2 + B * x / V ^ 2 <= 2 * x ^ q := by
    calc
      x ^ 2 / V ^ 2 + B * x / V ^ 2 =
          x ^ 2 / V ^ 2 + B * (x / V ^ 2) := by ring
      _ <=
          x ^ (2 - 2 * sigma) + x ^ (tau + 1 - 2 * sigma) := by
        gcongr
      _ <= 2 * x ^ q := add_two_rpow_le_two_mul_max hx1
  have hPower : card <= x ^ (zeta + q) := by
    calc
      card <= C * (x ^ 2 / V ^ 2 + B * x / V ^ 2) := hCardBound
      _ <= C * (2 * x ^ q) := mul_le_mul_of_nonneg_left hsum hC
      _ = (2 * C) * x ^ q := by ring
      _ <= x ^ zeta * x ^ q :=
        mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hx0.le _)
      _ = x ^ (zeta + q) := (Real.rpow_add hx0 _ _).symm
  have hExact : x ^ heathBrownLogExponent x card = card :=
    rpow_heathBrownLogExponent hx hcard
  apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
  simpa only [hExact] using hPower

/-- On a source scale `tau >= 1`, the linear height term is the larger
member of the classical mean-value estimate. -/
theorem heathBrown_card_log_le_main
    {x B V card C sigma tau zeta : Real}
    (hx : 1 < x) (hB : 0 < B) (hcard : 0 < card)
    (hC : 0 <= C)
    (htau : 1 <= tau)
    (hThreshold : x ^ sigma <= V)
    (hBExact : x ^ tau = B)
    (hCardBound : card <= C * (x ^ 2 / V ^ 2 + B * x / V ^ 2))
    (hCoeff : 2 * C <= x ^ zeta) :
    heathBrownLogExponent x card <= zeta + tau + 1 - 2 * sigma := by
  have h := heathBrown_card_log_le hx hB hcard hC hThreshold hBExact
    hCardBound hCoeff
  rw [max_eq_right (by linarith : 2 - 2 * sigma <=
    tau + 1 - 2 * sigma)] at h
  linarith

/-- If the analytic height does not exceed the polynomial length, both
classical mean-value terms are controlled by the quadratic term. -/
theorem heathBrown_card_log_le_companion
    {x B V card C sigma tau zeta : Real}
    (hx : 1 < x) (hB : 0 < B) (hcard : 0 < card)
    (hC : 0 <= C)
    (htau : tau <= 1)
    (hThreshold : x ^ sigma <= V)
    (hBExact : x ^ tau = B)
    (hCardBound : card <= C * (x ^ 2 / V ^ 2 + B * x / V ^ 2))
    (hCoeff : 2 * C <= x ^ zeta) :
    heathBrownLogExponent x card <= zeta + 2 - 2 * sigma := by
  have h := heathBrown_card_log_le hx hB hcard hC hThreshold hBExact
    hCardBound hCoeff
  rw [max_eq_left (by linarith : tau + 1 - 2 * sigma <=
    2 - 2 * sigma)] at h
  linarith

#print axioms add_two_rpow_le_two_mul_max
#print axioms heathBrown_card_log_le
#print axioms heathBrown_card_log_le_main
#print axioms heathBrown_card_log_le_companion

end

end GafniTao
