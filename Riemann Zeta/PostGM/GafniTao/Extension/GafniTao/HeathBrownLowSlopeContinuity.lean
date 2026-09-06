import GafniTao.HeathBrownZeroEnergyLowAlgebra

/-!
# Quantitative continuity of the low Heath--Brown slopes

The finite detector threshold lies slightly to the left of the requested
zero line.  These exact rational inequalities bound the resulting increase
in the source exponent.  The common Lipschitz constant seven is deliberately
non-optimal and uniform on the whole interval `[1/2,3/4]`.
-/

namespace GafniTao

noncomputable section

theorem heathBrownLowFirstSlope_lipschitz
    {sigma0 sigma : Real}
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigmaUpper : sigma <= 2 / 3)
    (horder : sigma0 <= sigma) :
    heathBrownLowFirstSlope sigma0 <=
      heathBrownLowFirstSlope sigma + 7 * (sigma - sigma0) := by
  have hden0 : 0 < 2 - sigma0 := by linarith
  have hden : 0 < 2 - sigma := by linarith
  have hprod : 0 < (2 - sigma0) * (2 - sigma) := mul_pos hden0 hden
  have hprodLower : 12 / 7 <= (2 - sigma0) * (2 - sigma) := by
    nlinarith
  have hid : heathBrownLowFirstSlope sigma0 -
      heathBrownLowFirstSlope sigma =
        12 * (sigma - sigma0) / ((2 - sigma0) * (2 - sigma)) := by
    unfold heathBrownLowFirstSlope
    field_simp [hden0.ne', hden.ne']
    ring
  have hdiff : heathBrownLowFirstSlope sigma0 -
      heathBrownLowFirstSlope sigma <= 7 * (sigma - sigma0) := by
    rw [hid, div_le_iff₀ hprod]
    nlinarith
  linarith

theorem heathBrownLowSecondSlope_lipschitz
    {sigma0 sigma : Real}
    (hsigma0Lower : 2 / 3 <= sigma0)
    (hsigmaUpper : sigma <= 3 / 4)
    (horder : sigma0 <= sigma) :
    heathBrownLowSecondSlope sigma0 <=
      heathBrownLowSecondSlope sigma + 7 * (sigma - sigma0) := by
  have hden0 : 0 < 4 - 2 * sigma0 := by linarith
  have hden : 0 < 4 - 2 * sigma := by linarith
  have hprod : 0 < (4 - 2 * sigma0) * (4 - 2 * sigma) :=
    mul_pos hden0 hden
  have hprodLower : 40 / 7 <=
      (4 - 2 * sigma0) * (4 - 2 * sigma) := by
    nlinarith
  have hden0' : Not (4 - sigma0 * 2 = 0) := by nlinarith
  have hden' : Not (4 - sigma * 2 = 0) := by nlinarith
  have hid : heathBrownLowSecondSlope sigma0 -
      heathBrownLowSecondSlope sigma =
        40 * (sigma - sigma0) /
          ((4 - 2 * sigma0) * (4 - 2 * sigma)) := by
    unfold heathBrownLowSecondSlope
    field_simp [hden0.ne', hden.ne', hden0', hden']
    ring
  have hdiff : heathBrownLowSecondSlope sigma0 -
      heathBrownLowSecondSlope sigma <= 7 * (sigma - sigma0) := by
    rw [hid, div_le_iff₀ hprod]
    nlinarith
  linarith

theorem heathBrownLowSlopes_at_transition :
    heathBrownLowFirstSlope (2 / 3) =
      heathBrownLowSecondSlope (2 / 3) := by
  norm_num [heathBrownLowFirstSlope, heathBrownLowSecondSlope]

/-- Uniform quantitative displacement bound for the exact piecewise maximum
used by the low Heath--Brown cells. -/
theorem heathBrownLowMaxSlope_lipschitz
    {sigma0 sigma : Real}
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigmaUpper : sigma <= 3 / 4)
    (horder : sigma0 <= sigma) :
    max (heathBrownLowFirstSlope sigma0)
        (heathBrownLowSecondSlope sigma0) <=
      max (heathBrownLowFirstSlope sigma)
          (heathBrownLowSecondSlope sigma) +
        7 * (sigma - sigma0) := by
  by_cases hsigma : sigma <= 2 / 3
  · rw [heathBrown_low_max_eq_first (horder.trans hsigma),
      heathBrown_low_max_eq_first hsigma]
    exact heathBrownLowFirstSlope_lipschitz hsigma0Lower hsigma horder
  · have hsigmaLower : 2 / 3 <= sigma := by linarith
    by_cases hsigma0 : 2 / 3 <= sigma0
    · rw [heathBrown_low_max_eq_second hsigma0 (horder.trans hsigmaUpper),
        heathBrown_low_max_eq_second hsigmaLower hsigmaUpper]
      exact heathBrownLowSecondSlope_lipschitz hsigma0 hsigmaUpper horder
    · have hsigma0Upper : sigma0 <= 2 / 3 := by linarith
      rw [heathBrown_low_max_eq_first hsigma0Upper,
        heathBrown_low_max_eq_second hsigmaLower hsigmaUpper]
      have hleft := heathBrownLowFirstSlope_lipschitz hsigma0Lower
        (show (2 / 3 : Real) <= 2 / 3 by rfl) hsigma0Upper
      have hright := heathBrownLowSecondSlope_lipschitz
        (show (2 / 3 : Real) <= 2 / 3 by rfl) hsigmaUpper hsigmaLower
      rw [heathBrownLowSlopes_at_transition] at hleft
      linarith

#print axioms heathBrownLowFirstSlope_lipschitz
#print axioms heathBrownLowSecondSlope_lipschitz
#print axioms heathBrownLowMaxSlope_lipschitz

end

end GafniTao
