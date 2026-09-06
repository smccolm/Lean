import GafniTao.PublishedExponentInputs

/-!
# Heath--Brown 1979 zero-energy algebra below three quarters

This file formalizes the real-variable elimination in the first half of
Heath--Brown's additive-energy proof, as reproduced in the pinned ANTEDB
blueprint.  The analytic input produces

`r <= min (tau + 1 - 2 * sigma) (3 - 3 * sigma)`

at a powered scale `1 <= tau <= 3/2`.  The lemmas below verify, without a
numerical oracle, each of the three resulting energy exponents and the exact
transition at `sigma = 2/3`.
-/

namespace GafniTao

noncomputable section

/-- The powered ordinary-cardinality exponent used in the low-range
Heath--Brown energy calculation. -/
def heathBrownLowRhoCap (sigma tau : ℝ) : ℝ :=
  min (tau + 1 - 2 * sigma) (3 - 3 * sigma)

/-- The first coefficient in Heath--Brown's low-range maximum. -/
def heathBrownLowFirstSlope (sigma : ℝ) : ℝ :=
  (10 - 11 * sigma) / (2 - sigma)

/-- The second coefficient in Heath--Brown's low-range maximum. -/
def heathBrownLowSecondSlope (sigma : ℝ) : ℝ :=
  (18 - 19 * sigma) / (4 - 2 * sigma)

/-- The ANTEDB prose currently assigns the third low-range term to the
second slope alone.  At the closed endpoint this intermediate assertion is
false (`3 ≤ 17/6`).  The source theorem is unaffected: the maximum with the
first slope is exactly `3` here, and `heathBrown_low_third_term` below proves
the corrected maximum statement on the whole range. -/
theorem heathBrown_antedb_low_third_intermediate_counterexample :
    ¬ ((5 / 2 : ℝ) * heathBrownLowRhoCap (1 / 2) 1 +
        (3 - 4 * (1 / 2 : ℝ)) / 2 ≤
      heathBrownLowSecondSlope (1 / 2) * 1) := by
  norm_num [heathBrownLowRhoCap, heathBrownLowSecondSlope]

theorem heathBrown_low_first_term
    {sigma tau r : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 3 / 4)
    (hr : r ≤ heathBrownLowRhoCap sigma tau) :
    3 * r + 1 - 2 * sigma ≤ heathBrownLowFirstSlope sigma * tau := by
  have hden : 0 < 2 - sigma := by linarith
  rw [heathBrownLowFirstSlope, div_mul_eq_mul_div, le_div_iff₀ hden]
  unfold heathBrownLowRhoCap at hr
  rw [le_min_iff] at hr
  by_cases htransition : tau ≤ 2 - sigma
  · have hr' : r ≤ tau + 1 - 2 * sigma := hr.1
    nlinarith
  · have hr' : r ≤ 3 - 3 * sigma := hr.2
    nlinarith

theorem heathBrown_low_second_term
    {sigma tau r : ℝ}
    (hsigmaUpper : sigma ≤ 3 / 4) (htauLower : 1 ≤ tau)
    (hr : r ≤ heathBrownLowRhoCap sigma tau) :
    r + 4 - 4 * sigma ≤
      max ((7 - 7 * sigma) / (2 - sigma)) (6 - 6 * sigma) * tau := by
  unfold heathBrownLowRhoCap at hr
  rw [le_min_iff] at hr
  have hr' : r ≤ tau + 1 - 2 * sigma := hr.1
  have hslope :
      6 - 6 * sigma ≤
        max ((7 - 7 * sigma) / (2 - sigma)) (6 - 6 * sigma) :=
    le_max_right _ _
  have hbase : r + 4 - 4 * sigma ≤ (6 - 6 * sigma) * tau := by
    nlinarith
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hslope (by linarith))

theorem heathBrown_low_third_term
    {sigma tau r : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 3 / 4)
    (htauLower : 1 ≤ tau)
    (hr : r ≤ heathBrownLowRhoCap sigma tau) :
    (5 / 2 : ℝ) * r + (3 - 4 * sigma) / 2 ≤
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) * tau := by
  unfold heathBrownLowRhoCap at hr
  rw [le_min_iff] at hr
  by_cases hsigmaSplit : sigma ≤ 2 / 3
  · have hden : 0 < 2 - sigma := by linarith
    have hbase : (5 / 2 : ℝ) * r + (3 - 4 * sigma) / 2 ≤
        heathBrownLowFirstSlope sigma * tau := by
      unfold heathBrownLowFirstSlope
      rw [show (10 - 11 * sigma) / (2 - sigma) * tau =
          ((10 - 11 * sigma) * tau) / (2 - sigma) by ring]
      apply (le_div_iff₀ hden).2
      by_cases htransition : tau ≤ 2 - sigma
      · have hr' : r ≤ tau + 1 - 2 * sigma := hr.1
        nlinarith
      · have hr' : r ≤ 3 - 3 * sigma := hr.2
        nlinarith
    exact hbase.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith))
  · have hsigmaSplit' : 2 / 3 ≤ sigma := by linarith
    have hden : 0 < 4 - 2 * sigma := by linarith
    have hbase : (5 / 2 : ℝ) * r + (3 - 4 * sigma) / 2 ≤
        heathBrownLowSecondSlope sigma * tau := by
      unfold heathBrownLowSecondSlope
      rw [show (18 - 19 * sigma) / (4 - 2 * sigma) * tau =
          ((18 - 19 * sigma) * tau) / (4 - 2 * sigma) by ring]
      apply (le_div_iff₀ hden).2
      by_cases htransition : tau ≤ 2 - sigma
      · have hr' : r ≤ tau + 1 - 2 * sigma := hr.1
        nlinarith
      · have hr' : r ≤ 3 - 3 * sigma := hr.2
        nlinarith
    exact hbase.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by linarith))

/-- The auxiliary second term never exceeds the maximum of the two source
slopes. -/
theorem heathBrown_low_auxiliary_slope_le
    {sigma : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 4) :
    max ((7 - 7 * sigma) / (2 - sigma)) (6 - 6 * sigma) ≤
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) := by
  have hdenTwo : 0 < 2 - sigma := by linarith
  have hdenFour : 0 < 4 - 2 * sigma := by linarith
  rw [max_le_iff]
  by_cases hsigmaSplit : sigma ≤ 2 / 3
  · constructor
    · apply (show (7 - 7 * sigma) / (2 - sigma) ≤
          heathBrownLowFirstSlope sigma from ?_).trans (le_max_left _ _)
      unfold heathBrownLowFirstSlope
      rw [div_le_div_iff₀ hdenTwo hdenTwo]
      nlinarith
    · apply (show 6 - 6 * sigma ≤ heathBrownLowFirstSlope sigma from ?_).trans
          (le_max_left _ _)
      unfold heathBrownLowFirstSlope
      rw [le_div_iff₀ hdenTwo]
      nlinarith
  · have hsigmaSplit' : 2 / 3 ≤ sigma := by linarith
    constructor
    · apply (show (7 - 7 * sigma) / (2 - sigma) ≤
          heathBrownLowSecondSlope sigma from ?_).trans (le_max_right _ _)
      unfold heathBrownLowSecondSlope
      rw [div_le_div_iff₀ hdenTwo hdenFour]
      nlinarith
    · apply (show 6 - 6 * sigma ≤ heathBrownLowSecondSlope sigma from ?_).trans
          (le_max_right _ _)
      unfold heathBrownLowSecondSlope
      rw [le_div_iff₀ hdenFour]
      nlinarith

/-- The first source slope dominates up to and including `sigma = 2/3`. -/
theorem heathBrown_low_max_eq_first
    {sigma : ℝ} (hsigmaUpper : sigma ≤ 2 / 3) :
    max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) =
      heathBrownLowFirstSlope sigma := by
  rw [max_eq_left]
  have hdenTwo : 0 < 2 - sigma := by linarith
  have hdenFour : 0 < 4 - 2 * sigma := by linarith
  unfold heathBrownLowFirstSlope heathBrownLowSecondSlope
  rw [div_le_div_iff₀ hdenFour hdenTwo]
  nlinarith

/-- The second source slope dominates from `sigma = 2/3` through `3/4`. -/
theorem heathBrown_low_max_eq_second
    {sigma : ℝ} (hsigmaLower : 2 / 3 ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 4) :
    max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) =
      heathBrownLowSecondSlope sigma := by
  rw [max_eq_right]
  have hdenTwo : 0 < 2 - sigma := by linarith
  have hdenFour : 0 < 4 - 2 * sigma := by linarith
  unfold heathBrownLowFirstSlope heathBrownLowSecondSlope
  rw [div_le_div_iff₀ hdenTwo hdenFour]
  nlinarith

#print axioms heathBrown_low_first_term
#print axioms heathBrown_antedb_low_third_intermediate_counterexample
#print axioms heathBrown_low_second_term
#print axioms heathBrown_low_third_term
#print axioms heathBrown_low_auxiliary_slope_le
#print axioms heathBrown_low_max_eq_first
#print axioms heathBrown_low_max_eq_second

end

end GafniTao
