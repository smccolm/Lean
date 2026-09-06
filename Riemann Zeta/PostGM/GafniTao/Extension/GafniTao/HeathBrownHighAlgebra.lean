import GafniTao.HeathBrownExponentRelation

/-!
# Heath--Brown 1979 zero-energy algebra above three quarters

This file isolates the exact real-variable calculation in the high-sigma
part of the pinned ANTEDB reproduction of Heath--Brown's Theorem 2.  The
analytic large-value inputs are deliberately hypotheses here; subsequent
modules must derive them from the actual finite detector families.
-/

namespace GafniTao

noncomputable section

/-- The high-sigma target slope before division by `1-sigma`. -/
def heathBrownHighEnergySlope (sigma : Real) : Real :=
  12 * (1 - sigma) / (4 * sigma - 1)

/-- The zeta-specific short-scale calculation in lines 145--153 of the
pinned ANTEDB proof. -/
theorem heathBrown_high_zeta_short_scale
    {sigma tau rho rhoStar : Real}
    (hsigma : 1 / 2 < sigma) (htauUpper : tau ≤ 4 * sigma - 1)
    (hrho : rho ≤ 2 * tau - 12 * (sigma - 1 / 2))
    (henergy : rhoStar ≤ 3 * rho) :
    rhoStar ≤ heathBrownHighEnergySlope sigma * tau := by
  have hden : 0 < 4 * sigma - 1 := by linarith
  unfold heathBrownHighEnergySlope
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith

/-- In the high-sigma range the ordinary large-value exponent entering the
powered relation is at most one. -/
theorem heathBrown_high_rho_le_one
    {sigma rho : Real} (hsigma : 3 / 4 ≤ sigma)
    (hrho : rho ≤ 3 - 3 * sigma) : rho ≤ 1 := by
  linarith

/-- When the first Heath--Brown maximum is controlled by `rho+1`, solving
the self-referential second maximum gives the first three expressions in the
source case split.  The first expression is `rho+4-4*sigma`: the
`rho/2+4-4*sigma` printed in the ANTEDB prose does not follow from its
immediately preceding displayed inequality. -/
theorem heathBrown_high_first_branch_relation
    {sigma tau rho rhoStar : Real}
    (hrhoOne : rho ≤ 1)
    (hbranch : 5 * rho / 4 + tau / 2 ≤ rho + 1)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar ≤ max (rho + 4 - 4 * sigma)
      (max (5 * rho / 2 + (3 - 4 * sigma) / 2)
        (8 * rho / 5 + 2 * tau / 5 + (12 - 16 * sigma) / 5)) := by
  unfold HeathBrownExponentRelation at hrel
  have hTwoRho : 2 * rho ≤ rho + 1 := by linarith
  have hInner : max (2 * rho) (5 * rho / 4 + tau / 2) ≤ rho + 1 :=
    max_le hTwoRho hbranch
  rw [max_eq_left hInner] at hrel
  by_cases hSecondA : max (4 * rho)
      (3 * rhoStar / 4 + rho + tau / 2) ≤ rhoStar + 1
  · rw [max_eq_left hSecondA] at hrel
    exact (show rhoStar ≤ rho + 4 - 4 * sigma by linarith).trans
      (le_max_left _ _)
  · have hSecondA' : rhoStar + 1 ≤ max (4 * rho)
        (3 * rhoStar / 4 + rho + tau / 2) := le_of_not_ge hSecondA
    rw [max_eq_right hSecondA'] at hrel
    by_cases hSecondB : 3 * rhoStar / 4 + rho + tau / 2 ≤ 4 * rho
    · rw [max_eq_left hSecondB] at hrel
      exact (show rhoStar ≤ 5 * rho / 2 + (3 - 4 * sigma) / 2 by
        linarith).trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hSecondB' : 4 * rho ≤
          3 * rhoStar / 4 + rho + tau / 2 := le_of_not_ge hSecondB
      rw [max_eq_right hSecondB'] at hrel
      exact (show rhoStar ≤
          8 * rho / 5 + 2 * tau / 5 + (12 - 16 * sigma) / 5 by
        linarith).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- When the oscillatory term controls the first Heath--Brown maximum,
solving the second maximum gives the remaining three source expressions. -/
theorem heathBrown_high_second_branch_relation
    {sigma tau rho rhoStar : Real}
    (hrhoOne : rho ≤ 1)
    (hbranch : rho + 1 ≤ 5 * rho / 4 + tau / 2)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar ≤ max (5 * rho / 4 + tau / 2 + 3 - 4 * sigma)
      (max (21 * rho / 8 + tau / 4 + 1 - 2 * sigma)
        (9 * rho / 5 + 4 * tau / 5 + (8 - 16 * sigma) / 5)) := by
  unfold HeathBrownExponentRelation at hrel
  have hTwoRho : 2 * rho ≤ rho + 1 := by linarith
  have hTwoRhoOsc : 2 * rho ≤ 5 * rho / 4 + tau / 2 :=
    hTwoRho.trans hbranch
  rw [max_eq_right hTwoRhoOsc, max_eq_right hbranch] at hrel
  by_cases hSecondA : max (4 * rho)
      (3 * rhoStar / 4 + rho + tau / 2) ≤ rhoStar + 1
  · rw [max_eq_left hSecondA] at hrel
    exact (show rhoStar ≤
        5 * rho / 4 + tau / 2 + 3 - 4 * sigma by linarith).trans
      (le_max_left _ _)
  · have hSecondA' : rhoStar + 1 ≤ max (4 * rho)
        (3 * rhoStar / 4 + rho + tau / 2) := le_of_not_ge hSecondA
    rw [max_eq_right hSecondA'] at hrel
    by_cases hSecondB : 3 * rhoStar / 4 + rho + tau / 2 ≤ 4 * rho
    · rw [max_eq_left hSecondB] at hrel
      exact (show rhoStar ≤
          21 * rho / 8 + tau / 4 + 1 - 2 * sigma by linarith).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · have hSecondB' : 4 * rho ≤
          3 * rhoStar / 4 + rho + tau / 2 := le_of_not_ge hSecondB
      rw [max_eq_right hSecondB'] at hrel
      exact (show rhoStar ≤
          9 * rho / 5 + 4 * tau / 5 + (8 - 16 * sigma) / 5 by
        linarith).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The complete high-sigma generic-energy cell calculation in lines
155--201 of the pinned ANTEDB proof.  Both first-maximum cases and every
self-referential second-maximum case are discharged here. -/
theorem heathBrown_high_generic_cell
    {sigma tau rho rhoStar : Real}
    (hsigmaLower : 3 / 4 ≤ sigma) (hsigmaUpper : sigma < 25 / 28)
    (htauLower : (4 * sigma - 1) / 2 ≤ tau)
    (htauUpper : tau ≤ 3 * (4 * sigma - 1) / 4)
    (hrhoMain : rho ≤ max (2 - 2 * sigma) (tau + 4 - 6 * sigma))
    (hrhoCompanion : rho ≤ 3 - 3 * sigma)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar ≤ heathBrownHighEnergySlope sigma * tau := by
  have hden : 0 < 4 * sigma - 1 := by linarith
  have hrhoOne := heathBrown_high_rho_le_one hsigmaLower hrhoCompanion
  have hTargetIff : ∀ x : Real,
      x * (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau →
        x ≤ heathBrownHighEnergySlope sigma * tau := by
    intro x hx
    unfold heathBrownHighEnergySlope
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    exact hx
  by_cases hcap : 2 - 2 * sigma ≤ tau + 4 - 6 * sigma
  · rw [max_eq_right hcap] at hrhoMain
    by_cases hfirst : 5 * rho / 4 + tau / 2 ≤ rho + 1
    · have hsolved := heathBrown_high_first_branch_relation
        hrhoOne hfirst hrel
      have h1 : (rho + 4 - 4 * sigma) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      have h2 : (5 * rho / 2 + (3 - 4 * sigma) / 2) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h3 : (8 * rho / 5 + 2 * tau / 5 +
          (12 - 16 * sigma) / 5) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      exact hsolved.trans (max_le (hTargetIff _ h1)
        (max_le (hTargetIff _ h2) (hTargetIff _ h3)))
    · have hfirst' : rho + 1 ≤ 5 * rho / 4 + tau / 2 :=
        le_of_not_ge hfirst
      have hsolved := heathBrown_high_second_branch_relation
        hrhoOne hfirst' hrel
      have h1 : (5 * rho / 4 + tau / 2 + 3 - 4 * sigma) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h2 : (21 * rho / 8 + tau / 4 + 1 - 2 * sigma) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h3 : (9 * rho / 5 + 4 * tau / 5 +
          (8 - 16 * sigma) / 5) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      exact hsolved.trans (max_le (hTargetIff _ h1)
        (max_le (hTargetIff _ h2) (hTargetIff _ h3)))
  · have hcap' : tau + 4 - 6 * sigma ≤ 2 - 2 * sigma :=
      le_of_not_ge hcap
    rw [max_eq_left hcap'] at hrhoMain
    by_cases hfirst : 5 * rho / 4 + tau / 2 ≤ rho + 1
    · have hsolved := heathBrown_high_first_branch_relation
        hrhoOne hfirst hrel
      have h1 : (rho + 4 - 4 * sigma) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      have h2 : (5 * rho / 2 + (3 - 4 * sigma) / 2) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h3 : (8 * rho / 5 + 2 * tau / 5 +
          (12 - 16 * sigma) / 5) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      exact hsolved.trans (max_le (hTargetIff _ h1)
        (max_le (hTargetIff _ h2) (hTargetIff _ h3)))
    · have hfirst' : rho + 1 ≤ 5 * rho / 4 + tau / 2 :=
        le_of_not_ge hfirst
      have hsolved := heathBrown_high_second_branch_relation
        hrhoOne hfirst' hrel
      have h1 : (5 * rho / 4 + tau / 2 + 3 - 4 * sigma) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h2 : (21 * rho / 8 + tau / 4 + 1 - 2 * sigma) *
          (4 * sigma - 1) ≤ 12 * (1 - sigma) * tau := by nlinarith
      have h3 : (9 * rho / 5 + 4 * tau / 5 +
          (8 - 16 * sigma) / 5) * (4 * sigma - 1) ≤
          12 * (1 - sigma) * tau := by nlinarith
      exact hsolved.trans (max_le (hTargetIff _ h1)
        (max_le (hTargetIff _ h2) (hTargetIff _ h3)))

#print axioms heathBrown_high_zeta_short_scale
#print axioms heathBrown_high_first_branch_relation
#print axioms heathBrown_high_second_branch_relation
#print axioms heathBrown_high_generic_cell

end

end GafniTao
