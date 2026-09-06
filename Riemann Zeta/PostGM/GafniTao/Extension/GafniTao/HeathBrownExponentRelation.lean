import GafniTao.HeathBrownFiniteMixedEnergy
import GafniTao.HeathBrownZeroEnergyLowAlgebra

/-!
# Heath--Brown exponent relation

This file records the exact logarithmic relation obtained from the finite
second/third/fourth-moment inequality and proves Heath--Brown's simplified
relation for scales at most `3/2`.  The proof keeps the self-referential
energy exponent visible and solves all four branches of the two maxima.
-/

namespace GafniTao

noncomputable section

/-- Equation (33) of Heath--Brown (1979), in the exponent normalization used
by the pinned ANTEDB blueprint. -/
def HeathBrownExponentRelation
    (sigma tau rho rhoStar : Real) : Prop :=
  rhoStar <= 1 - 2 * sigma +
    (1 / 2 : Real) *
      max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
    (1 / 2 : Real) *
      max (rhoStar + 1)
        (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))

/-- Source conclusion of the simplified Heath--Brown relation. -/
def SimplifiedHeathBrownExponentRelation
    (sigma rho rhoStar : Real) : Prop :=
  rhoStar <= max (3 * rho + 1 - 2 * sigma)
    (max (rho + 4 - 4 * sigma)
      (5 * rho / 2 + (3 - 4 * sigma) / 2))

theorem heathBrown_first_max_le_of_tau_le_three_halves
    {tau rho : Real} (htau : tau <= 3 / 2) :
    max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) <=
      max (rho + 1) (2 * rho) := by
  apply max_le
  · exact le_max_left _ _
  apply max_le
  · exact le_max_right _ _
  have hconvex : 5 * rho / 4 + (3 / 2 : Real) / 2 =
      (3 / 4 : Real) * (rho + 1) + (1 / 4 : Real) * (2 * rho) := by
    ring
  calc
    5 * rho / 4 + tau / 2 <= 5 * rho / 4 + (3 / 2 : Real) / 2 := by
      linarith
    _ = (3 / 4 : Real) * (rho + 1) +
        (1 / 4 : Real) * (2 * rho) := hconvex
    _ <= (3 / 4 : Real) * max (rho + 1) (2 * rho) +
        (1 / 4 : Real) * max (rho + 1) (2 * rho) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max (rho + 1) (2 * rho) := by ring

theorem heathBrown_second_max_le_of_tau_le_three_halves
    {tau rho rhoStar : Real} (htau : tau <= 3 / 2) :
    max (rhoStar + 1)
        (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2)) <=
      max (rhoStar + 1) (4 * rho) := by
  apply max_le
  · exact le_max_left _ _
  apply max_le
  · exact le_max_right _ _
  have hconvex : 3 * rhoStar / 4 + rho + (3 / 2 : Real) / 2 =
      (3 / 4 : Real) * (rhoStar + 1) +
        (1 / 4 : Real) * (4 * rho) := by
    ring
  calc
    3 * rhoStar / 4 + rho + tau / 2 <=
        3 * rhoStar / 4 + rho + (3 / 2 : Real) / 2 := by
      linarith
    _ = (3 / 4 : Real) * (rhoStar + 1) +
        (1 / 4 : Real) * (4 * rho) := hconvex
    _ <= (3 / 4 : Real) * max (rhoStar + 1) (4 * rho) +
        (1 / 4 : Real) * max (rhoStar + 1) (4 * rho) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max (rhoStar + 1) (4 * rho) := by ring

/-- Heath--Brown's simplified exponent relation, including the elimination
of the fourth branch by the hypothesis `sigma >= 1/2`. -/
theorem simplifiedHeathBrownExponentRelation_of_relation
    {sigma tau rho rhoStar : Real}
    (hsigma : 1 / 2 <= sigma) (htau : tau <= 3 / 2)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    SimplifiedHeathBrownExponentRelation sigma rho rhoStar := by
  have hFirst := heathBrown_first_max_le_of_tau_le_three_halves
    (rho := rho) htau
  have hSecond := heathBrown_second_max_le_of_tau_le_three_halves
    (rho := rho) (rhoStar := rhoStar) htau
  have hReduced : rhoStar <= 1 - 2 * sigma +
      (1 / 2 : Real) * max (rho + 1) (2 * rho) +
      (1 / 2 : Real) * max (rhoStar + 1) (4 * rho) := by
    apply hrel.trans
    unfold HeathBrownExponentRelation at hrel
    gcongr
  unfold SimplifiedHeathBrownExponentRelation
  by_cases hFirstBranch : rho + 1 <= 2 * rho
  · rw [max_eq_right hFirstBranch] at hReduced
    by_cases hSecondBranch : rhoStar + 1 <= 4 * rho
    · rw [max_eq_right hSecondBranch] at hReduced
      have hBound : rhoStar <= 3 * rho + 1 - 2 * sigma := by
        linarith
      exact hBound.trans (le_max_left _ _)
    · have hSecondBranch' : 4 * rho <= rhoStar + 1 := le_of_not_ge hSecondBranch
      rw [max_eq_left hSecondBranch'] at hReduced
      have hMiddle : rhoStar <= 2 * rho + 3 - 4 * sigma := by
        linarith
      have hAverage : 2 * rho + 3 - 4 * sigma <=
          max (3 * rho + 1 - 2 * sigma) (rho + 4 - 4 * sigma) := by
        have hleft := le_max_left
          (3 * rho + 1 - 2 * sigma) (rho + 4 - 4 * sigma)
        have hright := le_max_right
          (3 * rho + 1 - 2 * sigma) (rho + 4 - 4 * sigma)
        linarith
      have hEmbed :
          max (3 * rho + 1 - 2 * sigma) (rho + 4 - 4 * sigma) <=
            max (3 * rho + 1 - 2 * sigma)
              (max (rho + 4 - 4 * sigma)
                (5 * rho / 2 + (3 - 4 * sigma) / 2)) := by
        apply max_le
        · exact le_max_left _ _
        · exact (le_max_left _ _).trans (le_max_right _ _)
      exact hMiddle.trans (hAverage.trans hEmbed)
  · have hFirstBranch' : 2 * rho <= rho + 1 := le_of_not_ge hFirstBranch
    rw [max_eq_left hFirstBranch'] at hReduced
    by_cases hSecondBranch : rhoStar + 1 <= 4 * rho
    · rw [max_eq_right hSecondBranch] at hReduced
      have hBound : rhoStar <=
          5 * rho / 2 + (3 - 4 * sigma) / 2 := by
        linarith
      exact hBound.trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · have hSecondBranch' : 4 * rho <= rhoStar + 1 := le_of_not_ge hSecondBranch
      rw [max_eq_left hSecondBranch'] at hReduced
      have hBound : rhoStar <= rho + 4 - 4 * sigma := by
        linarith
      exact hBound.trans
        (le_max_of_le_right (le_max_left _ _))

/-- The low-scale Heath--Brown relation after inserting the two ordinary
cardinality bounds used in the power argument. -/
theorem heathBrown_low_scale_energy_slope
    {sigma tau rho rhoStar : Real}
    (hsigmaLower : 1 / 2 <= sigma) (hsigmaUpper : sigma <= 3 / 4)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hrho : rho <= heathBrownLowRhoCap sigma tau)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar <=
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) * tau := by
  have hSimple := simplifiedHeathBrownExponentRelation_of_relation
    hsigmaLower htauUpper hrel
  have hFirst := heathBrown_low_first_term hsigmaLower hsigmaUpper hrho
  have hSecond := heathBrown_low_second_term hsigmaUpper htauLower hrho
  have hThird := heathBrown_low_third_term hsigmaLower hsigmaUpper
    htauLower hrho
  have hThird' : 5 * rho / 2 + (3 - 4 * sigma) / 2 <=
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) * tau := by
    convert hThird using 1
    ring
  have hAux := heathBrown_low_auxiliary_slope_le
    hsigmaLower hsigmaUpper
  have htauNonneg : 0 <= tau := zero_le_one.trans htauLower
  have hFirst' : 3 * rho + 1 - 2 * sigma <=
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) * tau :=
    hFirst.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) htauNonneg)
  have hSecond' : rho + 4 - 4 * sigma <=
      max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma) * tau :=
    hSecond.trans (mul_le_mul_of_nonneg_right hAux htauNonneg)
  unfold SimplifiedHeathBrownExponentRelation at hSimple
  exact hSimple.trans (max_le hFirst' (max_le hSecond' hThird'))

/-- First cell of the powered low-scale calculation. -/
theorem heathBrown_low_scale_first_cell
    {sigma tau rho rhoStar : Real}
    (hsigmaLower : 1 / 2 <= sigma) (hsigmaUpper : sigma <= 2 / 3)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hrho : rho <= heathBrownLowRhoCap sigma tau)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar <= heathBrownLowFirstSlope sigma * tau := by
  have h := heathBrown_low_scale_energy_slope hsigmaLower
    (hsigmaUpper.trans (by norm_num : (2 / 3 : Real) <= 3 / 4))
    htauLower htauUpper hrho hrel
  rw [heathBrown_low_max_eq_first hsigmaUpper] at h
  exact h

/-- Second cell of the powered low-scale calculation. -/
theorem heathBrown_low_scale_second_cell
    {sigma tau rho rhoStar : Real}
    (hsigmaLower : 2 / 3 <= sigma) (hsigmaUpper : sigma <= 3 / 4)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hrho : rho <= heathBrownLowRhoCap sigma tau)
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    rhoStar <= heathBrownLowSecondSlope sigma * tau := by
  have hhalf : (1 / 2 : Real) <= sigma :=
    (by norm_num : (1 / 2 : Real) <= 2 / 3).trans hsigmaLower
  have h := heathBrown_low_scale_energy_slope hhalf hsigmaUpper
    htauLower htauUpper hrho hrel
  rw [heathBrown_low_max_eq_second hsigmaLower hsigmaUpper] at h
  exact h

end

#print axioms simplifiedHeathBrownExponentRelation_of_relation
#print axioms heathBrown_low_scale_energy_slope
#print axioms heathBrown_low_scale_first_cell
#print axioms heathBrown_low_scale_second_cell

end GafniTao
