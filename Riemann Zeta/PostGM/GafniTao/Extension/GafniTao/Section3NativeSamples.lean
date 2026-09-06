import GafniTao.HeathBrownZeroEnergyLowNative
import GafniTao.PintzPublishedCutoffNative
import GafniTao.Section3Algebra

/-!
# Native Gafni--Tao Section 3 samples

The first displayed sample only uses the first two Heath--Brown energy cells:
the frozen Guth--Maynard density estimate confines the optimizing parameter to
an arbitrarily small neighbourhood of `7/10`, hence below `3/4`.  This module
therefore consumes those two proved cells directly instead of assuming the
strictly stronger three-cell package needed elsewhere in Section 3.
-/

namespace GafniTao

noncomputable section

/-- Fixed-epsilon first-sample estimate consuming the two native
Heath--Brown cells actually reached by the optimizer. -/
theorem first_sample_fixed_epsilon_bound_native
    {eps : ℝ} (heps : 0 < eps) (hepsUpper : eps < 1 / 40) :
    refinedFixedEpsilonExponent (17 / 30) eps ≤
      ((7 / 12 + 4 * eps : ℝ) : EReal) := by
  unfold refinedFixedEpsilonExponent
  apply sSup_le
  rintro x ⟨sigma, hsigma, rfl⟩
  by_cases hLower : sigma ≤ 1 / 2
  · refine (min_le_left _ _).trans ?_
    exact (ordinaryMomentExponent_le_one_sub_theta_of_lowerHalf
      (by norm_num) hsigma.1 hLower).trans (by
        exact_mod_cast (show (1 - 17 / 30 : ℝ) ≤ 7 / 12 + 4 * eps by
          nlinarith))
  · have hsigmaHalf : 1 / 2 ≤ sigma := (lt_of_not_ge hLower).le
    have hsigmaBound : sigma ≤ 7 / 10 + eps :=
      first_sample_admissible_sigma_upper heps.le
        hsigmaHalf hsigma.2.1 hsigma
    have hsigmaThreeQuarters : sigma ≤ 3 / 4 := by nlinarith
    by_cases hFirst : sigma ≤ 2 / 3
    · refine (min_le_right _ _).trans
        ((additiveEnergyMomentExponent_le_of_exponent_upper
          (by norm_num) hsigma.2.1
          (zeroAdditiveEnergyExponent_le
            (heathBrown_zeroAdditiveEnergy_first_native
              hsigmaHalf hFirst))).trans ?_)
      exact_mod_cast (heathBrown_first_sample_cell hFirst heps.le)
    · have hsigmaSecond : 2 / 3 < sigma := lt_of_not_ge hFirst
      refine (min_le_right _ _).trans
        ((additiveEnergyMomentExponent_le_of_exponent_upper
          (by norm_num) hsigma.2.1
          (zeroAdditiveEnergyExponent_le
            (heathBrown_zeroAdditiveEnergy_second_native
              hsigmaSecond hsigmaThreeQuarters))).trans ?_)
      exact_mod_cast (heathBrown_second_sample_cell
        hsigmaBound heps.le hepsUpper.le)

/-- Exact native first numerical sample from Gafni--Tao Section 3. -/
theorem refinedExceptionalUpperExponent_seventeen_thirtieths_le_native :
    refinedExceptionalUpperExponent (17 / 30) ≤ ((7 / 12 : ℝ) : EReal) := by
  apply refinedExceptionalUpperExponent_le_of_eventually_fixed_le
      (K := 4) (epsZero := 1 / 40)
  · norm_num
  · norm_num
  · intro eps heps hepsUpper
    exact first_sample_fixed_epsilon_bound_native heps hepsUpper

/-- Publication-facing first sample for the actual exceptional exponent. -/
theorem exceptionalExponent_seventeen_thirtieths_le_native :
    exceptionalExponent (17 / 30) ≤ ((7 / 12 : ℝ) : EReal) :=
  (gafniTaoTheorem13_native (by norm_num) (by norm_num)).trans
    refinedExceptionalUpperExponent_seventeen_thirtieths_le_native

/-- Exact native second numerical sample on the explicit sufficiently-small
range used by the formalized Pintz cutoff consumer. -/
theorem exceptionalExponent_two_fifteenths_add_le_native
    {Delta : ℝ} (hDelta : 0 < Delta) (hDeltaUpper : Delta ≤ 1 / 100) :
    exceptionalExponent (2 / 15 + Delta) ≤
      ((1 - 9 * Delta / 13 : ℝ) : EReal) := by
  have hthetaLower : 0 < 2 / 15 + Delta := by nlinarith
  have hthetaUpper : 2 / 15 + Delta < 1 := by nlinarith
  exact (gafniTaoTheorem13_native hthetaLower hthetaUpper).trans
    (refinedExceptionalUpperExponent_two_fifteenths_add_le
      pintzTwentyThreeTwentyFourCutoff_native hDelta hDeltaUpper)

#print axioms first_sample_fixed_epsilon_bound_native
#print axioms refinedExceptionalUpperExponent_seventeen_thirtieths_le_native
#print axioms exceptionalExponent_seventeen_thirtieths_le_native
#print axioms exceptionalExponent_two_fifteenths_add_le_native

end

end GafniTao
