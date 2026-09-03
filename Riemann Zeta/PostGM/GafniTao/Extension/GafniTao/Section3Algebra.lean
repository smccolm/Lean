import GafniTao.PublishedExponentInputs

/-!
# Exact algebra for the Gafni--Tao Section 3 samples

The public exponent formula retains an infimum over every positive epsilon.
This file first proves the complete-lattice epsilon-removal lemma needed by
the rational sample calculations.  No continuity or attainment of `A` or
`A*` is used.
-/

namespace GafniTao

noncomputable section

/-- A uniform affine error at each sufficiently small source epsilon can be
removed after taking the literal positive-epsilon infimum. -/
theorem refinedExceptionalUpperExponent_le_of_eventually_fixed_le
    {theta q K epsZero : ℝ}
    (hK : 0 < K) (hepsZero : 0 < epsZero)
    (hfixed : ∀ eps : ℝ, 0 < eps → eps < epsZero →
      refinedFixedEpsilonExponent theta eps ≤ ((q + K * eps : ℝ) : EReal)) :
    refinedExceptionalUpperExponent theta ≤ (q : EReal) := by
  apply le_of_not_gt
  intro hbad
  obtain ⟨r, hqr, hr⟩ := EReal.exists_between_coe_real hbad
  have hqrReal : q < r := by exact_mod_cast hqr
  let eps : ℝ := min (epsZero / 2) ((r - q) / (2 * K))
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hepsLt : eps < epsZero := by
    dsimp only [eps]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hKeps : K * eps ≤ (r - q) / 2 := by
    have hmin : eps ≤ (r - q) / (2 * K) := by
      dsimp only [eps]
      exact min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hmin hK.le
    calc
      K * eps ≤ K * ((r - q) / (2 * K)) := hmul
      _ = (r - q) / 2 := by field_simp [hK.ne']
  have hqeps : q + K * eps < r := by linarith
  have hinf : refinedExceptionalUpperExponent theta ≤
      refinedFixedEpsilonExponent theta eps :=
    refinedExceptionalUpperExponent_le_fixedEpsilon heps
  have hlt : refinedExceptionalUpperExponent theta < (r : EReal) :=
    hinf.trans_lt ((hfixed eps heps hepsLt).trans_lt (by exact_mod_cast hqeps))
  exact (not_lt_of_ge hr.le) hlt

/-- Substitute any proved pointwise ordinary zero-density coefficient into
the exact second-moment candidate. -/
theorem ordinaryMomentExponent_le_of_exponent_upper
    {theta sigma a : ℝ} (htheta : theta < 1) (hsigma : sigma < 1)
    (hA : zeroDensityExponent sigma ≤ (a : EReal)) :
    ordinaryMomentExponent theta sigma ≤
      (((1 - theta) * (1 - sigma) * a + 2 * sigma - 1 : ℝ) : EReal) := by
  unfold ordinaryMomentExponent
  have hcoef : 0 ≤ (1 - theta) * (1 - sigma) := by positivity
  calc
    (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          zeroDensityExponent sigma + ((2 * sigma - 1 : ℝ) : EReal) ≤
        (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          (a : EReal) + ((2 * sigma - 1 : ℝ) : EReal) := by
      gcongr
    _ = (((1 - theta) * (1 - sigma) * a +
          2 * sigma - 1 : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

/-- Substitute any proved pointwise four-zero density-energy coefficient
into the exact fourth-moment candidate. -/
theorem additiveEnergyMomentExponent_le_of_exponent_upper
    {theta sigma a : ℝ} (htheta : theta < 1) (hsigma : sigma < 1)
    (hA : zeroAdditiveEnergyExponent sigma ≤ (a : EReal)) :
    additiveEnergyMomentExponent theta sigma ≤
      (((1 - theta) * (1 - sigma) * a + 4 * sigma - 3 : ℝ) : EReal) := by
  unfold additiveEnergyMomentExponent
  have hcoef : 0 ≤ (1 - theta) * (1 - sigma) := by positivity
  calc
    (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          zeroAdditiveEnergyExponent sigma + ((4 * sigma - 3 : ℝ) : EReal) ≤
        (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          (a : EReal) + ((4 * sigma - 3 : ℝ) : EReal) := by
      gcongr
    _ = (((1 - theta) * (1 - sigma) * a +
          4 * sigma - 3 : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

/-- The first Heath--Brown cell is below the first sample exponent. -/
theorem heathBrown_first_sample_cell
    {sigma eps : ℝ} (hsigmaUpper : sigma ≤ 2 / 3)
    (heps : 0 ≤ eps) :
    (1 - 17 / 30) * (1 - sigma) *
          ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) +
        4 * sigma - 3 ≤ 7 / 12 + 4 * eps := by
  have hOne : 1 - sigma ≠ 0 := by linarith
  have hTwo : 0 < 2 - sigma := by linarith
  have hcancel :
      (1 - sigma) *
          ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) =
        (10 - 11 * sigma) / (2 - sigma) := by
    field_simp [hOne]
  rw [mul_assoc, hcancel]
  have hquot : ((10 - 11 * sigma) / (2 - sigma)) * (2 - sigma) =
      10 - 11 * sigma := div_mul_cancel₀ _ hTwo.ne'
  nlinarith

/-- In the middle Heath--Brown cell, displacement by at most `eps` from
`sigma=7/10` costs at most `4 eps`. -/
theorem heathBrown_second_sample_cell
    {sigma eps : ℝ} (hsigmaUpper : sigma ≤ 7 / 10 + eps)
    (heps : 0 ≤ eps)
    (hepsUpper : eps ≤ 1 / 40) :
    (1 - 17 / 30) * (1 - sigma) *
          ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) +
        4 * sigma - 3 ≤ 7 / 12 + 4 * eps := by
  have hSigmaLt : sigma < 1 := by nlinarith
  have hOne : 1 - sigma ≠ 0 := by linarith
  have hFour : 0 < 4 - 2 * sigma := by linarith
  have hcancel :
      (1 - sigma) *
          ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) =
        (18 - 19 * sigma) / (4 - 2 * sigma) := by
    field_simp [hOne]
  rw [mul_assoc, hcancel]
  have hquot : ((18 - 19 * sigma) / (4 - 2 * sigma)) *
      (4 - 2 * sigma) = 18 - 19 * sigma :=
    div_mul_cancel₀ _ hFour.ne'
  nlinarith

/-- Admissibility and the actual frozen Guth--Maynard envelope confine the
first sample to an `eps`-neighbourhood of `sigma=7/10`. -/
theorem first_sample_admissible_sigma_upper
    {sigma eps : ℝ} (heps : 0 ≤ eps)
    (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaUpper : sigma < 1)
    (hadmissible : RefinedSigmaAdmissible (17 / 30) eps sigma) :
    sigma ≤ 7 / 10 + eps := by
  have hA := hadmissible.2.2.trans
    (zeroDensityExponent_le_guthMaynard hsigmaHalf hsigmaUpper.le)
  have hreal : 30 / 13 - eps ≤ 15 / (3 + 5 * sigma) := by
    have hrealSource : 1 / (1 - 17 / 30) - eps ≤
        15 / (3 + 5 * sigma) := by
      exact_mod_cast hA
    norm_num at hrealSource ⊢
    exact hrealSource
  have hden : 0 < 3 + 5 * sigma := by linarith
  rw [le_div_iff₀ hden] at hreal
  nlinarith

/-- Fixed-epsilon form of the first Gafni--Tao sample, conditional only on
the exact published Heath--Brown four-zero density-energy statement. -/
theorem first_sample_fixed_epsilon_bound
    (hHeathBrown : HeathBrownZeroEnergyBounds)
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
          (zeroAdditiveEnergyExponent_le_heathBrown_first hHeathBrown
            hsigmaHalf hFirst)).trans ?_)
      exact_mod_cast (heathBrown_first_sample_cell hFirst heps.le)
    · have hsigmaSecond : 2 / 3 < sigma := lt_of_not_ge hFirst
      refine (min_le_right _ _).trans
        ((additiveEnergyMomentExponent_le_of_exponent_upper
          (by norm_num) hsigma.2.1
          (zeroAdditiveEnergyExponent_le_heathBrown_second hHeathBrown
            hsigmaSecond hsigmaThreeQuarters)).trans ?_)
      exact_mod_cast (heathBrown_second_sample_cell
        hsigmaBound heps.le hepsUpper.le)

/-- The exact first sample exponent, with the source epsilon infimum left in
place until the preceding affine error is removed. -/
theorem refinedExceptionalUpperExponent_seventeen_thirtieths_le
    (hHeathBrown : HeathBrownZeroEnergyBounds) :
    refinedExceptionalUpperExponent (17 / 30) ≤ ((7 / 12 : ℝ) : EReal) := by
  apply refinedExceptionalUpperExponent_le_of_eventually_fixed_le
      (K := 4) (epsZero := 1 / 40)
  · norm_num
  · norm_num
  · intro eps heps hepsUpper
    exact first_sample_fixed_epsilon_bound hHeathBrown heps hepsUpper

/-- The publication-facing Ingham theorem in the coefficient normalization
used by the Gafni--Tao exponent formula. -/
theorem ingham_zeroDensityEnvelope {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    ZeroDensityEnvelope sigma (3 / (2 - sigma)) := by
  have hIngham :=
    RiemannZeta.GuthMaynard.inghamZeroDensity_published_native
      sigma hsigmaLower hsigmaUpper
  unfold ZeroDensityEnvelope EpsilonExponentBound
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hIngham

theorem zeroDensityExponent_le_ingham {sigma : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1) :
    zeroDensityExponent sigma ≤ ((3 / (2 - sigma) : ℝ) : EReal) :=
  zeroDensityExponent_le (ingham_zeroDensityEnvelope hsigmaLower hsigmaUpper)

/-- Pintz's coefficient-one cutoff makes every admissible sigma in the
second sample lie strictly below `23/24`. -/
theorem second_sample_admissible_sigma_le_twentyThree_twentyFour
    (hPintz : PintzTwentyThreeTwentyFourCutoff)
    {Delta eps sigma : ℝ} (hDelta : 0 < Delta)
    (hDeltaUpper : Delta ≤ 1 / 100) (hepsUpper : eps ≤ 1 / 100)
    (hsigmaUpper : sigma < 1)
    (hadmissible : RefinedSigmaAdmissible (2 / 15 + Delta) eps sigma) :
    sigma ≤ 23 / 24 := by
  by_contra hnot
  have hsigmaLower : 23 / 24 < sigma := lt_of_not_ge hnot
  have hA := hadmissible.2.2.trans
    (zeroDensityExponent_le_one_of_pintzCutoff hPintz
      hsigmaLower hsigmaUpper)
  have hreal : 1 / (1 - (2 / 15 + Delta)) - eps ≤ 1 := by
    exact_mod_cast hA
  have hden : 0 < 1 - (2 / 15 + Delta) := by nlinarith
  have hstrict : 1 < 1 / (1 - (2 / 15 + Delta)) - eps := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hden]
    nlinarith
  linarith

/-- Ingham's coefficient gives its largest second-sample contribution at
the common endpoint `sigma=7/10`. -/
theorem ingham_second_sample_cell
    {Delta sigma eps : ℝ} (hDelta : 0 ≤ Delta)
    (hsigmaUpper : sigma ≤ 7 / 10)
    (heps : 0 ≤ eps) :
    (1 - (2 / 15 + Delta)) * (1 - sigma) * (3 / (2 - sigma)) +
        2 * sigma - 1 ≤ 1 - 9 * Delta / 13 + 4 * eps := by
  have hden : 0 < 2 - sigma := by linarith
  have hfactor :
      (1 - 9 * Delta / 13 + 4 * eps) -
          ((1 - (2 / 15 + Delta)) * (1 - sigma) *
            (3 / (2 - sigma)) + 2 * sigma - 1) =
        (-(10 * sigma - 7) *
          ((1 - sigma) / 5 + 3 * Delta / 13) +
            4 * eps * (2 - sigma)) / (2 - sigma) := by
    field_simp [hden.ne']
    ring
  rw [← sub_nonneg, hfactor]
  apply div_nonneg
  · have hFirst : 0 ≤ -(10 * sigma - 7) := by linarith
    have hSecond : 0 ≤ (1 - sigma) / 5 + 3 * Delta / 13 := by
      have hSigmaGap : 0 ≤ 1 - sigma := by linarith
      positivity
    have hEps : 0 ≤ 4 * eps * (2 - sigma) := by positivity
    positivity
  · exact hden.le

/-- On the Guth--Maynard cell remaining after Pintz's cutoff, the ordinary
candidate is bounded by the second sample exponent. -/
theorem guthMaynard_second_sample_cell
    {Delta sigma eps : ℝ} (hDeltaUpper : Delta ≤ 1 / 100)
    (hsigmaLower : 7 / 10 ≤ sigma) (hsigmaUpper : sigma ≤ 23 / 24)
    (heps : 0 ≤ eps) :
    (1 - (2 / 15 + Delta)) * (1 - sigma) *
          (15 / (3 + 5 * sigma)) +
        2 * sigma - 1 ≤ 1 - 9 * Delta / 13 + 4 * eps := by
  have hden : 0 < 3 + 5 * sigma := by linarith
  have hmargin : 0 ≤ (1 - sigma) - 24 * Delta / 13 := by
    nlinarith
  have hfactor :
      (1 - 9 * Delta / 13 + 4 * eps) -
          ((1 - (2 / 15 + Delta)) * (1 - sigma) *
            (15 / (3 + 5 * sigma)) + 2 * sigma - 1) =
        ((10 * sigma - 7) * ((1 - sigma) - 24 * Delta / 13) +
          4 * eps * (3 + 5 * sigma)) / (3 + 5 * sigma) := by
    field_simp [hden.ne']
    ring
  rw [← sub_nonneg, hfactor]
  apply div_nonneg
  · have hFirst : 0 ≤ 10 * sigma - 7 := by linarith
    have hEps : 0 ≤ 4 * eps * (3 + 5 * sigma) := by positivity
    positivity
  · exact hden.le

/-- Fixed-epsilon form of the second Gafni--Tao sample, conditional only on
the exact Pintz cutoff theorem. -/
theorem second_sample_fixed_epsilon_bound
    (hPintz : PintzTwentyThreeTwentyFourCutoff)
    {Delta eps : ℝ} (hDelta : 0 < Delta)
    (hDeltaUpper : Delta ≤ 1 / 100)
    (heps : 0 < eps) (hepsUpper : eps < 1 / 100) :
    refinedFixedEpsilonExponent (2 / 15 + Delta) eps ≤
      ((1 - 9 * Delta / 13 + 4 * eps : ℝ) : EReal) := by
  unfold refinedFixedEpsilonExponent
  apply sSup_le
  rintro x ⟨sigma, hsigma, rfl⟩
  have hthetaUpper : 2 / 15 + Delta < 1 := by nlinarith
  by_cases hLower : sigma ≤ 1 / 2
  · refine (min_le_left _ _).trans ?_
    exact (ordinaryMomentExponent_le_one_sub_theta_of_lowerHalf
      hthetaUpper hsigma.1 hLower).trans (by
        exact_mod_cast (show 1 - (2 / 15 + Delta) ≤
            1 - 9 * Delta / 13 + 4 * eps by nlinarith))
  · have hsigmaHalf : 1 / 2 ≤ sigma := (lt_of_not_ge hLower).le
    have hsigmaPintz : sigma ≤ 23 / 24 :=
      second_sample_admissible_sigma_le_twentyThree_twentyFour hPintz
        hDelta hDeltaUpper hepsUpper.le hsigma.2.1 hsigma
    by_cases hIngham : sigma ≤ 7 / 10
    · refine (min_le_left _ _).trans
        ((ordinaryMomentExponent_le_of_exponent_upper hthetaUpper
          hsigma.2.1 (zeroDensityExponent_le_ingham hsigmaHalf
            hsigma.2.1.le)).trans ?_)
      exact_mod_cast (ingham_second_sample_cell hDelta.le
        hIngham heps.le)
    · have hsigmaGM : 7 / 10 ≤ sigma := (lt_of_not_ge hIngham).le
      refine (min_le_left _ _).trans
        ((ordinaryMomentExponent_le_of_exponent_upper hthetaUpper
          hsigma.2.1 (zeroDensityExponent_le_guthMaynard hsigmaHalf
            hsigma.2.1.le)).trans ?_)
      exact_mod_cast (guthMaynard_second_sample_cell hDeltaUpper
        hsigmaGM hsigmaPintz heps.le)

/-- The exact second sample exponent on an explicit sufficiently-small
range, again with no continuity assumption on the density exponent. -/
theorem refinedExceptionalUpperExponent_two_fifteenths_add_le
    (hPintz : PintzTwentyThreeTwentyFourCutoff)
    {Delta : ℝ} (hDelta : 0 < Delta) (hDeltaUpper : Delta ≤ 1 / 100) :
    refinedExceptionalUpperExponent (2 / 15 + Delta) ≤
      ((1 - 9 * Delta / 13 : ℝ) : EReal) := by
  apply refinedExceptionalUpperExponent_le_of_eventually_fixed_le
      (K := 4) (epsZero := 1 / 100)
  · norm_num
  · norm_num
  · intro eps heps hepsUpper
    exact second_sample_fixed_epsilon_bound hPintz hDelta hDeltaUpper
      heps hepsUpper

#print axioms refinedExceptionalUpperExponent_le_of_eventually_fixed_le
#print axioms refinedExceptionalUpperExponent_seventeen_thirtieths_le
#print axioms refinedExceptionalUpperExponent_two_fifteenths_add_le

end

end GafniTao
