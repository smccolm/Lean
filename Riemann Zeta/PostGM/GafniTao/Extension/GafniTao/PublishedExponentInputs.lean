import GafniTao.NativeTheorems

/-!
# Published exponent inputs used in Gafni--Tao Section 3

This file fixes the exact source-facing statements that remain to be proved
from Pintz and Heath--Brown.  They are predicates on the genuine
multiplicity-weighted zero counts from `GafniTao.ZeroEnergy`; no independent
exponent function or numerical certificate is introduced.
-/

namespace GafniTao

/-- The right endpoint of the first Pintz cell in the Gafni--Tao/ANTEDB
ordinary zero-density table. -/
noncomputable def pintzFirstSegmentUpper : ℝ := 2211487 / 2274732

/-- Pintz's first displayed near-one zero-density cell, in the normalization
`N(sigma,T) <= T^(A(sigma)(1-sigma)+epsilon)`.  The lower endpoint is closed
and the upper endpoint is half-open, exactly as in the source table. -/
def PintzFirstDensitySegment : Prop :=
  ∀ sigma : ℝ, 23 / 24 ≤ sigma → sigma < pintzFirstSegmentUpper →
    ZeroDensityEnvelope sigma (3 / (24 * sigma - 20))

/-- The consequence of Pintz's complete near-one series used in the second
sample calculation: throughout the open strip to the right of `23/24`, the
ordinary density coefficient is at most one.  The strict endpoint is
essential: Pintz's `k,ell` cells change at `eta=1/24`, while the Gafni--Tao
consumer only concludes `sigma <= 23/24`. -/
def PintzTwentyThreeTwentyFourCutoff : Prop :=
  ∀ sigma : ℝ, 23 / 24 < sigma → sigma < 1 →
    ZeroDensityEnvelope sigma 1

/-- Heath--Brown's three classical four-zero density-energy cells, with the
endpoint convention stated after Gafni--Tao Theorem 1.3. -/
def HeathBrownZeroEnergyBounds : Prop :=
  (∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ 2 / 3 →
    ZeroAdditiveEnergyEnvelope sigma
      ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma)))) ∧
  (∀ sigma : ℝ, 2 / 3 < sigma → sigma ≤ 3 / 4 →
    ZeroAdditiveEnergyEnvelope sigma
      ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma)))) ∧
  (∀ sigma : ℝ, 3 / 4 < sigma → sigma < 1 →
    ZeroAdditiveEnergyEnvelope sigma (12 / (4 * sigma - 1)))

theorem zeroDensityExponent_le_pintzFirstSegment
    (hPintz : PintzFirstDensitySegment)
    {sigma : ℝ} (hsigmaLower : 23 / 24 ≤ sigma)
    (hsigmaUpper : sigma < pintzFirstSegmentUpper) :
    zeroDensityExponent sigma ≤
      ((3 / (24 * sigma - 20) : ℝ) : EReal) :=
  zeroDensityExponent_le (hPintz sigma hsigmaLower hsigmaUpper)

theorem zeroDensityExponent_le_one_of_pintzCutoff
    (hPintz : PintzTwentyThreeTwentyFourCutoff)
    {sigma : ℝ} (hsigmaLower : 23 / 24 < sigma)
    (hsigmaUpper : sigma < 1) :
    zeroDensityExponent sigma ≤ ((1 : ℝ) : EReal) :=
  zeroDensityExponent_le (hPintz sigma hsigmaLower hsigmaUpper)

theorem zeroAdditiveEnergyExponent_le_heathBrown_first
    (hHeathBrown : HeathBrownZeroEnergyBounds)
    {sigma : ℝ} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 2 / 3) :
    zeroAdditiveEnergyExponent sigma ≤
      (((10 - 11 * sigma) /
        ((2 - sigma) * (1 - sigma)) : ℝ) : EReal) :=
  zeroAdditiveEnergyExponent_le
    (hHeathBrown.1 sigma hsigmaLower hsigmaUpper)

theorem zeroAdditiveEnergyExponent_le_heathBrown_second
    (hHeathBrown : HeathBrownZeroEnergyBounds)
    {sigma : ℝ} (hsigmaLower : 2 / 3 < sigma)
    (hsigmaUpper : sigma ≤ 3 / 4) :
    zeroAdditiveEnergyExponent sigma ≤
      (((18 - 19 * sigma) /
        ((4 - 2 * sigma) * (1 - sigma)) : ℝ) : EReal) :=
  zeroAdditiveEnergyExponent_le
    (hHeathBrown.2.1 sigma hsigmaLower hsigmaUpper)

theorem zeroAdditiveEnergyExponent_le_heathBrown_third
    (hHeathBrown : HeathBrownZeroEnergyBounds)
    {sigma : ℝ} (hsigmaLower : 3 / 4 < sigma)
    (hsigmaUpper : sigma < 1) :
    zeroAdditiveEnergyExponent sigma ≤
      ((12 / (4 * sigma - 1) : ℝ) : EReal) :=
  zeroAdditiveEnergyExponent_le
    (hHeathBrown.2.2 sigma hsigmaLower hsigmaUpper)

/-- At the sample endpoint, the middle Heath--Brown coefficient is exactly
`235/39`. -/
theorem heathBrown_second_at_seven_tenths :
    ((18 - 19 * (7 / 10 : ℝ)) /
      ((4 - 2 * (7 / 10 : ℝ)) * (1 - (7 / 10 : ℝ)))) =
        235 / 39 := by
  norm_num

/-- The four-zero exponent appearing in the first Gafni--Tao sample is
exactly `7/12`. -/
theorem gafniTao_first_sample_arithmetic :
    (1 - (17 / 30 : ℝ)) * (1 - 7 / 10) * (235 / 39) +
        4 * (7 / 10) - 3 = 7 / 12 := by
  norm_num

/-- The ordinary exponent at `sigma=7/10` in the second sample. -/
theorem gafniTao_second_sample_arithmetic (Delta : ℝ) :
    (1 - (2 / 15 + Delta)) * (1 - 7 / 10) * (30 / 13) +
        2 * (7 / 10) - 1 = 1 - 9 * Delta / 13 := by
  ring

#print axioms zeroDensityExponent_le_pintzFirstSegment
#print axioms zeroAdditiveEnergyExponent_le_heathBrown_second
#print axioms gafniTao_first_sample_arithmetic

end GafniTao
