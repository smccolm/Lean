import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.InghamBound
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.TypeIIZeros
import RiemannZeta.GuthMaynard.DyadicTransfer
import RiemannZeta.GuthMaynard.CentralTypeI

namespace RiemannZeta.GuthMaynard

/-- The exact Type-I/residual partition turns the two central slab bounds into
the total positive-slab estimate. -/
theorem central_positive_slab_of_typeI_and_residual
    (hTypeI : TypeIPositiveSlabBoundProp)
    (hResidual : ResidualZeroBoundProp)
    (σ : ℝ) (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ final_exponent σ) := by
  have hType := hTypeI σ hσLower hσUpper
  have hResidualRaw := hResidual σ hσLower hσUpper
  have hResidualTarget : EpsilonPowerBound
      (fun T => (residualZeroCount σ T (2 * T) T : ℝ))
      (fun T => T ^ final_exponent σ) := by
    apply EpsilonPowerBound_mono _ _ _ hResidualRaw
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (residual_exponent_le_final σ hσLower hσUpper)
  apply EpsilonPowerBound.congr_left (hType.add hResidualTarget)
  intro T
  rw [← Nat.cast_add]
  congr 1
  exact typeI_add_residual_eq_total σ T (2 * T) T

/-- The high-sigma part of the target follows from the explicit Huxley input. -/
theorem high_sigma_of_huxley
    (hHuxley : HuxleyZeroDensity (fun σ T => N σ T))
    (σ : ℝ) (hσLower : 4 / 5 ≤ σ) (hσUpper : σ ≤ 1) :
    EpsilonPowerBound
      (fun T => (N σ T : ℝ))
      (fun T => T ^ final_exponent σ) := by
  have hRaw := hHuxley σ (by linarith) hσUpper
  apply EpsilonPowerBound_mono _ _ _ hRaw
  intro T hT
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
    (huxley_exponent_le_final σ hσLower hσUpper)

/-- Primitive-input conditional transfer for Section 13.1. Every intermediate
Type-I, Type-II, powered-coefficient, extraction, dyadic, and high-sigma
proposition is derived internally from its individually named source input. -/
theorem conditionalZeroDensityTransfer
    (hLargeValues : GuthMaynardLargeValues)
    (hMeanValue : MontgomeryMeanValue)
    (hBeta : DetectorBetaShiftProp)
    (hLocal : LocalZeroMultiplicityBoundProp)
    (hDivisor : DivisorCountBoundProp)
    (hFactorization : FactorizationCountBoundProp)
    (hCover : TypeIContourTypeIICoverProp)
    (hReduction : TypeIIFourthMomentReductionProp dyadicZetaZeros
      (analyticVanishingOrder riemannZeta) zetaIsContourTypeII)
    (hMoment : TwistedZetaFourthMomentProp)
    (hHuxley : HuxleyZeroDensity (fun σ T => N σ T)) :
    GuthMaynardZeroDensity (fun σ T => N σ T) := by
  have hExtract := extractSeparated_of_beta_shift_and_local_multiplicity hBeta hLocal
  have hPow := powCoeff_bound_of_divisor_and_factorization hDivisor hFactorization
  have hTypeI := typeIPositiveSlabBound_of_section13_inputs
    hLargeValues hMeanValue hExtract hPow
  have hResidual := residualZeroBound_of_contourTypeII_reduction_and_fourthMoment
    hCover hReduction hMoment
  intro σ hσLower hσUpper
  by_cases hCentral : σ ≤ 4 / 5
  · exact dyadicToGlobalZeroCount σ (final_exponent σ)
      (final_exponent_nonneg σ hσLower hCentral)
      (central_positive_slab_of_typeI_and_residual
        hTypeI hResidual σ hσLower hCentral)
  · exact high_sigma_of_huxley hHuxley σ (by linarith) hσUpper

end RiemannZeta.GuthMaynard
